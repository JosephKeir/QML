import QML.QML_v12m_BRetOutC

/-!
# QML v12m — B's canonical model: `ret` membership ⇒ truth at witnessed companion shapes

The witnessed shapes `N × ◇Z` of item 6 (docs §11.21), on the plain leg, for every T:

* the packing at a witnessed shape, the possible part carried along
  (`holeAt_packG_unpackGW_slot`, `holeAt_packG_unpackGW_val`, `retS_packGW`);
* ⭐`BData.RetOutDC`, ⭐`BData.sat_retDC_of_mem` and ⭐`BData.sat_retS_wit_of_memC`;
* ⭐`bdataS_retOutDC`: name the missing companions (`ret_comps_namedW`), reorder (`subC`), alias
  the tuple `arrB W` (`y`), the possible part's value (`z`) and a unit (`o`, after `y`), move the
  value to `⟨unarrT y, z⟩` and take the back-witness child (`lretDC`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## Packing at a witnessed shape -/

/-- Packing then unpacking at a witnessed shape, on the slot. -/
theorem holeAt_packG_unpackGW_slot (N : NShape) (Z : VarType) :
    (⟨_, Term.holeAt (ShapeMap.liftObj (σ := σ) (.wit N Z) (packG N)).2
        (ShapeMap.liftObj (σ := σ) (.wit N.packed Z) (unpackG N)).2⟩ :
      Σ e, Term σ (Ctx.empty.insert (.bnd 0) (RShape.wit N Z).ty) (RShape.wit N Z).ty e) =
      ⟨_, Term.eta (.root (.bnd 0)) (RShape.wit N Z).ty (Ctx.ref_insert_root _ _ _)⟩ := by
  dsimp only [ShapeMap.liftObj]
  refine sig_pair ?_ (Term.holeAt_pair_snd _ _)
  refine (Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
    (Term.holeAt_pair_fst _ _) _).trans ?_)
  exact holeAt_packG_unpackG N _

omit [ModalSys.NoFour] in
/-- ⭐Unpacking packed values at a witnessed shape is the identity. -/
theorem holeAt_packG_unpackGW_val (N : NShape) (Z : VarType) : {Γ : Ctx} →
    {c : Ann (RShape.wit N Z).flat} → (w : Term σ Γ (RShape.wit N Z).flat c) →
    (⟨_, Term.holeAt (Term.holeAt w (ShapeMap.liftVal (σ := σ) (.wit N Z) (packG N)).2)
        (ShapeMap.liftVal (σ := σ) (.wit N.packed Z) (unpackG N)).2⟩ :
      Σ e, Term σ Γ (RShape.wit N Z).flat e) = ⟨c, w⟩
  | _, _, .pair w₁ w₂ =>
      (Term.holeAt_congr_sig (holeAt_liftVal_wit (packG N) w₁ w₂) _).trans
        ((holeAt_liftVal_wit (unpackG N) _ w₂).trans
          (sig_pair (holeAt_packG_unpackG_val N w₁) rfl))

/-- ⭐A returning possibility at a witnessed shape is one at its packed shape: `ret_map` along
    `packG`, the possible part carried along. -/
def retS_packGW (hS : ModalSys.BStrong = true) {Γ : Ctx} [Γ.NoSlots] (O : OutLeg Γ)
    {Δ : List (WFF σ Γ 0)} {N : NShape} {Z : VarType} {a : Ann (RShape.wit N Z).flat}
    (t : Term σ Γ (RShape.wit N Z).flat a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit N Z).ty) 1)
    (p : Proof σ Γ Δ (O.retS hS (.wit N Z) t Φ)) :
    Proof σ Γ Δ (O.retS hS (.wit N.packed Z)
      (Term.holeRead t (ShapeMap.liftVal (.wit N Z) (packG N)).2)
      (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
        (ShapeMap.liftObj (.wit N.packed Z) (unpackG N)).2) Φ)) := by
  refine Proof.ret_map hS O (S := .wit N Z) (packG N) t _ (Proof.conv ?_ p)
  change O.retS hS (.wit N Z) t Φ = O.retS hS (.wit N Z) t (WFF.bodyRepl _ (WFF.bodyRepl _ Φ))
  rw [WFF.bodyRepl_bodyRepl, WFF.bodyRepl_congr (sig_mono _ (holeAt_packG_unpackGW_slot N Z))]
  exact congrArg (O.retS hS (.wit N Z) t) (WFF.bodyRepl_eta Φ).symm

omit [ModalSys.NoFour] in
/-- `subC` lifted to a witnessed shape keeps the object. -/
theorem liftObj_subC_wit (A : VarType) (cs cs' : List (List Step)) (h : A.CompOk cs)
    (h' : A.CompOk cs') (hsub : ∀ p ∈ cs', p ∈ cs) (Z : VarType) :
    (⟨_, (ShapeMap.liftObj (σ := σ) (.wit (.boxC A cs h) Z)
        (ShapeMap.subC A cs cs' h h' hsub)).2⟩ :
      Σ e, Term σ (Ctx.empty.insert (.bnd 0) (RShape.wit (.boxC A cs h) Z).ty)
        (RShape.wit (.boxC A cs h) Z).ty e) =
      ⟨_, Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root _ _ _)⟩ :=
  sig_pair (Term.holeAt_eta_root _) rfl

namespace BData

variable {B : BData σ}

/-- ⭐**Returning successors at witnessed companion shapes** (plain leg): a returning possibility
    valued at a pair has an arrow `s → k`, a term `g` of `k`'s `□` view and a witness `e` of `k`
    whose way home is the witness edge back, with `Φ(⟨□g, e⟩)` at `k`; `g`'s value with companions
    read home is `Ind` to the first value (as in `RetOutC`), `e`'s content there to the second.
    The limit of a strong chain has it (`bdataS_retOutDC`). -/
def RetOutDC (B : BData σ) (hS : ModalSys.BStrong = true) : Prop :=
  ∀ {s : B.W} {i : ℕ} {A Z : VarType} {cs : List (List Step)} {h : A.CompOk cs}
    {a₁ : Ann (A.compsFlat cs)} {a₂ : Ann Z}
    (t₁ : Term σ ((B.w s).ctx i) (A.compsFlat cs) a₁) (t₂ : Term σ ((B.w s).ctx i) Z a₂)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) (RShape.wit (.boxC A cs h) Z).ty) 1),
    WFF.retS hS (.wit (.boxC A cs h) Z) (Term.pair t₁ t₂) Φ ∈ (B.w s).M i →
      ∃ (k : B.W) (hR : B.R s k) (j : ℕ) (hj : B.stg s k i ≤ j) (b : Ann A)
        (g : Term σ ((B.w k).ctx j).boxIn A b) (e : VarSymb)
        (he : ((B.w k).ctx j).ref e = some (.VTypeDia Z)) (hk : B.kd k s = some (e, Z)),
        readArrow ((B.imgOk hR i).mono ((B.w k).le hj))
          (Term.pair (Term.boxtm g) (Term.eta e (.VTypeDia Z) he)) Φ ∈ (B.w k).M j ∧
        B.Ind (B.toDom (A.compsFlat cs) s (B.rden s (B.stg k s j) (Ctx.Le.refl _)
            (Term.subst (arrowIdx (B.img k s)) (arrowS σ _ (B.img k s))
              (ok_arrowS (B.imgOk (B.symm hR) j)) (coh_arrowS (B.imgOk (B.symm hR) j))
              (compsVal g cs h).2)) (definable_rden _ _))
          (B.toDom (A.compsFlat cs) s (B.rden s i (Ctx.Le.refl _) t₁) (definable_rden _ _)) ∧
        B.Ind (B.toDom Z s (B.rden s (B.stg k s j) (Ctx.Le.refl _)
            (Term.eta (.root (.free (B.cx k s e))) Z (B.hcx hk j))) (definable_rden _ _))
          (B.toDom Z s (B.rden s i (Ctx.Le.refl _) t₂) (definable_rden _ _))

/-- ⭐⭐**`ret` at a witnessed companion shape, membership ⇒ truth** (plain leg): the necessary
    part as in `sat_retC_of_mem`, the possible part along the witness edge home
    (`posEval_eta_home`). -/
theorem sat_retDC_of_mem (hS : ModalSys.BStrong = true) (hRO : B.RetOutDC hS) {s : B.W} {i : ℕ}
    {A Z : VarType} {cs : List (List Step)} {h : A.CompOk cs} {a₁ : Ann (A.compsFlat cs)}
    {a₂ : Ann Z} (t₁ : Term σ ((B.w s).ctx i) (A.compsFlat cs) a₁)
    (t₂ : Term σ ((B.w s).ctx i) Z a₂)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) (RShape.wit (.boxC A cs h) Z).ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0), φ.size < Φ.size + 1 →
      (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (hm : (WFF.retS hS (.wit (.boxC A cs h) Z) (Term.pair t₁ t₂) Φ : WFF σ _ 0) ∈ (B.w s).M i) :
    B.model.sat (B.canonEnv s i)
      (WFF.retS hS (.wit (.boxC A cs h) Z) (Term.pair t₁ t₂) Φ : WFF σ _ 0) := by
  obtain ⟨k, hR, j, hj, b, g, e, he, hk, hmem, hInd₁, hInd₂⟩ := hRO t₁ t₂ Φ hm
  have hsat := (IH k j _ (by unfold readArrow; rw [WFF.size_subst]; omega)).mpr hmem
  rw [sat_readArrow, ← boxPush_canon_at s i ⟨k, ⟨Or.inl hR⟩⟩ hR hj] at hsat
  refine ⟨⟨k, ⟨Or.inl hR⟩⟩, _, hsat, Or.inl (B.symm hR), ?_, ?_⟩
  · change B.model.compsBack A cs (Model.interp (B.canonEnv k j) (Term.boxtm g)) _ _
    refine compsBack_of_ind A _ _ cs h _ ?_
    rw [← interp_canon _ (Model.Env.Agree.refl' _), ← interp_canon t₁ (Model.Env.Agree.refl' _),
      Model.interp_subst _ _ _ (Ctx.noProjLast_boxIn _),
      ← boxPush_canon_at k _ ⟨s, ⟨Or.inl (B.symm hR)⟩⟩ (B.symm hR) le_rfl,
      Model.interp_compsVal] at hInd₁
    exact hInd₁
  · have := posEval_eta_home he hk hInd₂
    rw [← interp_canon t₂ (Model.Env.Agree.refl' _)] at this
    exact this

/-- ⭐⭐**`ret`, membership ⇒ truth at every witnessed shape** (plain leg; any T): pack the
    necessary part (`retS_packGW`), take the truth there (`sat_retDC_of_mem`), and map it back
    (`sat_ret_map` along `unpackG`, `indCongr`, `holeAt_packG_unpackGW_val`). -/
theorem sat_retS_wit_of_memC (hS : ModalSys.BStrong = true) (hRO : B.RetOutDC hS) {s : B.W}
    {i : ℕ} {N : NShape} {Z : VarType} {a : Ann (RShape.wit N Z).flat}
    (t : Term σ ((B.w s).ctx i) (RShape.wit N Z).flat a)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) (RShape.wit N Z).ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0).size →
        (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (h : (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0) ∈ (B.w s).M i) :
    B.model.sat (B.canonEnv s i) (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0) := by
  have hsz : (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0).size =
      Φ.size + (RShape.wit N Z).flat.eqRecSize + 1 := rfl
  have hp := BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by
    rw [List.mem_singleton.mp hψ]; exact h)
    ⟨retS_packGW hS .nec t Φ (Proof.lookup List.mem_cons_self)⟩
  obtain ⟨_, _, t₁, t₂, ht⟩ := Term.exists_pair
    (Term.holeRead t (ShapeMap.liftVal (σ := σ) (.wit N Z) (packG N)).2)
  have hp' := (congrArg (· ∈ (B.w s).M i)
    (OutLeg.retS_congr hS .nec (.wit N.packed Z) ht rfl)).mp hp
  have hsat := sat_retDC_of_mem hS hRO t₁ t₂ _ (fun s' K φ hφ => IH s' K φ (by
    unfold WFF.bodyRepl at hφ
    rw [WFF.size_subst] at hφ
    omega)) hp'
  have hsat' := (congrArg (B.model.sat _)
    (OutLeg.retS_congr hS .nec (.wit N.packed Z) ht rfl)).mpr hsat
  have hb := Model.sat_ret_map (B.canonEnv s i) (noProjLast s i) indCongr hS .nec
    (S := .wit N.packed Z) (unpackG N) _ Φ hsat'
  refine (congrArg (B.model.sat _) (OutLeg.retS_congr hS .nec (.wit N Z) ?_ rfl)).mp hb
  rw [Term.holeRead_eq_holeAt, Term.holeRead_eq_holeAt]
  exact holeAt_packG_unpackGW_val N Z t

/-- ⭐**Returning successors along a witness at witnessed companion shapes**: as `RetOutDC`,
    along an arrow of `y`'s extent.  The limit of a strong chain has it (`bdataS_retOutXDC`). -/
def RetOutXDC (B : BData σ) (hS : ModalSys.BStrong = true) : Prop :=
  ∀ {s : B.W} {i : ℕ} {y : VarSymb} {Y : VarType}
    (hy : ((B.w s).ctx i).ref y = some (.VTypeDia Y)) {A Z : VarType} {cs : List (List Step)}
    {h : A.CompOk cs} {a₁ : Ann (A.compsFlat cs)} {a₂ : Ann Z}
    (t₁ : Term σ ((B.w s).ctx i) (A.compsFlat cs) a₁) (t₂ : Term σ ((B.w s).ctx i) Z a₂)
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) (RShape.wit (.boxC A cs h) Z).ty) 1),
    (OutLeg.pos y ⟨Y, hy⟩ : OutLeg ((B.w s).ctx i)).retS hS (.wit (.boxC A cs h) Z)
        (Term.pair t₁ t₂) Φ ∈ (B.w s).M i →
      ∃ (k : B.W) (hk : B.kd s k = some (y, Y)) (j : ℕ) (hj : B.stg s k i ≤ j) (b : Ann A)
        (g : Term σ ((B.w k).ctx j).boxIn A b) (e : VarSymb)
        (he : ((B.w k).ctx j).ref e = some (.VTypeDia Z)) (hke : B.kd k s = some (e, Z)),
        readArrowX ((B.imgOk (B.kdR hk) i).mono ((B.w k).le hj)) hy
            (((B.w k).le hj).ref (B.hcx hk i))
            (Term.pair (Term.boxtm g) (Term.eta e (.VTypeDia Z) he)) Φ ∈ (B.w k).M j ∧
        B.Ind (B.toDom (A.compsFlat cs) s (B.rden s (B.stg k s j) (Ctx.Le.refl _)
            (Term.subst (arrowIdx (B.img k s)) (arrowS σ _ (B.img k s))
              (ok_arrowS (B.imgOk (B.symm (B.kdR hk)) j))
              (coh_arrowS (B.imgOk (B.symm (B.kdR hk)) j)) (compsVal g cs h).2))
            (definable_rden _ _))
          (B.toDom (A.compsFlat cs) s (B.rden s i (Ctx.Le.refl _) t₁) (definable_rden _ _)) ∧
        B.Ind (B.toDom Z s (B.rden s (B.stg k s j) (Ctx.Le.refl _)
            (Term.eta (.root (.free (B.cx k s e))) Z (B.hcx hke j))) (definable_rden _ _))
          (B.toDom Z s (B.rden s i (Ctx.Le.refl _) t₂) (definable_rden _ _))

/-- ⭐⭐**`ret` along a witness at a witnessed companion shape, membership ⇒ truth**: as
    `sat_retDC_of_mem`, along an arrow of `y`'s extent (`diaPush_canon_at`). -/
theorem sat_retxDC_of_mem (hS : ModalSys.BStrong = true) (hRX : B.RetOutXDC hS) {s : B.W}
    {i : ℕ} {y : VarSymb} {Y : VarType} (hY : ((B.w s).ctx i).ref y = some (.VTypeDia Y))
    {A Z : VarType} {cs : List (List Step)} {h : A.CompOk cs} {a₁ : Ann (A.compsFlat cs)}
    {a₂ : Ann Z} (t₁ : Term σ ((B.w s).ctx i) (A.compsFlat cs) a₁)
    (t₂ : Term σ ((B.w s).ctx i) Z a₂)
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) (RShape.wit (.boxC A cs h) Z).ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0), φ.size < Φ.size + 1 →
      (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (hm : ((OutLeg.pos y ⟨Y, hY⟩ : OutLeg ((B.w s).ctx i)).retS hS (.wit (.boxC A cs h) Z)
      (Term.pair t₁ t₂) Φ : WFF σ _ 0) ∈ (B.w s).M i) :
    B.model.sat (B.canonEnv s i)
      ((OutLeg.pos y ⟨Y, hY⟩ : OutLeg ((B.w s).ctx i)).retS hS (.wit (.boxC A cs h) Z)
        (Term.pair t₁ t₂) Φ : WFF σ _ 0) := by
  obtain ⟨k, hk, j, hj, b, g, e, he, hke, hmem, hInd₁, hInd₂⟩ := hRX hY t₁ t₂ Φ hm
  have hR := B.kdR hk
  have hsat := (IH k j _ (by unfold readArrowX; rw [WFF.size_subst]; omega)).mpr hmem
  have ha : (⟨k, ⟨Or.inl hR⟩⟩ : B.Acc s) ∈
      (B.model.posEval ((B.canonEnv s i).ref y hY)).1 := by
    rw [canonEnv_extent s i hY]
    exact Or.inl ⟨Y, B.kd_lb hk⟩
  rw [sat_readArrowX, ← diaPush_canon_at s i hY ⟨⟨k, ⟨Or.inl hR⟩⟩, ha⟩ (B.kd_lb hk) hj]
    at hsat
  refine ⟨Y, hY, ⟨⟨k, ⟨Or.inl hR⟩⟩, ha⟩, _, hsat, Or.inl (B.symm hR), ?_, ?_⟩
  · change B.model.compsBack A cs (Model.interp (B.canonEnv k j) (Term.boxtm g)) _ _
    refine compsBack_of_ind A _ _ cs h _ ?_
    rw [← interp_canon _ (Model.Env.Agree.refl' _), ← interp_canon t₁ (Model.Env.Agree.refl' _),
      Model.interp_subst _ _ _ (Ctx.noProjLast_boxIn _),
      ← boxPush_canon_at k _ ⟨s, ⟨Or.inl (B.symm hR)⟩⟩ (B.symm hR) le_rfl,
      Model.interp_compsVal] at hInd₁
    exact hInd₁
  · have := posEval_eta_home he hke hInd₂
    rw [← interp_canon t₂ (Model.Env.Agree.refl' _)] at this
    exact this

/-- ⭐⭐**`ret` along a witness, membership ⇒ truth at every witnessed shape** (any T): as
    `sat_retS_wit_of_memC`, along `y` (`RetOutXDC`).  The induction hypothesis is asked only
    below the body's size, so that rows 3–4 can reach this case from smaller atoms. -/
theorem sat_retxS_wit_of_memC (hS : ModalSys.BStrong = true) (hRX : B.RetOutXDC hS) {s : B.W}
    {i : ℕ} {y : VarSymb} (hy : ∃ Y, ((B.w s).ctx i).ref y = some (.VTypeDia Y)) {N : NShape}
    {Z : VarType} {a : Ann (RShape.wit N Z).flat}
    (t : Term σ ((B.w s).ctx i) (RShape.wit N Z).flat a)
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) (RShape.wit N Z).ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < Φ.size + 1 → (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (h : ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.wit N Z) t Φ : WFF σ _ 0) ∈
      (B.w s).M i) :
    B.model.sat (B.canonEnv s i)
      ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.wit N Z) t Φ : WFF σ _ 0) := by
  obtain ⟨Y, hY⟩ := hy
  have hp := BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by
    rw [List.mem_singleton.mp hψ]; exact h)
    ⟨retS_packGW hS (.pos y ⟨Y, hY⟩) t Φ (Proof.lookup List.mem_cons_self)⟩
  obtain ⟨_, _, t₁, t₂, ht⟩ := Term.exists_pair
    (Term.holeRead t (ShapeMap.liftVal (σ := σ) (.wit N Z) (packG N)).2)
  have hp' := (congrArg (· ∈ (B.w s).M i)
    (OutLeg.retS_congr hS (.pos y ⟨Y, hY⟩) (.wit N.packed Z) ht rfl)).mp hp
  have hsat := sat_retxDC_of_mem hS hRX hY t₁ t₂ _ (fun s' K φ hφ => IH s' K φ (by
    unfold WFF.bodyRepl at hφ
    rw [WFF.size_subst] at hφ
    omega)) hp'
  have hsat' := (congrArg (B.model.sat _)
    (OutLeg.retS_congr hS (.pos y ⟨Y, hY⟩) (.wit N.packed Z) ht rfl)).mpr hsat
  have hb := Model.sat_ret_map (B.canonEnv s i) (noProjLast s i) indCongr hS (.pos y ⟨Y, hY⟩)
    (S := .wit N.packed Z) (unpackG N) _ Φ hsat'
  refine (congrArg (B.model.sat _)
    (OutLeg.retS_congr hS (.pos y ⟨Y, hY⟩) (.wit N Z) ?_ rfl)).mp hb
  rw [Term.holeRead_eq_holeAt, Term.holeRead_eq_holeAt]
  exact holeAt_packG_unpackGW_val N Z t

end BData


/-! ## The limit -/

section LimitOutDC

variable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} {hS : ModalSys.BStrong = true}
  (C : StrongChain hS M₀) (E : LimitEx C.toFairChain)

/-- ⭐⭐**The limit has returning successors at witnessed companion shapes** (plain leg; any T).
    As `bdataS_retOutC` for the necessary part (`ret_comps_namedW`, `subC`, the alias `y` of
    `arrB W`); the possible part's value gets an alias `z`, and a unit alias `o` (after `y`) fills
    the back image of the witness; the value moves to `⟨unarrT y, z⟩` item by item
    (`OutLeg.instantiate_compSlot`, `WFF.instantiate_pairSnd`); then the back-witness child
    (`lretDC`). -/
theorem bdataS_retOutDC (hW : ModalSys.BStrongW = false) : (bdataS C E).RetOutDC hS := by
  classical
  intro s i A Z cs h a a₂ V t₂ Φ hm
  -- name the missing companions, and reorder to the born order
  obtain ⟨j₁, hij₁, a₁, V₁, hV₁, hm₁⟩ := BWorld.ret_comps_namedW ((bdataS C E).w s) hS
    (missComps A cs) (missComps_ok h) .nec V t₂ Φ hm
  set R := ShapeMap.subC (σ := σ) A (missComps A cs ++ cs) (bornComps A) (missComps_ok h)
    (bornComps_ok A) (missComps_sub A cs)
  set e₁ := ((bdataS C E).w s).le hij₁
  set Φ₁ := WFF.mono (e₁.boxIn.insert (.bnd 0) (RShape.wit (.boxC A cs h) Z).ty) Φ
  have hm₂ : WFF.retS hS (.wit (bornShape A) Z)
      (Term.pair (Term.holeRead V₁ R.val.2) (Term.mono e₁ t₂)) Φ₁ ∈ ((bdataS C E).w s).M j₁ := by
    have hp := BWorld.mem_of_provable (Δ := [_])
      (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hm₁)
      ⟨Proof.ret_map hS .nec (S := .wit (.boxC A (missComps A cs ++ cs) (missComps_ok h)) Z)
        R (Term.pair V₁ (Term.mono e₁ t₂)) Φ₁ (Proof.conv (congrArg _
          ((WFF.bodyRepl_congr (sig_mono _ (liftObj_subC_wit (σ := σ) A _ _ (missComps_ok h)
            (bornComps_ok A) (missComps_sub A cs) Z)) Φ₁).trans (WFF.bodyRepl_eta Φ₁)).symm)
          (Proof.lookup List.mem_cons_self))⟩
    refine (congrArg (· ∈ _) (OutLeg.retS_congr hS .nec _ ?_ rfl)).mp hp
    rw [Term.holeRead_eq_holeAt, Term.holeRead_eq_holeAt]
    exact holeAt_liftVal_wit R V₁ _
  -- aliases: the value's tuple, the possible part's value, and a unit after the first
  set W := Term.holeRead V₁ R.val.2
  set t := Term.holeAt W (arrB (σ := σ) A).2
  obtain ⟨i₂, hj₁i₂, l₁, hl₁, hal₁⟩ := lalias C s j₁ t
  obtain ⟨i₃, hii₃, l₂, hl₂, hal₂⟩ := lalias C s i t₂
  obtain ⟨i₄, hi₂₄, l₃, hl₃, hal₃⟩ :=
    lalias C s i₂ (Term.unit : Term σ (ctxOf (lat s i₂)) .VTypeOne _)
  set J := max i₃ i₄ with hJ
  have hi₂J : i₂ ≤ J := hi₂₄.trans (le_max_right _ _)
  have hi₃J : i₃ ≤ J := le_max_left _ _
  have hj₁J : j₁ ≤ J := hj₁i₂.trans hi₂J
  have hiJ : i ≤ J := hij₁.trans hj₁J
  obtain ⟨hs₁, hf₁⟩ := hal₁ J hi₂J
  obtain ⟨hs₂, hf₂⟩ := hal₂ J hi₃J
  obtain ⟨hs₃, -⟩ := hal₃ J (le_max_right _ _)
  have hMJ := (C.good _).mcs s.1 (live_birth C.toFairChain s.2 (Nat.le_add_right _ J))
  have hyJ : (ctxOf (lat s J)).ref (.root (.free l₁.length)) = some (VarType.VTypeBox A).bc :=
    (ctxOf_le_of_suffix hs₁).ref (ctxOf_ref_new _ l₁)
  have hz : (ctxOf (lat s J)).ref (.root (.free l₂.length)) = some Z :=
    (ctxOf_le_of_suffix hs₂).ref (ctxOf_ref_new Z l₂)
  have ho : (ctxOf (lat s J)).ref (.root (.free l₃.length)) = some .VTypeOne :=
    (ctxOf_le_of_suffix hs₃).ref (ctxOf_ref_new _ l₃)
  have hyo : l₁.length ≠ l₃.length := by
    have h1 := (hal₁ i₂ le_rfl).1.length_le
    have h2 := hl₃.length_le
    simp only [List.length_cons] at h1
    omega
  set eJ := ((bdataS C E).w s).le hiJ
  set e₁J := ((bdataS C E).w s).le hj₁J
  set ΦJ : WFF σ ((ctxOf (lat s J)).boxIn.insert (.bnd 0) (RShape.wit (bornShape A) Z).ty) 1 :=
    WFF.mono (eJ.boxIn.insert (.bnd 0) (RShape.wit (.boxC A cs h) Z).ty) Φ
  have hJm : WFF.retS hS (.wit (bornShape A) Z)
      (Term.pair (Term.mono e₁J W) (Term.mono eJ t₂)) ΦJ ∈
        ((C.net (birth C.toFairChain s.2 + J)).st s.1).M := by
    have := (BWorld.mem_lift (w := (bdataS C E).w s) hj₁J).mp hm₂
    change WFF.retS hS (.wit (bornShape A) Z)
      (Term.pair (Term.mono e₁J W) (Term.mono e₁J (Term.mono e₁ t₂)))
      (WFF.mono _ (WFF.mono _ Φ)) ∈ _ at this
    rw [WFF.mono_mono, Term.mono_mono] at this
    exact this
  -- the necessary part moves to `unarrT y`
  have m1 : WFF.retS hS (.wit (bornShape A) Z) (Term.pair (unarrT hyJ).2 (Term.mono eJ t₂)) ΦJ ∈
      ((C.net (birth C.toFairChain s.2 + J)).st s.1).M := by
    have hi := alias_interch hs₁ hMJ (Term.mono (ctxOf_le_of_suffix hl₁) t) hf₁
      (WFF.bodyRepl (Term.pair
        (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (unarrHole (σ := σ) A).2)
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf (lat s J))).root _)
          (Term.mono eJ t₂))) (WFF.retSlot hS (.wit (bornShape A) Z) ΦJ))
    have ea := OutLeg.instantiate_compSlot hS .nec (.wit (bornShape A) Z) (Term.pair
        (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (unarrHole (σ := σ) A).2)
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf (lat s J))).root _)
          (Term.mono eJ t₂))) ΦJ
      (Term.mono (ctxOf_le_of_suffix hs₁) (Term.eta (.root (.free l₁.length)) _
        (ctxOf_ref_new _ l₁)))
    have eb := OutLeg.instantiate_compSlot hS .nec (.wit (bornShape A) Z) (Term.pair
        (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (unarrHole (σ := σ) A).2)
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf (lat s J))).root _)
          (Term.mono eJ t₂))) ΦJ
      (Term.mono (ctxOf_le_of_suffix hs₁) (Term.mono (aliasLe _ l₁)
        (Term.mono (ctxOf_le_of_suffix hl₁) t)))
    have e_y : (⟨_, Term.holeRead (Term.mono (ctxOf_le_of_suffix hs₁)
        (Term.eta (.root (.free l₁.length)) _ (ctxOf_ref_new _ l₁))) (unarrHole (σ := σ) A).2⟩ :
        Σ c, Term σ (ctxOf (lat s J)) _ c) = unarrT hyJ := by
      rw [Term.holeRead_eq_holeAt]
      refine (holeAt_unarrHole A _).trans ?_
      rw [Term.mono_eta]
      exact unarrAt_eta hyJ
    have e_t : (⟨_, Term.holeRead (Term.mono (ctxOf_le_of_suffix hs₁)
        (Term.mono (aliasLe _ l₁) (Term.mono (ctxOf_le_of_suffix hl₁) t)))
          (unarrHole (σ := σ) A).2⟩ :
        Σ c, Term σ (ctxOf (lat s J)) _ c) = ⟨_, Term.mono e₁J W⟩ := by
      rw [Term.holeRead_eq_holeAt]
      refine (holeAt_unarrHole A _).trans ?_
      rw [Term.mono_mono, Term.mono_mono]
      refine (unarrAt_sig A (Term.mono_holeAt_sig _ W _)).trans ?_
      exact unarrAt_arrB A _
    exact (congrArg (· ∈ _) (ea.trans (OutLeg.retS_congr hS .nec _
      (sig_pair e_y (Term.subst_single_mono_sig _ _)) rfl))).mp
      (hi.mpr ((congrArg (· ∈ _) (eb.trans (OutLeg.retS_congr hS .nec _
        (sig_pair e_t (Term.subst_single_mono_sig _ _)) rfl))).mpr hJm))
  -- the possible part's value moves to `z`
  have m2 : WFF.retS hS (.wit (bornShape A) Z) (unarrDT (σ := σ) hyJ hz).2 ΦJ ∈
      ((C.net (birth C.toFairChain s.2 + J)).st s.1).M := by
    have hi := (alias_interch hs₂ hMJ (Term.mono (ctxOf_le_of_suffix hl₂) t₂) hf₂
      (WFF.bodyRepl (Term.pair
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf (lat s J))).root Z)
          (unarrT hyJ).2)
        (Term.eta (.root (.bnd 0)) Z (Ctx.ref_insert_root _ _ _)))
        (WFF.retSlot hS (.wit (bornShape A) Z) ΦJ))).mpr
    rw [WFF.instantiate_pairSnd, WFF.instantiate_pairSnd, Term.mono_mono, Term.mono_mono] at hi
    have h₁ := WFF.instantiate_retSlot (Γ := ctxOf (lat s J)) hS (.wit (bornShape A) Z) ΦJ
      (Term.pair (unarrT hyJ).2 (Term.mono eJ t₂))
    have h₂ := WFF.instantiate_retSlot (Γ := ctxOf (lat s J)) hS (.wit (bornShape A) Z) ΦJ
      (Term.pair (unarrT hyJ).2
        (Term.mono (ctxOf_le_of_suffix hs₂) (Term.eta (.root (.free l₂.length)) Z
          (ctxOf_ref_new Z l₂))))
    refine (congrArg (· ∈ _) (OutLeg.retS_congr hS .nec (.wit (bornShape A) Z)
      (sig_pair rfl (congrArg (Sigma.mk _) (Term.mono_eta (ctxOf_le_of_suffix hs₂)
        (.root (.free l₂.length)) Z (ctxOf_ref_new Z l₂)))) rfl)).mp ?_
    exact (congrArg (· ∈ _) h₂).mp (hi ((congrArg (· ∈ _) h₁).mpr m1))
  -- the back-witness child
  obtain ⟨k, hsk, hkd, hcl, hback, hlcx, hmk⟩ := lretDC C hW s J hyJ ho hz hyo ΦJ m2
  have hj : lstg C.toFairChain s k i ≤ lstg C.toFairChain s k J := lstg_mono C hsk hiJ
  have hcK : (ctxOf (lat k (lstg C.toFairChain s k J))).ref (.root (.free 0)) =
      some (.VTypeBox A) := (ctxOf_le_of_suffix hcl).ref (bclD_c A Z)
  set K := lstg C.toFairChain k s (lstg C.toFairChain s k J)
  have hJK : J ≤ K := by
    have h₁ := (lstg_spec C.toFairChain hsk J).1
    have h₂ := (lstg_spec C.toFairChain hsk.symm (lstg C.toFairChain s k J)).1
    omega
  have hy₂ : (ctxOf (lat s i₂)).ref (.root (.free l₁.length)) = some (VarType.VTypeBox A).bc :=
    (ctxOf_le_of_suffix (hal₁ i₂ le_rfl).1).ref (ctxOf_ref_new _ l₁)
  have hiK : i₂ ≤ K := hi₂J.trans hJK
  refine ⟨k, hsk, lstg C.toFairChain s k J, hj, _,
    Term.eta (VarSymb.root (.free 0)).inner A (Ctx.ref_inner hcK), .root (.free 1),
    (ctxOf_le_of_suffix hcl).ref (bclD_e A Z), hkd, ?_, ?_, ?_⟩
  · have e := readArrow_mono_congr (C.lang_suffix (by omega)
      (live_birth C.toFairChain s.2 (Nat.le_add_right _ i))) (Ctx.Le.refl _)
      ((limgOk C.toFairChain hsk i).mono (((bdataS C E).w k).le hj))
      (limgOk C.toFairChain hsk J) (fun _ _ => rfl)
      (Term.pair (Term.boxtm (Term.eta (VarSymb.root (.free 0)).inner A (Ctx.ref_inner hcK)))
        (Term.eta (.root (.free 1)) (.VTypeDia Z) ((ctxOf_le_of_suffix hcl).ref (bclD_e A Z)))) Φ
    rw [Term.mono_refl, WFF.mono_refl] at e
    exact (congrArg (· ∈ _) e).mpr hmk
  swap
  · obtain ⟨hsuf₂, -⟩ := hal₂ i₃ le_rfl
    have hz₂ : (ctxOf (lat s i₃)).ref (.root (.free l₂.length)) = some Z :=
      (ctxOf_le_of_suffix hsuf₂).ref (ctxOf_ref_new Z l₂)
    have hzK := (((bdataS C E).w s).le (hi₃J.trans hJK)).ref hz₂
    have e2 := congrArg (fun p : Σ b, Term σ _ Z b =>
      (bdataS C E).rden s _ (Ctx.Le.refl _) p.2)
      (eta_addr_congr (σ := σ) (congrArg (fun c => VarSymb.root (.free c)) hlcx)
        ((bdataS C E).hcx hkd (lstg C.toFairChain s k J)) hzK)
    have e3 : (bdataS C E).rden s _ (Ctx.Le.refl _)
        (Term.eta (.root (.free l₂.length)) Z hzK) =
        (bdataS C E).rden s i₃ (Ctx.Le.refl _) (Term.eta (.root (.free l₂.length)) Z hz₂) := by
      have := BData.rden_lift (B := bdataS C E) (hi₃J.trans hJK)
        (Term.eta (.root (.free l₂.length)) Z hz₂)
      rwa [Term.mono_eta] at this
    refine (congrArg (fun o => (bdataS C E).Ind o _) ?_).mpr
      (lalias_ind C E s t₂ hl₂ hal₂ hz₂)
    exact BData.toDom_congr (e2.trans e3) _ _
  -- the born root's readings home, `Ind` to `V`
  have hyK := (((bdataS C E).w s).le hiK).ref hy₂
  set Sel := ShapeMap.subC (σ := σ) A (bornComps A) cs (bornComps_ok A) h (compOk_sub_born h)
  have eR : (⟨_, Term.subst (arrowIdx (limg C.toFairChain k s))
      (arrowS σ (ctxOf (lat s K)) (limg C.toFairChain k s))
      (ok_arrowS (limgOk C.toFairChain hsk.symm (lstg C.toFairChain s k J)))
      (coh_arrowS (limgOk C.toFairChain hsk.symm (lstg C.toFairChain s k J)))
      (compsVal (Term.eta (VarSymb.root (.free 0)).inner A (Ctx.ref_inner hcK)) cs h).2⟩ :
      Σ c, Term σ (ctxOf (lat s K)) (A.compsFlat cs) c) =
      ⟨_, Term.holeAt (unarrT (σ := σ) hyK).2 Sel.val.2⟩ := by
    rw [compsVal_eta hcK cs h]
    exact subst_arrow_compsSlot_born hcK (limgOk C.toFairChain hsk.symm _) hyK hback cs h
      (compOk_sub_born h)
  -- the alias, mapped
  have hA := lalias_ind C E s t hl₁ hal₁ hy₂
  rw [← BData.interp_canon _ (Model.Env.Agree.refl' _),
    ← BData.interp_canon t (Model.Env.Agree.refl' _)] at hA
  have hM := BData.ind_map (Term.holeAt (unarrHole (σ := σ) A).2 Sel.val.2) hA
  rw [← Model.interp_holeAt, ← Model.interp_holeAt] at hM
  have eL := congrArg (fun x : Σ c, Term σ (ctxOf (lat s i₂)) (A.compsFlat cs) c =>
    Model.interp ((bdataS C E).canonEnv s i₂) x.2)
    ((Term.holeAt_holeAt_sig _ _ _).trans (Term.holeAt_congr_sig
      ((holeAt_unarrHole A _).trans (unarrAt_eta hy₂)) Sel.val.2))
  have eRt := congrArg (fun x : Σ c, Term σ (ctxOf (lat s j₁)) (A.compsFlat cs) c =>
    Model.interp ((bdataS C E).canonEnv s j₁) x.2)
    ((Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
      ((holeAt_unarrHole A t).trans (unarrAt_arrB A W)) Sel.val.2).trans
      ((Term.holeAt_congr_sig (congrArg (Sigma.mk _) (Term.holeRead_eq_holeAt V₁ R.val.2))
        Sel.val.2).trans (holeAt_subC_sel h _ V₁ hV₁))))
  dsimp only at eL eRt
  rw [eL, eRt, Model.interp_mono (BData.canonEnv_le (B := bdataS C E) s hij₁) V] at hM
  have eK : Model.interp ((bdataS C E).canonEnv s K) (Term.holeAt (unarrT hyK).2 Sel.val.2) =
      Model.interp ((bdataS C E).canonEnv s i₂) (Term.holeAt (unarrT hy₂).2 Sel.val.2) := by
    have e := congrArg (fun x : Σ c, Term σ (ctxOf (lat s K)) (A.compsFlat cs) c =>
      Model.interp ((bdataS C E).canonEnv s K) x.2)
      ((Term.holeAt_congr_sig (mono_unarrT (((bdataS C E).w s).suf hiK) hy₂).symm
        Sel.val.2).trans (Term.mono_holeAt_sig _ _ _).symm)
    exact e.trans (Model.interp_mono (BData.canonEnv_le (B := bdataS C E) s hiK) _)
  rw [← BData.interp_canon _ (Model.Env.Agree.refl' _),
    ← BData.interp_canon V (Model.Env.Agree.refl' _)]
  refine (congrArg (fun o => (bdataS C E).Ind o _)
    ((congrArg (fun x : Σ c, Term σ (ctxOf (lat s K)) (A.compsFlat cs) c =>
      Model.interp ((bdataS C E).canonEnv s K) x.2) eR).trans eK)).mpr hM


/-- ⭐⭐**The limit has returning successors along a witness at witnessed companion shapes**
    (any T): as `bdataS_retOutDC`, along `x` (the slot formulas along the leg, the doubly
    witnessed child `lretXDC`). -/
theorem bdataS_retOutXDC : (bdataS C E).RetOutXDC hS := by
  classical
  intro s i x X hx A Z cs h a a₂ V t₂ Φ hm
  -- name the missing companions, and reorder to the born order
  obtain ⟨j₁, hij₁, a₁, V₁, hV₁, hm₁⟩ := BWorld.ret_comps_namedW ((bdataS C E).w s) hS
    (missComps A cs) (missComps_ok h) (.pos x ⟨X, hx⟩) V t₂ Φ hm
  have hx₁ := (((bdataS C E).w s).le hij₁).ref hx
  set R := ShapeMap.subC (σ := σ) A (missComps A cs ++ cs) (bornComps A) (missComps_ok h)
    (bornComps_ok A) (missComps_sub A cs)
  set e₁ := ((bdataS C E).w s).le hij₁
  set Φ₁ := WFF.mono ((e₁.diaIn x).insert (.bnd 0) (RShape.wit (.boxC A cs h) Z).ty) Φ
  have hm₂ : WFF.retxS hS x ⟨X, hx₁⟩ (.wit (bornShape A) Z)
      (Term.pair (Term.holeRead V₁ R.val.2) (Term.mono e₁ t₂)) Φ₁ ∈ ((bdataS C E).w s).M j₁ := by
    have hp := BWorld.mem_of_provable (Δ := [_])
      (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hm₁)
      ⟨Proof.ret_map hS (.pos x ⟨X, hx₁⟩)
        (S := .wit (.boxC A (missComps A cs ++ cs) (missComps_ok h)) Z)
        R (Term.pair V₁ (Term.mono e₁ t₂)) Φ₁ (Proof.conv (congrArg _
          ((WFF.bodyRepl_congr (sig_mono _ (liftObj_subC_wit (σ := σ) A _ _ (missComps_ok h)
            (bornComps_ok A) (missComps_sub A cs) Z)) Φ₁).trans (WFF.bodyRepl_eta Φ₁)).symm)
          (Proof.lookup List.mem_cons_self))⟩
    refine (congrArg (· ∈ _) (OutLeg.retS_congr hS (.pos x ⟨X, hx₁⟩) _ ?_ rfl)).mp hp
    rw [Term.holeRead_eq_holeAt, Term.holeRead_eq_holeAt]
    exact holeAt_liftVal_wit R V₁ _
  -- aliases: the value's tuple, the possible part's value, and a unit after the first
  set W := Term.holeRead V₁ R.val.2
  set t := Term.holeAt W (arrB (σ := σ) A).2
  obtain ⟨i₂, hj₁i₂, l₁, hl₁, hal₁⟩ := lalias C s j₁ t
  obtain ⟨i₃, hii₃, l₂, hl₂, hal₂⟩ := lalias C s i t₂
  obtain ⟨i₄, hi₂₄, l₃, hl₃, hal₃⟩ :=
    lalias C s i₂ (Term.unit : Term σ (ctxOf (lat s i₂)) .VTypeOne _)
  set J := max i₃ i₄ with hJ
  have hi₂J : i₂ ≤ J := hi₂₄.trans (le_max_right _ _)
  have hi₃J : i₃ ≤ J := le_max_left _ _
  have hj₁J : j₁ ≤ J := hj₁i₂.trans hi₂J
  have hiJ : i ≤ J := hij₁.trans hj₁J
  obtain ⟨hs₁, hf₁⟩ := hal₁ J hi₂J
  obtain ⟨hs₂, hf₂⟩ := hal₂ J hi₃J
  obtain ⟨hs₃, -⟩ := hal₃ J (le_max_right _ _)
  have hMJ := (C.good _).mcs s.1 (live_birth C.toFairChain s.2 (Nat.le_add_right _ J))
  have hyJ : (ctxOf (lat s J)).ref (.root (.free l₁.length)) = some (VarType.VTypeBox A).bc :=
    (ctxOf_le_of_suffix hs₁).ref (ctxOf_ref_new _ l₁)
  have hz : (ctxOf (lat s J)).ref (.root (.free l₂.length)) = some Z :=
    (ctxOf_le_of_suffix hs₂).ref (ctxOf_ref_new Z l₂)
  have ho : (ctxOf (lat s J)).ref (.root (.free l₃.length)) = some .VTypeOne :=
    (ctxOf_le_of_suffix hs₃).ref (ctxOf_ref_new _ l₃)
  have hyo : l₁.length ≠ l₃.length := by
    have h1 := (hal₁ i₂ le_rfl).1.length_le
    have h2 := hl₃.length_le
    simp only [List.length_cons] at h1
    omega
  set eJ := ((bdataS C E).w s).le hiJ
  have hxJ : (ctxOf (lat s J)).ref x = some (.VTypeDia X) := eJ.ref hx
  set e₁J := ((bdataS C E).w s).le hj₁J
  set ΦJ : WFF σ (((ctxOf (lat s J)).diaIn x).insert (.bnd 0) (RShape.wit (bornShape A) Z).ty)
      1 := WFF.mono ((eJ.diaIn x).insert (.bnd 0) (RShape.wit (.boxC A cs h) Z).ty) Φ
  have hJm : WFF.retxS hS x ⟨X, hxJ⟩ (.wit (bornShape A) Z)
      (Term.pair (Term.mono e₁J W) (Term.mono eJ t₂)) ΦJ ∈
        ((C.net (birth C.toFairChain s.2 + J)).st s.1).M := by
    have := (BWorld.mem_lift (w := (bdataS C E).w s) hj₁J).mp hm₂
    change WFF.retxS hS x ⟨X, hxJ⟩ (.wit (bornShape A) Z)
      (Term.pair (Term.mono e₁J W) (Term.mono e₁J (Term.mono e₁ t₂)))
      (WFF.mono _ (WFF.mono _ Φ)) ∈ _ at this
    rw [WFF.mono_mono, Term.mono_mono] at this
    exact this
  -- the necessary part moves to `unarrT y`
  have m1 : WFF.retxS hS x ⟨X, hxJ⟩ (.wit (bornShape A) Z)
      (Term.pair (unarrT hyJ).2 (Term.mono eJ t₂)) ΦJ ∈
      ((C.net (birth C.toFairChain s.2 + J)).st s.1).M := by
    have hi := alias_interch hs₁ hMJ (Term.mono (ctxOf_le_of_suffix hl₁) t) hf₁
      (WFF.bodyRepl (Term.pair
        (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (unarrHole (σ := σ) A).2)
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf (lat s J))).root _)
          (Term.mono eJ t₂))) (WFF.retxSlot hS x ⟨X, hxJ⟩ (.wit (bornShape A) Z) ΦJ))
    have ea := OutLeg.instantiate_compSlot hS (.pos x ⟨X, hxJ⟩) (.wit (bornShape A) Z) (Term.pair
        (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (unarrHole (σ := σ) A).2)
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf (lat s J))).root _)
          (Term.mono eJ t₂))) ΦJ
      (Term.mono (ctxOf_le_of_suffix hs₁) (Term.eta (.root (.free l₁.length)) _
        (ctxOf_ref_new _ l₁)))
    have eb := OutLeg.instantiate_compSlot hS (.pos x ⟨X, hxJ⟩) (.wit (bornShape A) Z) (Term.pair
        (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (unarrHole (σ := σ) A).2)
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf (lat s J))).root _)
          (Term.mono eJ t₂))) ΦJ
      (Term.mono (ctxOf_le_of_suffix hs₁) (Term.mono (aliasLe _ l₁)
        (Term.mono (ctxOf_le_of_suffix hl₁) t)))
    have e_y : (⟨_, Term.holeRead (Term.mono (ctxOf_le_of_suffix hs₁)
        (Term.eta (.root (.free l₁.length)) _ (ctxOf_ref_new _ l₁))) (unarrHole (σ := σ) A).2⟩ :
        Σ c, Term σ (ctxOf (lat s J)) _ c) = unarrT hyJ := by
      rw [Term.holeRead_eq_holeAt]
      refine (holeAt_unarrHole A _).trans ?_
      rw [Term.mono_eta]
      exact unarrAt_eta hyJ
    have e_t : (⟨_, Term.holeRead (Term.mono (ctxOf_le_of_suffix hs₁)
        (Term.mono (aliasLe _ l₁) (Term.mono (ctxOf_le_of_suffix hl₁) t)))
          (unarrHole (σ := σ) A).2⟩ :
        Σ c, Term σ (ctxOf (lat s J)) _ c) = ⟨_, Term.mono e₁J W⟩ := by
      rw [Term.holeRead_eq_holeAt]
      refine (holeAt_unarrHole A _).trans ?_
      rw [Term.mono_mono, Term.mono_mono]
      refine (unarrAt_sig A (Term.mono_holeAt_sig _ W _)).trans ?_
      exact unarrAt_arrB A _
    exact (congrArg (· ∈ _) (ea.trans (OutLeg.retS_congr hS (.pos x ⟨X, hxJ⟩) _
      (sig_pair e_y (Term.subst_single_mono_sig _ _)) rfl))).mp
      (hi.mpr ((congrArg (· ∈ _) (eb.trans (OutLeg.retS_congr hS (.pos x ⟨X, hxJ⟩) _
        (sig_pair e_t (Term.subst_single_mono_sig _ _)) rfl))).mpr hJm))
  -- the possible part's value moves to `z`
  have m2 : WFF.retxS hS x ⟨X, hxJ⟩ (.wit (bornShape A) Z) (unarrDT (σ := σ) hyJ hz).2 ΦJ ∈
      ((C.net (birth C.toFairChain s.2 + J)).st s.1).M := by
    have hi := (alias_interch hs₂ hMJ (Term.mono (ctxOf_le_of_suffix hl₂) t₂) hf₂
      (WFF.bodyRepl (Term.pair
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf (lat s J))).root Z)
          (unarrT hyJ).2)
        (Term.eta (.root (.bnd 0)) Z (Ctx.ref_insert_root _ _ _)))
        (WFF.retxSlot hS x ⟨X, hxJ⟩ (.wit (bornShape A) Z) ΦJ))).mpr
    rw [WFF.instantiate_pairSnd, WFF.instantiate_pairSnd, Term.mono_mono, Term.mono_mono] at hi
    have h₁ := WFF.instantiate_retxSlot (Γ := ctxOf (lat s J)) hS x ⟨X, hxJ⟩
      (.wit (bornShape A) Z) ΦJ
      (Term.pair (unarrT hyJ).2 (Term.mono eJ t₂))
    have h₂ := WFF.instantiate_retxSlot (Γ := ctxOf (lat s J)) hS x ⟨X, hxJ⟩
      (.wit (bornShape A) Z) ΦJ
      (Term.pair (unarrT hyJ).2
        (Term.mono (ctxOf_le_of_suffix hs₂) (Term.eta (.root (.free l₂.length)) Z
          (ctxOf_ref_new Z l₂))))
    refine (congrArg (· ∈ _) (OutLeg.retS_congr hS (.pos x ⟨X, hxJ⟩) (.wit (bornShape A) Z)
      (sig_pair rfl (congrArg (Sigma.mk _) (Term.mono_eta (ctxOf_le_of_suffix hs₂)
        (.root (.free l₂.length)) Z (ctxOf_ref_new Z l₂)))) rfl)).mp ?_
    exact (congrArg (· ∈ _) h₂).mp (hi ((congrArg (· ∈ _) h₁).mpr m1))
  -- the back-witness child
  obtain ⟨k, hkx, hkd, hcl, hback, hlcx, hmk, -⟩ := lretXDC C s J hyJ ho hz hyo hxJ ΦJ m2
  have hsk := lkdR hkx
  have hj : lstg C.toFairChain s k i ≤ lstg C.toFairChain s k J := lstg_mono C hsk hiJ
  have hcK : (ctxOf (lat k (lstg C.toFairChain s k J))).ref (.root (.free 0)) =
      some (.VTypeBox A) := (ctxOf_le_of_suffix hcl).ref (bclD_c A Z)
  set K := lstg C.toFairChain k s (lstg C.toFairChain s k J)
  have hJK : J ≤ K := by
    have h₁ := (lstg_spec C.toFairChain hsk J).1
    have h₂ := (lstg_spec C.toFairChain hsk.symm (lstg C.toFairChain s k J)).1
    omega
  have hy₂ : (ctxOf (lat s i₂)).ref (.root (.free l₁.length)) = some (VarType.VTypeBox A).bc :=
    (ctxOf_le_of_suffix (hal₁ i₂ le_rfl).1).ref (ctxOf_ref_new _ l₁)
  have hiK : i₂ ≤ K := hi₂J.trans hJK
  refine ⟨k, hkx, lstg C.toFairChain s k J, hj, _,
    Term.eta (VarSymb.root (.free 0)).inner A (Ctx.ref_inner hcK), .root (.free 1),
    (ctxOf_le_of_suffix hcl).ref (bclD_e A Z), hkd, ?_, ?_, ?_⟩
  · have e := readArrowX_mono_congr (C.lang_suffix (by omega)
      (live_birth C.toFairChain s.2 (Nat.le_add_right _ i))) (Ctx.Le.refl _)
      ((limgOk C.toFairChain hsk i).mono (((bdataS C E).w k).le hj))
      (limgOk C.toFairChain hsk J) (fun _ _ => rfl) hx hxJ
      ((((bdataS C E).w k).le hj).ref ((bdataS C E).hcx hkx i)) (lhcx C.toFairChain hkx J)
      (Term.pair (Term.boxtm (Term.eta (VarSymb.root (.free 0)).inner A (Ctx.ref_inner hcK)))
        (Term.eta (.root (.free 1)) (.VTypeDia Z) ((ctxOf_le_of_suffix hcl).ref (bclD_e A Z)))) Φ
    rw [Term.mono_refl, WFF.mono_refl] at e
    exact (congrArg (· ∈ _) e).mpr hmk
  swap
  · obtain ⟨hsuf₂, -⟩ := hal₂ i₃ le_rfl
    have hz₂ : (ctxOf (lat s i₃)).ref (.root (.free l₂.length)) = some Z :=
      (ctxOf_le_of_suffix hsuf₂).ref (ctxOf_ref_new Z l₂)
    have hzK := (((bdataS C E).w s).le (hi₃J.trans hJK)).ref hz₂
    have e2 := congrArg (fun p : Σ b, Term σ _ Z b =>
      (bdataS C E).rden s _ (Ctx.Le.refl _) p.2)
      (eta_addr_congr (σ := σ) (congrArg (fun c => VarSymb.root (.free c)) hlcx)
        ((bdataS C E).hcx hkd (lstg C.toFairChain s k J)) hzK)
    have e3 : (bdataS C E).rden s _ (Ctx.Le.refl _)
        (Term.eta (.root (.free l₂.length)) Z hzK) =
        (bdataS C E).rden s i₃ (Ctx.Le.refl _) (Term.eta (.root (.free l₂.length)) Z hz₂) := by
      have := BData.rden_lift (B := bdataS C E) (hi₃J.trans hJK)
        (Term.eta (.root (.free l₂.length)) Z hz₂)
      rwa [Term.mono_eta] at this
    refine (congrArg (fun o => (bdataS C E).Ind o _) ?_).mpr
      (lalias_ind C E s t₂ hl₂ hal₂ hz₂)
    exact BData.toDom_congr (e2.trans e3) _ _
  -- the born root's readings home, `Ind` to `V`
  have hyK := (((bdataS C E).w s).le hiK).ref hy₂
  set Sel := ShapeMap.subC (σ := σ) A (bornComps A) cs (bornComps_ok A) h (compOk_sub_born h)
  have eR : (⟨_, Term.subst (arrowIdx (limg C.toFairChain k s))
      (arrowS σ (ctxOf (lat s K)) (limg C.toFairChain k s))
      (ok_arrowS (limgOk C.toFairChain hsk.symm (lstg C.toFairChain s k J)))
      (coh_arrowS (limgOk C.toFairChain hsk.symm (lstg C.toFairChain s k J)))
      (compsVal (Term.eta (VarSymb.root (.free 0)).inner A (Ctx.ref_inner hcK)) cs h).2⟩ :
      Σ c, Term σ (ctxOf (lat s K)) (A.compsFlat cs) c) =
      ⟨_, Term.holeAt (unarrT (σ := σ) hyK).2 Sel.val.2⟩ := by
    rw [compsVal_eta hcK cs h]
    exact subst_arrow_compsSlot_born hcK (limgOk C.toFairChain hsk.symm _) hyK hback cs h
      (compOk_sub_born h)
  -- the alias, mapped
  have hA := lalias_ind C E s t hl₁ hal₁ hy₂
  rw [← BData.interp_canon _ (Model.Env.Agree.refl' _),
    ← BData.interp_canon t (Model.Env.Agree.refl' _)] at hA
  have hM := BData.ind_map (Term.holeAt (unarrHole (σ := σ) A).2 Sel.val.2) hA
  rw [← Model.interp_holeAt, ← Model.interp_holeAt] at hM
  have eL := congrArg (fun x : Σ c, Term σ (ctxOf (lat s i₂)) (A.compsFlat cs) c =>
    Model.interp ((bdataS C E).canonEnv s i₂) x.2)
    ((Term.holeAt_holeAt_sig _ _ _).trans (Term.holeAt_congr_sig
      ((holeAt_unarrHole A _).trans (unarrAt_eta hy₂)) Sel.val.2))
  have eRt := congrArg (fun x : Σ c, Term σ (ctxOf (lat s j₁)) (A.compsFlat cs) c =>
    Model.interp ((bdataS C E).canonEnv s j₁) x.2)
    ((Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
      ((holeAt_unarrHole A t).trans (unarrAt_arrB A W)) Sel.val.2).trans
      ((Term.holeAt_congr_sig (congrArg (Sigma.mk _) (Term.holeRead_eq_holeAt V₁ R.val.2))
        Sel.val.2).trans (holeAt_subC_sel h _ V₁ hV₁))))
  dsimp only at eL eRt
  rw [eL, eRt, Model.interp_mono (BData.canonEnv_le (B := bdataS C E) s hij₁) V] at hM
  have eK : Model.interp ((bdataS C E).canonEnv s K) (Term.holeAt (unarrT hyK).2 Sel.val.2) =
      Model.interp ((bdataS C E).canonEnv s i₂) (Term.holeAt (unarrT hy₂).2 Sel.val.2) := by
    have e := congrArg (fun x : Σ c, Term σ (ctxOf (lat s K)) (A.compsFlat cs) c =>
      Model.interp ((bdataS C E).canonEnv s K) x.2)
      ((Term.holeAt_congr_sig (mono_unarrT (((bdataS C E).w s).suf hiK) hy₂).symm
        Sel.val.2).trans (Term.mono_holeAt_sig _ _ _).symm)
    exact e.trans (Model.interp_mono (BData.canonEnv_le (B := bdataS C E) s hiK) _)
  rw [← BData.interp_canon _ (Model.Env.Agree.refl' _),
    ← BData.interp_canon V (Model.Env.Agree.refl' _)]
  refine (congrArg (fun o => (bdataS C E).Ind o _)
    ((congrArg (fun x : Σ c, Term σ (ctxOf (lat s K)) (A.compsFlat cs) c =>
      Model.interp ((bdataS C E).canonEnv s K) x.2) eR).trans eK)).mpr hM

end LimitOutDC

end BArrow

end V12M
