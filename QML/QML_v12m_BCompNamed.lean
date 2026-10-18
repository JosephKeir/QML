import QML.QML_v12m_BArr
import QML.QML_v12m_BRetTruth

/-!
# QML v12m — naming a returning possibility's companions in a limit world (strong B with T)

Under T a returning possibility at a necessary object with some companions names one more
companion's return by `Proof.ret_compS`, an existence rule (docs §11.21, item 6).  In a world of
the canonical model that is an existential, `∃z. ◇^{boxC A (p :: cs)}[d ↦ ⟨V, z⟩] Φ(d)`, stated with
the slot formula `◇[d ↦ ⟨V, z⟩] Φ(d)` (`WFF.retSlot` with its value replaced, `WFF.bodyRepl`), and
witnessed at a later stage (`BWorld.exW_term`).

* `WFF.mono_retSlot`, `WFF.mono_retxSlot`, `WFF.instantiate_compSlot`; the slot formula along a
  leg, `OutLeg.retSlot` (`instantiate_retSlot`, `mono_retSlot`, `instantiate_compSlot`);
* ⭐`BWorld.ret_comp_named`: one companion named, along any leg; ⭐`BWorld.ret_comps_named`: a
  list.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

omit [ModalSys.NoFour] in
/-- Weakening the slot formula of a returning possibility weakens its body. -/
theorem WFF.mono_retSlot {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ')
    (hS : ModalSys.BStrong = true) (S : RShape) (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) S.ty) 1) :
    WFF.mono (h.insert (.bnd 0) S.flat) (WFF.retSlot hS S Φ) =
      WFF.retSlot hS S (WFF.mono (h.boxIn.insert (.bnd 0) S.ty) Φ) := by
  unfold WFF.retSlot bodyUp
  dsimp only [WFF.mono]
  rw [WFF.mono_subst _ _ _ _ _ _ (slots_insert_boxIn (Γ := Γ').insert _),
    WFF.subst_mono _ _ _ _ ((Ctx.NoSlots.slots (Γ := Γ)).boxIn.insert _)]
  refine OutLeg.retS_congr (O := .nec) hS S (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)) ?_
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v U hlp hv => ?_) Φ
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    change SubE.Sim U (SubE.mono _ (if (VarSymb.root (.bnd 0)) = .root (.bnd 0) then _ else _))
      (if (VarSymb.root (.bnd 0)) = .root (.bnd 0) then _ else _)
    rw [if_pos rfl, if_pos rfl]
    exact .refl _
  · change SubE.Sim U (SubE.mono _ (if v = .root (.bnd 0) then _ else _))
      (if v = .root (.bnd 0) then _ else _)
    rw [if_neg hvr, if_neg hvr]
    exact .refl _

/-- Instantiating a slot formula of a returning possibility whose value was replaced. -/
theorem WFF.instantiate_compSlot {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    (S : RShape) {C : VarType} {b : Ann S.flat} (X : Term σ (Γ.insert (.bnd 0) C) S.flat b)
    (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) S.ty) 1) {c : Ann C} (z : Term σ Γ C c) :
    WFF.instantiate Ctx.NoSlots.slots z (WFF.bodyRepl X (WFF.retSlot hS S Φ)) =
      WFF.retS hS S (Term.subst (Subst.singleIdx (.bnd 0) (.tm z)) (Subst.single (.bnd 0) (.tm z))
        (Subst.ok_single (Ctx.Le.refl Γ) rfl)
        (Subst.coh_single ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) (Ctx.Le.refl Γ)
          rfl) X) Φ :=
  (WFF.instantiate_bodyRepl X _ z).trans (WFF.instantiate_retSlot hS S Φ _)

omit [ModalSys.NoFour] in
/-- Weakening the slot formula of a returning possibility along `y` weakens its body. -/
theorem WFF.mono_retxSlot {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ')
    (hS : ModalSys.BStrong = true) (y : VarSymb) (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y))
    (S : RShape) (Φ : WFF σ ((Γ.diaIn y).insert (.bnd 0) S.ty) 1) :
    WFF.mono (h.insert (.bnd 0) S.flat) (WFF.retxSlot hS y hy S Φ) =
      WFF.retxSlot hS y (hy.imp fun _ e => h.ref e) S
        (WFF.mono ((h.diaIn y).insert (.bnd 0) S.ty) Φ) := by
  unfold WFF.retxSlot bodyUpX
  dsimp only [WFF.mono]
  rw [WFF.mono_subst _ _ _ _ _ _
      ((((Ctx.NoSlots.slots (Γ := Γ')).insert _).diaIn y).insert _),
    WFF.subst_mono _ _ _ _ (((Ctx.NoSlots.slots (Γ := Γ)).diaIn y).insert _)]
  refine OutLeg.retS_congr (O := .pos y _) hS S
    (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)) ?_
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v U hlp hv => ?_) Φ
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    change SubE.Sim U (SubE.mono _ (if (VarSymb.root (.bnd 0)) = .root (.bnd 0) then _ else _))
      (if (VarSymb.root (.bnd 0)) = .root (.bnd 0) then _ else _)
    rw [if_pos rfl, if_pos rfl]
    exact .refl _
  · change SubE.Sim U (SubE.mono _ (if v = .root (.bnd 0) then _ else _))
      (if v = .root (.bnd 0) then _ else _)
    rw [if_neg hvr, if_neg hvr]
    exact .refl _

/-! ## The slot formula along a leg -/

/-- The slot formula of a returning possibility along a leg: `WFF.retSlot` or `WFF.retxSlot`. -/
def _root_.V12M.OutLeg.retSlot {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) :
    (O : OutLeg Γ) → (S : RShape) → WFF σ (O.view.insert (.bnd 0) S.ty) 1 →
      WFF σ (Γ.insert (.bnd 0) S.flat) 1
  | .nec, S, Φ => WFF.retSlot hS S Φ
  | .pos y hy, S, Φ => WFF.retxSlot hS y hy S Φ

theorem _root_.V12M.OutLeg.instantiate_retSlot {Γ : Ctx} [Γ.NoSlots]
    (hS : ModalSys.BStrong = true) :
    (O : OutLeg Γ) → (S : RShape) → (Φ : WFF σ (O.view.insert (.bnd 0) S.ty) 1) →
    {a : Ann S.flat} → (z : Term σ Γ S.flat a) →
    WFF.instantiate Ctx.NoSlots.slots z (O.retSlot hS S Φ) = O.retS hS S z Φ
  | .nec, S, Φ, _, z => WFF.instantiate_retSlot hS S Φ z
  | .pos y hy, S, Φ, _, z => WFF.instantiate_retxSlot hS y hy S Φ z

omit [ModalSys.NoFour] in
theorem _root_.V12M.OutLeg.mono_retSlot {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ')
    (hS : ModalSys.BStrong = true) : (O : OutLeg Γ) → (S : RShape) →
    (Φ : WFF σ (O.view.insert (.bnd 0) S.ty) 1) →
    WFF.mono (h.insert (.bnd 0) S.flat) (O.retSlot hS S Φ) =
      (O.mono h).retSlot hS S (WFF.mono ((OutLeg.le_view_mono h O).insert (.bnd 0) S.ty) Φ)
  | .nec, S, Φ => WFF.mono_retSlot h hS S Φ
  | .pos y hy, S, Φ => WFF.mono_retxSlot h hS y hy S Φ

/-- Instantiating a slot formula along a leg whose value was replaced. -/
theorem _root_.V12M.OutLeg.instantiate_compSlot {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    (O : OutLeg Γ) (S : RShape) {C : VarType} {b : Ann S.flat}
    (X : Term σ (Γ.insert (.bnd 0) C) S.flat b) (Φ : WFF σ (O.view.insert (.bnd 0) S.ty) 1)
    {c : Ann C} (z : Term σ Γ C c) :
    WFF.instantiate Ctx.NoSlots.slots z (WFF.bodyRepl X (O.retSlot hS S Φ)) =
      O.retS hS S (Term.subst (Subst.singleIdx (.bnd 0) (.tm z)) (Subst.single (.bnd 0) (.tm z))
        (Subst.ok_single (Ctx.Le.refl Γ) rfl)
        (Subst.coh_single ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) (Ctx.Le.refl Γ)
          rfl) X) Φ :=
  (WFF.instantiate_bodyRepl X _ z).trans (OutLeg.instantiate_retSlot hS O S Φ _)

section CompNamed

variable {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) {A : VarType}
  {cs : List (List Step)} {h : A.CompOk cs} (p : List Step) (h' : A.CompOk (p :: cs))

/-- ⭐The slot formula `◇^{boxC A (p :: cs)}[d ↦ ⟨V, z⟩] Φ(d)` along a leg, with `z` the slot. -/
def compSlot (O : OutLeg Γ) {a : Ann (A.compsFlat cs)} (V : Term σ Γ (A.compsFlat cs) a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1) :
    WFF σ (Γ.insert (.bnd 0) ((A.compAt p).getD .VTypeOne)) 1 :=
  WFF.bodyRepl (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root _) V)
      (Term.eta (.root (.bnd 0)) ((A.compAt p).getD .VTypeOne) (Ctx.ref_insert_root _ _ _)))
    (O.retSlot hS (.nec (.boxC A (p :: cs) h')) Φ)

/-- ⭐The slot formula, weakened and instantiated: the returning possibility at one more
    companion, valued at the weakened value and the term. -/
theorem instantiate_compSlot_mono {Γ' : Ctx} [Γ'.NoSlots] (hle : Γ.Le Γ') (O : OutLeg Γ)
    {a : Ann (A.compsFlat cs)} (V : Term σ Γ (A.compsFlat cs) a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1) {c : Ann ((A.compAt p).getD .VTypeOne)}
    (z : Term σ Γ' ((A.compAt p).getD .VTypeOne) c) :
    WFF.instantiate Ctx.NoSlots.slots z
        (WFF.mono (hle.insert (.bnd 0) _) (compSlot hS p h' O V Φ)) =
      (O.mono hle).retS hS (.nec (.boxC A (p :: cs) h')) (Term.pair (Term.mono hle V) z)
        (WFF.mono ((OutLeg.le_view_mono hle O).insert (.bnd 0) _) Φ) := by
  unfold compSlot
  rw [WFF.mono_bodyRepl hle, OutLeg.mono_retSlot hle]
  refine (OutLeg.instantiate_compSlot hS (O.mono hle) (.nec (.boxC A (p :: cs) h')) _ _
    z).trans ?_
  refine OutLeg.retS_congr (O := O.mono hle) hS _ ?_ rfl
  have e₁ : (⟨_, Term.mono (hle.insert (.bnd 0) ((A.compAt p).getD .VTypeOne))
      (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root _) V)⟩ :
      Σ e, Term σ (Γ'.insert (.bnd 0) ((A.compAt p).getD .VTypeOne)) _ e) =
      ⟨_, Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ')).root _) (Term.mono hle V)⟩ := by
    rw [Term.mono_mono, Term.mono_mono]
  have e₂ := congrArg (Sigma.mk _) (Term.mono_eta (σ := σ)
    (hle.insert (.bnd 0) ((A.compAt p).getD .VTypeOne)) (.root (.bnd 0))
    ((A.compAt p).getD .VTypeOne) (Ctx.ref_insert_root _ _ _))
  exact (sig_subst _ _ _ (sig_pair e₁ e₂)).trans
    (sig_pair (Term.subst_single_mono_sig z (Term.mono hle V))
      (Term.subst_eta_tm _ _ _ _ _ _ z (Subst.at_single_root _ _)))

/-- ⭐⭐**Naming a companion's return, in a world** (any leg): `◇^{boxC A cs}[d ↦ V] Φ` at a
    stage gives, at a later one, `◇^{boxC A (p :: cs)}[d ↦ ⟨V, z⟩] Φ` for some term `z` —
    `ret_compS` at a fresh root, as `∃z` (`ex_intro`), witnessed (`exW_term`). -/
theorem BWorld.ret_comp_named (w : BWorld σ) {i : ℕ} (O : OutLeg (w.ctx i))
    {a : Ann (A.compsFlat cs)} (V : Term σ (w.ctx i) (A.compsFlat cs) a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1)
    (hm : O.retS hS (.nec (.boxC A cs h)) V Φ ∈ w.M i) :
    ∃ (j : ℕ) (hij : i ≤ j) (c : Ann ((A.compAt p).getD .VTypeOne))
      (z : Term σ (w.ctx j) ((A.compAt p).getD .VTypeOne) c),
      (O.mono (w.le hij)).retS hS (.nec (.boxC A (p :: cs) h'))
        (Term.pair (Term.mono (w.le hij) V) z)
        (WFF.mono ((OutLeg.le_view_mono (w.le hij) O).insert (.bnd 0) _) Φ) ∈ w.M j := by
  have hu : (w.ctx i).RootFresh (.free (w.l i).length) := ctxOf_fresh le_rfl
  have hex : WFF.ex _ (compSlot hS p h' O V Φ) ∈ w.M i :=
    BWorld.mem_of_provable (Δ := [_]) (fun φ hφ => by rw [List.mem_singleton.mp hφ]; exact hm)
      ⟨Proof.ret_compS hS O (.nec (.boxC A cs h)) p h' V Φ _ hu
        (Proof.lookup List.mem_cons_self)
        (Proof.ex_intro _ (Term.eta (.root (.free (w.l i).length)) _
          (Ctx.ref_insert_root _ _ _))
          (Proof.conv ?_ (Proof.lookup List.mem_cons_self)))⟩
  · obtain ⟨j, hij, c, z, hz⟩ := w.exW_term hex
    refine ⟨j, hij, c, z, ?_⟩
    rw [instantiate_compSlot_mono] at hz
    exact hz
  · rw [instantiate_compSlot_mono hS p h' (Ctx.le_insert hu.root _)]
    exact congrArg (fun φ => (O.mono (Ctx.le_insert hu.root _)).retS hS
      (.nec (.boxC A (p :: cs) h'))
      (Term.pair (Term.mono (Ctx.le_insert hu.root _) V)
        (Term.eta (.root (.free (w.l i).length)) _ (Ctx.ref_insert_root _ _ _)))
      (WFF.mono ((OutLeg.le_view_mono (Ctx.le_insert hu.root _) O).insert (.bnd 0) _) φ))
      (WFF.bodyRepl_eta' Φ)

end CompNamed

omit [ModalSys.NoFour] in
theorem _root_.V12M.OutLeg.mono_mono {Γ Γ' Γ'' : Ctx} (h : Γ.Le Γ') (h' : Γ'.Le Γ'') :
    (O : OutLeg Γ) → (O.mono h).mono h' = O.mono (h.trans h')
  | .nec => rfl
  | .pos _ _ => rfl

/-- ⭐⭐**Naming several companions' returns, in a world** (any leg): `◇^{boxC A cs}[d ↦ V] Φ` at
    a stage gives, at a later one, `◇^{boxC A (Q ++ cs)}[d ↦ V'] Φ` for some value `V'` that has
    `V` in front of the new companions (`V'` read along `|Q|` first components is `V`). -/
theorem BWorld.ret_comps_named (w : BWorld σ) (hS : ModalSys.BStrong = true) {A : VarType}
    {cs : List (List Step)} {h : A.CompOk cs} :
    ∀ (Q : List (List Step)) (hQ : A.CompOk (Q ++ cs)) {i : ℕ} (O : OutLeg (w.ctx i))
      {a : Ann (A.compsFlat cs)} (V : Term σ (w.ctx i) (A.compsFlat cs) a)
      (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1),
      O.retS hS (.nec (.boxC A cs h)) V Φ ∈ w.M i →
      ∃ (j : ℕ) (hij : i ≤ j) (a' : Ann (A.compsFlat (Q ++ cs)))
        (V' : Term σ (w.ctx j) (A.compsFlat (Q ++ cs)) a'),
        V'.getP (List.replicate Q.length .fst) = some ⟨_, _, Term.mono (w.le hij) V⟩ ∧
        (O.mono (w.le hij)).retS hS (.nec (.boxC A (Q ++ cs) hQ)) V'
          (WFF.mono ((OutLeg.le_view_mono (w.le hij) O).insert (.bnd 0) _) Φ) ∈ w.M j
  | [], _, i, O, a, V, Φ, hm => by
      refine ⟨i, le_rfl, a, V, by rw [Term.mono_refl]; exact getP_nil V, ?_⟩
      cases O <;> (rw [WFF.mono_refl]; exact hm)
  | q :: Q, hQ, i, O, a, V, Φ, hm => by
      obtain ⟨j₁, hij₁, a₁, V₁, hV₁, hm₁⟩ :=
        BWorld.ret_comps_named w hS Q hQ.tail O V Φ hm
      obtain ⟨j₂, hj₁₂, c, z, hm₂⟩ := BWorld.ret_comp_named hS q hQ w _ V₁ _ hm₁
      refine ⟨j₂, hij₁.trans hj₁₂, _, Term.pair (Term.mono (w.le hj₁₂) V₁) z, ?_, ?_⟩
      · change (Term.pair _ _).getP (.fst :: List.replicate Q.length .fst) = _
        rw [getP_pair_fst, getP_mono _ _ _ hV₁, Term.mono_mono]
      · cases O <;> (rw [WFF.mono_mono] at hm₂; exact hm₂)


/-! ## Naming companions at a witnessed shape -/

omit [ModalSys.NoFour] in
/-- `ret_compS`'s value at a witnessed shape: the new companion's value beside the necessary
    part's, the possible part kept. -/
theorem compTm_wit {Γ : Ctx} [Γ.NoSlots] {A X : VarType} {cs : List (List Step)}
    {h : A.CompOk cs} (p : List Step) (h' : A.CompOk (p :: cs)) {M : NShape}
    {a : Ann (A.compsFlat cs)} {b : Ann X} (V : Term σ Γ (A.compsFlat cs) a)
    (t : Term σ Γ X b) {c : Ann ((A.compAt p).getD .VTypeOne)}
    (u : Term σ Γ ((A.compAt p).getD .VTypeOne) c) :
    RShape.compTm A cs h p h' (.wit M X) (Term.pair V t) u =
      ⟨_, Term.pair (Term.pair V u) t⟩ := by
  change (⟨_, Term.holeRead (Term.pair (Term.pair V t) u) _⟩ : Σ e, Term σ Γ _ e) = _
  rw [Term.holeRead_eq_holeAt]
  change (⟨_, Term.pair (Term.pair (Term.holeAt _ _) (Term.holeAt _ _)) (Term.holeAt _ _)⟩ :
    Σ e, Term σ Γ _ e) = _
  exact sig_pair (sig_pair (Term.holeAt_pair_fst_fst V t u) (Term.holeAt_pair_snd _ u))
    (Term.holeAt_pair_fst_snd V t u)

section CompNamedW

variable {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) {A X : VarType}
  {cs : List (List Step)} {h : A.CompOk cs} (p : List Step) (h' : A.CompOk (p :: cs))

/-- The slot formula `◇^{boxC A (p :: cs) × ◇X}[d ↦ ⟨⟨V, z⟩, t⟩] Φ(d)` along a leg, with `z` the
    slot. -/
def compSlotW (O : OutLeg Γ) {a : Ann (A.compsFlat cs)} {b : Ann X}
    (V : Term σ Γ (A.compsFlat cs) a) (t : Term σ Γ X b)
    (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit (.box A) X).ty) 1) :
    WFF σ (Γ.insert (.bnd 0) ((A.compAt p).getD .VTypeOne)) 1 :=
  WFF.bodyRepl (Term.pair
      (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root _) V)
        (Term.eta (.root (.bnd 0)) ((A.compAt p).getD .VTypeOne) (Ctx.ref_insert_root _ _ _)))
      (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root _) t))
    (O.retSlot hS (.wit (.boxC A (p :: cs) h') X) Φ)

/-- The witnessed slot formula, weakened and instantiated. -/
theorem instantiate_compSlotW_mono {Γ' : Ctx} [Γ'.NoSlots] (hle : Γ.Le Γ') (O : OutLeg Γ)
    {a : Ann (A.compsFlat cs)} {b : Ann X} (V : Term σ Γ (A.compsFlat cs) a)
    (t : Term σ Γ X b) (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit (.box A) X).ty) 1)
    {c : Ann ((A.compAt p).getD .VTypeOne)} (z : Term σ Γ' ((A.compAt p).getD .VTypeOne) c) :
    WFF.instantiate Ctx.NoSlots.slots z
        (WFF.mono (hle.insert (.bnd 0) _) (compSlotW hS p h' O V t Φ)) =
      (O.mono hle).retS hS (.wit (.boxC A (p :: cs) h') X)
        (Term.pair (Term.pair (Term.mono hle V) z) (Term.mono hle t))
        (WFF.mono ((OutLeg.le_view_mono hle O).insert (.bnd 0) _) Φ) := by
  unfold compSlotW
  rw [WFF.mono_bodyRepl hle, OutLeg.mono_retSlot hle]
  refine (OutLeg.instantiate_compSlot hS (O.mono hle) (.wit (.boxC A (p :: cs) h') X) _ _
    z).trans ?_
  refine OutLeg.retS_congr (O := O.mono hle) hS _ ?_ rfl
  have e₁ : (⟨_, Term.mono (hle.insert (.bnd 0) ((A.compAt p).getD .VTypeOne))
      (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root _) V)⟩ :
      Σ e, Term σ (Γ'.insert (.bnd 0) ((A.compAt p).getD .VTypeOne)) _ e) =
      ⟨_, Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ')).root _) (Term.mono hle V)⟩ := by
    rw [Term.mono_mono, Term.mono_mono]
  have e₂ := congrArg (Sigma.mk _) (Term.mono_eta (σ := σ)
    (hle.insert (.bnd 0) ((A.compAt p).getD .VTypeOne)) (.root (.bnd 0))
    ((A.compAt p).getD .VTypeOne) (Ctx.ref_insert_root _ _ _))
  have e₃ : (⟨_, Term.mono (hle.insert (.bnd 0) ((A.compAt p).getD .VTypeOne))
      (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root _) t)⟩ :
      Σ e, Term σ (Γ'.insert (.bnd 0) ((A.compAt p).getD .VTypeOne)) _ e) =
      ⟨_, Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ')).root _) (Term.mono hle t)⟩ := by
    rw [Term.mono_mono, Term.mono_mono]
  exact (sig_subst _ _ _ (sig_pair (sig_pair e₁ e₂) e₃)).trans
    (sig_pair (sig_pair (Term.subst_single_mono_sig z (Term.mono hle V))
      (Term.subst_eta_tm _ _ _ _ _ _ z (Subst.at_single_root _ _)))
      (Term.subst_single_mono_sig z (Term.mono hle t)))

/-- ⭐⭐**Naming a companion's return at a witnessed shape, in a world** (any leg):
    `◇^{boxC A cs × ◇X}[d ↦ ⟨V, t⟩] Φ` at a stage gives, at a later one,
    `◇^{boxC A (p :: cs) × ◇X}[d ↦ ⟨⟨V, z⟩, t⟩] Φ` for some term `z`. -/
theorem BWorld.ret_comp_namedW (w : BWorld σ) {i : ℕ} (O : OutLeg (w.ctx i))
    {a : Ann (A.compsFlat cs)} {b : Ann X} (V : Term σ (w.ctx i) (A.compsFlat cs) a)
    (t : Term σ (w.ctx i) X b)
    (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit (.box A) X).ty) 1)
    (hm : O.retS hS (.wit (.boxC A cs h) X) (Term.pair V t) Φ ∈ w.M i) :
    ∃ (j : ℕ) (hij : i ≤ j) (c : Ann ((A.compAt p).getD .VTypeOne))
      (z : Term σ (w.ctx j) ((A.compAt p).getD .VTypeOne) c),
      (O.mono (w.le hij)).retS hS (.wit (.boxC A (p :: cs) h') X)
        (Term.pair (Term.pair (Term.mono (w.le hij) V) z) (Term.mono (w.le hij) t))
        (WFF.mono ((OutLeg.le_view_mono (w.le hij) O).insert (.bnd 0) _) Φ) ∈ w.M j := by
  have hu : (w.ctx i).RootFresh (.free (w.l i).length) := ctxOf_fresh le_rfl
  have hex : WFF.ex _ (compSlotW hS p h' O V t Φ) ∈ w.M i :=
    BWorld.mem_of_provable (Δ := [_]) (fun φ hφ => by rw [List.mem_singleton.mp hφ]; exact hm)
      ⟨Proof.ret_compS hS O (.wit (.boxC A cs h) X) p h' (Term.pair V t) Φ _ hu
        (Proof.lookup List.mem_cons_self)
        (Proof.ex_intro _ (Term.eta (.root (.free (w.l i).length)) _
          (Ctx.ref_insert_root _ _ _))
          (Proof.conv ?_ (Proof.lookup List.mem_cons_self)))⟩
  · obtain ⟨j, hij, c, z, hz⟩ := w.exW_term hex
    refine ⟨j, hij, c, z, ?_⟩
    rw [instantiate_compSlotW_mono] at hz
    exact hz
  · rw [instantiate_compSlotW_mono hS p h' (Ctx.le_insert hu.root _)]
    exact OutLeg.retS_congr hS _ _ (compTm_wit (M := .boxC A cs h) p h'
      (Term.mono (Ctx.le_insert hu.root _) V) (Term.mono (Ctx.le_insert hu.root _) t) _)
      (congrArg (WFF.mono _) (WFF.bodyRepl_eta' Φ))

end CompNamedW

/-- ⭐⭐**Naming several companions' returns at a witnessed shape, in a world** (any leg): as
    `ret_comps_named`, the possible part's value kept. -/
theorem BWorld.ret_comps_namedW (w : BWorld σ) (hS : ModalSys.BStrong = true) {A X : VarType}
    {cs : List (List Step)} {h : A.CompOk cs} :
    ∀ (Q : List (List Step)) (hQ : A.CompOk (Q ++ cs)) {i : ℕ} (O : OutLeg (w.ctx i))
      {a : Ann (A.compsFlat cs)} {b : Ann X} (V : Term σ (w.ctx i) (A.compsFlat cs) a)
      (t : Term σ (w.ctx i) X b)
      (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit (.box A) X).ty) 1),
      O.retS hS (.wit (.boxC A cs h) X) (Term.pair V t) Φ ∈ w.M i →
      ∃ (j : ℕ) (hij : i ≤ j) (a' : Ann (A.compsFlat (Q ++ cs)))
        (V' : Term σ (w.ctx j) (A.compsFlat (Q ++ cs)) a'),
        V'.getP (List.replicate Q.length .fst) = some ⟨_, _, Term.mono (w.le hij) V⟩ ∧
        (O.mono (w.le hij)).retS hS (.wit (.boxC A (Q ++ cs) hQ) X)
          (Term.pair V' (Term.mono (w.le hij) t))
          (WFF.mono ((OutLeg.le_view_mono (w.le hij) O).insert (.bnd 0) _) Φ) ∈ w.M j
  | [], _, i, O, a, b, V, t, Φ, hm => by
      refine ⟨i, le_rfl, a, V, by rw [Term.mono_refl]; exact getP_nil V, ?_⟩
      cases O <;> (rw [WFF.mono_refl, Term.mono_refl]; exact hm)
  | q :: Q, hQ, i, O, a, b, V, t, Φ, hm => by
      obtain ⟨j₁, hij₁, a₁, V₁, hV₁, hm₁⟩ :=
        BWorld.ret_comps_namedW w hS Q hQ.tail O V t Φ hm
      obtain ⟨j₂, hj₁₂, c, z, hm₂⟩ := BWorld.ret_comp_namedW hS q hQ w _ V₁ _ _ hm₁
      refine ⟨j₂, hij₁.trans hj₁₂, _, Term.pair (Term.mono (w.le hj₁₂) V₁) z, ?_, ?_⟩
      · change (Term.pair _ _).getP (.fst :: List.replicate Q.length .fst) = _
        rw [getP_pair_fst, getP_mono _ _ _ hV₁, Term.mono_mono]
      · cases O <;> (rw [WFF.mono_mono, Term.mono_mono] at hm₂; exact hm₂)

end BArrow

end V12M
