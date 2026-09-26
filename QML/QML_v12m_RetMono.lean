import QML.QML_v12m_ProofSubst

/-!
# QML v12m — weakening commutes with the strong T hypotheses

The canonical model for strong T adds, for a term `t`, a fresh witness `c` together with every
hypothesis `WFF.retHyp` at every later stage.  A derivation at a later stage uses those hypotheses
*lifted* along stage inclusions, while the rule `T_dia` wants them as `WFF.retHyp` at that stage.
The lemmas here identify the two:

* `WFF.collapse_mono`: collapsing commutes with weakening (the term version is
  `Term.collapse_mono`);
* `WFF.mono_instantiate`, `WFF.mono_hereRead`: the `here` reading commutes with weakening;
* `WFF.mono_viewRead`, `WFF.mono_bindFree`: renamings commute with weakening;
* ⭐`WFF.mono_retHyp`: so does a whole hypothesis.
-/

namespace V12M

variable [ModalSys]

namespace Subst

variable {σ : Signature} {Δ : Ctx}

theorem mono_apply {Δ' : Ctx} (θ : Subst σ Δ) (h : Δ.Le Δ') (v : VarSymb) :
    θ.mono h v = (θ v).mono h :=
  rfl

end Subst

variable {σ : Signature}

/-! ## Collapsing commutes with weakening -/

theorem Rel.collapse_mono {k : ℕ} {Γ₁ Γ₂ Γ₁' Γ₂' : Ctx}
    (h : Ctx.Collapses k Γ₁ Γ₂) (h' : Ctx.Collapses k Γ₁' Γ₂') (l₁ : Γ₁.Le Γ₁')
    (l₂ : Γ₂.Le Γ₂') : ∀ {n : ℕ} (ρ : Rel σ Γ₁ n),
      Rel.collapse h' (Rel.mono l₁ ρ) = Rel.mono l₂ (Rel.collapse h ρ)
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.collapse h' (Rel.mono l₁ ρ)) (Term.collapse h' (Term.mono l₁ t)) = _
      rw [Rel.collapse_mono h h' l₁ l₂ ρ, Term.collapse_mono h h' l₁ l₂ t]
      rfl

theorem WFF.collapse_mono : ∀ {k : ℕ} {Γ₁ Γ₂ Γ₁' Γ₂' : Ctx} {d : ℕ}
    (h : Ctx.Collapses k Γ₁ Γ₂) (h' : Ctx.Collapses k Γ₁' Γ₂') (l₁ : Γ₁.Le Γ₁')
    (l₂ : Γ₂.Le Γ₂') (hs : Γ₁.SlotsFrom d) (hs' : Γ₁'.SlotsFrom d) (φ : WFF σ Γ₁ d),
    WFF.collapse h' hs' (WFF.mono l₁ φ) = WFF.mono l₂ (WFF.collapse h hs φ)
  | _, _, _, _, _, _, h, h', l₁, l₂, _, _, .atom ρ =>
      congrArg WFF.atom (Rel.collapse_mono h h' l₁ l₂ ρ)
  | _, _, _, _, _, _, h, h', l₁, l₂, _, _, .eq t s =>
      congrArg₂ WFF.eq (Term.collapse_mono h h' l₁ l₂ t) (Term.collapse_mono h h' l₁ l₂ s)
  | _, _, _, _, _, _, _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, _, _, h, h', l₁, l₂, hs, hs', .and φ ψ =>
      congrArg₂ WFF.and (WFF.collapse_mono h h' l₁ l₂ hs hs' φ)
        (WFF.collapse_mono h h' l₁ l₂ hs hs' ψ)
  | _, _, _, _, _, _, h, h', l₁, l₂, hs, hs', .or φ ψ =>
      congrArg₂ WFF.or (WFF.collapse_mono h h' l₁ l₂ hs hs' φ)
        (WFF.collapse_mono h h' l₁ l₂ hs hs' ψ)
  | _, _, _, _, _, _, h, h', l₁, l₂, hs, hs', .imp φ ψ =>
      congrArg₂ WFF.imp (WFF.collapse_mono h h' l₁ l₂ hs hs' φ)
        (WFF.collapse_mono h h' l₁ l₂ hs hs' ψ)
  | _, _, _, _, _, _, h, h', l₁, l₂, hs, hs', .all T φ =>
      congrArg (WFF.all T) (WFF.collapse_mono (h.insert (hs.rootFresh le_rfl) T)
        (h'.insert (hs'.rootFresh le_rfl) T) (l₁.insert _ T) (l₂.insert _ T) (hs.insert T)
        (hs'.insert T) φ)
  | _, _, _, _, _, _, h, h', l₁, l₂, hs, hs', .ex T φ =>
      congrArg (WFF.ex T) (WFF.collapse_mono (h.insert (hs.rootFresh le_rfl) T)
        (h'.insert (hs'.rootFresh le_rfl) T) (l₁.insert _ T) (l₂.insert _ T) (hs.insert T)
        (hs'.insert T) φ)
  | _, _, _, _, _, _, h, h', l₁, l₂, hs, hs', .box φ =>
      congrArg WFF.box (WFF.collapse_mono h.boxIn h'.boxIn l₁.boxIn l₂.boxIn hs.boxIn hs'.boxIn φ)
  | _, _, _, _, _, _, h, h', l₁, l₂, hs, hs', .dia x _ φ => by
      simp only [WFF.collapse, WFF.mono]
      rw [WFF.collapse_mono (h.diaIn x) (h'.diaIn x) (l₁.diaIn x) (l₂.diaIn _) (hs.diaIn x)
        (hs'.diaIn x) φ]
  | _, _, _, _, _, _, h, h', l₁, l₂, _, _, .here hT s t =>
      WFF.here_congr' hT (Term.collapse_mono h h' l₁ l₂ s) (Term.collapse_mono h h' l₁ l₂ t)
  | _, _, _, _, _, _, h, h', l₁, l₂, _, _, .diaEq s s' =>
      WFF.diaEq_congr' (Term.collapse_mono h h' l₁ l₂ s) (Term.collapse_mono h h' l₁ l₂ s')

/-! ## The two readings, and binding, commute with weakening -/

/-- Instantiating commutes with weakening. -/
theorem WFF.mono_instantiate {Γ Γ' : Ctx} (h : Γ.Le Γ') (hs : Γ.SlotsFrom 0)
    (hs' : Γ'.SlotsFrom 0) {T : VarType} {a : Ann T} (t : Term σ Γ T a)
    (φ : WFF σ (Γ.insert (.bnd 0) T) 1) :
    WFF.mono h (WFF.instantiate hs t φ) =
      WFF.instantiate hs' (Term.mono h t) (WFF.mono (h.insert (.bnd 0) T) φ) := by
  unfold WFF.instantiate WFF.substRoot
  rw [WFF.mono_subst, WFF.subst_mono]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ ?_ φ
  refine Subst.sim_of ?_
  intro v U _ _
  rw [Subst.mono_apply]
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    rw [Subst.single_root, Subst.single_root]
    exact .refl _
  · rw [Subst.single_ne _ hvr, Subst.single_ne _ hvr]
    exact .refl _

theorem WFF.mono_hereRead {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (hT : ModalSys.T = true)
    (h : Γ.Le Γ') {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    WFF.mono h (WFF.hereRead hT t ψ) =
      WFF.hereRead hT (Term.mono h t) (WFF.mono (h.boxIn.insert (.bnd 0) A) ψ) := by
  unfold WFF.hereRead
  rw [WFF.mono_instantiate h _ Ctx.NoSlots.slots t,
    ← WFF.collapse_mono _
      ((Ctx.collapses_boxIn_self hT Γ').insert
        ((Ctx.NoSlots.slots (Γ := Γ'.boxIn)).rootFresh (le_refl 0)) A)
      (h.boxIn.insert _ A) (h.insert _ A) _ ((Ctx.NoSlots.slots (Γ := Γ'.boxIn)).insert A) ψ]

theorem WFF.mono_viewRead {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ') {c : ℕ}
    (hc : Γ.RootFresh (.free c)) (hc' : Γ'.RootFresh (.free c)) (A : VarType)
    (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    WFF.mono ((h.insert (.free c) (.VTypeDia A)).diaIn (.root (.free c))) (WFF.viewRead c hc A ψ) =
      WFF.viewRead c hc' A (WFF.mono (h.boxIn.insert (.bnd 0) A) ψ) := by
  unfold WFF.viewRead WFF.renameRoot
  rw [WFF.mono_subst, WFF.subst_mono]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ ?_ ψ
  refine Subst.sim_of ?_
  intro v U _ _
  rw [Subst.mono_apply]
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    rw [Subst.single_root, Subst.single_root]
    exact .refl _
  · rw [Subst.single_ne _ hvr, Subst.single_ne _ hvr]
    exact .refl _

theorem WFF.mono_bindFree {Γ Γ' : Ctx} (h : Γ.Le Γ') {u : ℕ} (hu : Γ.RootFresh (.free u))
    (hu' : Γ'.RootFresh (.free u)) (hs : Γ.SlotsFrom 0) (hs' : Γ'.SlotsFrom 0) (T : VarType)
    (φ : WFF σ (Γ.insert (.free u) T) 0) :
    WFF.mono (h.insert (.bnd 0) T) (WFF.bindFree u hu hs T φ) =
      WFF.bindFree u hu' hs' T (WFF.mono (h.insert (.free u) T) φ) := by
  unfold WFF.bindFree WFF.renameRoot
  rw [WFF.mono_subst, WFF.subst_mono]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ ?_ φ
  refine Subst.sim_of ?_
  intro v U _ _
  rw [Subst.mono_apply]
  by_cases hvr : v = .root (.free u)
  · subst hvr
    rw [Subst.single_root, Subst.single_root]
    exact .refl _
  · rw [Subst.single_ne _ hvr, Subst.single_ne _ hvr]
    exact .refl _

/-- ⭐Weakening a strong T hypothesis is the hypothesis for the weakened term and hole formula. -/
theorem WFF.mono_retHyp {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (hT : ModalSys.T = true)
    (h : Γ.Le Γ') {A : VarType} {a : Ann A} (t : Term σ Γ A a) {c y : ℕ}
    (hc : Γ.RootFresh (.free c)) (hc' : Γ'.RootFresh (.free c)) (hy : Γ.RootFresh (.free y))
    (hy' : Γ'.RootFresh (.free y)) (hyc : y ≠ c) (B : VarType)
    (ψ : WFF σ ((Γ.insert (.free y) B).boxIn.insert (.bnd 0) A) 1) :
    WFF.mono (h.insert (.free c) (.VTypeDia A)) (WFF.retHyp hT t c y hc hy hyc B ψ) =
      WFF.retHyp hT (Term.mono h t) c y hc' hy' hyc B
        (WFF.mono ((h.insert (.free y) B).boxIn.insert (.bnd 0) A) ψ) := by
  have hne : Root.free y ≠ Root.free c := fun e => hyc (Root.free.inj e)
  have hcy : (Γ.insert (.free y) B).RootFresh (.free c) := hc.insert_ne hne B
  have hcy' : (Γ'.insert (.free y) B).RootFresh (.free c) := hc'.insert_ne hne B
  have ht : Term.mono (Ctx.le_insert hy'.root B) (Term.mono h t) =
      Term.mono (h.insert (.free y) B) (Term.mono (Ctx.le_insert hy.root B) t) := by
    rw [Term.mono_mono, Term.mono_mono]
  have hbody : WFF.mono ((h.insert (.free y) B).insert (.free c) (.VTypeDia A))
      (WFF.imp ((WFF.hereRead hT (Term.mono (Ctx.le_insert hy.root B) t) ψ).weaken hcy.root
          (.VTypeDia A))
        (.dia (.root (.free c)) ⟨A, Ctx.ref_insert_root _ (.free c) (.VTypeDia A)⟩
          (WFF.viewRead c hcy A ψ))) =
      WFF.imp ((WFF.hereRead hT (Term.mono (Ctx.le_insert hy'.root B) (Term.mono h t))
          (WFF.mono ((h.insert (.free y) B).boxIn.insert (.bnd 0) A) ψ)).weaken hcy'.root
          (.VTypeDia A))
        (.dia (.root (.free c)) ⟨A, Ctx.ref_insert_root _ (.free c) (.VTypeDia A)⟩
          (WFF.viewRead c hcy' A
            (WFF.mono ((h.insert (.free y) B).boxIn.insert (.bnd 0) A) ψ))) := by
    refine congrArg₂ WFF.imp ?_ ?_
    · unfold WFF.weaken
      rw [WFF.mono_mono, ht, ← WFF.mono_hereRead hT (h.insert (.free y) B), WFF.mono_mono]
    · change WFF.dia _ _ (WFF.mono (((h.insert (.free y) B).insert (.free c) (.VTypeDia A)).diaIn
        (.root (.free c))) (WFF.viewRead c hcy A ψ)) = _
      rw [WFF.mono_viewRead (h.insert (.free y) B) hcy hcy' A ψ]
  unfold WFF.retHyp
  refine congrArg (WFF.all B) ?_
  rw [WFF.mono_bindFree (h.insert (.free c) (.VTypeDia A)) (hy.insert_ne hne.symm _)
    (hy'.insert_ne hne.symm _) Ctx.NoSlots.slots Ctx.NoSlots.slots B]
  refine congrArg (WFF.bindFree y (hy'.insert_ne hne.symm (.VTypeDia A)) Ctx.NoSlots.slots B) ?_
  rw [WFF.mono_mono, ← hbody, WFF.mono_mono]

/-- ⭐Weakening commutes with the `Here` atom, along **any** inclusion that keeps the witness
    declared: `mono` of `here` is `here` of the two `mono`s, and the subject is an η-expansion
    (`Term.mono_eta`).  The declarations are propositions, so which proof each side carries does not
    matter.  This is all `WFF.mono_retHyp` amounted to for the new rule. -/
theorem WFF.mono_hereAt_of_le {Γ Γ' : Ctx} (hT : ModalSys.T = true) (h : Γ.Le Γ') {A : VarType}
    (x : VarSymb) (hx : Γ.ref x = some (.VTypeDia A)) (hx' : Γ'.ref x = some (.VTypeDia A))
    {a : Ann A} (t : Term σ Γ A a) :
    WFF.mono h (WFF.hereAt hT x hx t : WFF σ Γ 0) = WFF.hereAt hT x hx' (Term.mono h t) :=
  WFF.here_congr' hT (Term.mono_eta _ _ _ _) rfl

/-- The same at a declaration the inclusion itself makes, as `Proof.T_dia` states it. -/
theorem WFF.mono_hereAt {Γ Γ' : Ctx} (hT : ModalSys.T = true) (h : Γ.Le Γ') {A : VarType}
    {a : Ann A} (t : Term σ Γ A a) {c : ℕ} (hc : Γ.RootFresh (.free c))
    (hc' : Γ'.RootFresh (.free c)) :
    WFF.mono (h.insert (.free c) (.VTypeDia A))
        (WFF.hereAt hT (.root (.free c)) (Ctx.ref_insert_root Γ (.free c) (.VTypeDia A))
          (Term.weaken hc.root (.VTypeDia A) t) : WFF σ (Γ.insert (.free c) (.VTypeDia A)) 0) =
      WFF.hereAt hT (.root (.free c)) (Ctx.ref_insert_root Γ' (.free c) (.VTypeDia A))
        (Term.weaken hc'.root (.VTypeDia A) (Term.mono h t)) := by
  refine WFF.here_congr' hT (Term.mono_eta _ _ _ _) ?_
  simp only [Term.weaken]
  rw [Term.mono_mono, Term.mono_mono]

end V12M
