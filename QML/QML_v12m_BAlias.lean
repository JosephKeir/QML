import QML.QML_v12m_BNetRet

/-!
# QML v12m — strong B on the network: aliases

A child made for a returning-possibility atom `◇[d ↦ t] Φ` must come back as `t`, but a network
arrow commits roots to roots (docs §11.20).  So the parent first gets a fresh root `y` that is an
**alias** of `t`: its theory is extended by `ψ(y) ↔ ψ(t)` for every slot formula `ψ` over its
context.  No formula and no rule is added; `y` is a construction-level Henkin name.

* `aliasFormula`, `aliasSet`: the alias set;
* ⭐`alias_consistent`: a derivation of `⊥` from the theory and the alias set becomes one from the
  theory, substituting `t` for the fresh `y` (`Proof.subst`), under which every alias formula is
  `χ ↔ χ`;
* `aliasStep`, `aliasStep_ok`: the node grown by the alias.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

section Alias

variable {l : List VarType} {A : VarType}

/-- The old context inside the context with the fresh root. -/
abbrev aliasLe (A : VarType) (l : List VarType) : (ctxOf l).Le (ctxOf (A :: l)) :=
  ctxOf_le_append [A] l

/-- ⭐The alias formula of a slot formula `ψ`: `ψ(y) ↔ ψ(t)`, `y` the fresh root. -/
def aliasFormula {a : Ann A} (t : Term σ (ctxOf l) A a)
    (ψ : WFF σ ((ctxOf l).insert (.bnd 0) A) 1) : WFF σ (ctxOf (A :: l)) 0 :=
  WFF.and
    (WFF.imp
      (WFF.instantiate Ctx.NoSlots.slots
        (Term.eta (.root (.free l.length)) A (ctxOf_ref_new A l))
        (WFF.mono ((aliasLe A l).insert (.bnd 0) A) ψ))
      (WFF.instantiate Ctx.NoSlots.slots (Term.mono (aliasLe A l) t)
        (WFF.mono ((aliasLe A l).insert (.bnd 0) A) ψ)))
    (WFF.imp
      (WFF.instantiate Ctx.NoSlots.slots (Term.mono (aliasLe A l) t)
        (WFF.mono ((aliasLe A l).insert (.bnd 0) A) ψ))
      (WFF.instantiate Ctx.NoSlots.slots
        (Term.eta (.root (.free l.length)) A (ctxOf_ref_new A l))
        (WFF.mono ((aliasLe A l).insert (.bnd 0) A) ψ)))

/-- The alias set of `t`. -/
def aliasSet {a : Ann A} (t : Term σ (ctxOf l) A a) : Set (WFF σ (ctxOf (A :: l)) 0) :=
  {φ | ∃ ψ, φ = aliasFormula t ψ}

/-- Substituting `t` for the fresh root. -/
abbrev aliasS {a : Ann A} (t : Term σ (ctxOf l) A a) : Subst σ (ctxOf l) :=
  Subst.single (.free l.length) (.tm t)

theorem ok_aliasS {a : Ann A} (t : Term σ (ctxOf l) A a) :
    Subst.Ok (ctxOf (A :: l)) (aliasS t) :=
  Subst.ok_single (Ctx.Le.refl _) rfl

theorem coh_aliasS {a : Ann A} (t : Term σ (ctxOf l) A a) :
    Subst.Coh (Subst.singleIdx (.free l.length) (.tm t)) (ctxOf (A :: l)) (aliasS t) :=
  Subst.coh_single (ctxOf_fresh le_rfl) (Ctx.Le.refl _) rfl

/-- The substitution leaves the old context's addresses alone. -/
theorem aliasS_at_old {a : Ann A} (t : Term σ (ctxOf l) A a) :
    ∀ v T, (ctxOf l).ref v = some T → (aliasS (σ := σ) t).at v = .ren v :=
  fun _ _ hv => Subst.single_at_ne (Ctx.ref_rt_ne (ctxOf_fresh le_rfl) hv)

/-- An old formula, substituted, is itself. -/
theorem subst_alias_mono {a : Ann A} (t : Term σ (ctxOf l) A a) (φ : WFF σ (ctxOf l) 0) :
    WFF.subst _ (aliasS t) (ok_aliasS t) (coh_aliasS t) Ctx.NoSlots.slots Ctx.NoSlots.slots
      (WFF.mono (aliasLe A l) φ) = φ := by
  rw [WFF.subst_mono _ _ _ _ Ctx.NoSlots.slots,
    WFF.subst_ren (Ctx.Le.refl _) _ _ _ _ _ (aliasS_at_old t) φ, WFF.mono_refl]

/-- An old term, substituted, is itself. -/
theorem subst_alias_mono_tm {a : Ann A} (t : Term σ (ctxOf l) A a) {B : VarType} {b : Ann B}
    (s : Term σ (ctxOf l) B b) :
    (⟨_, Term.subst _ (aliasS t) (ok_aliasS t) (coh_aliasS t) (Term.mono (aliasLe A l) s)⟩ :
      Σ c, Term σ (ctxOf l) B c) = ⟨b, s⟩ := by
  rw [Term.subst_mono]
  exact (Term.subst_ren (Ctx.Le.refl _) _ _ _ (aliasS_at_old t) s).trans
    (congrArg (Sigma.mk _) (Term.mono_refl _ s))

/-- An old slot formula, substituted under its slot, is itself. -/
theorem subst_alias_mono_under {a : Ann A} (t : Term σ (ctxOf l) A a)
    (ψ : WFF σ ((ctxOf l).insert (.bnd 0) A) 1) :
    WFF.subst (VarSymb.shiftSlot (Subst.singleIdx (.free l.length) (.tm t)) 0 0)
      ((aliasS t).under 0 0 A (Ctx.NoSlots.slots (Γ := ctxOf l)).root)
      (Subst.ok_under (ok_aliasS t) A _) (Subst.coh_under (ok_aliasS t) (coh_aliasS t)
        Ctx.NoSlots.slots A _)
      (Ctx.NoSlots.slots.insert A) (Ctx.NoSlots.slots.insert A)
      (WFF.mono ((aliasLe A l).insert (.bnd 0) A) ψ) = ψ := by
  rw [WFF.subst_mono _ _ _ _ (Ctx.NoSlots.slots.insert A),
    WFF.subst_ren (Ctx.Le.refl _) _ _ _ _ _
      (Subst.ren_under (aliasS_at_old t) A (Ctx.NoSlots.slots (Γ := ctxOf l)).root) ψ,
    WFF.mono_refl]

/-- ⭐An alias formula, substituted, is `χ ↔ χ`. -/
theorem subst_aliasFormula {a : Ann A} (t : Term σ (ctxOf l) A a)
    (ψ : WFF σ ((ctxOf l).insert (.bnd 0) A) 1) :
    WFF.subst _ (aliasS t) (ok_aliasS t) (coh_aliasS t) Ctx.NoSlots.slots Ctx.NoSlots.slots
      (aliasFormula t ψ) =
      WFF.and (WFF.imp (WFF.instantiate Ctx.NoSlots.slots t ψ)
          (WFF.instantiate Ctx.NoSlots.slots t ψ))
        (WFF.imp (WFF.instantiate Ctx.NoSlots.slots t ψ)
          (WFF.instantiate Ctx.NoSlots.slots t ψ)) := by
  have hy : WFF.subst _ (aliasS t) (ok_aliasS t) (coh_aliasS t) Ctx.NoSlots.slots
      Ctx.NoSlots.slots (WFF.instantiate Ctx.NoSlots.slots
        (Term.eta (.root (.free l.length)) A (ctxOf_ref_new A l))
        (WFF.mono ((aliasLe A l).insert (.bnd 0) A) ψ)) =
      WFF.instantiate Ctx.NoSlots.slots t ψ := by
    rw [WFF.subst_instantiate, subst_alias_mono_under]
    exact WFF.instantiate_congr_sig _ (Term.subst_eta_tm _ _ _ _ _ _ t
      (by change Subst.single _ _ (.root (.free l.length)) = _; exact if_pos rfl)) ψ
  have ht : WFF.subst _ (aliasS t) (ok_aliasS t) (coh_aliasS t) Ctx.NoSlots.slots
      Ctx.NoSlots.slots (WFF.instantiate Ctx.NoSlots.slots (Term.mono (aliasLe A l) t)
        (WFF.mono ((aliasLe A l).insert (.bnd 0) A) ψ)) =
      WFF.instantiate Ctx.NoSlots.slots t ψ := by
    rw [WFF.subst_instantiate, subst_alias_mono_under]
    exact WFF.instantiate_congr_sig _ (subst_alias_mono_tm t t) ψ
  unfold aliasFormula
  change WFF.and (WFF.imp (WFF.subst _ _ _ _ _ _ _) (WFF.subst _ _ _ _ _ _ _))
    (WFF.imp (WFF.subst _ _ _ _ _ _ _) (WFF.subst _ _ _ _ _ _ _)) = _
  rw [hy, ht]

/-- ⭐**Aliases are consistent**: substituting `t` for the fresh root turns a refutation of the
    theory with the alias set into a refutation of the theory alone. -/
theorem alias_consistent {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.Consistent M) {a : Ann A}
    (t : Term σ (ctxOf l) A a) :
    Theory.Consistent (WFF.mono (aliasLe A l) '' M ∪ aliasSet t) := by
  rintro ⟨Δ, hΔ, ⟨p⟩⟩
  have q := Proof.subst p (aliasS t) (ok_aliasS t) (coh_aliasS t) Ctx.NoSlots.slots
  refine hM (Derives.trans (S' := {x | x ∈ Δ.map (WFF.subst _ (aliasS t) (ok_aliasS t)
    (coh_aliasS t) Ctx.NoSlots.slots Ctx.NoSlots.slots)}) ?_ ⟨_, fun _ h => h, ⟨q⟩⟩)
  intro δ hδ
  obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hδ
  rcases hΔ φ hφ with ⟨φ', hφ', rfl⟩ | ⟨ψ, rfl⟩
  · rw [subst_alias_mono]
    exact Theory.Derives.of_mem hφ'
  · rw [subst_aliasFormula]
    exact ⟨[], fun _ h => absurd h List.not_mem_nil,
      ⟨Proof.and_intro (Proof.imp_intro (Proof.lookup List.mem_cons_self))
        (Proof.imp_intro (Proof.lookup List.mem_cons_self))⟩⟩

end Alias

/-! ## The alias operation -/

/-- The node grown by an alias of `t`. -/
noncomputable def aliasStep (t : NodeSt σ) {A : VarType} {a : Ann A}
    (tm : Term σ (ctxOf t.l) A a) : NodeSt σ :=
  ⟨A :: t.l, complete (WFF.mono (aliasLe A t.l) '' t.M ∪ aliasSet tm)⟩

/-- ⭐The aliased node is maximal consistent, extends the old one, and holds the alias set. -/
theorem aliasStep_ok {t : NodeSt σ} (ht : Theory.IsMCS t.M) {A : VarType} {a : Ann A}
    (tm : Term σ (ctxOf t.l) A a) :
    Theory.IsMCS (aliasStep t tm).M ∧ Grows t (aliasStep t tm) ∧
      aliasSet tm ⊆ (aliasStep t tm).M := by
  obtain ⟨hsub, hmcs⟩ := complete_spec (alias_consistent ht.1 tm)
  exact ⟨hmcs, ⟨⟨[A], rfl⟩, fun φ hφ => hsub (Or.inl ⟨φ, hφ, rfl⟩)⟩, fun φ hφ => hsub (Or.inr hφ)⟩

namespace NetSt

/-- An alias obligation: a term over a list of a node's variables. -/
abbrev AliasObl (σ : Signature) :=
  Σ l : List VarType, Σ A : VarType, Σ a : Ann A, Term σ (ctxOf l) A a

/-- ⭐Give the node `s` an alias of a term over an earlier list of its variables. -/
noncomputable def mkAlias (N : NetSt σ) (s : Node) : AliasObl σ → NetSt σ
  | ⟨l, _, _, tm⟩ =>
      if h : l <:+ (N.st s).l then
        N.setSt s (aliasStep (N.st s) (Term.mono (ctxOf_le_of_suffix h) tm))
      else N

variable [ModalSys.NoFour]

/-- ⭐Aliases preserve the invariants under strong B. -/
theorem GoodS.mkAlias {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {s : Node}
    (hs : N.Live s) (o : AliasObl σ) : (N.mkAlias s o).GoodS hS := by
  obtain ⟨l, A, a, tm⟩ := o
  simp only [NetSt.mkAlias]
  split_ifs with h
  · obtain ⟨h₁, h₂, -⟩ := aliasStep_ok (hN.mcs s hs) (Term.mono (ctxOf_le_of_suffix h) tm)
    exact hN.setSt hs h₂ h₁
  · exact hN

theorem Ext.mkAlias {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {s : Node}
    (hs : N.Live s) (o : AliasObl σ) : Ext N (N.mkAlias s o) := by
  obtain ⟨l, A, a, tm⟩ := o
  simp only [NetSt.mkAlias]
  split_ifs with h
  · exact Ext.setSt (aliasStep_ok (hN.mcs s hs) (Term.mono (ctxOf_le_of_suffix h) tm)).2.1
  · exact Ext.refl N

end NetSt

end BArrow

end V12M
