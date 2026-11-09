import QML.QML_v12m_ProofSubst

/-!
# QML v12m — admissible rules, proof-theoretically

Rules shown admissible by transforming proofs, so for every combination of the flags (K5 and KD5
included).  The semantic counterparts, through completeness across the cube, are in
`QML_v12m_SemAdmissible`; what is still to do here is item 7 of `docs/v12-metatheory-todo.md`.

## Generalisation on declared variables

A proof of `φ(c)` from hypotheses that do not mention a declared variable `c` gives a proof of
`∀x. φ(x)` from the same hypotheses (`docs/v12-metatheory-todo.md`, item 2).  `all_intro` binds an
eigenvariable, the newest declaration; this binds **any** declared root.

* The context is written `Γ₁.insert (.free c) T` with `c` fresh for `Γ₁`.  As a function a context
  does not record the order of its declarations, so this covers a root declared anywhere at the
  top level.  The hypotheses live in `Γ₁`, so they do not mention `c`.
* **The declaration stays.**  No domain is assumed nonempty, and declaring `c : T` proves
  `∃x:T. ⊤`, so the conclusion keeps `c` declared and binds a copy of it.
* *The proof:* rename `c` to the first fresh name `u` (`genS`, by `Proof.subst`), then bind `u`
  (`all_intro`).  The renaming is the same map on addresses and on annotation indices
  (`Subst.setIdx`): that is what carries a variable of `◇` type, whose witnesses live in
  annotations.
* ⭐`WFF.genV c T hc φ`: `φ` with `c` made the bound variable.  ⭐`Proof.genVar`: the rule.
* *Not* generalisation on **constants** (nullary function symbols): those are read per world and
  occur under modalities.  The natural statement, generalising the promoted constant `□ᵏ f` to a
  variable of type `□ᵏ Var`, fails with T, 4 or strong B (the item's notes); it should hold in K, D
  and weak B.
-/

namespace V12M

variable [ModalSys]

namespace Subst

variable {σ : Signature} {Δ : Ctx}

/-- Setting a root's entry does not change the reading of an address below another root. -/
theorem at_set_of_rt_ne (θ : Subst σ Δ) (r : Root) (e : SubE σ Δ) :
    ∀ v : VarSymb, v.rt ≠ r → (θ.set r e).at v = θ.at v
  | .root r', h => set_ne θ e (fun he => h (by cases he; rfl))
  | .step v s, h => by
      change (if s.isProj then ((θ.set r e).at v).proj s else θ.set r e (.step v s)) =
        (if s.isProj then (θ.at v).proj s else θ (.step v s))
      rw [at_set_of_rt_ne θ r e v h, set_ne θ e (fun he => VarSymb.noConfusion he)]

end Subst

variable {σ : Signature}

section

variable {Γ₁ : Ctx} (c : ℕ) (T : VarType) (hc : Γ₁.RootFresh (.free c))
  [(Γ₁.insert (.free c) T).Presented]

/-- The fresh name `c` is renamed to: the first one the presentation leaves unused. -/
abbrev genU : ℕ := Ctx.Presented.bound (Γ₁.insert (.free c) T)

theorem genU_fresh : (Γ₁.insert (.free c) T).RootFresh (.free (genU (Γ₁ := Γ₁) c T)) :=
  Ctx.Presented.fresh_bound _ le_rfl

/-- The context the renamed formula lives in: `c` still declared, `u` declared after it. -/
abbrev genCtx : Ctx := (Γ₁.insert (.free c) T).insert (.free (genU (Γ₁ := Γ₁) c T)) T

include hc in
theorem genCtx_le : Γ₁.Le (genCtx (Γ₁ := Γ₁) c T) :=
  (Ctx.le_insert hc.root T).trans (Ctx.le_insert (genU_fresh (Γ₁ := Γ₁) c T).root T)

/-- ⭐**The renaming**: `c` to `u`, every other address to itself. -/
def genS : Subst σ (genCtx (Γ₁ := Γ₁) c T) :=
  (Subst.idS σ _).set (.free c) (.ren (.root (.free (genU (Γ₁ := Γ₁) c T))))

/-- The renaming's index map. -/
def genIdx : VarSymb → VarSymb :=
  Subst.setIdx id (.free c)
    (.ren (σ := σ) (Δ := genCtx (Γ₁ := Γ₁) c T) (.root (.free (genU (Γ₁ := Γ₁) c T))))

theorem genS_okRef :
    (SubE.ren (σ := σ) (Δ := genCtx (Γ₁ := Γ₁) c T)
      (.root (.free (genU (Γ₁ := Γ₁) c T)))).OkRef T :=
  Ctx.ref_insert_root _ _ _

include hc in
theorem genS_ok : Subst.Ok (Γ₁.insert (.free c) T) (genS (σ := σ) (Γ₁ := Γ₁) c T) :=
  Subst.ok_set (Subst.ok_idS_le (genCtx_le c T hc)) (genS_okRef c T)

include hc in
theorem genS_coh : Subst.Coh (genIdx (σ := σ) (Γ₁ := Γ₁) c T) (Γ₁.insert (.free c) T)
    (genS (σ := σ) (Γ₁ := Γ₁) c T) :=
  Subst.coh_set (Subst.ok_idS_le (genCtx_le c T hc)) (Subst.coh_idS_le (genCtx_le c T hc)) hc
    (genS_okRef c T)

/-- ⭐**`φ` with the constant `c` made the bound variable**, `∀x. φ(x)`'s body. -/
def WFF.genV (φ : WFF σ (Γ₁.insert (.free c) T) 0) :
    WFF σ ((Γ₁.insert (.free c) T).insert (.bnd 0) T) 1 :=
  WFF.bindFree (genU (Γ₁ := Γ₁) c T) (genU_fresh c T) Ctx.NoSlots.slots T
    (WFF.subst (genIdx c T) (genS c T) (genS_ok c T hc) (genS_coh c T hc) Ctx.NoSlots.slots
      Ctx.NoSlots.slots φ)

/-- A hypothesis that does not mention `c` is renamed to itself. -/
theorem WFF.genS_weaken (δ : WFF σ Γ₁ 0) :
    WFF.subst (genIdx c T) (genS c T) (genS_ok c T hc) (genS_coh c T hc) Ctx.NoSlots.slots
        Ctx.NoSlots.slots (WFF.weaken hc.root T δ) =
      WFF.weaken (genU_fresh (Γ₁ := Γ₁) c T).root T (WFF.weaken hc.root T δ) := by
  have hs₁ : Γ₁.SlotsFrom 0 := (Ctx.NoSlots.slots (Γ := Γ₁.insert (.free c) T)).of_le
    (Ctx.le_insert hc.root T)
  unfold WFF.weaken
  rw [WFF.subst_mono _ _ _ _ hs₁, WFF.mono_mono]
  refine WFF.subst_ren (genCtx_le c T hc) _ _ _ _ _ (fun v U hv => ?_) δ (fun _ _ _ _ => rfl)
  have hrt : v.rt ≠ .free c := fun he => by
    rw [Ctx.ref_none_of_rootFresh hc v he] at hv
    cases hv
  rw [genS, Subst.at_set_of_rt_ne _ _ _ v hrt, Subst.at_idS]

/-- ⭐**`∀x. φ(x)`'s body is `φ` with `c` bound**: instantiating it at `c` gives `φ` back. -/
theorem WFF.genV_inst (φ : WFF σ (Γ₁.insert (.free c) T) 0) :
    WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free c)) T (Ctx.ref_insert_root _ _ _))
      (WFF.genV c T hc φ) = φ := by
  have hG := Ctx.Le.refl (Γ₁.insert (.free c) T)
  have hu := genU_fresh (Γ₁ := Γ₁) c T
  have e := WFF.instantiate_bindFree hG (genU (Γ₁ := Γ₁) c T) hu
    (Term.eta (σ := σ) (.root (.free c)) T (Ctx.ref_insert_root _ _ _))
    (WFF.subst (genIdx c T) (genS c T) (genS_ok c T hc) (genS_coh c T hc) Ctx.NoSlots.slots
      Ctx.NoSlots.slots φ)
  rw [WFF.mono_refl] at e
  rw [WFF.genV, e]
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ (Subst.ok_idS_le hG) (Subst.coh_idS_le hG)
    _ _ _ ?_ φ).trans (WFF.subst_id _ _ _ φ)
  refine Subst.sim_of (hwit := fun _ _ _ _ => by wit_refl) ?_
  intro v U hlp hv
  rw [Subst.comp_apply]
  by_cases hvr : v = .root (.free c)
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    rw [genS, Subst.set_root, SubE.comp_ren, Subst.at_single_root]
    exact .ren_eta _ _
  · have hrt : v.rt ≠ .free (genU (Γ₁ := Γ₁) c T) :=
      Ctx.ref_rt_ne hu ((Ctx.ref_nonproj _ hlp).trans hv)
    rw [genS, Subst.set_ne _ _ hvr]
    simp only [Subst.idS]
    rw [SubE.comp_ren, Subst.single_at_ne hrt]
    exact .refl _

end

/-- ⭐**Generalisation on declared variables.**  From `Δ ⊢ φ(c)`, with `Δ` not mentioning the
    declared variable `c`, infer `Δ ⊢ ∀x. φ(x)`. -/
def Proof.genVar {Γ₁ : Ctx} (c : ℕ) (T : VarType) (hc : Γ₁.RootFresh (.free c))
    [(Γ₁.insert (.free c) T).Presented] {Δ₁ : List (WFF σ Γ₁ 0)}
    {φ : WFF σ (Γ₁.insert (.free c) T) 0}
    (p : Proof σ (Γ₁.insert (.free c) T) (Δ₁.map (WFF.weaken hc.root T)) φ) :
    Proof σ (Γ₁.insert (.free c) T) (Δ₁.map (WFF.weaken hc.root T))
      (.all T (WFF.genV c T hc φ)) :=
  Proof.all_intro _ T (genU_fresh c T)
    (Proof.castHyps
      (by
        rw [List.map_map, List.map_map]
        exact List.map_congr_left fun δ _ => WFF.genS_weaken c T hc δ)
      (Proof.subst p (genS c T) (genS_ok c T hc) (genS_coh c T hc) Ctx.NoSlots.slots))

end V12M
