import QML.QML_v12m_Pack
import QML.QML_v12m_DiaAbs
import QML.QML_v12m_ProofSubst
import QML.QML_v12m_RetMono

/-!
# QML v12m — using a strong T hypothesis at a later stage

A `T_dia` hypothesis (`WFF.retHyp`) is added to the theory once, at the stage where the witness is
declared: for every value of the parameter `y : B`, what holds of `t` here holds of the witness
content in `◇_c`.  The canonical model must use it at every later stage, where the parameter's
value is a tuple of constants that did not exist yet.

* ⭐`WFF.instantiate_mono_retBody`: weakening the hypothesis to a later context and instantiating
  its `∀` at a term there gives the implication with that term substituted for the parameter — the
  antecedent read here, the consequent read inside `◇_c`.
* ⭐`WFF.instantiate_mono_retBody_pack`: the instance a realised witness needs, with the later
  constants packed: `WFF.realiseAt … χ → ◇_c χ`, for any `χ` of the witness's view.

The two readings keep the hole formula over `Δ.boxIn` (the later context *without* the witness):
the antecedent stays in the weakened form `WFF.weaken` that `WFF.retHyp` gives it, so both sides
mention the same substituted hole formula.
-/

namespace V12M

variable [ModalSys]

/-- The hole formula with the parameter instantiated: the substitution taken one view in, under
    the hole. -/
abbrev WFF.holeInst {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    (A : VarType) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    WFF σ (Δ.boxIn.insert (.bnd 0) A) 1 :=
  WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.box.under 0 0 A hΔ.boxIn.root)
    (Subst.ok_under (Subst.ok_box hθ) A hΔ.boxIn.root)
    (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn A hΔ.boxIn.root)
    (hΓ.boxIn.insert A) (hΔ.boxIn.insert A) ψ

/-- The body of a `T_dia` hypothesis, under its `∀`. -/
def WFF.retBody {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true) {A : VarType}
    {a : Ann A} (t : Term σ Γ A a) (c y : ℕ) (hc : Γ.RootFresh (.free c))
    (hy : Γ.RootFresh (.free y)) (hyc : y ≠ c) (B : VarType)
    (ψ : WFF σ ((Γ.insert (.free y) B).boxIn.insert (.bnd 0) A) 1) :
    WFF σ ((Γ.insert (.free c) (.VTypeDia A)).insert (.bnd 0) B) 1 :=
  have hne : Root.free y ≠ Root.free c := fun h => hyc (Root.free.inj h)
  have hcy : (Γ.insert (.free y) B).RootFresh (.free c) := hc.insert_ne hne B
  WFF.bindFree y (hy.insert_ne hne.symm (.VTypeDia A)) Ctx.NoSlots.slots B
    (WFF.mono (Ctx.insert_swap_le hne B (.VTypeDia A))
      (WFF.imp
        ((WFF.hereRead hT (Term.mono (Ctx.le_insert hy.root B) t) ψ).weaken hcy.root
          (.VTypeDia A))
        (.dia (.root (.free c)) ⟨A, Ctx.ref_insert_root _ (.free c) (.VTypeDia A)⟩
          (WFF.viewRead c hcy A ψ))))

theorem WFF.retHyp_eq {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true)
    {A : VarType} {a : Ann A} (t : Term σ Γ A a) (c y : ℕ) (hc : Γ.RootFresh (.free c))
    (hy : Γ.RootFresh (.free y)) (hyc : y ≠ c) (B : VarType)
    (ψ : WFF σ ((Γ.insert (.free y) B).boxIn.insert (.bnd 0) A) 1) :
    WFF.retHyp hT t c y hc hy hyc B ψ = .all B (WFF.retBody hT t c y hc hy hyc B ψ) := rfl

omit [ModalSys] in
/-- Declaring a `◇`-typed root writes nothing else at that root. -/
theorem Ctx.fr_insert_dia {Δ : Ctx} {c : ℕ} (hcΔ : Δ.RootFresh (.free c)) (A : VarType) :
    ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) →
      (Δ.insert (.free c) (.VTypeDia A)) v = none := by
  intro v hv hne
  change (if v = .root (.free c) then some (.VTypeDia A) else Δ v) = none
  rw [if_neg hne]
  exact hcΔ v hv

/-- The reading inside `◇_c` at a context that has just declared the witness is the reading at any
    context that declares it. -/
theorem WFF.viewRead_eq_viewReadAt {σ : Signature} {Δ : Ctx} [Δ.NoSlots] {c : ℕ}
    (hcΔ : Δ.RootFresh (.free c)) (A : VarType) (ψ : WFF σ (Δ.boxIn.insert (.bnd 0) A) 1) :
    WFF.viewRead c hcΔ A ψ =
      WFF.viewReadAt c (Ctx.ref_insert_root Δ (.free c) (.VTypeDia A))
        (WFF.mono ((Ctx.le_insert hcΔ.root (.VTypeDia A)).boxIn.insert (.bnd 0) A) ψ) := by
  unfold WFF.viewRead WFF.viewReadAt WFF.renameRoot
  rw [WFF.subst_mono]

/-- Substituting a term for the parameter, as a substitution of the later context. -/
abbrev Subst.paramS {σ : Signature} {Δ : Ctx} (y : ℕ) {B : VarType} {b : Ann B}
    (s : Term σ Δ B b) : Subst σ Δ := Subst.single (.free y) (.tm s)

/-- Substituting for the parameter in the context that has just declared the witness is the
    witness-preserving rename of the substitution below it. -/
theorem Subst.single_eq_rename {σ : Signature} {Δ : Ctx} {y c : ℕ} (hyc : y ≠ c) {A B : VarType}
    {b : Ann B} (s : Term σ Δ B b) (h : Δ (.root (.free c)) = none) :
    Subst.single (σ := σ) (Δ := Δ.insert (.free c) (.VTypeDia A)) (.free y)
        (.tm (Term.mono (Ctx.le_insert h (.VTypeDia A)) s)) =
      Subst.rename (Subst.paramS y s) c c (.VTypeDia A) h := by
  funext v
  by_cases hvc : v = .root (.free c)
  · subst hvc
    rw [Subst.rename_root]
    exact if_neg (fun he => hyc (Root.free.inj (VarSymb.root.inj he)).symm)
  · rw [Subst.rename_ne _ c (.VTypeDia A) h hvc]
    by_cases hvy : v = .root (.free y)
    · subst hvy
      rw [show Subst.single (σ := σ) (Δ := Δ.insert (.free c) (.VTypeDia A)) (.free y)
          (.tm (Term.mono (Ctx.le_insert h (.VTypeDia A)) s)) (.root (.free y)) =
          .tm (Term.mono (Ctx.le_insert h (.VTypeDia A)) s) from if_pos rfl,
        show Subst.paramS (σ := σ) (Δ := Δ) y s (.root (.free y)) = .tm s from if_pos rfl]
      rfl
    · rw [show Subst.single (σ := σ) (Δ := Δ.insert (.free c) (.VTypeDia A)) (.free y)
          (.tm (Term.mono (Ctx.le_insert h (.VTypeDia A)) s)) v = .ren v from if_neg hvy,
        show Subst.paramS (σ := σ) (Δ := Δ) y s v = .ren v from if_neg hvy]
      rfl

/-- ⭐Weakening a `T_dia` hypothesis to a later context and instantiating its `∀` at a term there:
    the parameter is substituted by that term, in the reading here and in the reading inside
    `◇_c` alike. -/
theorem WFF.instantiate_mono_retBody {σ : Signature} {Γ Δ : Ctx}
    [Γ.NoSlots] [Δ.NoSlots] (hT : ModalSys.T = true) {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    (c y : ℕ) (hc : Γ.RootFresh (.free c)) (hy : Γ.RootFresh (.free y)) (hyc : y ≠ c)
    (B : VarType) (ψ : WFF σ ((Γ.insert (.free y) B).boxIn.insert (.bnd 0) A) 1)
    (hle : Γ.Le Δ) (hcΔ : Δ.RootFresh (.free c)) {b : Ann B} (s : Term σ Δ B b) :
    WFF.instantiate Ctx.NoSlots.slots (Term.mono (Ctx.le_insert hcΔ.root (.VTypeDia A)) s)
        (WFF.mono ((hle.insert (.free c) (.VTypeDia A)).insert (.bnd 0) B)
          (WFF.retBody hT t c y hc hy hyc B ψ)) =
      .imp
        ((WFF.hereRead hT
            (Term.subst (Subst.singleIdx (.free y) (.tm s)) (Subst.paramS y s)
              (Subst.ok_single (T := B) (e := SubE.tm s) hle rfl)
              (Subst.coh_single (T := B) (e := SubE.tm s) hy hle rfl)
              (Term.mono (Ctx.le_insert hy.root B) t))
            (WFF.holeInst (Subst.paramS y s) (Subst.ok_single (T := B) (e := SubE.tm s) hle rfl)
              (Subst.coh_single (T := B) (e := SubE.tm s) hy hle rfl) Ctx.NoSlots.slots
              Ctx.NoSlots.slots A ψ)).weaken
          hcΔ.root (.VTypeDia A))
        (.dia (.root (.free c)) ⟨A, Ctx.ref_insert_root Δ (.free c) (.VTypeDia A)⟩
          (WFF.viewRead c hcΔ A
            (WFF.holeInst (Subst.paramS y s) (Subst.ok_single (T := B) (e := SubE.tm s) hle rfl)
              (Subst.coh_single (T := B) (e := SubE.tm s) hy hle rfl) Ctx.NoSlots.slots
              Ctx.NoSlots.slots A ψ))) := by
  have hne : Root.free y ≠ Root.free c := fun h => hyc (Root.free.inj h)
  have hcy : (Γ.insert (.free y) B).RootFresh (.free c) := hc.insert_ne hne B
  -- Binding the parameter and instantiating it is substituting the term for it.
  rw [show WFF.retBody hT t c y hc hy hyc B ψ =
      WFF.bindFree y (hy.insert_ne hne.symm (.VTypeDia A)) Ctx.NoSlots.slots B
        (WFF.mono (Ctx.insert_swap_le hne B (.VTypeDia A))
          (WFF.imp
            ((WFF.hereRead hT (Term.mono (Ctx.le_insert hy.root B) t) ψ).weaken hcy.root
              (.VTypeDia A))
            (.dia (.root (.free c)) ⟨A, Ctx.ref_insert_root _ (.free c) (.VTypeDia A)⟩
              (WFF.viewRead c hcy A ψ)))) from rfl,
    WFF.instantiate_mono_bindFree (hle.insert (.free c) (.VTypeDia A)) y
      (hy.insert_ne hne.symm (.VTypeDia A)) Ctx.NoSlots.slots Ctx.NoSlots.slots
      (Term.mono (Ctx.le_insert hcΔ.root (.VTypeDia A)) s),
    WFF.subst_mono (hΓ := Ctx.NoSlots.slots) (Ctx.insert_swap_le hne B (.VTypeDia A))]
  -- The same substitution, seen as the rename that keeps the witness.
  have hok : Subst.Ok (Γ.insert (.free y) B) (Subst.paramS (σ := σ) y s) :=
    Subst.ok_single (T := B) (e := SubE.tm s) hle rfl
  have hcoh : Subst.Coh (Subst.singleIdx (.free y) (.tm s)) (Γ.insert (.free y) B)
      (Subst.paramS (σ := σ) y s) := Subst.coh_single (T := B) (e := SubE.tm s) hy hle rfl
  refine (WFF.subst_congr _ (Subst.rename (Subst.paramS y s) c c (.VTypeDia A) hcΔ.root) _
    (Subst.ok_rename hok (.VTypeDia A) hcΔ.root) _
    (Subst.coh_rename hok hcoh hcy (.VTypeDia A) hcΔ.root)
    Ctx.NoSlots.slots Ctx.NoSlots.slots
    (Subst.sim_of (fun v _ _ _ => by rw [Subst.single_eq_rename hyc s hcΔ.root]; exact .refl _))
    _).trans ?_
  refine congrArg₂ WFF.imp ?_ ?_
  · -- What holds of `t` here: the weakening comes out, and the reading here substitutes.
    refine (WFF.subst_mono_eq (Ctx.le_insert hcy.root (.VTypeDia A))
      (Ctx.le_insert hcΔ.root (.VTypeDia A)) (Subst.paramS y s) hok hcoh _ _ _
      Ctx.NoSlots.slots Ctx.NoSlots.slots Ctx.NoSlots.slots Ctx.NoSlots.slots
      (Subst.sim_rename_mono hcy (.VTypeDia A) hcΔ.root) _).trans ?_
    exact congrArg (WFF.mono (Ctx.le_insert hcΔ.root (.VTypeDia A)))
      (WFF.subst_hereRead hT (Subst.paramS y s) hok hcoh Ctx.NoSlots.slots Ctx.NoSlots.slots _ ψ)
  · -- What the witness content satisfies in its view: the reading inside `◇_c` substitutes.
    exact WFF.subst_diaViewRead (Subst.paramS y s) hok hcoh Ctx.NoSlots.slots Ctx.NoSlots.slots
      hcy hcΔ A ψ

/-! ## Weakening the pieces -/

/-- Abstracting a view formula commutes with weakening (the `WFF` mirror of
    `Term.mono_diaAbs`). -/
theorem WFF.mono_diaAbs {σ : Signature} {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] {c : ℕ}
    {A : VarType} (h : Γ.Le Γ')
    (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hcA' : Γ'.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    (hfr' : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ' v = none)
    (χ : WFF σ (Γ.diaIn (.root (.free c))) 0) :
    WFF.mono (h.boxIn.insert (.bnd 0) A) (WFF.diaAbs c hcA hfr χ) =
      WFF.diaAbs c hcA' hfr' (WFF.mono (h.diaIn (.root (.free c))) χ) := by
  unfold WFF.diaAbs
  rw [WFF.mono_subst, WFF.subst_mono]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ ?_ χ
  refine Subst.sim_of ?_
  intro v U _ _
  match v with
  | .step u .dia =>
      change SubE.Sim U (SubE.mono _ (if u = .root (.free c) then SubE.ren (.root (.bnd 0))
        else .hide)) (if u = .root (.free c) then SubE.ren (.root (.bnd 0)) else .hide)
      by_cases hu : u = .root (.free c)
      · simp only [if_pos hu]
        exact .refl _
      · simp only [if_neg hu]
        exact .refl _
  | .step _ .box => exact .refl _
  | .step _ .keep => exact .refl _
  | .root _ => exact .refl _
  | .step _ .fst => exact .refl _
  | .step _ .snd => exact .refl _
  | .step _ .here => exact .refl _

/-- ⭐Realisation commutes with weakening. -/
theorem WFF.mono_realiseAt {σ : Signature} {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots]
    (hT : ModalSys.T = true) {c : ℕ} {A : VarType} (h : Γ.Le Γ')
    (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hcA' : Γ'.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    (hfr' : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ' v = none)
    {a₀ : Ann A} (t₀ : Term σ Γ A a₀) (χ : WFF σ (Γ.diaIn (.root (.free c))) 0) :
    WFF.mono h (WFF.realiseAt hT c hcA hfr t₀ χ) =
      WFF.realiseAt hT c hcA' hfr' (Term.mono h t₀) (WFF.mono (h.diaIn (.root (.free c))) χ) := by
  unfold WFF.realiseAt
  rw [WFF.mono_hereRead hT h t₀ (WFF.diaAbs c hcA hfr χ),
    WFF.mono_diaAbs h hcA hcA' hfr hfr' χ]

/-- The tuple of the packed roots commutes with weakening. -/
theorem Term.mono_tuple {σ : Signature} {Γ Γ' : Ctx} (h : Γ.Le Γ') :
    ∀ (zs : List (VarType × ℕ)) (hz : ∀ z ∈ zs, Γ.ref (.root (.free z.2)) = some z.1)
      (hz' : ∀ z ∈ zs, Γ'.ref (.root (.free z.2)) = some z.1),
      Term.mono h (Term.tuple (σ := σ) zs hz) = Term.tuple zs hz'
  | [], _, _ => rfl
  | z :: zs, hz, hz' => by
      change Term.pair (Term.mono h (Term.eta _ z.1 _)) (Term.mono h (Term.tuple zs _)) =
        Term.pair (Term.eta _ z.1 _) (Term.tuple zs _)
      rw [Term.mono_eta h _ z.1 _,
        Term.mono_tuple h zs (fun z' hz'' => hz z' (List.mem_cons_of_mem _ hz''))
          (fun z' hz'' => hz' z' (List.mem_cons_of_mem _ hz''))]

/-! ## The instance a realised witness needs -/

section Instance

variable {σ : Signature} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots] {c y : ℕ} {A : VarType}
  {zs : List (VarType × ℕ)}

/-- The hole formula of the hypothesis a realised witness needs: the abstraction of `χ` — read one
    context down, since a `◇`-typed root contributes nothing to the `□` view — with the constants
    declared after the witness packed into the parameter. -/
def WFF.retHole (hy : Γ.RootFresh (.free y)) (hcΔ : Δ.RootFresh (.free c))
    (hz : ∀ z ∈ zs, Δ.ref (.root (.free z.2)) = some z.1)
    (honly : ∀ (v : VarSymb) (n : ℕ), v.rt = .free n → Subst.packOf zs n ≠ none →
      v ≠ .root (.free n) → Δ v = none)
    (hsub : ∀ (v : VarSymb) (T : VarType), (∀ n, v.rt = .free n → Subst.packOf zs n = none) →
      Δ v = some T → Γ v = some T)
    (χ : WFF σ ((Δ.insert (.free c) (.VTypeDia A)).diaIn (.root (.free c))) 0) :
    WFF σ ((Γ.insert (.free y) (Subst.packType zs)).boxIn.insert (.bnd 0) A) 1 :=
  WFF.holeInst (Subst.pack σ (Γ.insert (.free y) (Subst.packType zs)) y zs)
    (Subst.ok_pack hy hz honly hsub) (Subst.coh_pack hy hz honly hsub)
    Ctx.NoSlots.slots Ctx.NoSlots.slots A
    (WFF.mono ((Ctx.boxIn_insert_dia_le hcΔ A).insert (.bnd 0) A)
      (WFF.diaAbs c (Ctx.ref_insert_root Δ (.free c) (.VTypeDia A)) (Ctx.fr_insert_dia hcΔ A) χ))

/-- ⭐The instance: the packed hypothesis, weakened to the later stage and instantiated at the
    tuple of the constants declared after the witness, says exactly that what `χ` states of the
    realising term here gives `◇_c χ`. -/
theorem WFF.instantiate_mono_retBody_pack (hT : ModalSys.T = true) {a : Ann A} (t : Term σ Γ A a)
    (hc : Γ.RootFresh (.free c)) (hy : Γ.RootFresh (.free y)) (hyc : y ≠ c)
    (hle : Γ.Le Δ) (hcΔ : Δ.RootFresh (.free c))
    (hz : ∀ z ∈ zs, Δ.ref (.root (.free z.2)) = some z.1)
    (honly : ∀ (v : VarSymb) (n : ℕ), v.rt = .free n → Subst.packOf zs n ≠ none →
      v ≠ .root (.free n) → Δ v = none)
    (hsub : ∀ (v : VarSymb) (T : VarType), (∀ n, v.rt = .free n → Subst.packOf zs n = none) →
      Δ v = some T → Γ v = some T)
    (χ : WFF σ ((Δ.insert (.free c) (.VTypeDia A)).diaIn (.root (.free c))) 0) :
    WFF.instantiate Ctx.NoSlots.slots
        (Term.mono (Ctx.le_insert hcΔ.root (.VTypeDia A)) (Term.tuple zs hz))
        (WFF.mono ((hle.insert (.free c) (.VTypeDia A)).insert (.bnd 0) (Subst.packType zs))
          (WFF.retBody hT t c y hc hy hyc (Subst.packType zs)
            (WFF.retHole hy hcΔ hz honly hsub χ))) =
      .imp
        (WFF.realiseAt hT c (Ctx.ref_insert_root Δ (.free c) (.VTypeDia A))
          (Ctx.fr_insert_dia hcΔ A)
          (Term.mono (hle.trans (Ctx.le_insert hcΔ.root (.VTypeDia A))) t) χ)
        (.dia (.root (.free c)) ⟨A, Ctx.ref_insert_root Δ (.free c) (.VTypeDia A)⟩ χ) := by
  rw [WFF.instantiate_mono_retBody hT t c y hc hy hyc (Subst.packType zs)
      (WFF.retHole hy hcΔ hz honly hsub χ) hle hcΔ (Term.tuple zs hz),
    show WFF.holeInst (Subst.paramS y (Term.tuple zs hz)) (Subst.ok_single hle rfl)
        (Subst.coh_single hy hle rfl) Ctx.NoSlots.slots Ctx.NoSlots.slots A
        (WFF.retHole hy hcΔ hz honly hsub χ) =
        WFF.mono ((Ctx.boxIn_insert_dia_le hcΔ A).insert (.bnd 0) A)
          (WFF.diaAbs c (Ctx.ref_insert_root Δ (.free c) (.VTypeDia A))
            (Ctx.fr_insert_dia hcΔ A) χ) from
      WFF.subst_pack_single_view hy hle hz honly hsub Ctx.NoSlots.slots Ctx.NoSlots.slots A _]
  refine congrArg₂ WFF.imp ?_ ?_
  · -- What `χ` says of the realising term, read here.
    rw [show (WFF.hereRead hT
          (Term.subst (Subst.singleIdx (.free y) (.tm (Term.tuple zs hz)))
            (Subst.paramS y (Term.tuple zs hz))
            (Subst.ok_single (T := Subst.packType zs) (e := SubE.tm (Term.tuple zs hz)) hle rfl)
            (Subst.coh_single (T := Subst.packType zs) (e := SubE.tm (Term.tuple zs hz))
              hy hle rfl)
            (Term.mono (Ctx.le_insert hy.root (Subst.packType zs)) t))
          (WFF.mono ((Ctx.boxIn_insert_dia_le hcΔ A).insert (.bnd 0) A)
            (WFF.diaAbs c (Ctx.ref_insert_root Δ (.free c) (.VTypeDia A))
              (Ctx.fr_insert_dia hcΔ A) χ))).weaken hcΔ.root (.VTypeDia A) =
        WFF.mono (Ctx.le_insert hcΔ.root (.VTypeDia A)) _ from rfl,
      WFF.mono_hereRead hT (Ctx.le_insert hcΔ.root (.VTypeDia A)), WFF.mono_mono, WFF.mono_refl]
    refine WFF.hereRead_congr hT ?_ _
    have hsub' : (⟨_, Term.subst (Subst.singleIdx (.free y) (.tm (Term.tuple zs hz)))
          (Subst.paramS y (Term.tuple zs hz))
          (Subst.ok_single (T := Subst.packType zs) (e := SubE.tm (Term.tuple zs hz)) hle rfl)
          (Subst.coh_single (T := Subst.packType zs) (e := SubE.tm (Term.tuple zs hz)) hy hle rfl)
          (Term.mono (Ctx.le_insert hy.root (Subst.packType zs)) t)⟩ : Σ b, Term σ Δ A b) =
        ⟨a, Term.mono hle t⟩ := by
      rw [Term.subst_mono (Ctx.le_insert hy.root (Subst.packType zs))]
      refine (Term.subst_congr _ (Subst.idS σ Δ) _ (Subst.ok_idS.restrict hle) _
        (Subst.coh_idS.restrict hle) ?_ t).trans
        (Term.subst_idS_mono hle (Subst.ok_idS.restrict hle) (Subst.coh_idS.restrict hle) t)
      refine Subst.sim_of ?_
      intro v _ _ hv
      have hvy : v.rt ≠ .free y := fun he => by rw [hy v he] at hv; cases hv
      rw [show Subst.paramS (σ := σ) y (Term.tuple zs hz) v = .ren v from
        if_neg (fun he => hvy (by rw [he]; rfl))]
      exact .refl _
    exact congrArg (fun z => (⟨_, Term.mono (Ctx.le_insert hcΔ.root (.VTypeDia A)) z.2⟩ :
        Σ b, Term σ (Δ.insert (.free c) (.VTypeDia A)) A b)) hsub' |>.trans
      (congrArg (Sigma.mk _) (Term.mono_mono hle (Ctx.le_insert hcΔ.root (.VTypeDia A)) t))
  · -- What the witness content satisfies in its view.
    refine congrArg (WFF.dia (.root (.free c)) _) ?_
    rw [WFF.viewRead_eq_viewReadAt, WFF.mono_mono, WFF.mono_refl]
    exact WFF.viewReadAt_diaAbs c _ _ χ

end Instance

end V12M
