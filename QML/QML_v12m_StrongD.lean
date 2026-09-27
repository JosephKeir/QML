import QML.QML_v12m_DiaAbs
import QML.QML_v12m_ProofSubst
import QML.QML_v12m_SubstTwice

/-!
# QML v12m — strong D: the schema, derived from the axiom

Strong D's rule is the closed axiom `⊢ ∃x:◇𝟙. ◇_x ⊤` (`Proof.D_ex`).  What it says about
arbitrary types follows in K:

* ⭐`Proof.D_schema`: `□φ(u.box) ⊢ ∃x:◇A. ◇_x φ(x.dia)`, at every type `A`.  Take the axiom's
  witness `z`, and put `u`'s value on it as content: the possible term `diatm z _ (u.box)`.  In
  `z`'s view `u.box` is in scope — it is a `□`-item — so `K_dia` carries `□φ(u.box)` into
  `◇_z φ(u.box)`, and that is the schema's body instantiated at the new term.

The witness is re-used, not chosen per formula: the term depends on `u` alone.  This is the
syntactic side of the model's `strength`, which gives any necessary object a possible counterpart
with the extent of a given possible object.

`φ` is a `□`-view formula with a hole (`ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1`), as for strong T:
read in the `□` view with `u.box` in the hole, and in a bound witness's view with its content there
(`WFF.diaHoleRead`).
-/

namespace V12M

variable [ModalSys]

variable {σ : Signature}

/-- The `□`-view formula `ψ` read inside the bound witness `x := bnd 0 : ◇A`, with the witness
    content `x.dia` in its hole. -/
def WFF.diaHoleRead {Γ : Ctx} [Γ.NoSlots] (A : VarType) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    WFF σ ((Γ.insert (.bnd 0) (.VTypeDia A)).diaIn (.root (.bnd 0))) 1 :=
  WFF.renameRoot (.bnd 0) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0))
    ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root (.VTypeDia A)).boxIn.trans
      (Ctx.le_boxIn_diaIn _ (.root (.bnd 0))))
    (.step (.root (.bnd 0)) .dia)
    (Ctx.ref_diaIn_of (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A)))
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A)
    (((Ctx.NoSlots.slots (Γ := Γ)).insert (.VTypeDia A)).diaIn (.root (.bnd 0))) ψ

/-- `∃x:◇A. ◇_x ψ(x.dia)`. -/
def WFF.exDia {Γ : Ctx} [Γ.NoSlots] (A : VarType) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    WFF σ Γ 0 :=
  .ex (.VTypeDia A)
    (.dia (.root (.bnd 0)) ⟨A, Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A)⟩ (WFF.diaHoleRead A ψ))

/-- `□ψ(u.box)`: the hole takes the contents of the necessary object `u`. -/
def WFF.boxHole {Γ : Ctx} [Γ.NoSlots] {A : VarType} {u : VarSymb}
    (hu : Γ.ref u = some (.VTypeBox A)) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) : WFF σ Γ 0 :=
  .box (WFF.instantiate (Ctx.NoSlots.slots (Γ := Γ.boxIn))
    (Term.eta u.inner A (Ctx.ref_inner hu)) ψ)

/-- Modal β at a witness's own entry: its content is the possible term's body. -/
theorem SubE.diaBody_diatm_self {Δ : Ctx} {x : VarSymb} (hx : ∃ X, Δ.ref x = some (.VTypeDia X))
    {A : VarType} {a : Ann A} (s : Term σ (Δ.diaIn x) A a) :
    (SubE.tm (Term.diatm x hx s)).diaBody x = .tm s := by
  change dite (x = x) (fun _ => SubE.tm (Term.mono (Ctx.Le.refl _) s))
    (fun _ => .hide) = _
  rw [dif_pos rfl, Term.mono_refl]

/-- A reachable address of a context without slots is not rooted at a slot. -/
theorem Ctx.rt_ne_bnd_of_ref {Γ : Ctx} [Γ.NoSlots] {w : VarSymb} {T : VarType}
    (h : Γ.ref w = some T) (n : ℕ) : w.rt ≠ .bnd n := fun hrt => by
  rw [Ctx.ref_none_of_rootFresh (Ctx.NoSlots.slots.rootFresh (Nat.zero_le n)) w hrt] at h
  cases h

/-- ⭐Instantiating `∃x:◇A. ◇_x ψ(x.dia)` at a possible term that puts `u`'s value on an existing
    witness `x` gives `◇_x ψ(u.box)`, the hole formula carried into `x`'s view. -/
theorem WFF.instantiate_exDia {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots] (hle : Γ.Le Δ) {A : VarType}
    {u : VarSymb} (hu : Γ.ref u = some (.VTypeBox A)) (x : VarSymb)
    (hx : ∃ X, Δ.ref x = some (.VTypeDia X)) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    WFF.instantiate Ctx.NoSlots.slots
        (Term.diatm x hx (Term.eta u.inner A
          ((hle.boxIn.trans (Ctx.le_boxIn_diaIn Δ x)).ref (Ctx.ref_inner hu))))
        (WFF.mono (hle.insert (.bnd 0) (.VTypeDia A))
          (.dia (.root (.bnd 0)) ⟨A, Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A)⟩
            (WFF.diaHoleRead A ψ))) =
      .dia x hx (WFF.mono (hle.boxIn.trans (Ctx.le_boxIn_diaIn Δ x))
        (WFF.instantiate (Ctx.NoSlots.slots (Γ := Γ.boxIn))
          (Term.eta u.inner A (Ctx.ref_inner hu)) ψ)) := by
  refine congrArg (WFF.dia x hx) ?_
  -- The substitution plugging `u`'s value into the hole, as seen from `x`'s view.
  have hΓb : Γ.boxIn.SlotsFrom 0 := Ctx.NoSlots.slots
  have hΓ₀ : (Γ.boxIn.insert (.bnd 0) A).SlotsFrom 1 := hΓb.insert A
  have hL : Γ.boxIn.Le (Δ.diaIn x) := hle.boxIn.trans (Ctx.le_boxIn_diaIn Δ x)
  let η : Term σ Γ.boxIn A (Ann.eta u.inner A) := Term.eta u.inner A (Ctx.ref_inner hu)
  have hθ₃' : Subst.Ok (Γ.boxIn.insert (.bnd 0) A) (Subst.single (σ := σ) (.bnd 0) (.tm η)) :=
    Subst.ok_single (Ctx.Le.refl _) rfl
  have hc₃' : Subst.Coh (Subst.singleIdx (.bnd 0) (.tm η)) (Γ.boxIn.insert (.bnd 0) A)
      (Subst.single (σ := σ) (.bnd 0) (.tm η)) :=
    Subst.coh_single (hΓb.rootFresh le_rfl) (Ctx.Le.refl _) rfl
  -- Weakening before substituting is substituting less; renaming the hole to `x.dia` and then
  -- substituting the new term for the witness is plugging `u`'s value into the hole.
  refine (WFF.subst_mono _ _ _ _
    (((Ctx.NoSlots.slots (Γ := Γ)).insert (.VTypeDia A)).diaIn (.root (.bnd 0))) _ _ _).trans ?_
  refine (WFF.subst_comp _ _ ((Subst.single (.bnd 0) (.tm η)).mono hL) _ _ _ _
    (Subst.ok_mono hθ₃' hL) (Subst.coh_mono hc₃' hL) hΓ₀ _ _ ?_ ψ).trans ?_
  · refine Subst.sim_of fun v T hlp hv => ?_
    by_cases hv0 : v = .root (.bnd 0)
    · -- The hole: `x.dia`, then the new term's content — `u`'s value either way.
      subst hv0
      have hTA : A = T := by simpa [Ctx.insert] using hv
      subst hTA
      change SubE.Sim A (.tm (Term.mono hL η))
        ((SubE.tm (Term.diatm x hx (Term.eta u.inner A (hL.ref (Ctx.ref_inner hu))))).diaBody x)
      rw [SubE.diaBody_diatm_self, Term.mono_eta]
      exact .refl _
    · -- A `□`-item of `Γ`: left alone by both.
      have hv' : Γ.boxIn v = some T := by simpa [Ctx.insert, hv0] using hv
      have hsw : ∀ {w : VarSymb} {U : VarType}, Γ.ref w = some U →
          (Subst.single (σ := σ) (Δ := Δ) (.bnd 0)
            (.tm (Term.diatm x hx (Term.eta u.inner A (hL.ref (Ctx.ref_inner hu)))))).at w =
            .ren w :=
        fun hw => Subst.at_single_of_rt_ne (Ctx.rt_ne_bnd_of_ref hw 0)
      match v with
      | .step w .box =>
          obtain ⟨hk, hw⟩ := Ctx.boxIn_box hv'
          change SubE.Sim T (.ren (.step w .box))
            (((Subst.single (σ := σ) (Δ := Δ) (.bnd 0)
              (.tm (Term.diatm x hx (Term.eta u.inner A (hL.ref (Ctx.ref_inner hu)))))).at
                w).unbox.mono (Ctx.le_boxIn_diaIn Δ x))
          rw [hsw hw]
          change SubE.Sim T (.ren (.step w .box)) (.ren w.inner)
          rw [VarSymb.inner_box hk]
          exact .refl _
      | .step w .keep =>
          obtain ⟨-, hw, -⟩ := Ctx.boxIn_keep hv'
          change SubE.Sim T (.ren (.step w .keep))
            (((Subst.single (σ := σ) (Δ := Δ) (.bnd 0)
              (.tm (Term.diatm x hx (Term.eta u.inner A (hL.ref (Ctx.ref_inner hu)))))).at
                w).keepE.mono (Ctx.le_boxIn_diaIn Δ x))
          rw [hsw hw]
          exact .refl _
      | .root _ => cases hv'
      | .step _ .fst => cases hv'
      | .step _ .snd => cases hv'
      | .step _ .dia => cases hv'
      | .step _ .here => cases hv'
  -- And that is the instantiation, weakened.
  have e := WFF.subst_mono_eq (Ctx.Le.refl _) hL _ hθ₃' hc₃' _ (Subst.ok_mono hθ₃' hL)
    (Subst.coh_mono hc₃' hL) hΓ₀ hΓ₀ hΓb ((Ctx.NoSlots.slots (Γ := Δ)).diaIn x)
    (fun _ _ _ => .refl _) ψ
  rw [WFF.mono_refl] at e
  exact e

/-- `◇_x ⊤` depends on the witness only through its address. -/
theorem WFF.dia_top_congr {Γ : Ctx} {d : ℕ} {x y : VarSymb} (h : x = y)
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (hy : ∃ X, Γ.ref y = some (.VTypeDia X)) :
    (WFF.dia x hx .top : WFF σ Γ d) = WFF.dia y hy .top := by
  subst h
  rfl

/-- ⭐**Strong D's schema**, `□φ(u.box) ⊢ ∃x:◇A. ◇_x φ(x.dia)`, derived from the axiom `D_ex`: the
    axiom's witness `z`, with `u`'s value put on it as content, witnesses the `∃`, and `K_dia`
    carries `□φ(u.box)` into `◇_z φ(u.box)`.  The eigenvariable `z` only has to be fresh. -/
def Proof.D_schema (hDS : ModalSys.DStrong = true) {Γ : Ctx} [Γ.NoSlots] {A : VarType}
    {u : VarSymb} (hu : Γ.ref u = some (.VTypeBox A)) (z : ℕ) (hz : Γ.RootFresh (.free z))
    (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    Proof σ Γ [WFF.boxHole hu ψ] (WFF.exDia A ψ) := by
  have hzd : ∃ X, (Γ.insert (.free z) (.VTypeDia .VTypeOne)).ref (.root (.free z)) =
      some (.VTypeDia X) := ⟨_, Ctx.ref_insert_root Γ (.free z) _⟩
  refine Proof.ex_elim z (.VTypeDia .VTypeOne) hz (φ := .dia (.root (.free z)) hzd .top) ?_ ?_
  · -- The axiom, its witness bound: binding `z` puts the slot back where the axiom has it.
    have hidx : Subst.singleIdx (σ := σ) (Δ := Γ.insert (.bnd 0) (.VTypeDia .VTypeOne)) (.free z)
        (.ren (.root (.bnd 0))) (.root (.free z)) = .root (.bnd 0) := by
      simp [Subst.singleIdx, SubE.idxAlong, VarSymb.ext, VarSymb.rt, VarSymb.path]
    have e : (WFF.somePoss : WFF σ Γ 0) = .ex (.VTypeDia .VTypeOne)
        (WFF.bindFree z hz Ctx.NoSlots.slots _ (.dia (.root (.free z)) hzd .top)) :=
      congrArg (WFF.ex _) (WFF.dia_top_congr hidx.symm _ _)
    exact e ▸ Proof.D_ex hDS
  · -- At the witness: put `u`'s value on it, and carry the premise into its view.
    have hle : Γ.Le (Γ.insert (.free z) (.VTypeDia .VTypeOne)) :=
      Ctx.le_insert hz.root (.VTypeDia .VTypeOne)
    refine Proof.ex_intro (.VTypeDia A) (Term.diatm (.root (.free z)) hzd (Term.eta u.inner A
      ((hle.boxIn.trans (Ctx.le_boxIn_diaIn _ _)).ref (Ctx.ref_inner hu)))) ?_
    rw [WFF.instantiate_exDia hle hu (.root (.free z)) hzd ψ]
    refine Proof.K_dia (.root (.free z)) hzd (Δ₂ := []) (ψ := .top)
      (Δ₁ := [WFF.mono hle.boxIn (WFF.instantiate (Ctx.NoSlots.slots (Γ := Γ.boxIn))
        (Term.eta u.inner A (Ctx.ref_inner hu)) ψ)]) ?_
    simp only [List.nil_append, List.map_cons, List.map_nil, WFF.mono_mono]
    exact Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The schema in a presented context, with its eigenvariable chosen fresh. -/
def Proof.D_schema' (hDS : ModalSys.DStrong = true) {Γ : Ctx} [Γ.Presented] {A : VarType}
    {u : VarSymb} (hu : Γ.ref u = some (.VTypeBox A)) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    Proof σ Γ [WFF.boxHole hu ψ] (WFF.exDia A ψ) :=
  Proof.D_schema hDS hu (Ctx.Presented.bound Γ) (Ctx.Presented.fresh_bound _ le_rfl) ψ

end V12M
