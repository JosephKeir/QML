import QML.QML_v12m_GK

/-!
# QML v12m — substitution in GK

A substitution from a derivation's context into a presented context sends it to a derivation of
the substituted sequent **of the same height** (`GK.subst`), by the formula-level lemmas
`Proof.subst` uses: each rule goes to itself, eigenvariables renamed to the target's first fresh
name.  Weakening along a context inclusion is the identity renaming (`GK.monoCtx`).
-/

namespace V12M

variable [ModalSys] {σ : Signature}

/-- Substitution keeps an atom atomic. -/
theorem WFF.IsAtom.subst {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d d' : ℕ} {θ : Subst σ Δ}
    {hθ : Subst.Ok Γ θ} {hc : Subst.Coh ι Γ θ} {hΓ : Γ.SlotsFrom d} {hΔ : Δ.SlotsFrom d'}
    {P : WFF σ Γ d} (hP : P.IsAtom) : (WFF.subst ι θ hθ hc hΓ hΔ P).IsAtom := by
  cases P <;> first | exact trivial | exact hP.elim

namespace GK

/-- ⭐**Substitution**, height-preserving: a substitution from the context of a derivation into a
    presented context sends it to a derivation of the substituted sequent. -/
theorem subst {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} (p : GK σ n Γ Δ Θ) :
    ∀ {Γ' : Ctx} [Γ'.Presented] {ι : VarSymb → VarSymb} (θ : Subst σ Γ')
      (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0),
      GK σ n Γ' (Δ.map (WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots))
        (Θ.map (WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots)) := by
  induction p with
  | ax P hP h₁ h₂ =>
      intro Γ' _ ι θ hθ hc hΓ
      exact .ax _ hP.subst (List.mem_map_of_mem h₁) (List.mem_map_of_mem h₂)
  | botL h => intro Γ' _ ι θ hθ hc hΓ; exact .botL (List.mem_map_of_mem h)
  | topR h => intro Γ' _ ι θ hθ hc hΓ; exact .topR (List.mem_map_of_mem h)
  | andL h _ ih =>
      intro Γ' _ ι θ hθ hc hΓ; exact .andL (List.mem_map_of_mem h) (ih θ hθ hc hΓ)
  | andR h _ _ ih₁ ih₂ =>
      intro Γ' _ ι θ hθ hc hΓ
      exact .andR (List.mem_map_of_mem h) (ih₁ θ hθ hc hΓ) (ih₂ θ hθ hc hΓ)
  | orL h _ _ ih₁ ih₂ =>
      intro Γ' _ ι θ hθ hc hΓ
      exact .orL (List.mem_map_of_mem h) (ih₁ θ hθ hc hΓ) (ih₂ θ hθ hc hΓ)
  | orR h _ ih =>
      intro Γ' _ ι θ hθ hc hΓ; exact .orR (List.mem_map_of_mem h) (ih θ hθ hc hΓ)
  | impL h _ _ ih₁ ih₂ =>
      intro Γ' _ ι θ hθ hc hΓ
      exact .impL (List.mem_map_of_mem h) (ih₁ θ hθ hc hΓ) (ih₂ θ hθ hc hΓ)
  | impR h _ ih =>
      intro Γ' _ ι θ hθ hc hΓ; exact .impR (List.mem_map_of_mem h) (ih θ hθ hc hΓ)
  | allL T t h _ ih =>
      intro Γ' _ ι θ hθ hc hΓ
      have ih' := ih θ hθ hc hΓ
      rw [List.map_cons, WFF.subst_instantiate θ hθ hc hΓ Ctx.NoSlots.slots t] at ih'
      exact .allL T (Term.subst ι θ hθ hc t) (List.mem_map_of_mem h) ih'
  | exR T t h _ ih =>
      intro Γ' _ ι θ hθ hc hΓ
      have ih' := ih θ hθ hc hΓ
      rw [List.map_cons, WFF.subst_instantiate θ hθ hc hΓ Ctx.NoSlots.slots t] at ih'
      exact .exR T (Term.subst ι θ hθ hc t) (List.mem_map_of_mem h) ih'
  | @allR n Γ _ Δ Θ u T hu φ h _ ih =>
      intro Γ' _ ι θ hθ hc hΓ
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hu' : Γ'.RootFresh (.free (Ctx.Presented.bound Γ')) :=
        Ctx.Presented.fresh_bound _ le_rfl
      have ih' := ih (Γ' := Γ'.insert (.free (Ctx.Presented.bound Γ')) T)
        (θ.rename u _ T hu'.root) (Subst.ok_rename hθ T hu'.root)
        (Subst.coh_rename hθ hc hu T hu'.root) (hΓ.insertFree u T)
      have hf : (_ ∘ WFF.weaken hu.root T) =
          WFF.weaken hu'.root T ∘ WFF.subst ι θ hθ hc hΓ hΓ' :=
        funext fun ψ => WFF.subst_weaken_rename θ hθ hc hΓ hΓ' hu hu' T ψ
      rw [List.map_cons, List.map_map, List.map_map, hf, ← List.map_map, ← List.map_map] at ih'
      refine .allR _ T hu' ?_ ih'
      rw [← congrArg (WFF.all T) (WFF.subst_bindFree θ hθ hc hΓ hΓ' hu hu' T φ)]
      exact List.mem_map_of_mem h
  | @exL n Γ _ Δ Θ u T hu φ h _ ih =>
      intro Γ' _ ι θ hθ hc hΓ
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hu' : Γ'.RootFresh (.free (Ctx.Presented.bound Γ')) :=
        Ctx.Presented.fresh_bound _ le_rfl
      have ih' := ih (Γ' := Γ'.insert (.free (Ctx.Presented.bound Γ')) T)
        (θ.rename u _ T hu'.root) (Subst.ok_rename hθ T hu'.root)
        (Subst.coh_rename hθ hc hu T hu'.root) (hΓ.insertFree u T)
      have hf : (_ ∘ WFF.weaken hu.root T) =
          WFF.weaken hu'.root T ∘ WFF.subst ι θ hθ hc hΓ hΓ' :=
        funext fun ψ => WFF.subst_weaken_rename θ hθ hc hΓ hΓ' hu hu' T ψ
      rw [List.map_cons, List.map_map, List.map_map, hf, ← List.map_map, ← List.map_map] at ih'
      refine .exL _ T hu' ?_ ih'
      rw [← congrArg (WFF.ex T) (WFF.subst_bindFree θ hθ hc hΓ hΓ' hu hu' T φ)]
      exact List.mem_map_of_mem h
  | ref t _ ih =>
      intro Γ' _ ι θ hθ hc hΓ; exact .ref (Term.subst ι θ hθ hc t) (ih θ hθ hc hΓ)
  | repl hP t s h₁ h₂ _ ih =>
      intro Γ' _ ι θ hθ hc hΓ
      have ih' := ih θ hθ hc hΓ
      rw [List.map_cons, WFF.subst_instantiate θ hθ hc hΓ Ctx.NoSlots.slots s] at ih'
      refine .repl hP.subst (Term.subst ι θ hθ hc t) (Term.subst ι θ hθ hc s)
        (List.mem_map_of_mem h₁) ?_ ih'
      rw [← WFF.subst_instantiate θ hθ hc hΓ Ctx.NoSlots.slots t]
      exact List.mem_map_of_mem h₂
  | boxR h₁ h₂ _ ih =>
      intro Γ' _ ι θ hθ hc hΓ
      refine .boxR (List.mem_map_of_mem h₁) ?_
        (ih θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn)
      intro χ hχ
      obtain ⟨χ₀, hχ₀, rfl⟩ := List.mem_map.mp hχ
      exact List.mem_map_of_mem (h₂ χ₀ hχ₀)
  | @diaL n Γ Δ Θ x hx ψ Δ₁ Θ₁ h₁ h₂ h₃ _ ih =>
      intro Γ' _ ι θ hθ hc hΓ
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hwx : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      have ih' := ih (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
        (hΓ.diaIn x)
      have hf : (_ ∘ WFF.mono (Ctx.le_boxIn_diaIn Γ x)) =
          WFF.mono (Ctx.le_boxIn_diaIn Γ' (ι x)) ∘
            WFF.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn Ctx.NoSlots.slots :=
        funext fun χ => WFF.subst_diaIn_mono θ hθ hc hx hw hΓ Ctx.NoSlots.slots
          Ctx.NoSlots.slots χ
      rw [List.map_cons, List.map_map, hf, ← List.map_map] at ih'
      refine .diaL (ι x) hwx (List.mem_map_of_mem h₁) ?_ ?_ ih'
      · intro χ hχ
        obtain ⟨χ₀, hχ₀, rfl⟩ := List.mem_map.mp hχ
        exact List.mem_map_of_mem (h₂ χ₀ hχ₀)
      · intro χ hχ
        obtain ⟨χ₀, hχ₀, rfl⟩ := List.mem_map.mp hχ
        exact List.mem_map_of_mem (h₃ χ₀ hχ₀)

/-- ⭐**Weakening along a context inclusion**, height-preserving, into a presented context. -/
theorem monoCtx {n : ℕ} {Γ Γ' : Ctx} [Γ'.Presented] {Δ Θ : List (WFF σ Γ 0)} (h : Γ.Le Γ')
    (p : GK σ n Γ Δ Θ) : GK σ n Γ' (Δ.map (WFF.mono h)) (Θ.map (WFF.mono h)) := by
  have hΓ : Γ.SlotsFrom 0 := (Ctx.NoSlots.slots (Γ := Γ')).of_le h
  have key : ∀ ψ : WFF σ Γ 0, WFF.subst id (Subst.idRen Γ') (Subst.ok_idRen.restrict h)
      (Subst.coh_idRen.restrict h) hΓ Ctx.NoSlots.slots ψ = WFF.mono h ψ :=
    fun ψ => WFF.subst_ren h _ _ _ hΓ _ (fun v _ _ => Subst.at_idRen v) ψ
  have := p.subst (Subst.idRen Γ') (Subst.ok_idRen.restrict h) (Subst.coh_idRen.restrict h) hΓ
  rwa [List.map_congr_left (l := Δ) fun ψ _ => key ψ,
    List.map_congr_left (l := Θ) fun ψ _ => key ψ] at this

end GK

end V12M
