import QML.QML_v12m_SatInst

/-!
# QML v12m — soundness

⭐`Model.soundness`: if `Δ ⊢ φ` then, in every model, at every world, in every environment in which
all hypotheses hold, `φ` holds.  By induction on the proof.

The contexts of proofs have no visible address ending in a projection (`Ctx.NoProjLast`; every
presented context qualifies), which the substitution lemma needs.
-/

namespace V12M

variable [ModalSys]

universe u

namespace Model

variable {σ : Signature}

theorem hyps_cons {M : Model.{u} σ} {Γ : Ctx} {w : M.frame.W} {env : M.Env Γ w}
    {ψ : WFF σ Γ 0} {Δ : List (WFF σ Γ 0)} (h : M.sat env ψ) (hΔ : ∀ χ ∈ Δ, M.sat env χ) :
    ∀ χ ∈ ψ :: Δ, M.sat env χ := by
  intro χ hχ
  rcases List.mem_cons.mp hχ with rfl | h'
  · exact h
  · exact hΔ χ h'

/-- Pair elimination's formulas hold in one environment exactly when their premises hold in
    another (the components read by projection). -/
theorem sat_bindPair {M : Model.{u} σ} {Γ : Ctx} {d : ℕ} {w : M.frame.W} (hnp : Γ.NoProjLast)
    (u₁ u₂ z : ℕ) (hu : u₁ ≠ u₂) (hz₁ : z ≠ u₁) (hu₁ : Γ.RootFresh (.free u₁))
    (hu₂ : Γ.RootFresh (.free u₂)) (hzf : Γ.RootFresh (.free z)) (hs : Γ.SlotsFrom d)
    (A B : VarType) (envZ : M.Env (Γ.insert (.free z) (.VTypeProd A B)) w) :
    ∃ E : M.Env ((Γ.insert (.free u₁) A).insert (.free u₂) B) w,
      ∀ φ, M.sat envZ (WFF.bindPair u₁ u₂ z hu hz₁ hu₁ hu₂ hzf hs A B φ) ↔ M.sat E φ := by
  have hne₁₂ : Root.free u₁ ≠ Root.free u₂ := fun h => hu (Root.free.inj h)
  have hne_z₁ : Root.free z ≠ Root.free u₁ := fun h => hz₁ (Root.free.inj h)
  let E₁ := (envZ.restrict (Ctx.Le.refl _)).extend (.free u₁)
    (envZ.ref (.step (.root (.free z)) .fst) (Ctx.ref_insert_fst _ _ A B))
  let E₁' := E₁.restrict (Ctx.insert_swap_le hne_z₁.symm A (.VTypeProd A B))
  let E₂ := (E₁'.restrict
    (Ctx.le_insert (hzf.insert_ne hne_z₁.symm A).root (.VTypeProd A B))).extend
    (.free u₂) (E₁'.ref (.step (.root (.free z)) .snd) (Ctx.ref_insert_snd _ _ A B))
  refine ⟨E₂, fun φ => ?_⟩
  exact (sat_renameRoot envZ (hnp.insert _ _) (.free u₁) (hu₁.insert_ne hne_z₁ _) (Ctx.Le.refl _)
      (.step (.root (.free z)) .fst) (Ctx.ref_insert_fst _ _ A B)
      ((hs.insertFree z _).insertFree u₁ A) (hs.insertFree z _) _).trans
    ((sat_mono (Env.agree_restrict _ E₁) _).trans
      (sat_renameRoot E₁' (hnp.insert _ A) (.free u₂) (hu₂.insert_ne hne₁₂ A)
        (Ctx.le_insert (hzf.insert_ne hne_z₁.symm A).root _) (.step (.root (.free z)) .snd)
        (Ctx.ref_insert_snd _ _ A B) ((hs.insertFree u₁ A).insertFree u₂ B)
        ((hs.insertFree u₁ A).insertFree z _) φ))

/-- ⭐**Soundness.** -/
theorem soundness {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (p : Proof σ Γ Δ φ) :
    ∀ (M : Model.{u} σ) {w : M.frame.W} (env : M.Env Γ w), Γ.NoProjLast →
      (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ := by
  induction p with
  | @ax Γ φ =>
      intro M w env _ hΔ
      exact hΔ φ List.mem_cons_self
  | @weak Γ Δ φ ψ p ih =>
      intro M w env hnp hΔ
      exact ih M env hnp (fun χ hχ => hΔ χ (List.mem_cons_of_mem _ hχ))
  | @contr Γ Δ φ ψ p ih =>
      intro M w env hnp hΔ
      exact ih M env hnp (hyps_cons (hΔ ψ List.mem_cons_self) hΔ)
  | @exch Γ Δ₁ Δ₂ φ ψ χ p ih =>
      intro M w env hnp hΔ
      exact ih M env hnp (fun θ hθ => hΔ θ (by
        simp only [List.mem_append, List.mem_cons] at hθ ⊢
        tauto))
  | @weak_ctx Γ Δ φ u T hu p ih =>
      intro M w env hnp hΔ
      exact (sat_weaken_restrict hu.root env φ).mpr
        (ih M (env.restrict _) (hnp.of_insert hu.root) (fun ψ hψ =>
          (sat_weaken_restrict hu.root env ψ).mp (hΔ _ (List.mem_map.mpr ⟨ψ, hψ, rfl⟩))))
  | @and_intro Γ Δ φ ψ p q ihp ihq =>
      intro M w env hnp hΔ
      exact ⟨ihp M env hnp hΔ, ihq M env hnp hΔ⟩
  | @and_elim_l Γ Δ φ ψ p ih =>
      intro M w env hnp hΔ
      exact (ih M env hnp hΔ).1
  | @and_elim_r Γ Δ φ ψ p ih =>
      intro M w env hnp hΔ
      exact (ih M env hnp hΔ).2
  | @or_intro_l Γ Δ φ ψ p ih =>
      intro M w env hnp hΔ
      exact Or.inl (ih M env hnp hΔ)
  | @or_intro_r Γ Δ φ ψ p ih =>
      intro M w env hnp hΔ
      exact Or.inr (ih M env hnp hΔ)
  | @or_elim Γ Δ φ ψ χ p q r ihp ihq ihr =>
      intro M w env hnp hΔ
      exact (ihp M env hnp hΔ).elim (fun h => ihq M env hnp (hyps_cons h hΔ))
        (fun h => ihr M env hnp (hyps_cons h hΔ))
  | @imp_intro Γ Δ φ ψ p ih =>
      intro M w env hnp hΔ
      exact fun h => ih M env hnp (hyps_cons h hΔ)
  | @imp_elim Γ Δ φ ψ p q ihp ihq =>
      intro M w env hnp hΔ
      exact ihp M env hnp hΔ (ihq M env hnp hΔ)
  | @top_intro Γ Δ =>
      intro M w env _ _
      trivial
  | @bot_elim Γ Δ φ p ih =>
      intro M w env hnp hΔ
      exact (ih M env hnp hΔ).elim
  | @lem Γ Δ φ =>
      intro M w env _ _
      exact Classical.em (M.sat env φ)
  | @all_intro Γ _ Δ u T hu φ p ih =>
      intro M w env hnp hΔ o
      exact (sat_bindFree env hnp u hu Ctx.NoSlots.slots T o φ).mpr
        (ih M (env.extend (.free u) o) (hnp.insert _ T) (fun ψ hψ => by
          obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hψ
          exact (sat_weaken env hu.root o χ).mpr (hΔ χ hχ)))
  | @all_elim Γ _ Δ T φ a t p ih =>
      intro M w env hnp hΔ
      exact (sat_instantiate env hnp Ctx.NoSlots.slots t φ).mpr
        (ih M env hnp hΔ (interp env t))
  | @ex_intro Γ _ Δ T φ a t p ih =>
      intro M w env hnp hΔ
      exact ⟨interp env t, (sat_instantiate env hnp Ctx.NoSlots.slots t φ).mp (ih M env hnp hΔ)⟩
  | @ex_elim Γ _ Δ u T hu φ ψ p q ihp ihq =>
      intro M w env hnp hΔ
      obtain ⟨o, ho⟩ := ihp M env hnp hΔ
      have h₁ := (sat_bindFree env hnp u hu Ctx.NoSlots.slots T o φ).mp ho
      exact (sat_weaken env hu.root o ψ).mp
        (ihq M (env.extend (.free u) o) (hnp.insert _ T) (hyps_cons h₁ (fun χ hχ => by
          obtain ⟨χ', hχ', rfl⟩ := List.mem_map.mp hχ
          exact (sat_weaken env hu.root o χ').mpr (hΔ χ' hχ'))))
  | @eq_intro Γ Δ t =>
      intro M w env _ _
      exact rfl
  | @eq_elim Γ _ Δ φ t s p q ihp ihq =>
      intro M w env hnp hΔ
      have he : interp env t = interp env s := ihp M env hnp hΔ
      refine (sat_instantiate env hnp Ctx.NoSlots.slots s φ).mpr ?_
      rw [← he]
      exact (sat_instantiate env hnp Ctx.NoSlots.slots t φ).mp (ihq M env hnp hΔ)
  | @pair_elim Γ _ A B u₁ u₂ z hu hz₁ hu₁ hu₂ hzf Δ φ p ih =>
      intro M w env hnp hΔ
      have hnpΓ := hnp.of_insert hzf.root
      obtain ⟨E, hE⟩ := sat_bindPair hnpΓ u₁ u₂ z hu hz₁ hu₁ hu₂ hzf Ctx.NoSlots.slots A B env
      exact (hE φ).mpr (ih M E ((hnpΓ.insert _ A).insert _ B)
        (fun ψ hψ => (hE ψ).mp (hΔ _ (List.mem_map.mpr ⟨ψ, hψ, rfl⟩))))
  | @K_box Γ Δ φ p ih =>
      intro M w env _ hΔ w'
      exact ih M (env.boxPush w') (Ctx.noProjLast_boxIn Γ)
        (fun ψ hψ => hΔ _ (List.mem_map.mpr ⟨ψ, hψ, rfl⟩) w')
  | @K_dia Γ x hx Δ₁ Δ₂ φ ψ p ih =>
      intro M w env _ hΔ
      obtain ⟨X, hr, w', hψ⟩ := hΔ _ List.mem_cons_self
      refine ⟨X, hr, w', ih M (env.diaPush x hr w') (Ctx.noProjLast_diaIn Γ x)
        (hyps_cons hψ (fun χ hχ => ?_))⟩
      rcases List.mem_append.mp hχ with h₂ | h₁
      · have hb := hΔ (WFF.boxx x hx χ)
          (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨χ, h₂, rfl⟩)))
        by_contra hne
        exact hb ⟨X, hr, w', hne⟩
      · obtain ⟨χ', hχ', rfl⟩ := List.mem_map.mp h₁
        have hb := hΔ (WFF.box χ')
          (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨χ', hχ', rfl⟩)))
        exact (sat_mono (Env.box_dia_agree env hr w') χ').mpr (hb w'.1)
  | @dia_bot Γ Δ x hx p ih =>
      intro M w env hnp hΔ
      obtain ⟨_, _, _, h⟩ := ih M env hnp hΔ
      exact h
  | @T_box Γ _ hT Δ φ p ih =>
      intro M w env hnp hΔ
      exact (sat_boxHere hT env Ctx.NoSlots.slots φ).mpr
        (ih M env hnp hΔ ⟨w, M.frame.refl hT w⟩)

end Model

end V12M
