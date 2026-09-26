import QML.QML_v12m_SatInst
import QML.QML_v12m_SemStrongT
import QML.QML_v12m_SemHere

/-!
# QML v12m — soundness

⭐`Model.soundness`: if `Δ ⊢ φ` then, in every model, at every world, in every environment in which
all hypotheses hold, `φ` holds.  By induction on the proof.

The contexts of proofs have no visible address ending in a projection (`Ctx.NoProjLast`; every
presented context qualifies), which the substitution lemma needs.
-/

namespace V12M

variable [ModalSys]

universe u v

namespace Model

variable {σ : Signature}

theorem hyps_cons {M : Model.{u, v} σ} {Γ : Ctx} {w : M.frame.W} {env : M.Env Γ w}
    {ψ : WFF σ Γ 0} {Δ : List (WFF σ Γ 0)} (h : M.sat env ψ) (hΔ : ∀ χ ∈ Δ, M.sat env χ) :
    ∀ χ ∈ ψ :: Δ, M.sat env χ := by
  intro χ hχ
  rcases List.mem_cons.mp hχ with rfl | h'
  · exact h
  · exact hΔ χ h'

/-- Pair elimination's formulas hold in one environment exactly when their premises hold in
    another (the components read by projection). -/
theorem sat_bindPair {M : Model.{u, v} σ} {Γ : Ctx} {d : ℕ} {w : M.frame.W} (hnp : Γ.NoProjLast)
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

/-- A closed formula's truth depends only on the world. -/
theorem sat_closed {M : Model.{u, v} σ} {Γ Γ' : Ctx} {w : M.frame.W} (env : M.Env Γ w)
    (env' : M.Env Γ' w) {d : ℕ} (ψ : WFF σ Ctx.empty d) :
    M.sat env (ψ.closed Γ) ↔ M.sat env' (ψ.closed Γ') :=
  have e₀ : M.Env Ctx.empty w := fun _ _ h => nomatch h
  (sat_mono (env := e₀) (fun _ _ h => nomatch h) ψ).trans
    (sat_mono (env := e₀) (fun _ _ h => nomatch h) ψ).symm

/-- ⭐**Soundness.** -/
theorem soundness {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (p : Proof σ Γ Δ φ) :
    ∀ (M : Model.{u, v} σ) {w : M.frame.W} (env : M.Env Γ w), Γ.NoProjLast →
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
  | @diaEq_intro Γ Δ A b s =>
      intro M w env _ _
      exact rfl
  | @diaEq_elim Γ _ Δ A φ b b' s s' p q ihp ihq =>
      intro M w env hnp hΔ
      have he : interp env s = interp env s' := ihp M env hnp hΔ
      refine (sat_instantiate env hnp Ctx.NoSlots.slots s' φ).mpr ?_
      rw [← he]
      exact (sat_instantiate env hnp Ctx.NoSlots.slots s φ).mp (ihq M env hnp hΔ)
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
  | @D_box Γ Δ hD p ih =>
      intro M w env hnp hΔ
      obtain ⟨v, ⟨hv⟩⟩ := M.frame.serial hD w
      exact ih M env hnp hΔ ⟨v, ⟨hv⟩⟩
  | @D_ex Γ Δ hDS =>
      intro M w env _ _
      obtain ⟨p, ⟨v⟩⟩ := M.posSerial hDS w
      have hr : (env.extend (.bnd 0) (T := .VTypeDia .VTypeOne) p).ref (.root (.bnd 0))
          (Ctx.ref_insert_root Γ (.bnd 0) _) = p := by
        simp [Model.Env.ref, Model.Env.extend]
      exact ⟨p, .VTypeOne, Ctx.ref_insert_root Γ (.bnd 0) _, ⟨v.1, by rw [hr]; exact v.2⟩, trivial⟩
  | @T_box Γ _ hT Δ φ p ih =>
      intro M w env hnp hΔ
      exact (sat_boxHere hT env Ctx.NoSlots.slots φ).mpr
        (ih M env hnp hΔ ⟨w, ⟨M.frame.refl hT w⟩⟩)
  | @four_box Γ _ hF Δ φ p ih =>
      intro M w env hnp hΔ v s
      exact (sat_shift_twoBox hF env Ctx.NoSlots.slots φ v s).mpr
        (ih M env hnp hΔ ⟨s.1, ⟨M.frame.trans hF v.2.down s.2.down⟩⟩)
  | @T_dia Γ _ hT hS A a t c y hc hy hyc Δ φ Ψ p ih =>
      -- Interpret the eigenvariable as some possible object realised here.
      intro M w env hnp hΔ
      obtain ⟨q, hmem, hcont⟩ := M.posRet_exists hT hS (interp env t)
      refine (sat_weaken (T := .VTypeDia A) env hc.root q φ).mp
        (ih M (env.extend (T := .VTypeDia A) (.free c) q) (hnp.insert _ _) ?_)
      intro χ hχ
      rcases List.mem_append.mp hχ with h₁ | h₂
      · -- A `Ψ` hypothesis: for every value of its parameter, the `here` reading gives the `◇` one.
        obtain ⟨ψ, _, rfl⟩ := List.mem_map.mp h₁
        exact sat_retHyp hT env hnp t c y hc hy hyc ψ.1 ψ.2 q hmem hcont
      · -- An old hypothesis, merely weakened by the eigenvariable.
        obtain ⟨χ', hχ', rfl⟩ := List.mem_map.mp h₂
        exact (sat_weaken (T := .VTypeDia A) env hc.root q χ').mpr (hΔ χ' hχ')
  | @here_elim Γ _ Δ hT x hx t bd ψ ph pb ihh ihb =>
      intro M w env hnp hΔ
      exact sat_here_elim hT env hnp hx t bd ψ (ihh M env hnp hΔ) (ihb M env hnp hΔ)
  | @here_intro Γ _ Δ hT x hx t bd ψ ph pr ihh ihr =>
      intro M w env hnp hΔ
      exact sat_here_intro hT env hnp hx t bd ψ (ihh M env hnp hΔ) (ihr M env hnp hΔ)
  | @here_beta Γ _ Δ hT x hx t bd s ph ihh =>
      intro M w env hnp hΔ
      obtain ⟨Y, h⟩ := id hx
      exact sat_here_beta hT env hnp hx h t bd s (ihh M env hnp hΔ)
  | @here_fun Γ Δ hT b s t t' ph ph' ihh ihh' =>
      intro M w env hnp hΔ
      exact sat_here_fun hT env s t t' (ihh M env hnp hΔ) (ihh' M env hnp hΔ)
  | @B_dia Γ Δ hB ψ p ih =>
      -- `◇□ψ`: along some arrow `w → v`, `ψ` holds after every arrow out of `v`; one leads back.
      intro M w env hnp hΔ
      by_contra hn
      refine ih M env hnp hΔ fun v hv => ?_
      obtain ⟨b⟩ := M.frame.symm hB v.2.down
      exact hn ((sat_closed _ env ψ).mp (hv ⟨w, ⟨b⟩⟩))

end Model

end V12M
