import QML.QML_v12m_SatInst
import QML.QML_v12m_SemStrongT
import QML.QML_v12m_SemHere
import QML.QML_v12m_SemBack

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
    ∀ (M : Model.{u, v} σ), M.IndInvariant → ∀ {w : M.frame.W} (env : M.Env Γ w),
      Γ.Tame → Γ.NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ := by
  induction p with
  | @ax Γ φ =>
      intro M hM w env hfin _ hΔ
      exact hΔ φ List.mem_cons_self
  | @weak Γ Δ φ ψ p ih =>
      intro M hM w env hfin hnp hΔ
      exact ih M hM env hfin hnp (fun χ hχ => hΔ χ (List.mem_cons_of_mem _ hχ))
  | @contr Γ Δ φ ψ p ih =>
      intro M hM w env hfin hnp hΔ
      exact ih M hM env hfin hnp (hyps_cons (hΔ ψ List.mem_cons_self) hΔ)
  | @exch Γ Δ₁ Δ₂ φ ψ χ p ih =>
      intro M hM w env hfin hnp hΔ
      exact ih M hM env hfin hnp (fun θ hθ => hΔ θ (by
        simp only [List.mem_append, List.mem_cons] at hθ ⊢
        tauto))
  | @weak_ctx Γ Δ φ u T hu p ih =>
      intro M hM w env hfin hnp hΔ
      exact (sat_weaken_restrict hu.root env φ).mpr
        (ih M hM (env.restrict _) (hfin.mono (Ctx.le_insert hu.root T)) (hnp.of_insert hu.root)
          (fun ψ hψ =>
          (sat_weaken_restrict hu.root env ψ).mp (hΔ _ (List.mem_map.mpr ⟨ψ, hψ, rfl⟩))))
  | @and_intro Γ Δ φ ψ p q ihp ihq =>
      intro M hM w env hfin hnp hΔ
      exact ⟨ihp M hM env hfin hnp hΔ, ihq M hM env hfin hnp hΔ⟩
  | @and_elim_l Γ Δ φ ψ p ih =>
      intro M hM w env hfin hnp hΔ
      exact (ih M hM env hfin hnp hΔ).1
  | @and_elim_r Γ Δ φ ψ p ih =>
      intro M hM w env hfin hnp hΔ
      exact (ih M hM env hfin hnp hΔ).2
  | @or_intro_l Γ Δ φ ψ p ih =>
      intro M hM w env hfin hnp hΔ
      exact Or.inl (ih M hM env hfin hnp hΔ)
  | @or_intro_r Γ Δ φ ψ p ih =>
      intro M hM w env hfin hnp hΔ
      exact Or.inr (ih M hM env hfin hnp hΔ)
  | @or_elim Γ Δ φ ψ χ p q r ihp ihq ihr =>
      intro M hM w env hfin hnp hΔ
      exact (ihp M hM env hfin hnp hΔ).elim (fun h => ihq M hM env hfin hnp (hyps_cons h hΔ))
        (fun h => ihr M hM env hfin hnp (hyps_cons h hΔ))
  | @imp_intro Γ Δ φ ψ p ih =>
      intro M hM w env hfin hnp hΔ
      exact fun h => ih M hM env hfin hnp (hyps_cons h hΔ)
  | @imp_elim Γ Δ φ ψ p q ihp ihq =>
      intro M hM w env hfin hnp hΔ
      exact ihp M hM env hfin hnp hΔ (ihq M hM env hfin hnp hΔ)
  | @top_intro Γ Δ =>
      intro M hM w env _ _ _
      trivial
  | @bot_elim Γ Δ φ p ih =>
      intro M hM w env hfin hnp hΔ
      exact (ih M hM env hfin hnp hΔ).elim
  | @lem Γ Δ φ =>
      intro M hM w env _ _ _
      exact Classical.em (M.sat env φ)
  | @all_intro Γ _ Δ u T hu φ p ih =>
      intro M hM w env hfin hnp hΔ o
      exact (sat_bindFree env hnp u hu Ctx.NoSlots.slots T o φ).mpr
        (ih M hM (env.extend (.free u) o) (hfin.insert hu T) (hnp.insert _ T) (fun ψ hψ => by
          obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hψ
          exact (sat_weaken env hu.root o χ).mpr (hΔ χ hχ)))
  | @all_elim Γ _ Δ T φ a t p ih =>
      intro M hM w env hfin hnp hΔ
      exact (sat_instantiate env hnp Ctx.NoSlots.slots t φ).mpr
        (ih M hM env hfin hnp hΔ (interp env t))
  | @ex_intro Γ _ Δ T φ a t p ih =>
      intro M hM w env hfin hnp hΔ
      exact ⟨interp env t,
        (sat_instantiate env hnp Ctx.NoSlots.slots t φ).mp (ih M hM env hfin hnp hΔ)⟩
  | @ex_elim Γ _ Δ u T hu φ ψ p q ihp ihq =>
      intro M hM w env hfin hnp hΔ
      obtain ⟨o, ho⟩ := ihp M hM env hfin hnp hΔ
      have h₁ := (sat_bindFree env hnp u hu Ctx.NoSlots.slots T o φ).mp ho
      exact (sat_weaken env hu.root o ψ).mp
        (ihq M hM (env.extend (.free u) o) (hfin.insert hu T) (hnp.insert _ T)
          (hyps_cons h₁ (fun χ hχ => by
          obtain ⟨χ', hχ', rfl⟩ := List.mem_map.mp hχ
          exact (sat_weaken env hu.root o χ').mpr (hΔ χ' hχ'))))
  | @eq_intro Γ Δ t =>
      intro M hM w env _ _ _
      exact rfl
  | @eq_elim Γ _ Δ φ t s p q ihp ihq =>
      intro M hM w env hfin hnp hΔ
      have he : interp env t = interp env s := ihp M hM env hfin hnp hΔ
      refine (sat_instantiate env hnp Ctx.NoSlots.slots s φ).mpr ?_
      rw [← he]
      exact (sat_instantiate env hnp Ctx.NoSlots.slots t φ).mp (ihq M hM env hfin hnp hΔ)
  | @pair_elim Γ _ A B u₁ u₂ z hu hz₁ hu₁ hu₂ hzf Δ φ p ih =>
      intro M hM w env hfin hnp hΔ
      have hnpΓ := hnp.of_insert hzf.root
      obtain ⟨E, hE⟩ := sat_bindPair hnpΓ u₁ u₂ z hu hz₁ hu₁ hu₂ hzf Ctx.NoSlots.slots A B env
      have hfinΓ := hfin.mono (Ctx.le_insert hzf.root _)
      exact (hE φ).mpr (ih M hM E ((hfinΓ.insert hu₁ A).insert
        (hu₂.insert_ne (fun h => hu (Root.free.inj h)) A) B) ((hnpΓ.insert _ A).insert _ B)
        (fun ψ hψ => (hE ψ).mp (hΔ _ (List.mem_map.mpr ⟨ψ, hψ, rfl⟩))))
  | @K_box Γ Δ φ p ih =>
      intro M hM w env hfin _ hΔ w'
      exact ih M hM (env.boxPush w') hfin.boxIn (Ctx.noProjLast_boxIn Γ)
        (fun ψ hψ => hΔ _ (List.mem_map.mpr ⟨ψ, hψ, rfl⟩) w')
  | @K_dia Γ x hx Δ₁ Δ₂ φ ψ p ih =>
      intro M hM w env hfin _ hΔ
      obtain ⟨X, hr, w', hψ⟩ := hΔ _ List.mem_cons_self
      refine ⟨X, hr, w', ih M hM (env.diaPush x hr w') (hfin.diaIn x) (Ctx.noProjLast_diaIn Γ x)
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
      intro M hM w env hfin hnp hΔ
      obtain ⟨_, _, _, h⟩ := ih M hM env hfin hnp hΔ
      exact h
  | @D_box Γ Δ hD p ih =>
      intro M hM w env hfin hnp hΔ
      obtain ⟨v, ⟨hv⟩⟩ := M.frame.serial hD w
      exact ih M hM env hfin hnp hΔ ⟨v, ⟨hv⟩⟩
  | @D_ex Γ Δ hDS =>
      intro M hM w env _ _ _
      obtain ⟨p, ⟨v⟩⟩ := M.posSerial hDS w
      have hr : (env.extend (.bnd 0) (T := .VTypeDia .VTypeOne) p).ref (.root (.bnd 0))
          (Ctx.ref_insert_root Γ (.bnd 0) _) = p := by
        simp [Model.Env.ref, Model.Env.extend]
      exact ⟨p, .VTypeOne, Ctx.ref_insert_root Γ (.bnd 0) _, ⟨v.1, by rw [hr]; exact v.2⟩, trivial⟩
  | @T_box Γ _ hT Δ φ p ih =>
      intro M hM w env hfin hnp hΔ
      exact (sat_boxHere hT env Ctx.NoSlots.slots φ).mpr
        (ih M hM env hfin hnp hΔ ⟨w, ⟨M.frame.refl hT w⟩⟩)
  | @four_box Γ _ hF Δ φ p ih =>
      intro M hM w env hfin hnp hΔ v s
      exact (sat_shift_twoBox hF env Ctx.NoSlots.slots φ v s).mpr
        (ih M hM env hfin hnp hΔ ⟨s.1, ⟨M.frame.trans hF v.2.down s.2.down⟩⟩)
  | @T_dia Γ _ hT hS A a t c hc Δ φ p ih =>
      -- Interpret the eigenvariable as some possible object realised here — `posRet_exists` says
      -- there is one, and that *is* the hypothesis the subproof gets.
      intro M hM w env hfin hnp hΔ
      obtain ⟨q, hmem, hcont⟩ := M.posRet_exists hT hS (interp env t)
      refine (sat_weaken (T := .VTypeDia A) env hc.root q φ).mp
        (ih M hM (env.extend (T := .VTypeDia A) (.free c) q) (hfin.insert hc _) (hnp.insert _ _) ?_)
      intro χ hχ
      rcases List.mem_cons.mp hχ with h₁ | h₂
      · -- The `Here` hypothesis: the witness is realised here, by `t`.
        subst h₁
        refine (sat_hereAt_extend hT env (.free c) hc q t).mpr ⟨hmem, hcont⟩
      · -- An old hypothesis, merely weakened by the eigenvariable.
        obtain ⟨χ', hχ', rfl⟩ := List.mem_map.mp h₂
        exact (sat_weaken (T := .VTypeDia A) env hc.root q χ').mpr (hΔ χ' hχ')
  | @here_elim Γ _ Δ hT x hx A a t a₁ bd ψ ph pb ihh ihb =>
      intro M hM w env hfin hnp hΔ
      exact sat_here_elim hT env hnp hfin hM hx t bd ψ (ihh M hM env hfin hnp hΔ)
        (ihb M hM env hfin hnp hΔ)
  | @here_intro Γ _ Δ hT x hx A a t a₁ bd ψ ph pr ihh ihr =>
      intro M hM w env hfin hnp hΔ
      exact sat_here_intro hT env hnp hfin hM hx t bd ψ (ihh M hM env hfin hnp hΔ)
        (ihr M hM env hfin hnp hΔ)
  | @here_beta Γ _ Δ hT x hx A a t a₁ bd B b s ph ihh =>
      intro M hM w env hfin hnp hΔ
      obtain ⟨Y, h⟩ := id hx
      exact sat_here_beta hT env hnp hfin hM hx h t bd s (ihh M hM env hfin hnp hΔ)
  | @here_name Γ _ Δ hT x hx B β bd p ih =>
      intro M hM w env hfin hnp hΔ
      obtain ⟨Y, h⟩ := id hx
      exact sat_here_name hT env hx h bd (ih M hM env hfin hnp hΔ)
  | @here_subst Γ _ Δ hT A b s a a' t t' φ ph ph' pf ihh ihh' ihf =>
      intro M hM w env hfin hnp hΔ
      exact sat_here_subst hT env hnp hfin hM s t t' φ (ihh M hM env hfin hnp hΔ)
        (ihh' M hM env hfin hnp hΔ)
        (ihf M hM env hfin hnp hΔ)
  | @here_eq Γ _ Δ hT A b s a t t' ph pe ihh ihe =>
      intro M hM w env hfin hnp hΔ
      exact sat_here_eq hT env s t t' (ihh M hM env hfin hnp hΔ) (ihe M hM env hfin hnp hΔ)
  | @B_dia Γ Δ hB ψ p ih =>
      -- `◇□ψ`: along some arrow `w → v`, `ψ` holds after every arrow out of `v`; one leads back.
      intro M hM w env hfin hnp hΔ
      by_contra hn
      refine ih M hM env hfin hnp hΔ fun v hv => ?_
      obtain ⟨b⟩ := M.frame.symm hB v.2.down
      exact hn ((sat_closed _ env ψ).mp (hv ⟨w, ⟨b⟩⟩))
  | @back_counit Γ _ Δ hS O P hP A a₀ bd a t ψ pb pd ihb ihd =>
      intro M hM w env hfin hnp hΔ
      exact sat_back_counit env hnp hM hS O P hP bd t ψ (ihb M hM env hfin hnp hΔ)
        (ihd M hM env hfin hnp hΔ)
  | @back_unit Γ _ Δ hS O P hP A a₀ bd a t ψ pb pr ihb ihr =>
      intro M hM w env hfin hnp hΔ
      exact sat_back_unit env hnp hM hS O P hP bd t ψ (ihb M hM env hfin hnp hΔ)
        (ihr M hM env hfin hnp hΔ)
  | @back_ne Γ _ Δ hS O P hP A a₀ bd a t pb ihb =>
      intro M hM w env hfin hnp hΔ
      exact sat_back_ne env hS O P hP bd t (ihb M hM env hfin hnp hΔ)
  | @back_beta Γ _ Δ hS O P hP A a₀ bd a t B b s pb ihb =>
      intro M hM w env hfin hnp hΔ
      exact sat_back_beta env hnp hM hS O P hP bd t s (ihb M hM env hfin hnp hΔ)
  | @back_pair Γ _ Δ hS O P hP A a₀ bd a t B b₀ bd' b t' pb pb' ihb ihb' =>
      intro M hM w env hfin hnp hΔ
      exact sat_back_pair env hM hS O P hP bd t bd' t' (ihb M hM env hfin hnp hΔ)
        (ihb' M hM env hfin hnp hΔ)
  | @back_eq Γ _ Δ hS L A b s a t t' pb pe ihb ihe =>
      intro M hM w env hfin hnp hΔ
      exact sat_back_eq env hS L s t t' (ihb M hM env hfin hnp hΔ) (ihe M hM env hfin hnp hΔ)
  | @back_eqC Γ _ Δ hS L A b s s' a t pb pe ihb ihe =>
      intro M hM w env hfin hnp hΔ
      exact sat_back_eqC env hS L s s' t (ihb M hM env hfin hnp hΔ) (ihe M hM env hfin hnp hΔ)
  | @back_here Γ _ Δ hS hT A a₀ bd a t φ pb pφ ihb ihφ =>
      intro M hM w env hfin hnp hΔ
      exact sat_back_here env hnp hfin hM hS hT bd t φ (ihb M hM env hfin hnp hΔ)
        (ihφ M hM env hfin hnp hΔ)
  | @back_ret Γ _ hS hB O A hA a₀ bd a t c hc Δ pne p ihne ih =>
      -- Each arrow's return is a value of the carrier's returning possibility, which the
      -- subproof makes `t`.
      intro M hM w env hfin hnp hΔ
      refine sat_back_ret env hS hB O hA bd t c hc (ihne M hM env hfin hnp hΔ) fun o hr => ?_
      refine ih M hM (env.extend (T := A) (.free c) o) (hfin.insert hc _) (hnp.insert _ _) ?_
      intro χ hχ
      rcases List.mem_cons.mp hχ with h₁ | h₂
      · subst h₁
        exact hr
      · obtain ⟨χ', hχ', rfl⟩ := List.mem_map.mp h₂
        exact (sat_weaken (T := A) env hc.root o χ').mpr (hΔ χ' hχ')
  | @B_strong Γ _ hS A a t c hc Δ φ pne p ihne ih =>
      -- Interpret the eigenvariable as a carrier that comes back as `t` — `backRet_exists` says
      -- there is one wherever there is a way out, and that *is* the hypothesis the subproof gets.
      intro M hM w env hfin hnp hΔ
      obtain ⟨i, _⟩ := (OutLeg.sat_dia env .nec _).mp (ihne M hM env hfin hnp hΔ)
      obtain ⟨c₀, hc₀⟩ := M.backRet_exists hS ⟨i⟩ (interp env t)
      let q : M.frame.Dom (.VTypeBox (.VTypeBox A)) w := c₀
      refine (sat_weaken (T := .VTypeBox (.VTypeBox A)) env hc.root q φ).mp
        (ih M hM (env.extend (T := .VTypeBox (.VTypeBox A)) (.free c) q) (hfin.insert hc _)
          (hnp.insert _ _) ?_)
      intro χ hχ
      rcases List.mem_cons.mp hχ with h₁ | h₂
      · subst h₁
        exact (sat_back_eta_extend hS env (.free c) hc q t).mpr hc₀
      · obtain ⟨χ', hχ', rfl⟩ := List.mem_map.mp h₂
        exact (sat_weaken (T := .VTypeBox (.VTypeBox A)) env hc.root q χ').mpr (hΔ χ' hχ')
  | @B_strongW Γ _ hS hW A a t c hc Δ φ pne p ihne ih =>
      -- As `B_strong`, with `backRet_existsW`'s carrier of possible objects.
      intro M hM w env hfin hnp hΔ
      obtain ⟨i, _⟩ := (OutLeg.sat_dia env .nec _).mp (ihne M hM env hfin hnp hΔ)
      obtain ⟨c₀, hc₀⟩ := M.backRet_existsW hS hW ⟨i⟩ (interp env t)
      let q : M.frame.Dom (.VTypeBox (.VTypeDia A)) w := c₀
      refine (sat_weaken (T := .VTypeBox (.VTypeDia A)) env hc.root q φ).mp
        (ih M hM (env.extend (T := .VTypeBox (.VTypeDia A)) (.free c) q) (hfin.insert hc _)
          (hnp.insert _ _) ?_)
      intro χ hχ
      rcases List.mem_cons.mp hχ with h₁ | h₂
      · subst h₁
        exact (sat_back_eta_extendL hS (.necW hW) env (.free c) hc q t).mpr hc₀
      · obtain ⟨χ', hχ', rfl⟩ := List.mem_map.mp h₂
        exact (sat_weaken (T := .VTypeBox (.VTypeDia A)) env hc.root q χ').mpr (hΔ χ' hχ')
  | @ret_new Γ _ hS hB O A Φ c hc Δ φ pd p ihd ih =>
      -- Some arrow of the leg reaches an object with `Φ`; weak B brings it home as some value,
      -- which interprets the eigenvariable.
      intro M hM w env hfin hnp hΔ
      obtain ⟨i, e, hΦ⟩ := (OutLeg.sat_dia env O _).mp (ihd M hM env hfin hnp hΔ)
      obtain ⟨r⟩ := M.frame.symm hB (O.acc env i).2.down
      set o := M.necEval (e : M.frame.Nec A (O.acc env i).1) ⟨w, ⟨r⟩⟩
      refine (sat_weaken (T := A) env hc.root o φ).mp
        (ih M hM (env.extend (T := A) (.free c) o) (hfin.insert hc _) (hnp.insert _ _) ?_)
      intro χ hχ
      rcases List.mem_cons.mp hχ with h₁ | h₂
      · subst h₁
        exact sat_ret_fresh env hS O Φ c hc o i e hΦ r (M.Ind_refl _)
      · obtain ⟨χ', hχ', rfl⟩ := List.mem_map.mp h₂
        exact (sat_weaken (T := A) env hc.root o χ').mpr (hΔ χ' hχ')
  | @ret_extSH Γ _ hS O S B Zs hZs ws a t us Φ c hc Δ φ pr p ihr ih =>
      -- The companion's value along the same way home interprets the eigenvariable.
      intro M hM w env hfin hnp hΔ
      obtain ⟨i, d, ⟨b, hΦ⟩, r, hr, hh⟩ :=
        (OutLeg.sat_retSH hS env O S t _).mp (ihr M hM env hfin hnp hΔ)
      refine (sat_weaken (T := B) env hc.root
        (M.necEval (b : M.frame.Nec B (O.acc env i).1) ⟨w, ⟨r⟩⟩)
        φ).mp (ih M hM (env.extend (T := B) (.free c) _) (hfin.insert hc _) (hnp.insert _ _) ?_)
      intro χ hχ
      rcases List.mem_cons.mp hχ with h₁ | h₂
      · subst h₁
        exact sat_ret_extS env hnp hS O t Φ c hc i d b hΦ r hr hh
      · obtain ⟨χ', hχ', rfl⟩ := List.mem_map.mp h₂
        exact (sat_weaken (T := B) env hc.root _ χ').mpr (hΔ χ' hχ')
  | @ret_compSH Γ _ hS O S A cs h p h' Zs hZs ws a t us Φ c hc Δ φ pr pf ihr ih =>
      -- The companion's reading along the same way home interprets the eigenvariable.
      intro M hM w env hfin hnp hΔ
      obtain ⟨i, d, hΦ, r, hr, hh⟩ :=
        (OutLeg.sat_retSH hS env O _ t _).mp (ihr M hM env hfin hnp hΔ)
      obtain ⟨o, ho⟩ := sat_ret_compS env hnp hS O S p h' t Φ c hc i d hΦ r hr hh
      refine (sat_weaken env hc.root o φ).mp
        (ih M hM (env.extend (.free c) o) (hfin.insert hc _) (hnp.insert _ _) ?_)
      intro χ hχ
      rcases List.mem_cons.mp hχ with h₁ | h₂
      · subst h₁
        exact ho
      · obtain ⟨χ', hχ', rfl⟩ := List.mem_map.mp h₂
        exact (sat_weaken env hc.root _ χ').mpr (hΔ χ' hχ')
  | @ret_mapH Γ _ Δ hS O S T F Zs hZs ws a y us Φ p ih =>
      intro M hM w env hfin hnp hΔ
      exact sat_ret_map env hnp hM.toIndCongr hS O F y Φ (ih M hM env hfin hnp hΔ)
  | @ret_mapDH Γ _ Δ hS O C X Z cs hcs b h Zs hZs ws a y us Φ p ih =>
      intro M hM w env hfin hnp hΔ
      exact sat_ret_mapD env hnp hM hS O h y Φ (ih M hM env hfin hnp hΔ)
  | @ret_counit Γ _ Δ hS O A a t ψ p ih =>
      intro M hM w env hfin hnp hΔ
      exact (sat_holeRead hnp env t ψ).mpr
        (sat_ret_counit env hM hS O t ψ (ih M hM env hfin hnp hΔ))
  | @ret_counitC Γ _ Δ hS O A C a y c₀ bd c t ψ pr pb ihr ihb =>
      intro M hM w env hfin hnp hΔ
      exact (sat_holeRead hnp env _ ψ).mpr (sat_ret_counitC env hM hS O y bd t ψ
        (ihr M hM env hfin hnp hΔ) (ihb M hM env hfin hnp hΔ))
  | @ret_unitCH Γ _ Δ hS O C A co ho Zs hZs ws c y us Ψ a₀ sb cs h θ p q ihp ihq =>
      intro M hM w env hfin hnp hΔ
      exact sat_ret_unitC env hM hS O co ho y Ψ sb cs h θ (ihp M hM env hfin hnp hΔ)
        ((sat_holeRead hnp env _ θ).mp (ihq M hM env hfin hnp hΔ))
  | @ret_unitWCH Γ _ Δ hS x hx C A X co ho Zs hZs ws c y us Ψ a₀ sb b₀ u cs h θ p q ihp
      ihq =>
      intro M hM w env hfin hnp hΔ
      exact sat_ret_unitWC env hM hS hx co ho y Ψ sb u cs h θ (ihp M hM env hfin hnp hΔ)
        ((sat_holeRead hnp env _ θ).mp (ihq M hM env hfin hnp hΔ))
  | @ret_unitDCH Γ _ Δ hS O C X A co ho Zs hZs ws c y us Ψ a₀ sb cs h θ p q ihp ihq =>
      intro M hM w env hfin hnp hΔ
      exact sat_ret_unitDC env hM hS O co ho y Ψ sb cs h θ (ihp M hM env hfin hnp hΔ)
        ((sat_holeRead hnp env _ θ).mp (ihq M hM env hfin hnp hΔ))
  | @ret_unitWDCH Γ _ Δ hS x hx C Xe A X co ho Zs hZs ws c y us Ψ a₀ sb b₀ u cs h θ p q ihp
      ihq =>
      intro M hM w env hfin hnp hΔ
      exact sat_ret_unitWDC env hM hS hx co ho y Ψ sb u cs h θ (ihp M hM env hfin hnp hΔ)
        ((sat_holeRead hnp env _ θ).mp (ihq M hM env hfin hnp hΔ))
  | @ret_counitD Γ _ Δ hS C X c y ψ p ih =>
      intro M hM w env hfin hnp hΔ
      exact (sat_holeRead hnp env y ψ).mpr (sat_ret_counitD env hM hS y ψ (ih M hM env hfin hnp hΔ))
  | @ret_forgetW Γ _ Δ hS O S Z Zs hZs b pw ws a t c u us Φ p ih =>
      intro M hM w env hfin hnp hΔ
      obtain ⟨i, e, hΦ, r, hr, hh, _⟩ :=
        (OutLeg.sat_retSH hS env O S t Φ).mp (ih M hM env hfin hnp hΔ)
      exact (OutLeg.sat_retSH hS env O S t Φ).mpr ⟨i, e, hΦ, r, hr, hh⟩
  | @ret_homeN Γ _ hS O S Z C Zs hZs ws a t us Φ z hz hW b wz c₀ u c₁ t' c hc Δ φ pr pb p ihr
      ihb ih =>
      -- The named witness's content along the way home interprets the eigenvariable.
      intro M hM w env hfin hnp hΔ
      obtain ⟨o, ho⟩ := sat_ret_homeN env hS O hZs ws t us Φ hz hW wz u t' c hc
        (ihr M hM env hfin hnp hΔ) (ihb M hM env hfin hnp hΔ)
      refine (sat_weaken env hc.root o φ).mp
        (ih M hM (env.extend (.free c) o) (hfin.insert hc _) (hnp.insert _ _) ?_)
      intro χ hχ
      rcases List.mem_cons.mp hχ with h₁ | h₂
      · subst h₁
        exact ho
      · obtain ⟨χ', hχ', rfl⟩ := List.mem_map.mp h₂
        exact (sat_weaken env hc.root _ χ').mpr (hΔ χ' hχ')
  | @ret_counitN Γ _ Δ hS hW O A Z C Zs hZs z hz b wz ws a y cz c us c₀ u ct t ψ pr pb ihr ihb =>
      intro M hM w env hfin hnp hΔ
      exact (sat_holeRead hnp env _ ψ).mpr (sat_ret_counitN env hM hS hW O hZs hz wz ws y c us
        u t ψ (ihr M hM env hfin hnp hΔ) (ihb M hM env hfin hnp hΔ))
  | @ret_monoSH Γ _ Δ hS O S Zs hZs ws a t us Φ Φ' p q ihp ihq =>
      intro M hM w env hfin hnp hΔ
      exact sat_ret_mono env hS O t Φ Φ' (ihp M hM env hfin hnp hΔ) (ihq M hM env hfin hnp hΔ)
  | @ret_diaS Γ _ Δ hS O S a t Φ p ih =>
      intro M hM w env hfin hnp hΔ
      exact sat_ret_dia env hS O t Φ (ih M hM env hfin hnp hΔ)
  | @ret_eqSH Γ _ Δ hS O S Zs hZs ws a t t' us Φ p q ihp ihq =>
      intro M hM w env hfin hnp hΔ
      exact sat_ret_eqS env hS O t t' Φ (ihp M hM env hfin hnp hΔ) (ihq M hM env hfin hnp hΔ)
  | @ret_hereCH Γ _ Δ hS hT A Zs hZs ws us a₀ sb cs h Φ pl p ihl ih =>
      intro M hM w env hfin hnp hΔ
      exact sat_ret_hereC env hnp hS hT sb cs h Φ (ihl M hM env hfin hnp hΔ)
        (ih M hM env hfin hnp hΔ)
  | @ret_hereWCH Γ _ Δ hS hT A Y Zs hZs ws us a₀ sb cs h b pt c u Φ pl ph p ihl ihh ih =>
      intro M hM w env hfin hnp hΔ
      exact sat_ret_hereWC env hnp hS hT sb cs h pt u Φ (ihl M hM env hfin hnp hΔ)
        (ihh M hM env hfin hnp hΔ) (ih M hM env hfin hnp hΔ)
  | @ret_hereXC Γ _ Δ hS hT x hx X A a₁ bd a' t₀ a₀ sb cs h χ ph p ihh ih =>
      intro M hM w env hfin hnp hΔ
      exact sat_ret_hereXC env hnp hfin hM hS hT x hx bd t₀ sb cs h χ
        (ihh M hM env hfin hnp hΔ) (ih M hM env hfin hnp hΔ)
  | @ret_hereXWC Γ _ Δ hS hT x hx X A Y a₁ bd a' t₀ a₀ sb cs h b pt c u χ ph php p ihh ihp ih =>
      intro M hM w env hfin hnp hΔ
      exact sat_ret_hereXWC env hnp hfin hM hS hT x hx bd t₀ sb cs h pt u χ
        (ihh M hM env hfin hnp hΔ) (ihp M hM env hfin hnp hΔ) (ih M hM env hfin hnp hΔ)
  | @back_realW Γ _ Δ hS hT z hz hW C c₀ u a t pb ihb =>
      intro M hM w env hfin hnp hΔ
      exact sat_back_realW env hS hT z hz hW u t (ihb M hM env hfin hnp hΔ)
  | @back_hereW Γ _ Δ hS hT z hz hW A a₀ u a t a' t₀ φ pb ph pφ ihb ihh ihφ =>
      intro M hM w env hfin hnp hΔ
      exact sat_back_hereW env hnp hfin hM hS hT z hz hW u t t₀ φ (ihb M hM env hfin hnp hΔ)
        (ihh M hM env hfin hnp hΔ) (ihφ M hM env hfin hnp hΔ)
  | @back_hereX Γ _ Δ hS hT y hy A a₀ bd a t a' t₀ φ pb ph pφ ihb ihh ihφ =>
      intro M hM w env hfin hnp hΔ
      exact sat_back_hereX env hnp hfin hM hS hT y hy bd t t₀ φ (ihb M hM env hfin hnp hΔ)
        (ihh M hM env hfin hnp hΔ) (ihφ M hM env hfin hnp hΔ)
  | @ret_bridge Γ _ Δ hS O A a₀ bd a t Φ pb pd ihb ihd =>
      intro M hM w env hfin hnp hΔ
      exact sat_ret_bridge env hS O bd t Φ (ihb M hM env hfin hnp hΔ)
        (ihd M hM env hfin hnp hΔ)

end Model

end V12M
