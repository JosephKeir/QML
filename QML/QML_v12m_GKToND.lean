import QML.QML_v12m_GKFromND

/-!
# QML v12m — GK into natural deduction, and the equivalence at K

⭐`GK.toND`: a GK derivation of `Δ ⇒ Θ` gives an ND proof of `⊥` from `Δ` and the negations of
`Θ`, in every system (GK's rules are K's).  Left rules discharge their new hypotheses from the old
ones; right rules work by contradiction; `diaL` is `K_dia` with the negated conclusions as `□_x`
hypotheses, then `dia_bot`.

⭐`GK.provable_iff_der`: over a presented context, in K, a sequent is provable in natural
deduction exactly when it has a **cut-free** GK derivation — **cut elimination** for the ND
system, through GK (`docs/v12-metatheory-todo.md`, item 4).
-/

namespace V12M

variable [ModalSys] {σ : Signature}

/-! ## Natural deduction, at the level of provability -/

namespace NDP

variable {Γ : Ctx}

theorem lk {L : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (h : φ ∈ L) : Provable L φ := ⟨Proof.lookup h⟩

theorem sub {L L' : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (h : L ⊆ L') (p : Provable L φ) :
    Provable L' φ :=
  p.map (Proof.ofSubset h)

theorem mp {L : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (p : Provable L (φ.imp ψ))
    (q : Provable L φ) : Provable L ψ :=
  let ⟨p⟩ := p; let ⟨q⟩ := q; ⟨.imp_elim p q⟩

theorem lam {L : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (p : Provable (φ :: L) ψ) :
    Provable L (φ.imp ψ) :=
  p.map .imp_intro

/-- Drop hypotheses that are provable. -/
theorem dis : ∀ {L M : List (WFF σ Γ 0)} {φ : WFF σ Γ 0}, Provable L φ →
    (∀ ℓ ∈ L, Provable M ℓ) → Provable M φ
  | [], _, _, p, _ => sub (fun _ h => absurd h List.not_mem_nil) p
  | _ :: _, _, _, p, h =>
      mp (dis (lam p) fun x hx => h x (List.mem_cons_of_mem _ hx)) (h _ List.mem_cons_self)

/-- Extra hypotheses that are provable. -/
theorem extra {E H : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (p : Provable (E ++ H) φ)
    (h : ∀ e ∈ E, Provable H e) : Provable H φ :=
  dis p fun ℓ hℓ => (List.mem_append.mp hℓ).elim (h ℓ) lk

theorem contra {L : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (h : φ.neg ∈ L) (p : Provable L φ) :
    Provable L .bot :=
  mp (lk h) p

theorem byContra {L : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (p : Provable (φ.neg :: L) .bot) :
    Provable L φ :=
  let ⟨p⟩ := p
  ⟨.or_elim (.lem φ) (Proof.lookup List.mem_cons_self) (.bot_elim _ p)⟩

/-- From `¬◇_x χ`, `□_x ¬χ`. -/
theorem boxx_neg (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    {L : List (WFF σ Γ 0)} {χ : WFF σ (Γ.diaIn x) 0} (h : (WFF.dia x hx χ).neg ∈ L) :
    Provable L (WFF.boxx x hx χ.neg) := by
  refine lam (contra (List.mem_cons_of_mem _ h) ?_)
  have q : Provable (σ := σ) (Γ := Γ.diaIn x) [χ.neg.neg] χ :=
    byContra (contra (List.mem_cons_of_mem _ List.mem_cons_self) (lk List.mem_cons_self))
  obtain ⟨q⟩ := q
  exact sub (fun _ h => by rw [List.mem_singleton.mp h]; exact List.mem_cons_self)
    ⟨Proof.K_dia (Δ₁ := []) (Δ₂ := []) x hx q⟩

end NDP

open NDP

namespace GK

/-- ⭐**GK into natural deduction**: `Δ ⇒ Θ` gives `Δ, ¬Θ ⊢ ⊥`. -/
theorem toND {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} (d : GK σ n Γ Δ Θ) :
    Provable (Δ ++ Θ.map WFF.neg) .bot := by
  induction d with
  | ax P hP h₁ h₂ =>
      exact contra (List.mem_append_right _ (List.mem_map_of_mem h₂))
        (lk (List.mem_append_left _ h₁))
  | botL h => exact lk (List.mem_append_left _ h)
  | topR h => exact contra (List.mem_append_right _ (List.mem_map_of_mem h)) ⟨.top_intro⟩
  | @andL _ _ Δ Θ φ ψ h _ ih =>
      refine extra (E := [φ, ψ]) (sub (by lsub) ih) fun e he => ?_
      rcases List.mem_cons.mp he with rfl | he
      · exact (lk (List.mem_append_left _ h)).map .and_elim_l
      · rw [List.mem_singleton.mp he]
        exact (lk (List.mem_append_left _ h)).map .and_elim_r
  | @andR _ _ Δ Θ φ ψ h _ _ ihp ihq =>
      refine contra (List.mem_append_right _ (List.mem_map_of_mem h)) ?_
      obtain ⟨p⟩ := byContra (sub (L' := φ.neg :: (Δ ++ Θ.map WFF.neg)) (by lsub) ihp)
      obtain ⟨q⟩ := byContra (sub (L' := ψ.neg :: (Δ ++ Θ.map WFF.neg)) (by lsub) ihq)
      exact ⟨.and_intro p q⟩
  | @orL _ _ Δ Θ φ ψ h _ _ ihp ihq =>
      obtain ⟨p⟩ := sub (L' := φ :: (Δ ++ Θ.map WFF.neg)) (by lsub) ihp
      obtain ⟨q⟩ := sub (L' := ψ :: (Δ ++ Θ.map WFF.neg)) (by lsub) ihq
      obtain ⟨r⟩ := lk (L := Δ ++ Θ.map WFF.neg) (List.mem_append_left _ h)
      exact ⟨.or_elim r p q⟩
  | @orR _ _ Δ Θ φ ψ h _ ih =>
      have hn : (φ.or ψ).neg ∈ Δ ++ Θ.map WFF.neg := List.mem_append_right _ (List.mem_map_of_mem h)
      refine extra (E := [φ.neg, ψ.neg]) (sub (by lsub) ih) fun e he => ?_
      rcases List.mem_cons.mp he with rfl | he
      · exact lam (contra (List.mem_cons_of_mem _ hn) ((lk List.mem_cons_self).map (.or_intro_l _)))
      · rw [List.mem_singleton.mp he]
        exact lam (contra (List.mem_cons_of_mem _ hn) ((lk List.mem_cons_self).map (.or_intro_r _)))
  | @impL _ _ Δ Θ φ ψ h _ _ ihp ihq =>
      refine extra (E := [ψ]) (sub (by lsub) ihq) fun e he => ?_
      rw [List.mem_singleton.mp he]
      exact mp (lk (List.mem_append_left _ h))
        (byContra (sub (L' := φ.neg :: (Δ ++ Θ.map WFF.neg)) (by lsub) ihp))
  | @impR _ _ Δ Θ φ ψ h _ ih =>
      have hn : (φ.imp ψ).neg ∈ Δ ++ Θ.map WFF.neg :=
        List.mem_append_right _ (List.mem_map_of_mem h)
      refine extra (E := [φ, ψ.neg]) (sub (by lsub) ih) fun e he => ?_
      rcases List.mem_cons.mp he with rfl | he
      · refine byContra (contra (List.mem_cons_of_mem _ hn) (lam ?_))
        exact (contra (List.mem_cons_of_mem _ List.mem_cons_self) (lk List.mem_cons_self)).map
          (.bot_elim _)
      · rw [List.mem_singleton.mp he]
        exact lam (contra (List.mem_cons_of_mem _ hn)
          (lam (lk (List.mem_cons_of_mem _ List.mem_cons_self))))
  | @allL _ _ _ Δ Θ T φ _ t h _ ih =>
      refine extra (E := [WFF.instantiate Ctx.NoSlots.slots t φ]) (sub (by lsub) ih)
        fun e he => ?_
      rw [List.mem_singleton.mp he]
      exact (lk (List.mem_append_left _ h)).map (.all_elim T t)
  | @allR _ _ _ Δ Θ u T hu φ h _ ih =>
      have e : (Θ.map (WFF.weaken hu.root T)).map WFF.neg =
          (Θ.map WFF.neg).map (WFF.weaken hu.root T) := by
        rw [List.map_map, List.map_map]; rfl
      rw [List.map_cons, e] at ih
      have ih' := byContra (sub (L' := φ.neg :: (Δ ++ Θ.map WFF.neg).map (WFF.weaken hu.root T))
        (by rw [List.map_append]; lsub) ih)
      exact contra (List.mem_append_right _ (List.mem_map_of_mem h)) (ih'.map (.all_intro u T hu))
  | @exL _ _ _ Δ Θ u T hu φ h _ ih =>
      have e : (Θ.map (WFF.weaken hu.root T)).map WFF.neg =
          (Θ.map WFF.neg).map (WFF.weaken hu.root T) := by
        rw [List.map_map, List.map_map]; rfl
      rw [e] at ih
      obtain ⟨q⟩ := sub (L' := φ :: (Δ ++ Θ.map WFF.neg).map (WFF.weaken hu.root T))
        (by rw [List.map_append]; lsub) ih
      obtain ⟨r⟩ := lk (L := Δ ++ Θ.map WFF.neg) (List.mem_append_left _ h)
      exact ⟨.ex_elim u T hu r q⟩
  | @exR _ _ _ Δ Θ T φ _ t h _ ih =>
      have hn : (WFF.ex T φ).neg ∈ Δ ++ Θ.map WFF.neg :=
        List.mem_append_right _ (List.mem_map_of_mem h)
      refine extra (E := [(WFF.instantiate Ctx.NoSlots.slots t φ).neg]) (sub (by lsub) ih)
        fun e he => ?_
      rw [List.mem_singleton.mp he]
      exact lam (contra (List.mem_cons_of_mem _ hn)
        ((lk List.mem_cons_self).map (.ex_intro T t)))
  | @ref _ _ Δ Θ t _ ih =>
      refine extra (E := [.eq t t]) (sub (by lsub) ih) fun e he => ?_
      rw [List.mem_singleton.mp he]
      exact ⟨.eq_intro t⟩
  | @repl _ _ _ Δ Θ P hP t s h₁ h₂ _ ih =>
      refine extra (E := [WFF.instantiate Ctx.NoSlots.slots s P]) (sub (by lsub) ih)
        fun e he => ?_
      rw [List.mem_singleton.mp he]
      obtain ⟨p⟩ := lk (L := Δ ++ Θ.map WFF.neg) (List.mem_append_left _ h₁)
      obtain ⟨q⟩ := lk (L := Δ ++ Θ.map WFF.neg) (List.mem_append_left _ h₂)
      exact ⟨.eq_elim t s p q⟩
  | @boxR _ Γ Δ Θ Δ₁ φ h₁ h₂ _ ih =>
      obtain ⟨p⟩ := byContra (sub (L' := φ.neg :: Δ₁) (by lsub) ih)
      refine contra (List.mem_append_right _ (List.mem_map_of_mem h₁))
        (sub (fun ψ hψ => ?_) ⟨Proof.K_box p⟩)
      obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hψ
      exact List.mem_append_left _ (h₂ χ hχ)
  | @diaL _ Γ Δ Θ x hx ψ Δ₁ Θ₁ h₁ h₂ h₃ _ ih =>
      obtain ⟨p⟩ := sub (L' := ψ :: (Θ₁.map WFF.neg ++
        Δ₁.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))) (by lsub) ih
      refine dis (L := .dia x hx ψ :: ((Θ₁.map WFF.neg).map (WFF.boxx x hx) ++
        Δ₁.map fun χ => WFF.box (Γ := Γ) χ)) ⟨.dia_bot x hx (Proof.K_dia x hx p)⟩
        fun ℓ hℓ => ?_
      rcases List.mem_cons.mp hℓ with rfl | hℓ
      · exact lk (List.mem_append_left _ h₁)
      rcases List.mem_append.mp hℓ with hℓ | hℓ
      · obtain ⟨χ', hχ', rfl⟩ := List.mem_map.mp hℓ
        obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hχ'
        exact boxx_neg x hx (List.mem_append_right _ (List.mem_map_of_mem (h₃ χ hχ)))
      · obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hℓ
        exact lk (List.mem_append_left _ (h₂ χ hχ))

/-- ⭐**GK and natural deduction prove the same sequents**, over a presented context, in K: a
    sequent is ND-provable exactly when it has a cut-free GK derivation. -/
theorem provable_iff_der [ModalSys.IsK] {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)}
    {φ : WFF σ Γ 0} : Provable Δ φ ↔ Der σ Γ Δ φ := by
  refine ⟨fun ⟨p⟩ => Der.ofProof p, fun ⟨n, d⟩ => byContra (sub (by lsub) (toND d))⟩

end GK

end V12M
