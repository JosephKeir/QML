import QML.QML_v12m_GKNRelabel
import QML.QML_v12m_GKSubst
import QML.QML_v12m_GKEq
import QML.QML_v12m_GKFromND

/-!
# QML v12m — `GK` embeds in `GKN`

Every `GK` derivation of K or KD (`Opt` off) is a `GKN` derivation at a node of a tree (docs
§12.49, "the embedding"): `GK`'s rules are `GKN`'s at the node, and a modal rule makes a vacant
child, propagates the boxed hypotheses (and, for `◇_x`, the `◇_x` conclusions) into it, and goes
on there.  `GK`'s eigenvariables are fresh only for their own context, so each is renamed to a
tree-fresh name by `GK.subst` first; hence the induction is on the height.

* `Tree.presentedAt`: every node context is presented (`GK.subst`'s target).
* `GKN.boxL_list`, `GKN.diaR_list`: propagating a list.
* ⭐`GK.toGKN`, ⭐`GK.toGKN_root`.
-/

namespace V12M

set_option linter.unusedSectionVars false

variable [ModalSys]

/-! ## Presented node contexts -/

/-- Inserting fresh free roots, with distinct names, presents the extension. -/
def Ctx.Presented.inserts {Γ : Ctx} (h : Γ.Presented) :
    ∀ L : List (Root × VarType), L.Pairwise (fun b b' => b.1 ≠ b'.1) →
      (∀ b ∈ L, Γ.RootFresh b.1) → (∀ b ∈ L, ∃ u, b.1 = .free u) → (Γ.inserts L).Presented
  | [], _, _, _ => h
  | (.free u, T) :: L, hp, hf, hfr =>
      have hp' := (List.pairwise_cons.mp hp)
      (Ctx.Presented.inserts h L hp'.2 (fun b hb => hf b (List.mem_cons_of_mem _ hb))
          (fun b hb => hfr b (List.mem_cons_of_mem _ hb))).insertFree u
        ((hf _ List.mem_cons_self).inserts L fun b hb => (hp'.1 b hb).symm) T
  | (.bnd n, T) :: L, _, _, hfr => False.elim (by
      obtain ⟨u, hu⟩ := hfr _ List.mem_cons_self
      cases hu)

namespace GKN

namespace Tree

variable {D : Tree}

/-- The edge's view of a presented context is presented. -/
def presentedView (τ : Lab) {Γ : Ctx} (h : Γ.Presented) : (D.view τ Γ).Presented := by
  unfold view
  split
  · exact ⟨.diaIn h.expr _, h.fresh, congrArg (fun Δ => Ctx.diaIn Δ _) h.denote_eq⟩
  · exact ⟨.boxIn h.expr, h.fresh, congrArg Ctx.boxIn h.denote_eq⟩

/-- ⭐**Every node context is presented**, under the invariant. -/
noncomputable def presentedAt {Γ₀ : Ctx} (h0 : Γ₀.Presented) (h : D.OK Γ₀) :
    ∀ τ, (D.ctxAt Γ₀ τ).Presented
  | [] => by
      simp only [ctxAt]
      exact h0.inserts _ (birthsAt_pairwise h _) (fun b hb => h.fresh _ (mem_birthsAt.mp hb))
        (fun b hb => h.free _ (mem_birthsAt.mp hb))
  | k :: τ => by
      simp only [ctxAt]
      refine (presentedView (k :: τ) (presentedAt h0 h τ)).inserts _ (birthsAt_pairwise h _)
        (fun b hb => ?_) (fun b hb => h.free _ (mem_birthsAt.mp hb))
      have hb' := mem_birthsAt.mp hb
      have hfr : (D.ctxAt Γ₀ τ).RootFresh b.1 := by
        refine fresh_branch (h.fresh _ hb') τ fun b' hb'' hs he => ?_
        have := h.uniq b' hb'' _ hb' he
        rw [this] at hs
        have := hs.length_le
        simp at this
      unfold view
      split
      · exact hfr.diaIn _
      · exact hfr.boxIn

end Tree

variable {σ : Signature}

/-! ## Propagating lists -/

/-- ⭐`boxL` over a list: boxed hypotheses at `τ` put their bodies at the child `k :: τ`. -/
theorem boxL_list {Γ₀ : Ctx} {D : Tree} {τ : Lab} {k : ℕ} {e : EdgeKind}
    (he : D.edge (k :: τ) = some e) (hcL : (D.ctxAt Γ₀ τ).boxIn.Le (D.ctxAt Γ₀ (k :: τ)))
    {A : Ctx} (a : A.Le (D.ctxAt Γ₀ τ).boxIn) {Θ : Seq σ Γ₀ D} :
    ∀ (L : List (WFF σ A 0)) {Δ : Seq σ Γ₀ D},
      (∀ χ ∈ L, (⟨τ, WFF.box (Γ := D.ctxAt Γ₀ τ) (WFF.mono a χ)⟩ : LF σ Γ₀ D) ∈ Δ) →
      (∀ Δ'' : Seq σ Γ₀ D, Δ ⊆ Δ'' →
        (∀ χ ∈ L, (⟨k :: τ, WFF.mono (a.trans hcL) χ⟩ : LF σ Γ₀ D) ∈ Δ'') →
          ∃ m, GKN σ Γ₀ m D Δ'' Θ) →
      ∃ m, GKN σ Γ₀ m D Δ Θ
  | [], Δ, _, hk => hk Δ (List.Subset.refl _) fun _ h => by simp at h
  | χ :: L, Δ, hb, hk => by
      obtain ⟨m, d⟩ := boxL_list he hcL a L (Δ := ⟨k :: τ, WFF.mono hcL (WFF.mono a χ)⟩ :: Δ)
        (fun χ' hχ' => List.mem_cons_of_mem _ (hb χ' (List.mem_cons_of_mem _ hχ')))
        (fun Δ'' hs hL => hk Δ'' (fun x hx => hs (List.mem_cons_of_mem _ hx)) fun χ' hχ' => by
          rcases List.mem_cons.mp hχ' with rfl | hχ'
          · have := hs List.mem_cons_self
            rwa [WFF.mono_mono] at this
          · exact hL χ' hχ')
      exact ⟨m + 1, .boxL τ k e he hcL (hb χ List.mem_cons_self) d⟩

/-- ⭐`diaR` over a list: `◇_x` conclusions at `τ` put their bodies at the `◇_x`-child
    `k :: τ`. -/
theorem diaR_list {Γ₀ : Ctx} {D : Tree} {τ : Lab} {k : ℕ} {x : VarSymb}
    (hx : ∃ X, (D.ctxAt Γ₀ τ).ref x = some (.VTypeDia X))
    (he : D.edge (k :: τ) = some (.dia x))
    (hcL : ((D.ctxAt Γ₀ τ).diaIn x).Le (D.ctxAt Γ₀ (k :: τ)))
    {A : Ctx} (a : A.Le ((D.ctxAt Γ₀ τ).diaIn x)) {Δ : Seq σ Γ₀ D} :
    ∀ (L : List (WFF σ A 0)) {Θ : Seq σ Γ₀ D},
      (∀ θ ∈ L, (⟨τ, .dia x hx (WFF.mono a θ)⟩ : LF σ Γ₀ D) ∈ Θ) →
      (∀ Θ'' : Seq σ Γ₀ D, Θ ⊆ Θ'' →
        (∀ θ ∈ L, (⟨k :: τ, WFF.mono (a.trans hcL) θ⟩ : LF σ Γ₀ D) ∈ Θ'') →
          ∃ m, GKN σ Γ₀ m D Δ Θ'') →
      ∃ m, GKN σ Γ₀ m D Δ Θ
  | [], Θ, _, hk => hk Θ (List.Subset.refl _) fun _ h => by simp at h
  | θ :: L, Θ, hb, hk => by
      obtain ⟨m, d⟩ := diaR_list hx he hcL a L (Θ := ⟨k :: τ, WFF.mono hcL (WFF.mono a θ)⟩ :: Θ)
        (fun θ' hθ' => List.mem_cons_of_mem _ (hb θ' (List.mem_cons_of_mem _ hθ')))
        (fun Θ'' hs hL => hk Θ'' (fun y hy => hs (List.mem_cons_of_mem _ hy)) fun θ' hθ' => by
          rcases List.mem_cons.mp hθ' with rfl | hθ'
          · have := hs List.mem_cons_self
            rwa [WFF.mono_mono] at this
          · exact hL θ' hθ')
      exact ⟨m + 1, .diaR τ k x hx he hcL (hb θ List.mem_cons_self) d⟩

theorem mem_cons_of {α : Type*} {P : α → Prop} {a : α} {L : List α} (h0 : P a)
    (h : ∀ x ∈ L, P x) : ∀ x ∈ a :: L, P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h0
  · exact h x hx

end GKN

namespace GKN

/-- A tree-fresh name exists. -/
theorem exists_treeFresh {Γ₀ : Ctx} [Γ₀.Presented] (D : Tree) : ∃ u, D.Fresh Γ₀ (.free u) := by
  let f : Lab × Root × VarType → ℕ := fun b => match b.2.1 with
    | .free v => v + 1
    | .bnd _ => 0
  refine ⟨Ctx.Presented.bound Γ₀ + (D.births.map f).sum,
    ⟨Ctx.Presented.fresh_bound _ (Nat.le_add_right _ _), fun b hb he => ?_⟩⟩
  have hle : f b ≤ (D.births.map f).sum := List.le_sum_of_mem (List.mem_map_of_mem hb)
  have hf : f b = Ctx.Presented.bound Γ₀ + (D.births.map f).sum + 1 := by
    change (match b.2.1 with | .free v => v + 1 | .bnd _ => 0) = _
    rw [he]
  omega

end GKN

open GKN

variable {σ : Signature}

/-- ⭐**`GK` embeds in `GKN`**, K and KD with `Opt` off: a `GK` derivation over a context inside
    a node's gives a `GKN` derivation with its sequent at that node. -/
theorem GK.toGKN [ModalSys.GKSys] (hF : ModalSys.Four = false) {Γ₀ : Ctx} [h0 : Γ₀.Presented] :
    ∀ (n : ℕ) {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)}, GK σ n Γ Δ Θ →
      ∀ {D : Tree}, D.OK Γ₀ → ∀ {τ : Lab} (h : Γ.Le (D.ctxAt Γ₀ τ)) {Δ' Θ' : Seq σ Γ₀ D},
        (∀ φ ∈ Δ, (⟨τ, WFF.mono h φ⟩ : LF σ Γ₀ D) ∈ Δ') →
        (∀ φ ∈ Θ, (⟨τ, WFF.mono h φ⟩ : LF σ Γ₀ D) ∈ Θ') → ∃ m, GKN σ Γ₀ m D Δ' Θ' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro Γ Δ Θ p D hok τ h Δ' Θ' hΔ hΘ
  have hs0 : Γ₀.SlotsFrom 0 := Ctx.NoSlots.slots
  have hsτ := Tree.ctxAt_slots hs0 hok τ
  cases p with
  | ax P hP h₁ h₂ => exact ⟨0, .ax τ _ (isAtom_mono hP) (hΔ _ h₁) (hΘ _ h₂)⟩
  | botL h₁ => exact ⟨0, .botL τ (hΔ _ h₁)⟩
  | topR h₁ => exact ⟨0, .topR τ (hΘ _ h₁)⟩
  | @andL n' _ _ _ φ ψ h₁ q =>
      obtain ⟨m, d⟩ := IH n' (Nat.lt_succ_self _) q hok h
        (Δ' := ⟨τ, WFF.mono h φ⟩ :: ⟨τ, WFF.mono h ψ⟩ :: Δ')
        (mem_cons_of List.mem_cons_self (mem_cons_of (List.mem_cons_of_mem _ List.mem_cons_self)
          fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hΔ x hx)))) hΘ
      exact ⟨m + 1, .andL τ (hΔ _ h₁) d⟩
  | @andR n' _ _ _ φ ψ h₁ q₁ q₂ =>
      obtain ⟨m₁, d₁⟩ := IH n' (Nat.lt_succ_self _) q₁ hok h (Θ' := ⟨τ, WFF.mono h φ⟩ :: Θ') hΔ
        (mem_cons_of List.mem_cons_self fun x hx => List.mem_cons_of_mem _ (hΘ x hx))
      obtain ⟨m₂, d₂⟩ := IH n' (Nat.lt_succ_self _) q₂ hok h (Θ' := ⟨τ, WFF.mono h ψ⟩ :: Θ') hΔ
        (mem_cons_of List.mem_cons_self fun x hx => List.mem_cons_of_mem _ (hΘ x hx))
      exact ⟨max m₁ m₂ + 1, .andR τ (hΘ _ h₁) (d₁.mono_height (le_max_left _ _))
        (d₂.mono_height (le_max_right _ _))⟩
  | @orL n' _ _ _ φ ψ h₁ q₁ q₂ =>
      obtain ⟨m₁, d₁⟩ := IH n' (Nat.lt_succ_self _) q₁ hok h (Δ' := ⟨τ, WFF.mono h φ⟩ :: Δ')
        (mem_cons_of List.mem_cons_self fun x hx => List.mem_cons_of_mem _ (hΔ x hx)) hΘ
      obtain ⟨m₂, d₂⟩ := IH n' (Nat.lt_succ_self _) q₂ hok h (Δ' := ⟨τ, WFF.mono h ψ⟩ :: Δ')
        (mem_cons_of List.mem_cons_self fun x hx => List.mem_cons_of_mem _ (hΔ x hx)) hΘ
      exact ⟨max m₁ m₂ + 1, .orL τ (hΔ _ h₁) (d₁.mono_height (le_max_left _ _))
        (d₂.mono_height (le_max_right _ _))⟩
  | @orR n' _ _ _ φ ψ h₁ q =>
      obtain ⟨m, d⟩ := IH n' (Nat.lt_succ_self _) q hok h
        (Θ' := ⟨τ, WFF.mono h φ⟩ :: ⟨τ, WFF.mono h ψ⟩ :: Θ') hΔ
        (mem_cons_of List.mem_cons_self (mem_cons_of (List.mem_cons_of_mem _ List.mem_cons_self)
          fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hΘ x hx))))
      exact ⟨m + 1, .orR τ (hΘ _ h₁) d⟩
  | @impL n' _ _ _ φ ψ h₁ q₁ q₂ =>
      obtain ⟨m₁, d₁⟩ := IH n' (Nat.lt_succ_self _) q₁ hok h (Θ' := ⟨τ, WFF.mono h φ⟩ :: Θ') hΔ
        (mem_cons_of List.mem_cons_self fun x hx => List.mem_cons_of_mem _ (hΘ x hx))
      obtain ⟨m₂, d₂⟩ := IH n' (Nat.lt_succ_self _) q₂ hok h (Δ' := ⟨τ, WFF.mono h ψ⟩ :: Δ')
        (mem_cons_of List.mem_cons_self fun x hx => List.mem_cons_of_mem _ (hΔ x hx)) hΘ
      exact ⟨max m₁ m₂ + 1, .impL τ (hΔ _ h₁) (d₁.mono_height (le_max_left _ _))
        (d₂.mono_height (le_max_right _ _))⟩
  | @impR n' _ _ _ φ ψ h₁ q =>
      obtain ⟨m, d⟩ := IH n' (Nat.lt_succ_self _) q hok h (Δ' := ⟨τ, WFF.mono h φ⟩ :: Δ')
        (Θ' := ⟨τ, WFF.mono h ψ⟩ :: Θ')
        (mem_cons_of List.mem_cons_self fun x hx => List.mem_cons_of_mem _ (hΔ x hx))
        (mem_cons_of List.mem_cons_self fun x hx => List.mem_cons_of_mem _ (hΘ x hx))
      exact ⟨m + 1, .impR τ (hΘ _ h₁) d⟩
  | @allL n' _ _ _ _ T φ a t h₁ q =>
      obtain ⟨m, d⟩ := IH n' (Nat.lt_succ_self _) q hok h
        (Δ' := ⟨τ, WFF.instantiate hsτ (Term.mono h t) (WFF.mono (h.insert (.bnd 0) T) φ)⟩ :: Δ')
        (mem_cons_of (by rw [WFF.mono_instantiate h _ hsτ t φ]; exact List.mem_cons_self)
          fun x hx => List.mem_cons_of_mem _ (hΔ x hx)) hΘ
      exact ⟨m + 1, .allL τ hsτ T (Term.mono h t) (hΔ _ h₁) d⟩
  | @exR n' _ _ _ _ T φ a t h₁ q =>
      obtain ⟨m, d⟩ := IH n' (Nat.lt_succ_self _) q hok h
        (Θ' := ⟨τ, WFF.instantiate hsτ (Term.mono h t) (WFF.mono (h.insert (.bnd 0) T) φ)⟩ :: Θ')
        hΔ (mem_cons_of (by rw [WFF.mono_instantiate h _ hsτ t φ]; exact List.mem_cons_self)
          fun x hx => List.mem_cons_of_mem _ (hΘ x hx))
      exact ⟨m + 1, .exR τ hsτ T (Term.mono h t) (hΘ _ h₁) d⟩
  | @ref n' _ _ _ t q =>
      obtain ⟨m, d⟩ := IH n' (Nat.lt_succ_self _) q hok h
        (Δ' := ⟨τ, WFF.mono h (.eq t t)⟩ :: Δ')
        (mem_cons_of List.mem_cons_self fun x hx => List.mem_cons_of_mem _ (hΔ x hx)) hΘ
      exact ⟨m + 1, .ref τ (Term.mono h t) d⟩
  | @repl n' _ _ _ _ P hP t s h₁ h₂ q =>
      have hp₂ := hΔ _ h₂
      rw [WFF.mono_instantiate h _ hsτ t P] at hp₂
      obtain ⟨m, d⟩ := IH n' (Nat.lt_succ_self _) q hok h
        (Δ' := ⟨τ, WFF.instantiate hsτ (Term.mono h s)
          (WFF.mono (h.insert (.bnd 0) .Var) P)⟩ :: Δ')
        (mem_cons_of (by rw [WFF.mono_instantiate h _ hsτ s P]; exact List.mem_cons_self)
          fun x hx => List.mem_cons_of_mem _ (hΔ x hx)) hΘ
      exact ⟨m + 1, .repl τ hsτ (isAtom_mono hP) (Term.mono h t) (Term.mono h s)
        (hΔ _ h₁) hp₂ d⟩
  | optL hO => exact absurd hO (by rw [ModalSys.NoOpt.noOpt]; decide)
  | reopenR hO => exact absurd hO (by rw [ModalSys.NoOpt.noOpt]; decide)
  | TL hT => exact (ModalSys.NoT.absurd hT).elim
  | diaT hT => exact (ModalSys.NoT.absurd hT).elim
  | @allR n' _ hns _ _ u T hu φ h₁ q =>
      obtain ⟨u', hu'⟩ := exists_treeFresh (Γ₀ := Γ₀) D
      have hsΓ : Γ.SlotsFrom 0 := hns.slots
      have hfτ := hu'.at τ
      have hok₁ := hok.addBirth hu' τ T
      let θ₀ : Subst σ (D.ctxAt Γ₀ τ) := Subst.idRen _
      have hθ₀ : Subst.Ok Γ θ₀ := Subst.ok_idRen.restrict h
      have hc₀ : Subst.Coh id Γ θ₀ := Subst.coh_idRen.restrict h
      haveI : ((D.ctxAt Γ₀ τ).insert (.free u') T).Presented :=
        (Tree.presentedAt h0 hok τ).insertFree u' hfτ T
      have q' := q.subst (θ₀.rename u u' T hfτ.root) (Subst.ok_rename hθ₀ T hfτ.root)
        (Subst.coh_rename hθ₀ hc₀ hu T hfτ.root) (hsΓ.insertFree u T)
      have hren : ∀ ψ : WFF σ Γ 0, WFF.subst id θ₀ hθ₀ hc₀ hsΓ hsτ ψ = WFF.mono h ψ :=
        fun ψ => WFF.subst_ren h θ₀ hθ₀ hc₀ hsΓ hsτ (fun v _ _ => Subst.at_idRen v) ψ
          (fun _ _ _ _ => rfl)
      set φ'' := WFF.subst (VarSymb.renameIdx id u u') (θ₀.rename u u' T hfτ.root)
        (Subst.ok_rename hθ₀ T hfτ.root) (Subst.coh_rename hθ₀ hc₀ hu T hfτ.root)
        (hsΓ.insertFree u T) (hsτ.insertFree u' T) φ
      have hk := Tree.ctxAt_addBirth hu' τ T
      have hleI := Tree.insert_le_addBirth (D := D) (Γ₀ := Γ₀) τ (.free u') T
      have hside : ∀ (L : List (WFF σ Γ 0)) (L' : Seq σ Γ₀ D),
          (∀ ψ ∈ L, (⟨τ, WFF.mono h ψ⟩ : LF σ Γ₀ D) ∈ L') →
          ∀ x ∈ (L.map (WFF.weaken hu.root T)).map (WFF.subst (VarSymb.renameIdx id u u')
            (θ₀.rename u u' T hfτ.root) (Subst.ok_rename hθ₀ T hfτ.root)
            (Subst.coh_rename hθ₀ hc₀ hu T hfτ.root) (hsΓ.insertFree u T) Ctx.NoSlots.slots),
            (⟨τ, WFF.mono hleI x⟩ : LF σ Γ₀ (D.addBirth τ (.free u') T)) ∈ Seq.mono hk L' := by
        intro L L' hL x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hy
        rw [WFF.subst_weaken_rename θ₀ hθ₀ hc₀ hsΓ hsτ hu hfτ T ψ, hren ψ]
        have hm := List.mem_map_of_mem (f := fun p : LF σ Γ₀ D =>
          (⟨p.1, WFF.mono (hk p.1) p.2⟩ : LF σ Γ₀ (D.addBirth τ (.free u') T))) (hL ψ hψ)
        refine (congrArg (· ∈ Seq.mono hk L') ?_).mpr hm
        unfold WFF.weaken
        rw [WFF.mono_mono]
      obtain ⟨m, d⟩ := IH n' (Nat.lt_succ_self _) q' hok₁ hleI
        (Δ' := Seq.mono hk Δ') (Θ' := ⟨τ, WFF.mono hleI φ''⟩ :: Seq.mono hk Θ')
        (hside Δ Δ' hΔ)
        (mem_cons_of List.mem_cons_self fun x hx =>
          List.mem_cons_of_mem _ (hside Θ Θ' hΘ x hx))
      have hp := hΘ _ h₁
      have e : WFF.mono h (WFF.all T (WFF.bindFree u hu hsΓ T φ)) =
          WFF.all T (WFF.bindFree u' hfτ hsτ T φ'') := by
        rw [← hren]
        exact congrArg (WFF.all T) (WFF.subst_bindFree θ₀ hθ₀ hc₀ hsΓ hsτ hu hfτ T φ)
      rw [e] at hp
      exact ⟨m + 1, .allR τ hsτ u' T hu' hleI hp d⟩
  | @exL n' _ hns _ _ u T hu φ h₁ q =>
      obtain ⟨u', hu'⟩ := exists_treeFresh (Γ₀ := Γ₀) D
      have hsΓ : Γ.SlotsFrom 0 := hns.slots
      have hfτ := hu'.at τ
      have hok₁ := hok.addBirth hu' τ T
      let θ₀ : Subst σ (D.ctxAt Γ₀ τ) := Subst.idRen _
      have hθ₀ : Subst.Ok Γ θ₀ := Subst.ok_idRen.restrict h
      have hc₀ : Subst.Coh id Γ θ₀ := Subst.coh_idRen.restrict h
      haveI : ((D.ctxAt Γ₀ τ).insert (.free u') T).Presented :=
        (Tree.presentedAt h0 hok τ).insertFree u' hfτ T
      have q' := q.subst (θ₀.rename u u' T hfτ.root) (Subst.ok_rename hθ₀ T hfτ.root)
        (Subst.coh_rename hθ₀ hc₀ hu T hfτ.root) (hsΓ.insertFree u T)
      have hren : ∀ ψ : WFF σ Γ 0, WFF.subst id θ₀ hθ₀ hc₀ hsΓ hsτ ψ = WFF.mono h ψ :=
        fun ψ => WFF.subst_ren h θ₀ hθ₀ hc₀ hsΓ hsτ (fun v _ _ => Subst.at_idRen v) ψ
          (fun _ _ _ _ => rfl)
      set φ'' := WFF.subst (VarSymb.renameIdx id u u') (θ₀.rename u u' T hfτ.root)
        (Subst.ok_rename hθ₀ T hfτ.root) (Subst.coh_rename hθ₀ hc₀ hu T hfτ.root)
        (hsΓ.insertFree u T) (hsτ.insertFree u' T) φ
      have hk := Tree.ctxAt_addBirth hu' τ T
      have hleI := Tree.insert_le_addBirth (D := D) (Γ₀ := Γ₀) τ (.free u') T
      have hside : ∀ (L : List (WFF σ Γ 0)) (L' : Seq σ Γ₀ D),
          (∀ ψ ∈ L, (⟨τ, WFF.mono h ψ⟩ : LF σ Γ₀ D) ∈ L') →
          ∀ x ∈ (L.map (WFF.weaken hu.root T)).map (WFF.subst (VarSymb.renameIdx id u u')
            (θ₀.rename u u' T hfτ.root) (Subst.ok_rename hθ₀ T hfτ.root)
            (Subst.coh_rename hθ₀ hc₀ hu T hfτ.root) (hsΓ.insertFree u T) Ctx.NoSlots.slots),
            (⟨τ, WFF.mono hleI x⟩ : LF σ Γ₀ (D.addBirth τ (.free u') T)) ∈ Seq.mono hk L' := by
        intro L L' hL x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hy
        rw [WFF.subst_weaken_rename θ₀ hθ₀ hc₀ hsΓ hsτ hu hfτ T ψ, hren ψ]
        have hm := List.mem_map_of_mem (f := fun p : LF σ Γ₀ D =>
          (⟨p.1, WFF.mono (hk p.1) p.2⟩ : LF σ Γ₀ (D.addBirth τ (.free u') T))) (hL ψ hψ)
        refine (congrArg (· ∈ Seq.mono hk L') ?_).mpr hm
        unfold WFF.weaken
        rw [WFF.mono_mono]
      obtain ⟨m, d⟩ := IH n' (Nat.lt_succ_self _) q' hok₁ hleI
        (Δ' := ⟨τ, WFF.mono hleI φ''⟩ :: Seq.mono hk Δ') (Θ' := Seq.mono hk Θ')
        (mem_cons_of List.mem_cons_self fun x hx =>
          List.mem_cons_of_mem _ (hside Δ Δ' hΔ x hx))
        (hside Θ Θ' hΘ)
      have hp := hΔ _ h₁
      have e : WFF.mono h (WFF.ex T (WFF.bindFree u hu hsΓ T φ)) =
          WFF.ex T (WFF.bindFree u' hfτ hsτ T φ'') := by
        rw [← hren]
        exact congrArg (WFF.ex T) (WFF.subst_bindFree θ₀ hθ₀ hc₀ hsΓ hsτ hu hfτ T φ)
      rw [e] at hp
      exact ⟨m + 1, .exL τ hsτ u' T hu' hleI hp d⟩
  | @boxR n' _ hns _ _ Δ₁ φ L h₁ h₂ h₃ q =>
      rw [cp4_of_not hF, kp4_of_not hF ModalSys.NoOpt.noOpt, List.append_nil] at q
      obtain ⟨k, hv⟩ := exists_vacant τ D Δ' Θ'
      have hnone := hv.edge _ (List.suffix_refl _)
      have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hnone EdgeKind.box
      have hok₁ := hok.addEdge (k :: τ) EdgeKind.box
      have he₁ : (D.addEdge (k :: τ) .box).edge (k :: τ) = some .box := by
        rw [Tree.edge_addEdge, if_pos rfl]
      have hle₁ := Tree.boxIn_le_addEdge (Γ₀ := Γ₀) hnone hv.birthsAt
      have hcL := Tree.boxIn_le_child hok₁ k τ
      have a : Γ.boxIn.Le ((D.addEdge (k :: τ) .box).ctxAt Γ₀ τ).boxIn := (h.trans (hk τ)).boxIn
      obtain ⟨m, d⟩ := boxL_list he₁ hcL a Δ₁ (Δ := Seq.mono hk Δ')
        (Θ := ⟨k :: τ, WFF.mono hle₁ (WFF.mono h.boxIn φ)⟩ :: Seq.mono hk Θ')
        (fun χ hχ => by
          have hm := List.mem_map_of_mem (f := fun p : LF σ Γ₀ D =>
            (⟨p.1, WFF.mono (hk p.1) p.2⟩ : LF σ Γ₀ (D.addEdge (k :: τ) .box))) (hΔ _ (h₂ χ hχ))
          dsimp only at hm
          rw [WFF.mono_mono] at hm
          exact hm)
        (fun Δ'' _ hL => IH n' (Nat.lt_succ_self _) q hok₁ (a.trans hcL) hL
          (mem_cons_of (by rw [WFF.mono_mono]; exact List.mem_cons_self)
            fun _ h => by simp at h))
      exact ⟨m + 1, .boxR τ k hv hle₁ (hΘ _ h₁) d⟩
  | @serial n' _ hns _ _ hD Δ₁ L h₂ h₃ q =>
      rw [cp4_of_not hF, kp4_of_not hF ModalSys.NoOpt.noOpt, List.append_nil] at q
      obtain ⟨k, hv⟩ := exists_vacant τ D Δ' Θ'
      have hnone := hv.edge _ (List.suffix_refl _)
      have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hnone EdgeKind.box
      have hok₁ := hok.addEdge (k :: τ) EdgeKind.box
      have he₁ : (D.addEdge (k :: τ) .box).edge (k :: τ) = some .box := by
        rw [Tree.edge_addEdge, if_pos rfl]
      have hcL := Tree.boxIn_le_child hok₁ k τ
      have a : Γ.boxIn.Le ((D.addEdge (k :: τ) .box).ctxAt Γ₀ τ).boxIn := (h.trans (hk τ)).boxIn
      obtain ⟨m, d⟩ := boxL_list he₁ hcL a Δ₁ (Δ := Seq.mono hk Δ') (Θ := Seq.mono hk Θ')
        (fun χ hχ => by
          have hm := List.mem_map_of_mem (f := fun p : LF σ Γ₀ D =>
            (⟨p.1, WFF.mono (hk p.1) p.2⟩ : LF σ Γ₀ (D.addEdge (k :: τ) .box))) (hΔ _ (h₂ χ hχ))
          dsimp only at hm
          rw [WFF.mono_mono] at hm
          exact hm)
        (fun Δ'' _ hL => IH n' (Nat.lt_succ_self _) q hok₁ (a.trans hcL) hL
          fun _ h => by simp at h)
      exact ⟨m + 1, .serial hD τ k hv d⟩
  | @diaL n' _ hns _ _ x hx ψ Δ₁ Θ₁ L h₁ h₂ h₃ h₄ q =>
      rw [cp4_of_not hF, kp4_of_not hF ModalSys.NoOpt.noOpt, List.append_nil, List.map_nil,
        List.append_nil] at q
      obtain ⟨k, hv⟩ := exists_vacant τ D Δ' Θ'
      have hnone := hv.edge _ (List.suffix_refl _)
      have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hnone (EdgeKind.dia x)
      have hok₁ := hok.addEdge (k :: τ) (EdgeKind.dia x)
      have he₁ : (D.addEdge (k :: τ) (.dia x)).edge (k :: τ) = some (.dia x) := by
        rw [Tree.edge_addEdge, if_pos rfl]
      have hx' : ∃ X, (D.ctxAt Γ₀ τ).ref x = some (.VTypeDia X) := hx.imp fun _ hX => h.ref hX
      have hle₁ := Tree.diaIn_le_addEdge (Γ₀ := Γ₀) hnone hv.birthsAt x
      have hcL := Tree.boxIn_le_child hok₁ k τ
      have a : Γ.boxIn.Le ((D.addEdge (k :: τ) (.dia x)).ctxAt Γ₀ τ).boxIn :=
        (h.trans (hk τ)).boxIn
      have hcD := Tree.diaIn_le_child hok₁ he₁
      have aD : (Γ.diaIn x).Le (((D.addEdge (k :: τ) (.dia x)).ctxAt Γ₀ τ).diaIn x) :=
        (h.trans (hk τ)).diaIn x
      have hx₁ : ∃ X, ((D.addEdge (k :: τ) (.dia x)).ctxAt Γ₀ τ).ref x = some (.VTypeDia X) :=
        hx.imp fun _ hX => (h.trans (hk τ)).ref hX
      obtain ⟨m, d⟩ := boxL_list he₁ hcL a Δ₁
        (Δ := ⟨k :: τ, WFF.mono hle₁ (WFF.mono (h.diaIn x) ψ)⟩ :: Seq.mono hk Δ')
        (Θ := Seq.mono hk Θ')
        (fun χ hχ => by
          have hm := List.mem_map_of_mem (f := fun p : LF σ Γ₀ D =>
            (⟨p.1, WFF.mono (hk p.1) p.2⟩ : LF σ Γ₀ (D.addEdge (k :: τ) (.dia x))))
            (hΔ _ (h₂ χ hχ))
          dsimp only at hm
          rw [WFF.mono_mono] at hm
          exact List.mem_cons_of_mem _ hm)
        (fun Δ'' hsub hL => diaR_list hx₁ he₁ hcD aD Θ₁ (Δ := Δ'') (Θ := Seq.mono hk Θ')
          (fun θ hθ => by
            have hm := List.mem_map_of_mem (f := fun p : LF σ Γ₀ D =>
              (⟨p.1, WFF.mono (hk p.1) p.2⟩ : LF σ Γ₀ (D.addEdge (k :: τ) (.dia x))))
              (hΘ _ (h₃ θ hθ))
            dsimp only at hm
            rw [WFF.mono_mono] at hm
            exact hm)
          (fun Θ'' _ hL' => IH n' (Nat.lt_succ_self _) q hok₁ (aD.trans hcD)
            (mem_cons_of (by
                have := hsub List.mem_cons_self
                rw [WFF.mono_mono] at this
                exact this)
              fun y hy => by
                obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hy
                have := hL χ hχ
                rw [WFF.mono_mono]
                exact this)
            hL'))
      exact ⟨m + 1, .diaL τ k x hx' hv hle₁ (hΔ _ h₁) d⟩

/-- The tree with one node and nothing born. -/
theorem GKN.Tree.ok_empty {Γ₀ : Ctx} : (({} : GKN.Tree)).OK Γ₀ :=
  ⟨List.nodup_nil, fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h⟩

/-- ⭐**`GK` embeds in `GKN` at the root**: a `GK` derivation of `Δ ⇒ Θ` over `Γ₀` gives a
    `GKN` derivation of the one-node tree sequent. -/
theorem GK.toGKN_root [ModalSys.GKSys] (hF : ModalSys.Four = false) {Γ₀ : Ctx}
    [Γ₀.Presented] {n : ℕ} {Δ Θ : List (WFF σ Γ₀ 0)} (p : GK σ n Γ₀ Δ Θ) :
    ∃ m, GKN σ Γ₀ m {} (Δ.map fun φ => ⟨[], φ⟩) (Θ.map fun φ => ⟨[], φ⟩) := by
  refine GK.toGKN hF n p GKN.Tree.ok_empty (τ := []) (Ctx.Le.refl _) (fun φ hφ => ?_)
    (fun φ hφ => ?_)
  · rw [WFF.mono_refl]
    exact List.mem_map_of_mem hφ
  · rw [WFF.mono_refl]
    exact List.mem_map_of_mem hφ

/-- ⭐**Every ND-provable sequent has a cut-free `GKN` derivation**, K and KD with `Opt` off, over
    a presented context: ND → `GK` (`GK.Der.ofProof`) → `GKN` (`GK.toGKN_root`). -/
theorem GKN.ofProof [ModalSys.GKSys] (hF : ModalSys.Four = false) {Γ₀ : Ctx} [Γ₀.Presented]
    {Δ : List (WFF σ Γ₀ 0)} {φ : WFF σ Γ₀ 0} (p : Proof σ Γ₀ Δ φ) :
    ∃ m, GKN σ Γ₀ m {} (Δ.map fun ψ => ⟨[], ψ⟩) [⟨[], φ⟩] := by
  obtain ⟨n, d⟩ := GK.Der.ofProof p
  exact GK.toGKN_root hF d

end V12M
