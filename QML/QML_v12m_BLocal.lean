import QML.QML_v12m_BAbs
import QML.QML_v12m_Henkin

/-!
# QML v12m — B's arrow model: the local steps

Each step of the construction extends one world's theory in a larger context, and each needs a
consistency lemma.  They are stated for single maximal consistent theories over one context.

* ⭐`henkin_consistent`: an existential's witness, a fresh variable, keeps a theory consistent.
* `Transfer`: an arrow's **necessity transfer** — whatever the source necessitates about its first
  variables (those already given images), the target says of their images.
* ⭐`realise_consistent`: the target stays consistent when the source's next variable gets a
  fresh image realising everything the source necessitates about it.  The source's necessity
  `□ψ` gives `□∃y. ψ̃(y)` about the older variables only (`instantiate_tup_abs`); the transfer puts
  `∃y. ψ̃'(y)` into the target; its Henkin witness is the image (`subst_arrow_abs`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## Derivations -/

theorem derives_of_derives {Γ : Ctx} {S : Set (WFF σ Γ 0)} :
    ∀ {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0}, (∀ δ ∈ Δ, Theory.Derives S δ) → Provable Δ φ →
      Theory.Derives S φ
  | [], _, _, p => ⟨[], fun _ h => absurd h List.not_mem_nil, p⟩
  | δ :: _, _, h, p =>
      (derives_of_derives (fun d hd => h d (List.mem_cons_of_mem _ hd))
        (Provable.imp_intro p)).mp (h δ List.mem_cons_self)

theorem Derives.trans {Γ : Ctx} {S S' : Set (WFF σ Γ 0)} (h : ∀ ψ ∈ S', Theory.Derives S ψ)
    {φ : WFF σ Γ 0} (hd : Theory.Derives S' φ) : Theory.Derives S φ := by
  obtain ⟨Δ, hΔ, p⟩ := hd
  exact derives_of_derives (fun δ hδ => h δ (hΔ δ hδ)) p

/-! ## The Henkin step -/

/-- ⭐The witness of a derivable existential, a fresh variable, keeps a theory consistent. -/
theorem henkin_consistent {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)}
    (hM : Theory.Consistent M) {A : VarType} {ψ : WFF σ (Γ.insert (.bnd 0) A) 1}
    (hex : Theory.Derives M (.ex A ψ)) {u : ℕ} (hu : Γ.RootFresh (.free u)) :
    Theory.Consistent (WFF.mono (Ctx.le_insert hu.root A) '' M ∪
      {WFF.openFree u hu Ctx.NoSlots.slots ψ}) := by
  rintro ⟨Δ, hΔ, p⟩
  obtain ⟨Δ₀, h₀, h₁⟩ := exists_hyps_cons_map (P := fun x => x ∈ M)
    (fun x => WFF.mono (Ctx.le_insert hu.root A) x) (WFF.openFree u hu Ctx.NoSlots.slots ψ) Δ
    (fun δ hδ => by
      rcases hΔ δ hδ with ⟨x, hx, rfl⟩ | h
      · exact Or.inr ⟨x, hx, rfl⟩
      · exact Or.inl (Set.mem_singleton_iff.mp h))
  obtain ⟨q⟩ := Provable.mono h₁ p
  obtain ⟨Δ₁, hΔ₁, ⟨pex⟩⟩ := hex
  refine hM ⟨Δ₁ ++ Δ₀, fun x hx => (List.mem_append.mp hx).elim (hΔ₁ x) (h₀ x), ⟨?_⟩⟩
  refine Proof.ex_elim u A hu (φ := WFF.openFree u hu Ctx.NoSlots.slots ψ) (ψ := .bot)
    (Proof.conv (congrArg (WFF.ex A) (WFF.bindFree_openFree u hu Ctx.NoSlots.slots ψ).symm)
      (Proof.ofSubset (fun x hx => List.mem_append_left _ hx) pex))
    (Proof.ofSubset (fun x hx => ?_) q)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact List.mem_cons_self
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_append_right _ hy))

/-! ## Necessity transfer -/

/-- ⭐The necessity transfer of an arrow from a context `Γ` whose oldest variables `ls` have images
    in `Δ`: whatever the source necessitates about them, the target says of their images. -/
def Transfer [ModalSys.NoFour] {Γ : Ctx} (M : Set (WFF σ Γ 0)) (ls : List VarType)
    (hle : (ctxOf ls).Le Γ) {Δ : Ctx} [Δ.NoSlots] (N : Set (WFF σ Δ 0)) (img : ℕ → ℕ)
    (himg : ImgOk ls Δ img) : Prop :=
  ∀ ψ : WFF σ (ctxOf ls).boxIn 0, WFF.mono hle (.box ψ) ∈ M →
    WFF.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS himg) (coh_arrowS himg)
      Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈ N

/-- A maximal consistent theory is closed under the conjunction of necessities. -/
theorem box_and_mem {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)} (hM : Theory.IsMCS M)
    {Γ₀ : Ctx} (hle : Γ₀.Le Γ) {ψ₁ ψ₂ : WFF σ Γ₀.boxIn 0}
    (h₁ : WFF.mono hle (.box ψ₁) ∈ M) (h₂ : WFF.mono hle (.box ψ₂) ∈ M) :
    WFF.mono hle (.box (ψ₁.and ψ₂)) ∈ M := by
  refine hM.closed ⟨[WFF.mono hle (.box ψ₁), WFF.mono hle (.box ψ₂)], fun x hx => ?_, ?_⟩
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact h₁
    · rw [List.mem_singleton.mp hx]; exact h₂
  · exact Provable.monoCtx (Δs := [.box ψ₁, .box ψ₂]) hle
      ⟨Proof.K_box (Δ := [ψ₁, ψ₂]) (.and_intro (Proof.lookup List.mem_cons_self)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))⟩

theorem box_top_mem {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)} (hM : Theory.IsMCS M)
    {Γ₀ : Ctx} (hle : Γ₀.Le Γ) : WFF.mono hle (.box (.top : WFF σ Γ₀.boxIn 0)) ∈ M :=
  hM.closed ⟨[], fun _ h => absurd h List.not_mem_nil,
    Provable.monoCtx (Δs := []) hle ⟨Proof.K_box (Δ := []) .top_intro⟩⟩

/-- The necessary formulas about a fixed part of the context, as a finite list reduce to one. -/
theorem box_list {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)} (hM : Theory.IsMCS M)
    {Γ₀ : Ctx} (hle : Γ₀.Le Γ) {Δ : Ctx} (f : WFF σ Γ₀.boxIn 0 → WFF σ Δ 0)
    (hf : ∀ ψ₁ ψ₂, f (ψ₁.and ψ₂) = (f ψ₁).and (f ψ₂)) (S : Set (WFF σ Δ 0)) :
    ∀ L : List (WFF σ Δ 0), (∀ δ ∈ L, δ ∈ S ∨ ∃ ψ, WFF.mono hle (.box ψ) ∈ M ∧ δ = f ψ) →
      ∃ ψ, WFF.mono hle (.box ψ) ∈ M ∧ ∀ δ ∈ L, Theory.Derives (S ∪ {f ψ}) δ
  | [], _ => ⟨.top, box_top_mem hM hle, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨ψ₀, hψ₀, hL⟩ := box_list hM hle f hf S L (fun d hd => h d (List.mem_cons_of_mem _ hd))
      rcases h δ List.mem_cons_self with hS | ⟨ψ₁, hψ₁, rfl⟩
      · refine ⟨ψ₀, hψ₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact Theory.Derives.of_mem (Or.inl hS)
        · exact hL d hd
      · refine ⟨ψ₀.and ψ₁, box_and_mem hM hle hψ₀ hψ₁, fun d hd => ?_⟩
        have hconj : Theory.Derives (S ∪ {f (ψ₀.and ψ₁)}) ((f ψ₀).and (f ψ₁)) := by
          rw [← hf]
          exact Theory.Derives.of_mem (Or.inr rfl)
        rcases List.mem_cons.mp hd with rfl | hd
        · obtain ⟨Δ', hΔ', p⟩ := hconj
          exact ⟨Δ', hΔ', Provable.and_elim_r p⟩
        · refine Derives.trans (fun x hx => ?_) (hL d hd)
          rcases hx with hx | hx
          · exact Theory.Derives.of_mem (Or.inl hx)
          · rw [Set.mem_singleton_iff.mp hx]
            obtain ⟨Δ', hΔ', p⟩ := hconj
            exact ⟨Δ', hΔ', Provable.and_elim_l p⟩

/-! ## Realising the next variable -/

/-- The arrow extended by the source's next variable. -/
abbrev extArrow [ModalSys.NoFour] {A : VarType} {ls lt : List VarType} {img : ℕ → ℕ}
    (himg : ImgOk ls (ctxOf lt) img) (ψ : WFF σ (ctxOf (A :: ls)).boxIn 0) :
    WFF σ (ctxOf (A.bc :: lt)) 0 :=
  WFF.subst (arrowIdx (extImg img ls.length lt.length))
    (arrowS σ (ctxOf (A.bc :: lt)) (extImg img ls.length lt.length))
    (ok_arrowS (imgOk_ext himg)) (coh_arrowS (imgOk_ext himg)) Ctx.NoSlots.slots
    Ctx.NoSlots.slots ψ

/-- One necessity of the source about its next variable is consistent with the target. -/
theorem realise_one [ModalSys.NoFour] {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)}
    (hM : Theory.IsMCS M) {A : VarType} {ls lt : List VarType}
    (hle : (ctxOf (A :: ls)).Le Γ) {N : Set (WFF σ (ctxOf lt) 0)} (hN : Theory.IsMCS N)
    {img : ℕ → ℕ} (himg : ImgOk ls (ctxOf lt) img)
    (htr : Transfer M ls ((ctxOf_le_append [A] ls).trans hle) N img himg)
    {ψ : WFF σ (ctxOf (A :: ls)).boxIn 0} (hψ : WFF.mono hle (.box ψ) ∈ M) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [A.bc] lt) '' N ∪ {extArrow himg ψ}) := by
  -- `□ψ` gives `□∃y. ψ̃(y)`, about the older variables only.
  have hex : WFF.mono ((ctxOf_le_append [A] ls).trans hle)
      (.box (.ex A.bc (abs A ls ψ))) ∈ M := by
    refine hM.closed ⟨[WFF.mono hle (.box ψ)], fun x hx => by
      rw [List.mem_singleton.mp hx]; exact hψ, ?_⟩
    have h := Provable.monoCtx (Δs := [.box ψ]) hle
      ⟨Proof.K_box (Δ := [ψ]) (Proof.ex_intro A.bc (tup (.root (.free ls.length)) A
        (ctxOf_ref_new A ls)) (Proof.conv (instantiate_tup_abs A ls ψ).symm
          (Proof.lookup List.mem_cons_self)))⟩
    rw [← WFF.mono_mono (ctxOf_le_append [A] ls) hle]
    exact h
  -- The transfer puts the existential into the target, and its witness realises `ψ`.
  have hN' := htr _ hex
  have hsub := subst_arrow_abs (A := A) himg ψ
  rw [← WFF.instantiate_toFree (arrowS σ (ctxOf lt) img) (ok_arrowS himg) (coh_arrowS himg)
      Ctx.NoSlots.slots Ctx.NoSlots.slots lt.length (ctxOf_fresh le_rfl) A.bc Ctx.NoSlots.slots
      (abs A ls ψ), WFF.instantiate_eta_openFree _ (ctxOf_fresh le_rfl)
      Ctx.NoSlots.slots] at hsub
  change _ ∈ N at hN'
  have hc := henkin_consistent hN.1 (Theory.Derives.of_mem hN') (ctxOf_fresh (l := lt) le_rfl)
  rw [show extArrow himg ψ = _ from hsub]
  exact hc

/-- ⭐**Realising the next variable along an arrow.**  Everything the source necessitates about
    its variables up to the next one is consistent with the target, the next one's items going to
    a fresh variable. -/
theorem realise_consistent [ModalSys.NoFour] {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)}
    (hM : Theory.IsMCS M) {A : VarType} {ls lt : List VarType}
    (hle : (ctxOf (A :: ls)).Le Γ) {N : Set (WFF σ (ctxOf lt) 0)} (hN : Theory.IsMCS N)
    {img : ℕ → ℕ} (himg : ImgOk ls (ctxOf lt) img)
    (htr : Transfer M ls ((ctxOf_le_append [A] ls).trans hle) N img himg) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [A.bc] lt) '' N ∪
      {φ | ∃ ψ, WFF.mono hle (.box ψ) ∈ M ∧ φ = extArrow himg ψ}) := by
  rintro ⟨L, hL, p⟩
  obtain ⟨ψ, hψ, hder⟩ := box_list hM hle (extArrow himg) (fun _ _ => rfl)
    (WFF.mono (ctxOf_le_append [A.bc] lt) '' N) L (fun δ hδ => (hL δ hδ).imp id id)
  exact realise_one hM hle hN himg htr hψ (derives_of_derives hder p)

end BArrow

end V12M
