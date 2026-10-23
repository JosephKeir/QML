import QML.QML_v12m_GAbs
import QML.QML_v12m_BDia

/-!
# QML v12m — the growing tree: the local steps

`BArrow`'s local steps (`QML_v12m_BLocal.lean`, `QML_v12m_BDia.lean`) for the growing tree, over
item maps and for either kind of edge at once (`Ctx.kView`): an edge of kind `none` translates the
`□` view and transfers `□`, one of kind `some x` (a child made for `◇_x`) translates the `◇_x`
view and transfers `□_x` (`kBox`).

* `GTransfer`: an edge's **necessity transfer** — whatever the source `□_k`-necessitates about its
  first variables (those with images), the target says of their images.
* ⭐`grealise_consistent`: the target stays consistent when the source's next variable gets a
  fresh realisation (`gextF`): `□_k ψ` gives `□_k ∃y. ψ̃(y)` about the older variables only
  (`instantiate_gtup_gabs`), the transfer puts `∃y. ψ̃'(y)` into the target, and its Henkin
  witness is the realisation (`subst_gext_gabs`).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature}

/-! ## The necessity of an edge -/

/-- The witness of an edge's view, if any, is a declared possible address. -/
def KDecl (Γ : Ctx) (k : Option VarSymb) : Prop :=
  ∀ x, k = some x → ∃ X, Γ.ref x = some (.VTypeDia X)

theorem kDecl_none (Γ : Ctx) : KDecl Γ none := fun _ h => by cases h

theorem kDecl_mono {Γ Γ' : Ctx} (h : Γ.Le Γ') {k : Option VarSymb} (hk : KDecl Γ k) :
    KDecl Γ' k := fun x e => by
  obtain ⟨X, hX⟩ := hk x e
  exact ⟨X, h.ref hX⟩

theorem kOld_of_kDecl {l : List VarType} {k : Option VarSymb} (hk : KDecl (ctxOf l) k) :
    KOld k l.length := fun x e => by
  obtain ⟨X, hX⟩ := hk x e
  subst e
  exact kOld_some hX x rfl

/-- ⭐The necessity of an edge's kind: `□`, or `□_x` for a child made for `◇_x`. -/
def kBox {Γ : Ctx} {d : ℕ} : (k : Option VarSymb) → KDecl Γ k → WFF σ (Γ.kView k) d →
    WFF σ Γ d
  | none, _, φ => .box φ
  | some x, hk, φ => WFF.boxx x (hk x rfl) φ

theorem mono_kBox {Γ Γ' : Ctx} (h : Γ.Le Γ') {d : ℕ} :
    ∀ (k : Option VarSymb) (hk : KDecl Γ k) (φ : WFF σ (Γ.kView k) d),
      WFF.mono h (kBox k hk φ) = kBox k (kDecl_mono h hk) (WFF.mono (h.kView k) φ)
  | none, _, _ => rfl
  | some _, _, _ => rfl

/-- `□_k` distributes over a derivation in the edge's view. -/
def Proof.kBoxK {Γ : Ctx} : (k : Option VarSymb) → (hk : KDecl Γ k) →
    {Δ : List (WFF σ (Γ.kView k) 0)} → {φ : WFF σ (Γ.kView k) 0} →
    Proof σ (Γ.kView k) Δ φ → Proof σ Γ (Δ.map (kBox k hk)) (kBox k hk φ)
  | none, _, Δ, _, p => Proof.K_box (Δ := Δ) p
  | some x, hk, _, _, p => Proof.boxxK (hk x rfl) p

theorem kBox_and_mem {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)} (hM : Theory.IsMCS M)
    {Γ₀ : Ctx} (hle : Γ₀.Le Γ) {k : Option VarSymb} (hk : KDecl Γ₀ k)
    {ψ₁ ψ₂ : WFF σ (Γ₀.kView k) 0}
    (h₁ : WFF.mono hle (kBox k hk ψ₁) ∈ M) (h₂ : WFF.mono hle (kBox k hk ψ₂) ∈ M) :
    WFF.mono hle (kBox k hk (ψ₁.and ψ₂)) ∈ M := by
  cases k with
  | none => exact box_and_mem hM hle h₁ h₂
  | some x => exact boxx_and_mem hM hle (hk x rfl) h₁ h₂

theorem kBox_top_mem {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)} (hM : Theory.IsMCS M)
    {Γ₀ : Ctx} (hle : Γ₀.Le Γ) {k : Option VarSymb} (hk : KDecl Γ₀ k) :
    WFF.mono hle (kBox k hk (.top : WFF σ (Γ₀.kView k) 0)) ∈ M := by
  cases k with
  | none => exact box_top_mem hM hle
  | some x => exact boxx_top_mem hM hle (hk x rfl)

/-! ## Necessity transfer -/

/-- ⭐The necessity transfer of an edge of kind `k` from a context `Γ` whose oldest variables `ls`
    have images in `ctxOf lt` by the item map `f`: whatever the source `□_k`-necessitates about
    them, the target says of their images. -/
def GTransfer {Γ : Ctx} (M : Set (WFF σ Γ 0)) (ls : List VarType) (hle : (ctxOf ls).Le Γ)
    (k : Option VarSymb) (hk : KDecl (ctxOf ls) k) {lt : List VarType}
    (N : Set (WFF σ (ctxOf lt) 0)) (f : VarSymb → VarSymb)
    (hf : ItemOk ((ctxOf ls).kView k) (ctxOf lt) f) : Prop :=
  ∀ ψ : WFF σ ((ctxOf ls).kView k) 0, WFF.mono hle (kBox k hk ψ) ∈ M →
    WFF.subst (itemIdx f) (itemS σ (ctxOf lt) f) (ok_itemS_kView hf) (coh_itemS_kView hf)
      Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈ N

/-! ## Realising the next variable -/

/-- The edge's item map extended by the source's next variable, applied to a formula. -/
abbrev gextArrow (hF : ModalSys.Four = true) {k : Option VarSymb} {A : VarType}
    {ls lt : List VarType} (hk : KDecl (ctxOf ls) k) {f : VarSymb → VarSymb}
    (hf : ItemOk ((ctxOf ls).kView k) (ctxOf lt) f) (ψ : WFF σ ((ctxOf (A :: ls)).kView k) 0) :
    WFF σ (ctxOf (A.gc :: lt)) 0 :=
  WFF.subst (itemIdx (gextF f A ls.length lt.length))
    (itemS σ (ctxOf (A.gc :: lt)) (gextF f A ls.length lt.length))
    (ok_itemS_kView (itemOk_gextF hF (kOld_of_kDecl hk) hf))
    (coh_itemS_kView (itemOk_gextF hF (kOld_of_kDecl hk) hf)) Ctx.NoSlots.slots
    Ctx.NoSlots.slots ψ

/-- One necessity of the source about its next variable is consistent with the target. -/
theorem grealise_one (hF : ModalSys.Four = true) {Γ : Ctx} [Γ.Presented]
    {M : Set (WFF σ Γ 0)} (hM : Theory.IsMCS M) {A : VarType} {ls lt : List VarType}
    (hle : (ctxOf (A :: ls)).Le Γ) {N : Set (WFF σ (ctxOf lt) 0)} (hN : Theory.IsMCS N)
    {k : Option VarSymb} (hk : KDecl (ctxOf ls) k) {f : VarSymb → VarSymb}
    (hf : ItemOk ((ctxOf ls).kView k) (ctxOf lt) f)
    (htr : GTransfer M ls ((ctxOf_le_append [A] ls).trans hle) k hk N f hf)
    {ψ : WFF σ ((ctxOf (A :: ls)).kView k) 0}
    (hψ : WFF.mono hle (kBox k (kDecl_mono (ctxOf_le_append [A] ls) hk) ψ) ∈ M) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [A.gc] lt) '' N ∪
      {gextArrow hF hk hf ψ}) := by
  have hko := kOld_of_kDecl hk
  have hk' := kDecl_mono (ctxOf_le_append [A] ls) hk
  -- `□_k ψ` gives `□_k ∃y. ψ̃(y)`, about the older variables only.
  have hex : WFF.mono ((ctxOf_le_append [A] ls).trans hle)
      (kBox k hk (.ex A.gc (gabs hF k A ls hko ψ))) ∈ M := by
    refine hM.closed ⟨[WFF.mono hle (kBox k hk' ψ)], fun x hx => by
      rw [List.mem_singleton.mp hx]; exact hψ, ?_⟩
    have h := Provable.monoCtx (Δs := [kBox k hk' ψ]) hle
      ⟨Proof.kBoxK k hk' (Δ := [ψ]) (Proof.ex_intro A.gc
        (Term.mono (Ctx.le_boxIn_kView _ k)
          (gtup hF (.root (.free ls.length)) A (ctxOf_ref_new A ls)))
        (Proof.conv (instantiate_gtup_gabs hF k A ls hko ψ).symm
          (Proof.lookup List.mem_cons_self)))⟩
    have e : WFF.mono (ctxOf_le_append [A] ls) (kBox k hk (.ex A.gc (gabs hF k A ls hko ψ))) =
        kBox k hk' (.ex A.gc (WFF.mono (gabsCtx_le k A ls) (gabs hF k A ls hko ψ))) :=
      mono_kBox _ k hk _
    rw [← WFF.mono_mono (ctxOf_le_append [A] ls) hle, e]
    exact h
  -- The transfer puts the existential into the target, and its witness realises `ψ`.
  have hN' := htr _ hex
  have hsub := subst_gext_gabs hF hko hf ψ
  rw [← WFF.instantiate_toFree (itemS σ (ctxOf lt) f) (ok_itemS_kView hf) (coh_itemS_kView hf)
      Ctx.NoSlots.slots Ctx.NoSlots.slots lt.length (ctxOf_fresh le_rfl) A.gc Ctx.NoSlots.slots
      (gabs hF k A ls hko ψ), WFF.instantiate_eta_openFree _ (ctxOf_fresh le_rfl)
      Ctx.NoSlots.slots] at hsub
  change _ ∈ N at hN'
  have hc := henkin_consistent hN.1 (Theory.Derives.of_mem hN') (ctxOf_fresh (l := lt) le_rfl)
  rw [show gextArrow hF hk hf ψ = _ from hsub]
  exact hc

/-- ⭐**Realising the next variable along an edge.**  Everything the source `□_k`-necessitates
    about its variables up to the next one is consistent with the target, the next one's items
    going to a fresh variable of its `gc` type. -/
theorem grealise_consistent (hF : ModalSys.Four = true) {Γ : Ctx} [Γ.Presented]
    {M : Set (WFF σ Γ 0)} (hM : Theory.IsMCS M) {A : VarType} {ls lt : List VarType}
    (hle : (ctxOf (A :: ls)).Le Γ) {N : Set (WFF σ (ctxOf lt) 0)} (hN : Theory.IsMCS N)
    {k : Option VarSymb} (hk : KDecl (ctxOf ls) k) {f : VarSymb → VarSymb}
    (hf : ItemOk ((ctxOf ls).kView k) (ctxOf lt) f)
    (htr : GTransfer M ls ((ctxOf_le_append [A] ls).trans hle) k hk N f hf) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [A.gc] lt) '' N ∪
      {φ | ∃ ψ, WFF.mono hle (kBox k (kDecl_mono (ctxOf_le_append [A] ls) hk) ψ) ∈ M ∧
        φ = gextArrow hF hk hf ψ}) := by
  rintro ⟨L, hL, p⟩
  obtain ⟨ψ, hψ, hder⟩ := list_reduce
    (fun ψ => WFF.mono hle (kBox k (kDecl_mono (ctxOf_le_append [A] ls) hk) ψ) ∈ M)
    (kBox_top_mem hM hle _) (fun h₁ h₂ => kBox_and_mem hM hle _ h₁ h₂)
    (gextArrow hF hk hf) (fun _ _ => rfl)
    (WFF.mono (ctxOf_le_append [A.gc] lt) '' N) L (fun δ hδ => (hL δ hδ).imp id id)
  exact grealise_one hF hM hle hN hk hf htr hψ (derives_of_derives hder p)

end GArrow

end V12M
