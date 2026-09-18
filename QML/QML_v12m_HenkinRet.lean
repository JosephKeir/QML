import QML.QML_v12m_CanonWorld
import QML.QML_v12m_RetUse
import QML.QML_v12m_StageSkip

/-!
# QML v12m — the chain's realised witnesses (strong T)

The Henkin chain declares, at a strong T step, a witness `ρ n : ◇A` for the term it enumerated,
together with every `WFF.retHyp` instance for that term (`retSet`).  This file turns those
instances into a `Canon.RealDatum`: the evidence that makes the witness a **realised** one, whose
`spec` field must serve formulas of every later stage.

* `laterList`: the constants declared after the witness, as the parameter's packing;
* the packing's side conditions at a stage of a world language.
-/

namespace V12M

variable [ModalSys]

/-! ## The constants declared after the witness -/

/-- The own constants declared after the witness of stage `n`, up to stage `n + 1 + k`. -/
def laterList (τ : ℕ → VarType) (ρ : ℕ → ℕ) (n : ℕ) : ℕ → List (VarType × ℕ)
  | 0 => []
  | k + 1 => (τ (n + 1 + k), ρ (n + 1 + k)) :: laterList τ ρ n k

variable {τ : ℕ → VarType} {ρ : ℕ → ℕ} {n : ℕ}

omit [ModalSys] in
/-- A packed name is one of the later own names. -/
theorem packOf_laterList : ∀ (k : ℕ) {m : ℕ}, Subst.packOf (laterList τ ρ n k) m ≠ none →
    ∃ p, n < p ∧ p < n + 1 + k ∧ m = ρ p
  | 0, _, h => absurd rfl h
  | k + 1, m, h => by
      by_cases hm : m = ρ (n + 1 + k)
      · exact ⟨n + 1 + k, by omega, by omega, hm⟩
      · rw [show Subst.packOf (laterList τ ρ n (k + 1)) m =
          (Subst.packOf (laterList τ ρ n k) m).map (· + 1) from if_neg hm] at h
        obtain ⟨p, hp₁, hp₂, hp₃⟩ := packOf_laterList k (fun he => h (by rw [he]; rfl))
        exact ⟨p, hp₁, by omega, hp₃⟩

omit [ModalSys] in
/-- Every later own name is packed. -/
theorem packOf_laterList_mem (hρ : Function.Injective ρ) :
    ∀ (k p : ℕ), n < p → p < n + 1 + k → Subst.packOf (laterList τ ρ n k) (ρ p) ≠ none
  | 0, _, _, h₂ => absurd h₂ (by omega)
  | k + 1, p, h₁, h₂ => by
      by_cases hp : p = n + 1 + k
      · rw [show Subst.packOf (laterList τ ρ n (k + 1)) (ρ p) = some 0 from if_pos (by rw [hp])]
        exact fun he => by cases he
      · rw [show Subst.packOf (laterList τ ρ n (k + 1)) (ρ p) =
          (Subst.packOf (laterList τ ρ n k) (ρ p)).map (· + 1) from
          if_neg (fun he => hp (hρ he))]
        intro he
        exact packOf_laterList_mem hρ k p h₁ (by omega) (Option.map_eq_none_iff.mp he)

/-! ## The packing's side conditions at a stage -/

namespace Ctx

variable {B : Ctx}

omit [ModalSys] in
/-- The base of a stage is part of it. -/
theorem base_le_stage (hρ : Function.Injective ρ) (hB : ∀ p, B.RootFresh (.free (ρ p))) :
    ∀ k : ℕ, B.Le (B.stage τ ρ k)
  | 0 => Ctx.Le.refl _
  | k + 1 =>
      (base_le_stage hρ hB k).trans
        (Ctx.le_insert (Ctx.stage_fresh hρ hB (le_refl k) (.root (.free (ρ k))) rfl) (τ k))

/-- The packed constants are declared in the skipped stage. -/
theorem laterList_ref (hρ : Function.Injective ρ) (hB : ∀ p, B.RootFresh (.free (ρ p))) :
    ∀ (k j : ℕ), n + 1 + k ≤ j → ∀ z ∈ laterList τ ρ n k,
      (B.stageSkip τ ρ n j).ref (.root (.free z.2)) = some z.1
  | 0, _, _, _, h => absurd h List.not_mem_nil
  | k + 1, j, hj, z, hz => by
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact Ctx.stageSkip_ref_root hρ hB (by omega) (by omega)
      · exact laterList_ref hρ hB k j (by omega) z hz'

omit [ModalSys] in
/-- Nothing but the root is written at a packed constant. -/
theorem laterList_only_root (hρ : Function.Injective ρ) (hB : ∀ p, B.RootFresh (.free (ρ p)))
    (k j : ℕ) : ∀ (v : VarSymb) (m : ℕ), v.rt = .free m →
      Subst.packOf (laterList τ ρ n k) m ≠ none → v ≠ .root (.free m) →
      (B.stageSkip τ ρ n j) v = none := by
  intro v m hv hpack hne
  obtain ⟨p, _, _, rfl⟩ := packOf_laterList k hpack
  exact Ctx.stageSkip_only_root hρ hB j v hv hne

/-- Every unpacked entry of the skipped stage is already there at the witness's stage. -/
theorem laterList_sub (hρ : Function.Injective ρ) (hB : ∀ p, B.RootFresh (.free (ρ p)))
    (k j : ℕ) (hj : j ≤ n + 1 + k) :
    ∀ (v : VarSymb) (T : VarType),
      (∀ m, v.rt = .free m → Subst.packOf (laterList τ ρ n k) m = none) →
      (B.stageSkip τ ρ n j) v = some T → (B.stage τ ρ n) v = some T := by
  intro v T hun hv
  rcases Ctx.stageSkip_cases j hv with hb | ⟨p, hp, hpn, rfl, rfl⟩
  · exact base_le_stage hρ hB n v T hb
  · have hnone : Subst.packOf (laterList τ ρ n k) (ρ p) = none := hun _ rfl
    have hple : ¬ (n < p) := fun hlt =>
      packOf_laterList_mem hρ k p hlt (by omega) hnone
    have hpn2 : p < n := by omega
    have hst := Ctx.stage_ref_root (B := B) (τ := τ) ρ hρ hB hpn2
    rwa [Ctx.ref_nonproj (B.stage τ ρ n)
      (show (VarSymb.root (Root.free (ρ p))).lastProj = false from rfl)] at hst

omit [ModalSys] in
theorem le_of_eq {Γ Γ' : Ctx} (E : Γ = Γ') : Γ.Le Γ' := fun _ _ h => E ▸ h

end Ctx

/-! ## The witness's specification -/

namespace WorldLang

variable {σ : Signature} (F : WorldLang)

/-- The witness of stage `n`, as an address. -/
abbrev wit (n : ℕ) : VarSymb := .root (.free (F.ρ n))

variable {F}

/-- At a later stage the witness is declared at its own type. -/
theorem ref_wit {m j n : ℕ} (h : n < j) : (F.ctx (m, j)).ref (F.wit n) = some (F.τ n) :=
  Ctx.stage_ref_root F.ρ F.ρ_inj (F.fresh m) h

/-- Nothing else is written at the witness's root. -/
theorem fr_wit {m j n : ℕ} : ∀ v : VarSymb, v.rt = .free (F.ρ n) → v ≠ F.wit n →
    (F.ctx (m, j)) v = none :=
  Ctx.stage_only_root F.ρ F.ρ_inj (F.fresh m) j

theorem WFF.mono_imp {Γ Γ' : Ctx} (h : Γ.Le Γ') {d : ℕ} (φ ψ : WFF σ Γ d) :
    WFF.mono h (.imp φ ψ) = .imp (WFF.mono h φ) (WFF.mono h ψ) := rfl

theorem WFF.mono_dia {Γ Γ' : Ctx} (h : Γ.Le Γ') {d : ℕ} {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (χ : WFF σ (Γ.diaIn x) d) :
    WFF.mono h (.dia x hx χ) =
      .dia x (hx.imp fun _ hX => h.ref hX) (WFF.mono (h.diaIn x) χ) := rfl

/-- ⭐The chain's hypotheses give what `RealDatum.spec` asks: at any later stage, everything the
    realising term satisfies there, the witness satisfies in its view.

    The hypothesis is the one the chain adds for the packed abstraction of `χ`, at the base stage
    of `χ` itself; instantiating its `∀` at the tuple of the constants declared after the witness
    turns it into exactly the implication wanted. -/
theorem spec_of_retHyps {T : Set (F.sys.Sentence σ)} (hmcs : StageSys.IsMCS T)
    (hT : ModalSys.T = true) {n : ℕ} {A : VarType} (hτ : F.τ n = .VTypeDia A)
    {m₀ : ℕ} {a₀ : Ann A} (t₀ : Term σ (F.ctx (m₀, n)) A a₀)
    (hhyp : ∀ (m : ℕ) (hm : m₀ ≤ m) (B : VarType)
      (ψ : WFF σ (((F.ctx (m, n)).insert (.free (F.ρ (n + 1))) B).boxIn.insert (.bnd 0) A) 1),
      (⟨(m, n + 1), WFF.mono
          (Ctx.le_of_eq (show (F.ctx (m, n)).insert (.free (F.ρ n)) (.VTypeDia A) =
            F.ctx (m, n + 1) by rw [F.ctx_succ, hτ]))
          (WFF.retHyp hT (Term.mono (F.ctx_le (Prod.mk_le_mk.mpr ⟨hm, le_rfl⟩)) t₀)
            (F.ρ n) (F.ρ (n + 1)) (F.fresh_ctx le_rfl) (F.fresh_ctx (Nat.le_succ n))
            (fun he => Nat.succ_ne_self n (F.ρ_inj he)) B ψ)⟩ : F.sys.Sentence σ) ∈ T)
    {i : ℕ × ℕ} (hi : (m₀, n) ≤ i) (hlt : n < i.2)
    (χ : WFF σ ((F.ctx i).diaIn (F.wit n)) 0)
    (hmem : (⟨i, WFF.realiseAt hT (F.ρ n) (hτ ▸ ref_wit hlt) fr_wit
        (Term.mono (F.ctx_le hi) t₀) χ⟩ : F.sys.Sentence σ) ∈ T) :
    (⟨i, .dia (F.wit n) ⟨A, hτ ▸ ref_wit hlt⟩ χ⟩ : F.sys.Sentence σ) ∈ T := by
  obtain ⟨m, j⟩ := i
  have hm : m₀ ≤ m := hi.1
  have hnj : n < j := hlt
  obtain ⟨k, rfl⟩ : ∃ k, j = n + 1 + k := ⟨j - (n + 1), by omega⟩
  set Δ : Ctx := (F.base m).stageSkip F.τ F.ρ n (n + 1 + k) with hΔdef
  have E : F.ctx (m, n + 1 + k) = Δ.insert (.free (F.ρ n)) (.VTypeDia A) := by
    change (F.base m).stage F.τ F.ρ (n + 1 + k) = _
    rw [Ctx.stage_eq_skip_insert F.ρ_inj (show n < n + 1 + k by omega), hτ]
  have le₁ : (F.ctx (m, n + 1 + k)).Le (Δ.insert (.free (F.ρ n)) (.VTypeDia A)) := Ctx.le_of_eq E
  have le₂ : (Δ.insert (.free (F.ρ n)) (.VTypeDia A)).Le (F.ctx (m, n + 1 + k)) :=
    Ctx.le_of_eq E.symm
  haveI hΔslots : Δ.NoSlots := ⟨Ctx.stageSkip_slots (Ctx.NoSlots.slots) (n + 1 + k)⟩
  have hcΔ : Δ.RootFresh (.free (F.ρ n)) :=
    Ctx.stageSkip_fresh_skipped F.ρ_inj (F.fresh m) _
  have hleΓΔ : (F.ctx (m, n)).Le Δ :=
    Ctx.stage_le_stageSkip F.ρ_inj (F.fresh m) (Nat.le_succ n |>.trans (by omega))
  have hz : ∀ z ∈ laterList F.τ F.ρ n k, Δ.ref (.root (.free z.2)) = some z.1 :=
    Ctx.laterList_ref F.ρ_inj (F.fresh m) k (n + 1 + k) le_rfl
  have honly := Ctx.laterList_only_root (τ := F.τ) (n := n) F.ρ_inj (F.fresh m) k (n + 1 + k)
  have hsub := Ctx.laterList_sub (τ := F.τ) (n := n) F.ρ_inj (F.fresh m) k (n + 1 + k) le_rfl
  have key := WFF.instantiate_mono_retBody_pack (Γ := F.ctx (m, n)) (Δ := Δ) hT
    (Term.mono (F.ctx_le (Prod.mk_le_mk.mpr ⟨hm, le_rfl⟩)) t₀) (c := F.ρ n) (y := F.ρ (n + 1))
    (F.fresh_ctx le_rfl) (F.fresh_ctx (Nat.le_succ n))
    (fun he => Nat.succ_ne_self n (F.ρ_inj he)) hleΓΔ hcΔ hz honly hsub
    (WFF.mono (le₁.diaIn (F.wit n)) χ)
  -- the hypothesis for that hole formula, lifted to the stage of `χ`
  have hHmem := hhyp m hm (Subst.packType (laterList F.τ F.ρ n k))
    (WFF.retHole (F.fresh_ctx (Nat.le_succ n)) hcΔ hz honly hsub (WFF.mono (le₁.diaIn (F.wit n)) χ))
  have hlift : ((m, n + 1) : ℕ × ℕ) ≤ (m, n + 1 + k) := Prod.mk_le_mk.mpr ⟨le_rfl, by omega⟩
  have hHlift := (hmcs.mem_lift_iff hlift).mpr hHmem
  -- what the instance says, transported to the stage of `χ`
  have key₂ := congrArg (WFF.mono le₂) key
  have hz₂ : ∀ z ∈ laterList F.τ F.ρ n k,
      (F.ctx (m, n + 1 + k)).ref (.root (.free z.2)) = some z.1 :=
    fun z hzm => le₂.ref ((Ctx.le_insert hcΔ.root (.VTypeDia A)).ref (hz z hzm))
  rw [WFF.mono_instantiate le₂ _ Ctx.NoSlots.slots _, Term.mono_mono, WFF.mono_mono,
    Term.mono_tuple _ _ _ hz₂, WFF.mono_imp,
    WFF.mono_realiseAt hT le₂ _ (hτ ▸ ref_wit hlt) _ fr_wit,
    Term.mono_mono, Term.mono_mono, WFF.mono_mono, WFF.mono_refl, WFF.mono_dia,
    WFF.mono_mono, WFF.mono_refl] at key₂
  -- the hypothesis, as one weakening of the body
  rw [show StageSys.lift hlift = WFF.mono (F.sys.le hlift) from rfl, WFF.mono_mono] at hHlift
  -- modus ponens on the instance
  refine hmcs.closed (Theory.Derives.mp ?_ (Theory.Derives.of_mem
    (StageSys.mem_atStage_self hmem)))
  rw [← key₂]
  obtain ⟨Δ₀, hΔ₀, p⟩ := Theory.Derives.of_mem (StageSys.mem_atStage_self hHlift)
  exact ⟨Δ₀, hΔ₀, p.map (Proof.all_elim _ (Term.tuple (laterList F.τ F.ρ n k) hz₂))⟩

end WorldLang

end V12M
