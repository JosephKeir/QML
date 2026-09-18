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

/-- A `T_dia` hypothesis carried along equalities of its context, its two names and its target:
    all of them are equalities, so the weakenings collapse. -/
theorem WFF.retHyp_transport {σ : Signature} {Γ Γ' Δ : Ctx} [Γ.NoSlots] [Γ'.NoSlots]
    (hT : ModalSys.T = true) {A : VarType} {a : Ann A} (t : Term σ Γ A a) {c c' y y' : ℕ}
    (hΓ : Γ = Γ') (hcc : c = c') (hyy : y = y')
    (hc : Γ.RootFresh (.free c)) (hy : Γ.RootFresh (.free y)) (hyc : y ≠ c)
    (hc' : Γ'.RootFresh (.free c')) (hy' : Γ'.RootFresh (.free y')) (hyc' : y' ≠ c')
    (B : VarType) (ψ : WFF σ ((Γ.insert (.free y) B).boxIn.insert (.bnd 0) A) 1)
    (ht : Term σ Γ' A a) (hteq : ht = Term.mono (Ctx.le_of_eq hΓ) t)
    (hΔ : Γ'.insert (.free c') (.VTypeDia A) = Δ)
    (hle : (Γ.insert (.free c) (.VTypeDia A)).Le Δ)
    (hψ : ((Γ.insert (.free y) B).boxIn.insert (.bnd 0) A).Le
      ((Γ'.insert (.free y') B).boxIn.insert (.bnd 0) A)) :
    WFF.mono hle (WFF.retHyp hT t c y hc hy hyc B ψ) =
      WFF.mono (Ctx.le_of_eq hΔ) (WFF.retHyp hT ht c' y' hc' hy' hyc' B (WFF.mono hψ ψ)) := by
  subst hΓ
  subst hcc
  subst hyy
  subst hΔ
  subst hteq
  rw [Term.mono_refl, WFF.mono_refl, WFF.mono_refl, WFF.mono_refl]

/-- A `T_dia` hypothesis does not depend on how its two names are written. -/
theorem WFF.retHyp_congr {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true)
    {A : VarType} {a : Ann A} (t : Term σ Γ A a) {c c' y y' : ℕ} (hc₀ : c = c') (hy₀ : y = y')
    (hc : Γ.RootFresh (.free c)) (hy : Γ.RootFresh (.free y)) (hyc : y ≠ c)
    (hc' : Γ.RootFresh (.free c')) (hy' : Γ.RootFresh (.free y')) (hyc' : y' ≠ c')
    (B : VarType) (ψ : WFF σ ((Γ.insert (.free y) B).boxIn.insert (.bnd 0) A) 1)
    (hΓ : (Γ.insert (.free c) (.VTypeDia A)).Le (Γ.insert (.free c') (.VTypeDia A)))
    (hψ : ((Γ.insert (.free y) B).boxIn.insert (.bnd 0) A).Le
      ((Γ.insert (.free y') B).boxIn.insert (.bnd 0) A)) :
    WFF.mono hΓ (WFF.retHyp hT t c y hc hy hyc B ψ) =
      WFF.retHyp hT t c' y' hc' hy' hyc' B (WFF.mono hψ ψ) := by
  subst hc₀
  subst hy₀
  rw [WFF.mono_refl, WFF.mono_refl]

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

/-! ## The chain's hypotheses, in the finished language -/

section Chain

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms] (L : WorldLang)
  {S₀ : Set ((L.pre []).Sentence σ)}

/-- Step `n` of the chain declared a strong T witness: the formula it chose called for no witness
    of its own, so the step made the `retStep` declaration. -/
def IsRet (S₀ : Set ((L.pre []).Sentence σ)) (n : ℕ) : Prop :=
  (∀ (A : VarType) (ψ : WFF σ ((L.ctxL (decM n) (L.chain S₀ n).l).insert (.bnd 0) A) 1),
      L.choice n (L.chain S₀ n) ≠ .ex A ψ) ∧
    ∀ (A : VarType) (ψ : WFF σ ((L.ctxL (decM n) (L.chain S₀ n).l).insert (.bnd 0) A) 1),
      L.choice n (L.chain S₀ n) ≠ .imp (.all A ψ) .bot

variable {L}

/-- At such a step the declaration is the one `retStep` makes. -/
theorem witStep_eq_retStep {n : ℕ} (hret : IsRet L S₀ n) :
    L.witStep (decM n) (L.chain S₀ n).l
        (L.termQ (σ := σ) n (L.chain S₀ n).l) (L.choice n (L.chain S₀ n)) =
      L.retStep (decM n) (L.chain S₀ n).l (L.termQ (σ := σ) n (L.chain S₀ n).l) := by
  unfold WorldLang.witStep
  split
  · next A ψ h => exact absurd h (hret.1 A ψ)
  · next A ψ h => exact absurd h (hret.2 A ψ)
  · rfl

/-- At a strong T step the witness is declared at the `◇` of the enumerated term's type. -/
theorem finalτ_of_isRet (hT : ModalSys.T = true) (hTS : ModalSys.TStrong = true) {n : ℕ}
    (hret : IsRet L S₀ n) :
    L.finalτ S₀ n = .VTypeDia (L.termQ (σ := σ) n (L.chain S₀ n).l).1 := by
  unfold WorldLang.finalτ
  rw [witStep_eq_retStep hret,
    show L.retStep (decM n) (L.chain S₀ n).l (L.termQ (σ := σ) n (L.chain S₀ n).l) =
    ⟨.VTypeDia (L.termQ (σ := σ) n (L.chain S₀ n).l).1,
      L.retSet hT (L.chain S₀ n).l (decM n) (L.termQ (σ := σ) n (L.chain S₀ n).l).2.2⟩ from
    dif_pos ⟨hT, hTS⟩]

/-- ⭐The hypotheses the chain added for a strong T witness, as sentences of the finished
    theory. -/
theorem retHyp_mem_retSet (hT : ModalSys.T = true) {n : ℕ} (m : ℕ) (hm : decM n ≤ m) (B : VarType)
    (ψ : WFF σ (((L.ctxL m (L.chain S₀ n).l).insert
      (.free (L.ρ ((L.chain S₀ n).l.length + 1))) B).boxIn.insert (.bnd 0)
        (L.termQ (σ := σ) n (L.chain S₀ n).l).1) 1) :
    (⟨m, WFF.retHyp hT (Term.mono (L.ctxL_base_le hm (L.chain S₀ n).l)
        (L.termQ (σ := σ) n (L.chain S₀ n).l).2.2)
        (L.ρ (L.chain S₀ n).l.length) (L.ρ ((L.chain S₀ n).l.length + 1))
        (L.ctxL_fresh le_rfl) (L.ctxL_fresh (Nat.le_succ _)) (L.ρ_succ_ne _) B ψ⟩ :
      (L.pre (.VTypeDia (L.termQ (σ := σ) n (L.chain S₀ n).l).1 :: (L.chain S₀ n).l)).Sentence σ) ∈
      L.retSet hT (L.chain S₀ n).l (decM n) (L.termQ (σ := σ) n (L.chain S₀ n).l).2.2 :=
  ⟨m, hm, B, ψ, rfl⟩

/-- ⭐At a strong T step, every hypothesis the chain adds for the enumerated term is in the step's
    theory.  Stated with the step's declaration left stuck, so that the match can be split. -/
theorem step_ret (hT : ModalSys.T = true) (hTS : ModalSys.TStrong = true) {n : ℕ}
    (hret : IsRet L S₀ n) (m : ℕ) (hm : decM n ≤ m) (B : VarType)
    (ψ : WFF σ (((L.ctxL m (L.chain S₀ n).l).insert
      (.free (L.ρ ((L.chain S₀ n).l.length + 1))) B).boxIn.insert (.bnd 0)
        (L.termQ (σ := σ) n (L.chain S₀ n).l).1) 1)
    (hEq : (L.ctxL m (L.chain S₀ n).l).insert (.free (L.ρ (L.chain S₀ n).l.length))
        (.VTypeDia (L.termQ (σ := σ) n (L.chain S₀ n).l).1) =
      L.ctxL m (L.chain S₀ (n + 1)).l) :
    (⟨m, WFF.mono (Ctx.le_of_eq hEq)
        (WFF.retHyp hT (Term.mono (L.ctxL_base_le hm (L.chain S₀ n).l)
          (L.termQ (σ := σ) n (L.chain S₀ n).l).2.2)
          (L.ρ (L.chain S₀ n).l.length) (L.ρ ((L.chain S₀ n).l.length + 1))
          (L.ctxL_fresh le_rfl) (L.ctxL_fresh (Nat.le_succ _)) (L.ρ_succ_ne _) B ψ)⟩ :
      (L.pre (L.chain S₀ (n + 1)).l).Sentence σ) ∈ (L.chain S₀ (n + 1)).S := by
  refine Set.mem_union_right _ ?_
  -- the hypothesis, as a statement about the step's declaration, transported twice
  have base : ∀ hEq'' : (L.ctxL m (L.chain S₀ n).l).insert (.free (L.ρ (L.chain S₀ n).l.length))
        (.VTypeDia (L.termQ (σ := σ) n (L.chain S₀ n).l).1) =
      L.ctxL m ((⟨.VTypeDia (L.termQ (σ := σ) n (L.chain S₀ n).l).1,
        L.retSet hT (L.chain S₀ n).l (decM n) (L.termQ (σ := σ) n (L.chain S₀ n).l).2.2⟩ :
          Σ A : VarType, Set ((L.pre (A :: (L.chain S₀ n).l)).Sentence σ)).1 :: (L.chain S₀ n).l),
      (⟨m, WFF.mono (Ctx.le_of_eq hEq'')
          (WFF.retHyp hT (Term.mono (L.ctxL_base_le hm (L.chain S₀ n).l)
            (L.termQ (σ := σ) n (L.chain S₀ n).l).2.2)
            (L.ρ (L.chain S₀ n).l.length) (L.ρ ((L.chain S₀ n).l.length + 1))
            (L.ctxL_fresh le_rfl) (L.ctxL_fresh (Nat.le_succ _)) (L.ρ_succ_ne _) B ψ)⟩ :
        (L.pre ((⟨.VTypeDia (L.termQ (σ := σ) n (L.chain S₀ n).l).1,
          L.retSet hT (L.chain S₀ n).l (decM n)
            (L.termQ (σ := σ) n (L.chain S₀ n).l).2.2⟩ :
              Σ A : VarType, Set ((L.pre (A :: (L.chain S₀ n).l)).Sentence σ)).1 ::
                (L.chain S₀ n).l)).Sentence σ) ∈
        (⟨.VTypeDia (L.termQ (σ := σ) n (L.chain S₀ n).l).1,
          L.retSet hT (L.chain S₀ n).l (decM n)
            (L.termQ (σ := σ) n (L.chain S₀ n).l).2.2⟩ :
              Σ A : VarType, Set ((L.pre (A :: (L.chain S₀ n).l)).Sentence σ)).2 := by
    intro hEq''
    rw [WFF.mono_refl]
    exact ⟨m, hm, B, ψ, rfl⟩
  exact Eq.subst
    (motive := fun X : Σ A : VarType, Set ((L.pre (A :: (L.chain S₀ n).l)).Sentence σ) =>
      ∀ hEq'' : (L.ctxL m (L.chain S₀ n).l).insert (.free (L.ρ (L.chain S₀ n).l.length))
          (.VTypeDia (L.termQ (σ := σ) n (L.chain S₀ n).l).1) =
        L.ctxL m (X.1 :: (L.chain S₀ n).l),
        (⟨m, WFF.mono (Ctx.le_of_eq hEq'')
            (WFF.retHyp hT (Term.mono (L.ctxL_base_le hm (L.chain S₀ n).l)
              (L.termQ (σ := σ) n (L.chain S₀ n).l).2.2)
              (L.ρ (L.chain S₀ n).l.length) (L.ρ ((L.chain S₀ n).l.length + 1))
              (L.ctxL_fresh le_rfl) (L.ctxL_fresh (Nat.le_succ _)) (L.ρ_succ_ne _) B ψ)⟩ :
          (L.pre (X.1 :: (L.chain S₀ n).l)).Sentence σ) ∈ X.2)
    ((dif_pos ⟨hT, hTS⟩ : L.retStep (decM n) (L.chain S₀ n).l
        (L.termQ (σ := σ) n (L.chain S₀ n).l) = ⟨_, _⟩).symm.trans
      (witStep_eq_retStep hret).symm) base hEq
theorem ctxL_eq_final (S₀ : Set ((L.pre []).Sentence σ)) (m j : ℕ) :
    L.ctxL m (L.chain S₀ j).l = (L.final S₀).ctx (m, j) := (L.final_ctx S₀ m j).symm

/-- At a strong T step the next stage declares the witness at the `◇` of the term's type. -/
theorem ctx_succ_of_isRet (hT : ModalSys.T = true) (hTS : ModalSys.TStrong = true) {n : ℕ}
    (hret : IsRet L S₀ n) (m : ℕ) :
    ((L.final S₀).ctx (m, n)).insert (.free (L.ρ n))
        (.VTypeDia (L.termQ (σ := σ) n (L.chain S₀ n).l).1) = (L.final S₀).ctx (m, n + 1) := by
  rw [WorldLang.ctx_succ, show (L.final S₀).τ n =
    .VTypeDia (L.termQ (σ := σ) n (L.chain S₀ n).l).1 from finalτ_of_isRet hT hTS hret]
  rfl

/-- ⭐The chain's hypotheses for a strong T witness, as the finished theory's sentences: this is
    what `spec_of_retHyps` asks for. -/
theorem hhyp_of_isRet (hT : ModalSys.T = true) (hTS : ModalSys.TStrong = true) {n : ℕ}
    (hret : IsRet L S₀ n) (m : ℕ) (hm : decM n ≤ m) (B : VarType)
    (ψ : WFF σ (((((L.final S₀).ctx (m, n))).insert (.free (L.ρ (n + 1))) B).boxIn.insert
      (.bnd 0) (L.termQ (σ := σ) n (L.chain S₀ n).l).1) 1) :
    (⟨(m, n + 1), WFF.mono
        (Ctx.le_of_eq (ctx_succ_of_isRet hT hTS hret m))
        (WFF.retHyp hT
          (Term.mono ((L.final S₀).ctx_le (Prod.mk_le_mk.mpr ⟨hm, le_rfl⟩))
            (Term.mono (Ctx.le_of_eq (ctxL_eq_final S₀ (decM n) n))
              (L.termQ (σ := σ) n (L.chain S₀ n).l).2.2))
          (L.ρ n) (L.ρ (n + 1)) ((L.final S₀).fresh_ctx le_rfl)
          ((L.final S₀).fresh_ctx (Nat.le_succ n))
          (fun he => Nat.succ_ne_self n (L.ρ_inj he)) B ψ)⟩ :
      (L.final S₀).sys.Sentence σ) ∈ L.finalT S₀ := by
  refine ⟨n + 1, le_rfl, ?_⟩
  have hlen : (L.chain S₀ n).l.length = n := length_chain S₀ n
  have hctx : (L.final S₀).ctx (m, n) = L.ctxL m (L.chain S₀ n).l := L.final_ctx S₀ m n
  have hname : L.ρ n = L.ρ (L.chain S₀ n).l.length := by rw [hlen]
  have hnameS : L.ρ (n + 1) = L.ρ ((L.chain S₀ n).l.length + 1) := by rw [hlen]
  have hEq' : (L.ctxL m (L.chain S₀ n).l).insert (.free (L.ρ (L.chain S₀ n).l.length))
      (.VTypeDia (L.termQ (σ := σ) n (L.chain S₀ n).l).1) = L.ctxL m (L.chain S₀ (n + 1)).l := by
    rw [← hname, ← hctx]
    exact (ctx_succ_of_isRet hT hTS hret m).trans (L.final_ctx S₀ m (n + 1))
  have hψle : ((((L.final S₀).ctx (m, n)).insert (.free (L.ρ (n + 1))) B).boxIn.insert (.bnd 0)
        (L.termQ (σ := σ) n (L.chain S₀ n).l).1).Le
      (((L.ctxL m (L.chain S₀ n).l).insert (.free (L.ρ ((L.chain S₀ n).l.length + 1)))
        B).boxIn.insert (.bnd 0) (L.termQ (σ := σ) n (L.chain S₀ n).l).1) :=
    Ctx.le_of_eq (by rw [hctx, hnameS])
  refine Eq.mp (congrArg (fun φ => (⟨m, φ⟩ : (L.pre (L.chain S₀ (n + 1)).l).Sentence σ) ∈
    (L.chain S₀ (n + 1)).S) ?_) (step_ret hT hTS hret m hm B (WFF.mono hψle ψ) hEq')
  rw [WFF.mono_mono]
  refine (WFF.retHyp_transport hT _ hctx hname hnameS ((L.final S₀).fresh_ctx le_rfl)
    ((L.final S₀).fresh_ctx (Nat.le_succ n)) (fun he => Nat.succ_ne_self n (L.ρ_inj he))
    (L.ctxL_fresh le_rfl) (L.ctxL_fresh (Nat.le_succ _)) (L.ρ_succ_ne _) B ψ
    (Term.mono (L.ctxL_base_le hm (L.chain S₀ n).l) (L.termQ (σ := σ) n (L.chain S₀ n).l).2.2)
    ?_ hEq' _ hψle).symm
  rw [Term.mono_mono, Term.mono_mono]


/-! ## The realisation a strong T step provides -/

/-- ⭐The witness declared at a strong T step is a realised one: the term it was declared for is
    its realisation. -/
noncomputable def retDatum (hT : ModalSys.T = true) (hTS : ModalSys.TStrong = true) {n : ℕ}
    (hret : IsRet L S₀ n) (hS₀ : StageSys.Consistent S₀) :
    Canon.RealDatum σ (L.final S₀) (L.finalT S₀) (L.ρ n) where
  hT := hT
  hS := hTS
  A := (L.termQ (σ := σ) n (L.chain S₀ n).l).1
  i₀ := (decM n, n)
  a₀ := (L.termQ (σ := σ) n (L.chain S₀ n).l).2.1
  t₀ := Term.mono (Ctx.le_of_eq (ctxL_eq_final S₀ (decM n) n))
    (L.termQ (σ := σ) n (L.chain S₀ n).l).2.2
  hdecl := fun i hlt => by
    obtain ⟨m, j⟩ := i
    exact (finalτ_of_isRet hT hTS hret) ▸ ref_wit hlt
  hfr := fun i => by
    obtain ⟨m, j⟩ := i
    exact fr_wit (F := L.final S₀) (n := n) (m := m) (j := j)
  hstage := fun i hi => by
    obtain ⟨m, j⟩ := i
    by_contra hle
    obtain ⟨Y, hY⟩ := hi
    have hnone : ((L.final S₀).ctx (m, j)).ref (.root (.free (L.ρ n))) = none := by
      rw [Ctx.ref_nonproj _ (show (VarSymb.root (Root.free (L.ρ n))).lastProj = false from rfl)]
      exact (L.final S₀).fresh_ctx (Nat.le_of_not_lt hle) _ rfl
    rw [hnone] at hY
    cases hY
  spec := fun i hi hlt χ hmem =>
    spec_of_retHyps (WorldLang.finalT_isMCS hS₀) hT (finalτ_of_isRet hT hTS hret) _
      (hhyp_of_isRet hT hTS hret) hi hlt χ hmem

open Classical in
/-- ⭐The realisation the finished language names at each of its roots: the one the chain's strong
    T step for that constant provides, if it made one.  The name determines the step (`ρ` is
    injective), so this is a choice in name only. -/
noncomputable def chainReal (hS₀ : StageSys.Consistent S₀) (c : ℕ) :
    Option (Canon.RealDatum σ (L.final S₀) (L.finalT S₀) c) :=
  if h : ∃ n, ((ModalSys.T = true ∧ ModalSys.TStrong = true) ∧ IsRet L S₀ n) ∧ L.ρ n = c then
    some (h.choose_spec.2 ▸
      retDatum h.choose_spec.1.1.1 h.choose_spec.1.1.2 h.choose_spec.1.2 hS₀)
  else none


/-! ## Every term is realised -/

omit [Countable σ.RelSyms] in
/-- The term enumeration does not depend on how the list of own types is written (the mirror of
    `enumF_mono_congr`). -/
theorem enumT_mono_congr (m k : ℕ) {X : Ctx} :
    ∀ {l l' : List VarType} (_ : l = l') (h : (L.ctxL m l).Le X) (h' : (L.ctxL m l').Le X),
      (⟨_, _, Term.mono h (enumT (σ := σ) (L.ctxL m l) k).2.2⟩ :
          Σ A : VarType, Σ a : Ann A, Term σ X A a) =
        ⟨_, _, Term.mono h' (enumT (σ := σ) (L.ctxL m l') k).2.2⟩
  | _, _, rfl, _, _ => rfl

/-- The term read at step `n` is the enumerated term at its own stage, lifted (the mirror of
    `query_chain`). -/
theorem termQ_chain (S₀ : Set ((L.pre []).Sentence σ)) (n : ℕ)
    (h₀ : (L.ctxL (decM n) (L.chain S₀ (decJ n)).l).Le (L.ctxL (decM n) (L.chain S₀ n).l)) :
    L.termQ (σ := σ) n (L.chain S₀ n).l =
      ⟨_, _, Term.mono h₀
        (enumT (σ := σ) (L.ctxL (decM n) (L.chain S₀ (decJ n)).l) (decKT n)).2.2⟩ :=
  enumT_mono_congr (decM n) (decKT n) (drop_chain S₀ (decJ_le n)) _ _

/-- A step whose formula is `⊤` declares a strong T witness: neither `⊤` nor its negation calls
    for a witness of its own. -/
theorem isRet_of_top {n : ℕ}
    (htop : enumF (σ := σ) (L.ctxL (decM n) (L.chain S₀ (decJ n)).l) (decKF n) = .top) :
    IsRet L S₀ n := by
  have hq : L.query (σ := σ) n (L.chain S₀ n).l = .top := by
    rw [query_chain S₀ n (chain_le S₀ (decJ_le n) (decM n)), htop]
    rfl
  refine ⟨fun A ψ => ?_, fun A ψ => ?_⟩ <;>
    rcases choice_cases (L := L) n (L.chain S₀ n) with hc | hc <;> rw [hc, hq]
  · exact fun h => by cases h
  · exact fun h => by cases h
  · exact fun h => by cases h
  · intro h
    injection h
    rename_i h₁ h₂ h₃
    cases h₂


/-- ⭐Every term at every stage is the term some strong T step was declared for: the step that
    enumerates it and reads `⊤`. -/
theorem exists_isRet_term (m j : ℕ) {A : VarType} {a : Ann A}
    (t : Term σ (L.ctxL m (L.chain S₀ j).l) A a) :
    ∃ n, IsRet L S₀ n ∧ decM n = m ∧ decJ n = j ∧
      ∃ hle : (L.ctxL m (L.chain S₀ j).l).Le (L.ctxL (decM n) (L.chain S₀ n).l),
        L.termQ (σ := σ) n (L.chain S₀ n).l = ⟨A, a, Term.mono hle t⟩ := by
  obtain ⟨k', hk'⟩ := enumT_surjective (σ := σ) (L.ctxL m (L.chain S₀ j).l) ⟨A, a, t⟩
  obtain ⟨kt, hkt⟩ := enumF_surjective (σ := σ) (L.ctxL m (L.chain S₀ j).l) .top
  obtain ⟨n, hj, hm, hkf, hkT⟩ := exists_decFT m j kt k'
  subst hm
  subst hj
  refine ⟨n, isRet_of_top (by rw [hkf]; exact hkt), rfl, rfl,
    chain_le S₀ (decJ_le n) (decM n), ?_⟩
  rw [termQ_chain S₀ n (chain_le S₀ (decJ_le n) (decM n)), hkT, hk']


/-- The data a strong T step provides, read off under a renaming of its witness. -/
theorem retDatum_fields (hT : ModalSys.T = true) (hTS : ModalSys.TStrong = true) {n c : ℕ}
    (hret : IsRet L S₀ n) (hS₀ : StageSys.Consistent S₀) (hc : L.ρ n = c) :
    (⟨(hc ▸ retDatum hT hTS hret hS₀ :
            Canon.RealDatum σ (L.final S₀) (L.finalT S₀) c).A,
        (hc ▸ retDatum hT hTS hret hS₀ :
            Canon.RealDatum σ (L.final S₀) (L.finalT S₀) c).i₀,
        (hc ▸ retDatum hT hTS hret hS₀ :
            Canon.RealDatum σ (L.final S₀) (L.finalT S₀) c).a₀,
        (hc ▸ retDatum hT hTS hret hS₀ :
            Canon.RealDatum σ (L.final S₀) (L.finalT S₀) c).t₀⟩ :
        Σ (A : VarType) (i : ℕ × ℕ) (a : Ann A), Term σ ((L.final S₀).ctx i) A a) =
      ⟨(L.termQ (σ := σ) n (L.chain S₀ n).l).1, (decM n, n),
        (L.termQ (σ := σ) n (L.chain S₀ n).l).2.1,
        Term.mono (Ctx.le_of_eq (ctxL_eq_final S₀ (decM n) n))
          (L.termQ (σ := σ) n (L.chain S₀ n).l).2.2⟩ := by
  subst hc
  rfl

/-- ⭐What a world names at the witness of a strong T step: that step's own data. -/
theorem chainReal_ret (hT : ModalSys.T = true) (hTS : ModalSys.TStrong = true)
    (hS₀ : StageSys.Consistent S₀) {n : ℕ} (hret : IsRet L S₀ n) :
    ∃ d : Canon.RealDatum σ (L.final S₀) (L.finalT S₀) (L.ρ n),
      L.chainReal hS₀ (L.ρ n) = some d ∧
      (⟨d.A, d.i₀, d.a₀, d.t₀⟩ :
          Σ (A : VarType) (i : ℕ × ℕ) (a : Ann A), Term σ ((L.final S₀).ctx i) A a) =
        ⟨(L.termQ (σ := σ) n (L.chain S₀ n).l).1, (decM n, n),
          (L.termQ (σ := σ) n (L.chain S₀ n).l).2.1,
          Term.mono (Ctx.le_of_eq (ctxL_eq_final S₀ (decM n) n))
            (L.termQ (σ := σ) n (L.chain S₀ n).l).2.2⟩ := by
  have h : ∃ n', ((ModalSys.T = true ∧ ModalSys.TStrong = true) ∧ IsRet L S₀ n') ∧
      L.ρ n' = L.ρ n := ⟨n, ⟨⟨hT, hTS⟩, hret⟩, rfl⟩
  have hch : h.choose = n := L.ρ_inj h.choose_spec.2
  refine ⟨_, dif_pos h, ?_⟩
  conv_rhs => rw [← hch]
  exact retDatum_fields h.choose_spec.1.1.1 h.choose_spec.1.1.2 h.choose_spec.1.2 hS₀
    h.choose_spec.2

end Chain

end WorldLang

end V12M
