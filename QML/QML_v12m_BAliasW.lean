import QML.QML_v12m_BPackW
import QML.QML_v12m_BAlias

/-!
# QML v12m — strong B: aliases persist

An alias `y` of `t` is given its alias set at one stage: `ψ(y) ↔ ψ(t)` for the slot formulas `ψ`
over that stage's context (`QML_v12m_BAlias`).  Attestation (`DTerm.Rel`) asks for
interchangeability at **every** later stage, whose formulas mention roots born since.  They are
reached without changing the alias set (docs §11.20):

* a later slot formula `χ` is packed into a hole formula `H` (`packRoots`), so `χ(v) = H(⟨v, tup⟩)`;
* the closed hole formula `K(⟨v, w⟩) := ∀z (H(⟨v, z⟩) ↔ H(⟨w, z⟩))` (`tailK`) is true of every
  diagonal pair (`provable_tailK_diag`);
* so `ψ(v) := K(⟨v, t⟩)` (`tailψ`) is in the alias set with `ψ(t)` a theorem, the alias gives
  `ψ(y)`, and `∀`-elimination at the tuple of the later stage's roots gives `χ(y) ↔ χ(t)`
  (⭐`alias_interch`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

section Tail

variable {A T : VarType}

/-- The context of the tail formula's body: the pair's hole, and the bound tail. -/
abbrev pairCtx2 (A T : VarType) : Ctx :=
  (Ctx.empty.insert (.bnd 0) (.VTypeProd A A)).insert (.bnd 1) T

omit [ModalSys] in
theorem pairCtx2_slots : (pairCtx2 A T).SlotsFrom 2 :=
  (Ctx.slotsFrom_empty.insert _).insert T

theorem pairCtx2_ref_hole :
    (pairCtx2 A T).ref (.root (.bnd 0)) = some (.VTypeProd A A) :=
  (Ctx.le_insert (Ctx.slotsFrom_empty.insert (.VTypeProd A A)).root T).ref
    (Ctx.ref_insert_root _ _ _)

theorem pairCtx2_ref_tail : (pairCtx2 A T).ref (.root (.bnd 1)) = some T :=
  Ctx.ref_insert_root _ _ _

/-- One side of the tail formula: the hole formula at a component of the pair and the tail. -/
def tailSide (H : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A T)) 1) (s : Step)
    (hs : (pairCtx2 A T).ref (.step (.root (.bnd 0)) s) = some A) : WFF σ (pairCtx2 A T) 2 :=
  WFF.holeAt pairCtx2_slots
    (Term.pair (Term.eta (.step (.root (.bnd 0)) s) A hs)
      (Term.eta (.root (.bnd 1)) T pairCtx2_ref_tail)) H

/-- ⭐`K(⟨v, w⟩) := ∀z (H(⟨v, z⟩) ↔ H(⟨w, z⟩))`, closed apart from its hole. -/
def tailK (H : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A T)) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A A)) 1 :=
  .all T (.and
    (.imp (tailSide H .fst (Ctx.ref_fst_of pairCtx2_ref_hole))
      (tailSide H .snd (Ctx.ref_snd_of pairCtx2_ref_hole)))
    (.imp (tailSide H .snd (Ctx.ref_snd_of pairCtx2_ref_hole))
      (tailSide H .fst (Ctx.ref_fst_of pairCtx2_ref_hole))))

/-- A value and the bound tail, as the pair `H` is read at, one binder in. -/
def tailAt {Γ : Ctx} [Γ.NoSlots] {a : Ann A} (v : Term σ Γ A a)
    (H : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A T)) 1) : WFF σ (Γ.insert (.bnd 0) T) 1 :=
  WFF.holeAt ((Ctx.NoSlots.slots (Γ := Γ)).insert T)
    (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root T) v)
      (Term.eta (.root (.bnd 0)) T (Ctx.ref_insert_root Γ (.bnd 0) T))) H

/-- A side, substituted: the pair's component goes to its entry, the tail to its address. -/
theorem subst_tailSide {Δ : Ctx} {ι : VarSymb → VarSymb} (θ : Subst σ Δ)
    (hθ : Subst.Ok (pairCtx2 A T) θ) (hc : Subst.Coh ι (pairCtx2 A T) θ) {d' : ℕ}
    (hΔ : Δ.SlotsFrom d') (H : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A T)) 1) (s : Step)
    (hs : (pairCtx2 A T).ref (.step (.root (.bnd 0)) s) = some A) {c : Ann A}
    (u : Term σ Δ A c) (hu : θ.at (.step (.root (.bnd 0)) s) = .tm u) (z : VarSymb)
    (hz' : Δ.ref z = some T) (hz : θ.at (.root (.bnd 1)) = .ren z) :
    WFF.subst ι θ hθ hc pairCtx2_slots hΔ (tailSide H s hs) =
      WFF.holeAt hΔ (Term.pair u (Term.eta z T hz')) H := by
  unfold tailSide
  rw [WFF.subst_holeAt]
  exact WFF.holeAt_congr _ (sig_pair (Term.subst_eta_tm θ hθ hc A _ hs u hu)
    (Term.subst_eta_renAt θ hθ hc T _ z _ hz' hz)) H

/-- ⭐`K` read at a pair: the two sides, under the binder. -/
theorem holeAt_tailK {Γ : Ctx} [Γ.NoSlots] {a b : Ann A} (v : Term σ Γ A a) (w : Term σ Γ A b)
    (H : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A T)) 1) :
    WFF.holeAt Ctx.NoSlots.slots (Term.pair v w) (tailK H) =
      .all T (.and (.imp (tailAt v H) (tailAt w H)) (.imp (tailAt w H) (tailAt v H))) := by
  unfold WFF.holeAt tailK tailAt
  simp only [WFF.subst]
  rw [subst_tailSide (s := .fst) (u := Term.mono (Ctx.le_insert
      (Ctx.NoSlots.slots (Γ := Γ)).root T) v) (z := .root (.bnd 0))
      (hz' := Ctx.ref_insert_root Γ (.bnd 0) T),
    subst_tailSide (s := .snd) (u := Term.mono (Ctx.le_insert
      (Ctx.NoSlots.slots (Γ := Γ)).root T) w) (z := .root (.bnd 0))
      (hz' := Ctx.ref_insert_root Γ (.bnd 0) T)]
  all_goals rfl

/-- A term weakened past a slot, then given a value for the slot, is itself. -/
theorem subst_single_mono_tm {Γ : Ctx} [Γ.NoSlots] {U : VarType} {c : Ann U}
    (e : Term σ Γ U c) {B : VarType} {b : Ann B} (s : Term σ Γ B b) :
    (⟨_, Term.subst (Subst.singleIdx (.bnd 0) (.tm e)) (Subst.single (.bnd 0) (.tm e))
        (Subst.ok_single (Ctx.Le.refl Γ) rfl)
        (Subst.coh_single ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0))
          (Ctx.Le.refl Γ) rfl)
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root U) s)⟩ :
      Σ c', Term σ Γ B c') = ⟨b, s⟩ := by
  rw [Term.subst_mono]
  exact (Term.subst_ren (Ctx.Le.refl _) _ _ _ (fun _ _ hv => Subst.single_at_ne
    (Ctx.ref_rt_ne ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) hv)) s).trans
    (congrArg (Sigma.mk _) (Term.mono_refl _ s))

/-- The tail read at the tuple: `H` at the value and the tuple. -/
theorem instantiate_tailAt {Γ : Ctx} [Γ.NoSlots] {a : Ann A} (v : Term σ Γ A a)
    (H : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A T)) 1) {c : Ann T} (u : Term σ Γ T c) :
    WFF.instantiate Ctx.NoSlots.slots u (tailAt v H) =
      WFF.holeAt Ctx.NoSlots.slots (Term.pair v u) H := by
  unfold tailAt WFF.instantiate WFF.substRoot
  rw [WFF.subst_holeAt]
  refine WFF.holeAt_congr _ (sig_pair (subst_single_mono_tm u v) ?_) H
  exact Term.subst_eta_tm _ _ _ T _ _ u
    (by change Subst.single _ _ (.root (.bnd 0)) = _; exact if_pos rfl)

/-- ⭐**`K` holds of every diagonal pair**: both sides are one formula. -/
def provable_tailK_diag {l : List VarType} {a : Ann A} (w : Term σ (ctxOf l) A a)
    (H : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A T)) 1) :
    Proof σ (ctxOf l) [] (WFF.holeAt Ctx.NoSlots.slots (Term.pair w w) (tailK H)) := by
  rw [holeAt_tailK, ← WFF.bindFree_openFree l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots
    (WFF.and (WFF.imp (tailAt w H) (tailAt w H)) (WFF.imp (tailAt w H) (tailAt w H)))]
  refine Proof.all_intro l.length T (ctxOf_fresh le_rfl) ?_
  change Proof σ _ [] (WFF.and
    (WFF.imp (WFF.openFree l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots (tailAt w H))
      (WFF.openFree l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots (tailAt w H)))
    (WFF.imp (WFF.openFree l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots (tailAt w H))
      (WFF.openFree l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots (tailAt w H))))
  exact .and_intro (.imp_intro (.lookup List.mem_cons_self))
    (.imp_intro (.lookup List.mem_cons_self))

/-- ⭐The tail formula of a value `t`: `ψ(v) := K(⟨v, t⟩)`. -/
def tailψ {Γ : Ctx} [Γ.NoSlots] {a : Ann A} (t : Term σ Γ A a)
    (H : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A T)) 1) : WFF σ (Γ.insert (.bnd 0) A) 1 :=
  WFF.holeAt ((Ctx.NoSlots.slots (Γ := Γ)).insert A)
    (Term.pair (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root Γ (.bnd 0) A))
      (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root A) t)) (tailK H)

/-- The tail formula, weakened and instantiated: `K` at the value and `t`. -/
theorem instantiate_tailψ {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ') {a : Ann A}
    (t : Term σ Γ A a) (H : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A T)) 1) {c : Ann A}
    (s : Term σ Γ' A c) :
    WFF.instantiate Ctx.NoSlots.slots s (WFF.mono (h.insert (.bnd 0) A) (tailψ t H)) =
      WFF.holeAt Ctx.NoSlots.slots (Term.pair s (Term.mono h t)) (tailK H) := by
  unfold tailψ
  rw [WFF.mono_holeAt _ _ ((Ctx.NoSlots.slots (Γ := Γ')).insert A)]
  unfold WFF.instantiate WFF.substRoot
  rw [WFF.subst_holeAt]
  refine WFF.holeAt_congr _ (sig_pair ?_ ?_) _
  · rw [Term.mono_eta]
    exact Term.subst_eta_tm _ _ _ A _ _ s
      (by change Subst.single _ _ (.root (.bnd 0)) = _; exact if_pos rfl)
  · rw [Term.mono_mono]
    have e : Term.mono ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root A).trans
        (h.insert (.bnd 0) A)) t =
        Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ')).root A) (Term.mono h t) := by
      rw [Term.mono_mono]
    rw [e]
    exact subst_single_mono_tm s (Term.mono h t)

end Tail

/-! ## Aliases persist -/

/-- ⭐⭐**An alias is interchangeable with its term at every later stage** (docs §11.20): if a
    stage's theory has the alias set of `t` (weakened from the alias stage), then the alias root
    and `t` satisfy the same slot formulas there.  The formula is packed (`packRoots`), and the
    alias formula of its tail formula (`tailψ`) does the rest. -/
theorem alias_interch {l lj : List VarType} {A : VarType} (hsuf : (A :: l) <:+ lj)
    {M : Set (WFF σ (ctxOf lj) 0)} (hM : Theory.IsMCS M) {a : Ann A} (t : Term σ (ctxOf l) A a)
    (hal : ∀ ψ, WFF.mono (ctxOf_le_of_suffix hsuf) (aliasFormula t ψ) ∈ M)
    (χ : WFF σ ((ctxOf lj).insert (.bnd 0) A) 1) :
    WFF.instantiate Ctx.NoSlots.slots (Term.mono (ctxOf_le_of_suffix hsuf)
        (Term.eta (.root (.free l.length)) A (ctxOf_ref_new A l))) χ ∈ M ↔
      WFF.instantiate Ctx.NoSlots.slots
        (Term.mono (ctxOf_le_of_suffix hsuf) (Term.mono (aliasLe A l) t)) χ ∈ M := by
  set e := ctxOf_le_of_suffix hsuf
  set H := packRoots lj χ
  have h1 := hal (tailψ t H)
  unfold aliasFormula at h1
  rw [instantiate_tailψ (aliasLe A l), instantiate_tailψ (aliasLe A l)] at h1
  simp only [WFF.mono] at h1
  rw [WFF.mono_holeAt _ _ Ctx.NoSlots.slots, WFF.mono_holeAt _ _ Ctx.NoSlots.slots] at h1
  obtain ⟨-, hQP⟩ := hM.and_mem_iff.mp h1
  have hQ : WFF.holeAt Ctx.NoSlots.slots (Term.mono e (Term.pair (Term.mono (aliasLe A l) t)
      (Term.mono (aliasLe A l) t))) (tailK H) ∈ M :=
    hM.closed ⟨[], fun _ h => absurd h List.not_mem_nil,
      ⟨provable_tailK_diag (Term.mono e (Term.mono (aliasLe A l) t)) H⟩⟩
  have hP := hM.imp_mem_iff.mp hQP hQ
  change WFF.holeAt Ctx.NoSlots.slots (Term.pair (Term.mono e (Term.eta _ A _))
    (Term.mono e (Term.mono (aliasLe A l) t))) (tailK H) ∈ M at hP
  rw [holeAt_tailK] at hP
  have hinst := hM.closed ⟨[_], fun _ h => by rw [List.mem_singleton.mp h]; exact hP,
    ⟨Proof.all_elim (tyT lj) (tupW lj).2 (Proof.lookup List.mem_cons_self)⟩⟩
  change WFF.and (WFF.imp (WFF.instantiate _ _ (tailAt _ H)) (WFF.instantiate _ _ (tailAt _ H)))
    (WFF.imp (WFF.instantiate _ _ (tailAt _ H)) (WFF.instantiate _ _ (tailAt _ H))) ∈ M at hinst
  rw [instantiate_tailAt, instantiate_tailAt, holeAt_pair_tupW_packRoots,
    holeAt_pair_tupW_packRoots] at hinst
  obtain ⟨h₁, h₂⟩ := hM.and_mem_iff.mp hinst
  exact ⟨hM.imp_mem_iff.mp h₁, hM.imp_mem_iff.mp h₂⟩

end BArrow

end V12M
