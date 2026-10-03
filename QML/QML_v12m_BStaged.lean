import QML.QML_v12m_BCanonWorld
import QML.QML_v12m_CanonInterch

/-!
# QML v12m — B's worlds as staged theories

The theory-level `Here` layer (`Canon.RealDatum` with `hdeclOf`, `hhereAt` and `spec`;
`Canon.Interch`, `Canon.DTerm.Rel`, `Canon.rel_of_coname`; `Canon.datum_of_here`,
`Canon.mem_here_datum`) is stated for a **staged theory**: a stage system with a maximal consistent
set of its sentences.  A world of the network is one: its stages are the rounds, its contexts its
own variables (`ctxOf`), and its sentences `⟨i, φ⟩` with `φ ∈ M i`
(docs/v12-arrow-canonical.md §9.3, roadmap milestone 1 step 2).

* `BWorld.sys`, `BWorld.T`: the stage system and the sentences;
* ⭐`BWorld.mcsT`: maximal consistent, from each stage being so and stages growing;
* ⭐`BWorld.rootWitnessed`: Henkin witnessing at a declared root, which the network provides;
* `BWorld.datum_of_here`: so a `Here` atom in a network world's theory gives its witness a datum.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

namespace BWorld

variable (w : BWorld σ)

/-- A world's stages, as a stage system. -/
def sys : StageSys ℕ := ⟨w.ctx, fun h => w.le h, fun i => presented_ctxOf (w.l i)⟩

/-- A world's theory, as sentences: `⟨i, φ⟩` with `φ ∈ M i`. -/
def T : Set (w.sys.Sentence σ) := {s | s.2 ∈ w.M s.1}

variable {w}

theorem mem_T {i : ℕ} {φ : WFF σ (w.ctx i) 0} :
    (⟨i, φ⟩ : w.sys.Sentence σ) ∈ w.T ↔ φ ∈ w.M i := Iff.rfl

/-- What the sentences give at a stage is that stage's theory: earlier stages' members lift into
    it (`BWorld.sub`). -/
theorem atStage_T (i : ℕ) : StageSys.atStage w.T i = w.M i := by
  ext ψ
  constructor
  · rintro ⟨⟨j, φ⟩, hφ, hji, rfl⟩
    exact w.sub hji φ hφ
  · intro hψ
    exact ⟨⟨i, ψ⟩, hψ, le_rfl, StageSys.lift_refl _ _⟩

variable (w)

/-- ⭐A network world's theory is maximal consistent as a staged theory. -/
theorem mcsT : StageSys.IsMCS w.T := by
  refine ⟨fun i => by rw [atStage_T]; exact (w.mcs i).1, fun s hs => ?_⟩
  obtain ⟨i, φ⟩ := s
  apply (w.mcs i).2
  refine (hs i).mono ?_
  intro ψ hψ
  rcases hψ with rfl | hψ
  · exact ⟨⟨i, ψ⟩, Set.mem_insert _ _, le_rfl, StageSys.lift_refl _ _⟩
  · exact ⟨⟨i, ψ⟩, Set.mem_insert_of_mem _ hψ, le_rfl, StageSys.lift_refl _ _⟩

instance mcsFact : Fact (StageSys.IsMCS w.T) := ⟨w.mcsT⟩

/-- ⭐The network witnesses existentials at declared roots. -/
theorem rootWitnessed : Canon.RootWitnessed w.sys w.T := fun h => by
  obtain ⟨j, hij, c, hc, hm⟩ := w.exW h
  exact ⟨j, hij, c, hc, hm⟩

/-- A `Here` atom in a network world's theory gives its witness a datum. -/
theorem datum_of_here (hT : ModalSys.T = true) {x : VarSymb} {i : ℕ} {X : VarType}
    (hx : (w.ctx i).ref x = some (.VTypeDia X)) {B : VarType} {β : Ann B}
    (bd : Term σ ((w.ctx i).diaIn x) B β) {a : Ann B} (t : Term σ (w.ctx i) B a)
    (h : WFF.here hT (Term.diatm x ⟨X, hx⟩ bd) t ∈ w.M i) :
    Nonempty (Canon.RealDatum σ w.sys w.T x) :=
  Canon.datum_of_here w.rootWitnessed hT (S := w.sys) hx bd t h

/-! ## Realised witnesses -/

/-- ⭐A network world **realises** the witness `x` when its theory says so: some datum — the
    declarations and the `Here` atom at one stage — exists.  As for the tree's worlds
    (`Canon.World.real`, docs §2d step 4), nothing is chosen when the world is built. -/
def Realised (x : VarSymb) : Prop := Nonempty (Canon.RealDatum σ w.sys w.T x)

variable {w}

/-- The datum the world reads a realised witness by. -/
noncomputable def Realised.data {x : VarSymb} (h : w.Realised x) :
    Canon.RealDatum σ w.sys w.T x := h.some

theorem Realised.T {x : VarSymb} (h : w.Realised x) : ModalSys.T = true := h.data.hT

/-- Without T nothing is realised. -/
theorem not_realised (hT : ModalSys.T = false) {x : VarSymb} : ¬ w.Realised x := fun h => by
  have := h.T
  rw [hT] at this
  cases this

end BWorld

end BArrow

/-! ## Strong T: every term has a witness, by Henkin witnessing alone -/

/-- ⭐Filling the subject slot of `∃y:◇A. Here y t`: the slot's η-expansion becomes the term, and
    `t`, weakened past the slot, comes back unchanged (cf. `WFF.instantiate_here_slot`). -/
theorem WFF.instantiate_hereAt_slot {σ : Signature} {Γ : Ctx} [Γ.NoSlots]
    (hT : ModalSys.T = true) {A : VarType} {a : Ann A} (t : Term σ Γ A a) {b : Ann (.VTypeDia A)}
    (u : Term σ Γ (.VTypeDia A) b) :
    WFF.instantiate (d := 0) Ctx.NoSlots.slots u
        (WFF.here hT
          (Term.eta (.root (.bnd 0)) (.VTypeDia A) (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A)))
          (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root (.VTypeDia A)) t)) =
      WFF.here hT u t := by
  rw [WFF.instantiate, WFF.substRoot]
  refine WFF.here_congr hT ?_ ?_
  · exact Term.subst_eta_tm _ _ _ (.VTypeDia A) (.root (.bnd 0)) _ u (Subst.at_single_root _ _)
  · refine (congrArg (Sigma.mk _) (Term.subst_mono _ _ _ _ t)).trans ?_
    refine ((Term.subst_ren (Ctx.Le.refl Γ) _ _ _ ?_ t).trans
      (congrArg (Sigma.mk _) (Term.mono_refl _ t)))
    intro v T hv
    exact Subst.single_at_ne
      (Ctx.ref_rt_ne ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) hv)

/-- `∃y:◇A. Here y t`: some possible object is realised here by `t` — `Model.sat_here_ex`'s
    formula. -/
abbrev WFF.retEx {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true) {A : VarType}
    {a : Ann A} (t : Term σ Γ A a) : WFF σ Γ 0 :=
  .ex (.VTypeDia A) (WFF.here hT
    (Term.eta (.root (.bnd 0)) (.VTypeDia A) (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A)))
    (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root (.VTypeDia A)) t))

/-- ⭐**Strong T, as a theorem**: `⊢ ∃y:◇A. Here y t`.  `T_dia` at a fresh root `c` leaves
    `Here c t ⊢ ∃y:◇A. Here y t`, which is `∃`-introduction at `c`.  So a theory with Henkin
    witnesses has a `Here` atom for every term without a dedicated step for it. -/
def Proof.retEx {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)}
    (hT : ModalSys.T = true) (hS : ModalSys.TStrong = true) {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) (c : ℕ) (hc : Γ.RootFresh (.free c)) :
    Proof σ Γ Δ (WFF.retEx hT t) := by
  refine Proof.T_dia hT hS A t c hc ?_
  refine Proof.ex_intro (.VTypeDia A)
    (Term.eta (.root (.free c)) (.VTypeDia A) (Ctx.ref_insert_root Γ (.free c) (.VTypeDia A))) ?_
  refine Proof.conv ?_ (Proof.lookup List.mem_cons_self)
  refine Eq.symm ((congrArg (WFF.instantiate _ _) ?_).trans
    (WFF.instantiate_hereAt_slot hT (Term.weaken hc.root (.VTypeDia A) t) _))
  refine WFF.here_congr' hT (Term.mono_eta _ _ _ _) ?_
  simp only [Term.weaken, Term.mono_mono]

namespace BArrow

variable {σ : Signature}

/-- ⭐**Strong T in a network world**: every term, of any type, is the content of some witness by
    the theory's own word — a `Here` atom about a declared root, at a later stage.  The theory
    contains `∃y:◇A. Here y t` (`Proof.retEx`), and Henkin witnessing (`exW`) declares the root:
    unlike the tree's chain, the network needs no term query (the tree's `World.retW`). -/
theorem BWorld.retW (w : BWorld σ) (hT : ModalSys.T = true) (hS : ModalSys.TStrong = true)
    (i : ℕ) {A : VarType} {a : Ann A} (t : Term σ (w.ctx i) A a) :
    ∃ (i' : ℕ) (hi : i ≤ i') (y : VarSymb) (hy : (w.ctx i').ref y = some (.VTypeDia A)),
      WFF.hereAt hT y hy (Term.mono (w.le hi) t) ∈ w.M i' := by
  have hmem : WFF.retEx hT t ∈ w.M i :=
    BWorld.mem_of_provable (Δ := []) (fun _ h => by simp at h)
      ⟨Proof.retEx hT hS t (w.l i).length (ctxOf_fresh le_rfl)⟩
  obtain ⟨j, hij, c, hc, hm⟩ := w.exW hmem
  refine ⟨j, hij, .root (.free c), hc, ?_⟩
  convert hm using 1
  refine Eq.symm ((congrArg (WFF.instantiate _ _) ?_).trans
    (WFF.instantiate_hereAt_slot hT (Term.mono (w.le hij) t) _))
  refine WFF.here_congr' hT (Term.mono_eta _ _ _ _) ?_
  simp only [Term.mono_mono]

end BArrow

end V12M
