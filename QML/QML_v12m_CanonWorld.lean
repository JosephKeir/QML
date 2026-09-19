import QML.QML_v12m_HenkinFinal
import QML.QML_v12m_Soundness
import QML.QML_v12m_DiaAbs

/-!
# QML v12m — the canonical model: worlds and accessibility

A **world** is a world language with a maximal consistent theory that has witnesses for its
existentials and counter-instances for its failing universals.  Its own variables are named by
its modal depth (`names N₀ d n = N₀ + ⟪d, n⟫`), so the variables of a world reached through a
modality are fresh for the world it was reached from.

* `BoxView w w'` / `DiaView x w w'`: the base of `w'` is the `□` / `◇_x` view of `w`'s language;
* `Acc' w w'`: `w'` is one level deeper, has one of the views, and holds everything necessary at
  `w` — the **proper** successors;
* `Chain n w w'`: `n` proper steps; `R w w'`: a chain, of length 0 only under T (the world itself)
  and of length at least 2 only under 4.  So `R` is reflexive under T and transitive under 4.  A
  successor's chain is as long as its depth difference (`Succ.chain`): 0 is the world itself
  (`Succ.self`), 1 a proper successor (`Succ.acc`), and a far successor is a successor of a proper
  successor (`Succ.split`).  The views along a chain embed into its last world (`Chain.le`).
* `extent w x`: the proper successors with the `◇_x` view that hold everything `□_x`-necessary at
  `w`.
-/

namespace V12M

namespace Canon

/-- The name of the `n`-th own variable of a world at modal depth `d`. -/
def names (N₀ d n : ℕ) : ℕ := N₀ + Nat.pair d n

theorem names_injective (N₀ d : ℕ) : Function.Injective (names N₀ d) :=
  fun _ _ h => (Nat.pair_eq_pair.mp (Nat.add_left_cancel h)).2

theorem names_ne {N₀ d d' n n' : ℕ} (h : d ≠ d') : names N₀ d n ≠ names N₀ d' n' :=
  fun he => h (Nat.pair_eq_pair.mp (Nat.add_left_cancel he)).1

end Canon

variable [ModalSys]

theorem CtxExpr.noProjLast : ∀ e : CtxExpr, e.denote.NoProjLast
  | .empty => fun _ _ h => by simp [CtxExpr.denote, Ctx.empty] at h
  | .insertFree e _ T => (CtxExpr.noProjLast e).insert _ T
  | .boxIn _ => Ctx.noProjLast_boxIn _
  | .diaIn _ x => Ctx.noProjLast_diaIn _ x

/-- Presented contexts have no visible address ending in a projection. -/
theorem Ctx.Presented.noProjLast (Γ : Ctx) [h : Γ.Presented] : Γ.NoProjLast :=
  h.denote_eq ▸ h.expr.noProjLast

/-- The `□` view taken `n` times, innermost first. -/
def Ctx.boxIter : ℕ → Ctx → Ctx
  | 0, Γ => Γ
  | n + 1, Γ => Ctx.boxIter n Γ.boxIn

theorem Ctx.Le.boxIter : ∀ (n : ℕ) {Γ Γ' : Ctx}, Γ.Le Γ' →
    (Ctx.boxIter n Γ).Le (Ctx.boxIter n Γ')
  | 0, _, _, h => h
  | n + 1, _, _, h => Ctx.Le.boxIter n h.boxIn

namespace Canon

variable (σ : Signature) (N₀ : ℕ)

/-- ⭐Strong T: the data making the root `c` a **realised** witness of the language `L` under the
    theory `T`.  The root is declared at type `◇A` from just past the own stage `i₀.2` on, `t₀` is
    the term it realises, and `spec` says the theory turns what `t₀` satisfies at a stage into the
    corresponding `◇_c` statement — which is exactly what the rule `T_dia` puts into the theory for
    the chain's witnesses. -/
structure RealDatum (L : WorldLang) (T : Set (L.sys.Sentence σ)) (c : ℕ) where
  hT : ModalSys.T = true
  /-- Only strong T realises a witness. -/
  hS : ModalSys.TStrong = true
  A : VarType
  i₀ : ℕ × ℕ
  a₀ : Ann A
  t₀ : Term σ (L.ctx i₀) A a₀
  /-- The witness is declared at every later own stage.  In the chain it is declared at the step
      after the one that enumerated `t₀`, so it is exactly the own stages past `i₀`. -/
  hdecl : ∀ i : ℕ × ℕ, i₀.2 < i.2 → (L.ctx i).ref (.root (.free c)) = some (.VTypeDia A)
  /-- Nothing else is written at its root. -/
  hfr : ∀ (i : ℕ × ℕ) (v : VarSymb), v.rt = .free c → v ≠ .root (.free c) → (L.ctx i) v = none
  /-- Conversely, wherever the witness is declared the realising term comes from a strictly earlier
      own stage.  This is what makes the induction of `interp_canon` well founded: the content at
      the world itself is read off `t₀`, which therefore belongs to an earlier stage than the term
      being interpreted. -/
  hstage : ∀ i : ℕ × ℕ, (∃ Y, (L.ctx i).ref (.root (.free c)) = some (.VTypeDia Y)) → i₀.2 < i.2
  /-- Everything `t₀` satisfies at a stage, the witness satisfies in its view. -/
  spec : ∀ (i : ℕ × ℕ) (hi : i₀ ≤ i) (hlt : i₀.2 < i.2)
    (χ : WFF σ ((L.ctx i).diaIn (.root (.free c))) 0),
    (⟨i, WFF.realiseAt hT c (hdecl i hlt) (hfr i) (Term.mono (L.ctx_le hi) t₀) χ⟩ :
      L.sys.Sentence σ) ∈ T →
      (⟨i, .dia (.root (.free c)) ⟨A, hdecl i hlt⟩ χ⟩ : L.sys.Sentence σ) ∈ T

/-- A world of the canonical model. -/
structure World where
  depth : ℕ
  L : WorldLang
  hρ : ∀ n, L.ρ n = names N₀ depth n
  hfresh : ∀ m d n, depth ≤ d → (L.base m).RootFresh (.free (names N₀ d n))
  T : Set (L.sys.Sentence σ)
  mcs : StageSys.IsMCS T
  exW : ∀ {i : ℕ × ℕ} {A : VarType} {ψ : WFF σ ((L.ctx i).insert (.bnd 0) A) 1},
    (⟨i, .ex A ψ⟩ : L.sys.Sentence σ) ∈ T →
    ∃ (i' : ℕ × ℕ) (hi : i ≤ i') (a : Ann A) (t : Term σ (L.ctx i') A a),
      (⟨i', WFF.instantiate Ctx.NoSlots.slots t
        (WFF.mono ((L.ctx_le hi).insert (.bnd 0) A) ψ)⟩ : L.sys.Sentence σ) ∈ T
  allW : ∀ {i : ℕ × ℕ} {A : VarType} {ψ : WFF σ ((L.ctx i).insert (.bnd 0) A) 1},
    (⟨i, .all A ψ⟩ : L.sys.Sentence σ) ∉ T →
    ∃ (i' : ℕ × ℕ) (hi : i ≤ i') (a : Ann A) (t : Term σ (L.ctx i') A a),
      (⟨i', (WFF.instantiate Ctx.NoSlots.slots t
        (WFF.mono ((L.ctx_le hi).insert (.bnd 0) A) ψ)).neg⟩ : L.sys.Sentence σ) ∈ T
  /-- Strong T: the realisation the world **chooses** for each of its roots.  Data rather than mere
      existence because the content of a realised witness at the world itself is read off the
      realising term: the model has to name one, not merely know that there is one. -/
  real : ∀ c : ℕ, Option (RealDatum σ L T c)
  /-- Strong T: every term is the realising term of some root.  This is what `posRet_exists`
      needs — every object of a domain is the content, at the world itself, of a possible
      object. -/
  realW : ModalSys.T = true → ModalSys.TStrong = true → ∀ (i : ℕ × ℕ) {A : VarType} {a : Ann A}
      (t : Term σ (L.ctx i) A a),
      ∃ (c : ℕ) (i' : ℕ × ℕ) (hle : i ≤ i') (d : RealDatum σ L T c), real c = some d ∧
        (⟨d.A, d.i₀, d.a₀, d.t₀⟩ :
            Σ (A : VarType) (i'' : ℕ × ℕ) (a : Ann A), Term σ (L.ctx i'') A a) =
          ⟨A, i', a, Term.mono (L.ctx_le hle) t⟩

variable {σ N₀}

namespace World

/-- Names of deeper worlds are fresh at every stage. -/
theorem fresh_deeper (w : World σ N₀) {d : ℕ} (hd : w.depth < d) (n : ℕ) (i : ℕ × ℕ) :
    (w.L.ctx i).RootFresh (.free (names N₀ d n)) :=
  w.L.fresh_ctx_of (fun m => w.hfresh m d n hd.le)
    (fun n' => by
      rw [w.hρ]
      exact names_ne (Nat.ne_of_lt hd)) i

/-- An own variable is declared with its own type. -/
theorem ctx_ref_own (w : World σ N₀) {m j k : ℕ} (h : k < j) :
    (w.L.ctx (m, j)).ref (.root (.free (w.L.ρ k))) = some (w.L.τ k) :=
  Ctx.stage_ref_root w.L.ρ w.L.ρ_inj (fun n => w.L.fresh m n) h

/-- Declaring an own variable writes only at its root, so nothing else there is reachable. -/
theorem ctx_only_root (w : World σ N₀) {m j k : ℕ} :
    ∀ v : VarSymb, v.rt = .free (w.L.ρ k) → v ≠ .root (.free (w.L.ρ k)) →
      (w.L.ctx (m, j)) v = none :=
  Ctx.stage_only_root w.L.ρ w.L.ρ_inj (fun n => w.L.fresh m n) j

end World

/-! ## Realised witnesses (strong T) -/

namespace World

variable (w : World σ N₀)

/-- ⭐Strong T: the data making the address `x` a **realised** witness — a `RealDatum` of the
    world's language together with the root it sits at. -/
structure RealData (x : VarSymb) where
  c : ℕ
  hx : x = .root (.free c)
  datum : RealDatum σ w.L w.T c

variable {w}

/-- The fields of the underlying datum, read off the address. -/
@[reducible] def RealData.hT {x : VarSymb} (d : w.RealData x) : ModalSys.T = true := d.datum.hT
@[reducible] def RealData.hS {x : VarSymb} (d : w.RealData x) : ModalSys.TStrong = true :=
  d.datum.hS
@[reducible] def RealData.A {x : VarSymb} (d : w.RealData x) : VarType := d.datum.A
@[reducible] def RealData.i₀ {x : VarSymb} (d : w.RealData x) : ℕ × ℕ := d.datum.i₀
@[reducible] def RealData.a₀ {x : VarSymb} (d : w.RealData x) : Ann d.A := d.datum.a₀
@[reducible] def RealData.t₀ {x : VarSymb} (d : w.RealData x) :
    Term σ (w.L.ctx d.i₀) d.A d.a₀ := d.datum.t₀
@[reducible] def RealData.hdecl {x : VarSymb} (d : w.RealData x) :
    ∀ i : ℕ × ℕ, d.i₀.2 < i.2 → (w.L.ctx i).ref (.root (.free d.c)) = some (.VTypeDia d.A) :=
  d.datum.hdecl
@[reducible] def RealData.hfr {x : VarSymb} (d : w.RealData x) :
    ∀ (i : ℕ × ℕ) (v : VarSymb), v.rt = .free d.c → v ≠ .root (.free d.c) → (w.L.ctx i) v = none :=
  d.datum.hfr
@[reducible] def RealData.hstage {x : VarSymb} (d : w.RealData x) :
    ∀ i : ℕ × ℕ, (∃ Y, (w.L.ctx i).ref (.root (.free d.c)) = some (.VTypeDia Y)) → d.i₀.2 < i.2 :=
  d.datum.hstage
@[reducible] def RealData.spec {x : VarSymb} (d : w.RealData x) :
    ∀ (i : ℕ × ℕ) (hi : d.i₀ ≤ i) (hlt : d.i₀.2 < i.2)
      (χ : WFF σ ((w.L.ctx i).diaIn (.root (.free d.c))) 0),
      (⟨i, WFF.realiseAt d.hT d.c (d.hdecl i hlt) (d.hfr i) (Term.mono (w.L.ctx_le hi) d.t₀) χ⟩ :
        w.L.sys.Sentence σ) ∈ w.T →
        (⟨i, .dia (.root (.free d.c)) ⟨d.A, d.hdecl i hlt⟩ χ⟩ : w.L.sys.Sentence σ) ∈ w.T :=
  d.datum.spec

variable (w)

/-- The realisation the world names at an address, if any: only a bare free root can carry one. -/
def realAt : ∀ x : VarSymb, Option (w.RealData x)
  | .root (.free c) => (w.real c).map fun d => ⟨c, rfl, d⟩
  | .root (.bnd _) => none
  | .step _ _ => none

/-- ⭐The addresses realised at `w`. -/
def Realised (x : VarSymb) : Prop := (w.realAt x).isSome

variable {w}

/-- The realisation named at a realised address — determined by the world, not chosen here. -/
def Realised.data {x : VarSymb} (h : w.Realised x) : w.RealData x := (w.realAt x).get h

theorem Realised.T {x : VarSymb} (h : w.Realised x) : ModalSys.T = true := h.data.hT

theorem Realised.TStrong {x : VarSymb} (h : w.Realised x) : ModalSys.TStrong = true := h.data.hS

/-- ⭐What the world names at a root is what it realises there. -/
theorem realAt_of_real {c : ℕ} {d : RealDatum σ w.L w.T c} (hsome : w.real c = some d) :
    w.realAt (.root (.free c)) = some ⟨c, rfl, d⟩ := by
  change (w.real c).map (fun d' => (⟨c, rfl, d'⟩ : w.RealData (.root (.free c)))) = _
  rw [hsome]
  rfl

/-- So that root is realised … -/
theorem realised_of_real {c : ℕ} {d : RealDatum σ w.L w.T c} (hsome : w.real c = some d) :
    w.Realised (.root (.free c)) := by
  unfold Realised
  rw [realAt_of_real hsome]
  rfl

/-- … by that datum. -/
theorem data_of_real {c : ℕ} {d : RealDatum σ w.L w.T c} (hsome : w.real c = some d) :
    (realised_of_real hsome).data = ⟨c, rfl, d⟩ := by
  unfold Realised.data
  simp only [realAt_of_real hsome]
  rfl

/-- ⭐Conversely, a realised address carries the datum the world names at its root.  This is what
    lets a proof forget the address and work with the world's own naming, where the datum is a
    variable and the equations can be `subst`ed. -/
theorem real_of_realised {x : VarSymb} (h : w.Realised x) :
    w.real h.data.c = some h.data.datum := by
  match x with
  | .root (.free c) =>
      rcases hc : w.real c with _ | d
      · exact absurd h (by simp [Realised, realAt, hc])
      · exact Eq.mpr (congrArg (fun D : w.RealData (.root (.free c)) => w.real D.c = some D.datum)
          (data_of_real hc)) hc
  | .root (.bnd _) => exact absurd h (by simp [Realised, realAt])
  | .step _ _ => exact absurd h (by simp [Realised, realAt])

end World

/-! ## Views and accessibility -/

/-- The base of `w'` is the `□` view of `w`'s language. -/
def BoxView (w w' : World σ N₀) : Prop := ∀ m, w'.L.base m = (w.L.ctx (m, m)).boxIn

/-- The base of `w'` is the `◇_x` view of `w`'s language. -/
def DiaView (x : VarSymb) (w w' : World σ N₀) : Prop :=
  ∀ m, w'.L.base m = (w.L.ctx (m, m)).diaIn x

theorem BoxView.le {w w' : World σ N₀} (h : BoxView w w') {i : ℕ × ℕ} {k : ℕ} (h₁ : i.1 ≤ k)
    (h₂ : i.2 ≤ k) (j : ℕ) : (w.L.ctx i).boxIn.Le (w'.L.ctx (k, j)) := by
  have hb : (w.L.ctx i).boxIn.Le (w'.L.base k) := by
    rw [h k]
    exact (w.L.le_diag h₁ h₂).boxIn
  exact hb.trans (w'.L.base_le_ctx k j)

theorem DiaView.le {x : VarSymb} {w w' : World σ N₀} (h : DiaView x w w') {i : ℕ × ℕ} {k : ℕ}
    (h₁ : i.1 ≤ k) (h₂ : i.2 ≤ k) (j : ℕ) : ((w.L.ctx i).diaIn x).Le (w'.L.ctx (k, j)) := by
  have hb : ((w.L.ctx i).diaIn x).Le (w'.L.base k) := by
    rw [h k]
    exact (w.L.le_diag h₁ h₂).diaIn x
  exact hb.trans (w'.L.base_le_ctx k j)

theorem DiaView.le_boxIn {x : VarSymb} {w w' : World σ N₀} (h : DiaView x w w') {i : ℕ × ℕ}
    {k : ℕ} (h₁ : i.1 ≤ k) (h₂ : i.2 ≤ k) (j : ℕ) : (w.L.ctx i).boxIn.Le (w'.L.ctx (k, j)) :=
  (Ctx.le_boxIn_diaIn _ x).trans (h.le h₁ h₂ j)

/-- Everything necessary at `w` holds at `w'`. -/
def BoxContents (w w' : World σ N₀) : Prop :=
  ∀ (i : ℕ × ℕ) (χ : WFF σ (w.L.ctx i).boxIn 0) (j : ℕ × ℕ)
    (h : (w.L.ctx i).boxIn.Le (w'.L.ctx j)),
    (⟨i, .box χ⟩ : w.L.sys.Sentence σ) ∈ w.T → (⟨j, WFF.mono h χ⟩ : w'.L.sys.Sentence σ) ∈ w'.T

/-- Everything `□_x`-necessary at `w` holds at `w'`. -/
def BoxxContents (x : VarSymb) (w w' : World σ N₀) : Prop :=
  ∀ (i : ℕ × ℕ) (hx : ∃ X, (w.L.ctx i).ref x = some (.VTypeDia X))
    (χ : WFF σ ((w.L.ctx i).diaIn x) 0) (j : ℕ × ℕ) (h : ((w.L.ctx i).diaIn x).Le (w'.L.ctx j)),
    (⟨i, WFF.boxx x hx χ⟩ : w.L.sys.Sentence σ) ∈ w.T →
      (⟨j, WFF.mono h χ⟩ : w'.L.sys.Sentence σ) ∈ w'.T

/-- Proper accessibility: one level deeper, with a view, holding everything necessary. -/
def Acc' (w w' : World σ N₀) : Prop :=
  w'.depth = w.depth + 1 ∧ (BoxView w w' ∨ ∃ x, DiaView x w w') ∧ BoxContents w w'

/-- The stage of a successor that contains the modal views of stage `i`. -/
def childStage (i : ℕ × ℕ) : ℕ × ℕ := (max i.1 i.2, 0)

/-- The stage reached after `n` proper steps. -/
def childIter : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, i => i
  | n + 1, i => childIter n (childStage i)

theorem Acc'.boxIn_le {w w' : World σ N₀} (h : Acc' w w') (i : ℕ × ℕ) :
    (w.L.ctx i).boxIn.Le (w'.L.ctx (childStage i)) := by
  rcases h.2.1 with hv | ⟨x, hv⟩
  · exact hv.le (le_max_left _ _) (le_max_right _ _) 0
  · exact hv.le_boxIn (le_max_left _ _) (le_max_right _ _) 0

/-- A chain of `n` proper steps, the first step first. -/
def Chain : ℕ → World σ N₀ → World σ N₀ → Prop
  | 0, w, w' => w' = w
  | n + 1, w, w' => ∃ u, Acc' w u ∧ Chain n u w'

theorem Chain.depth : ∀ {n : ℕ} {w w' : World σ N₀}, Chain n w w' → w'.depth = w.depth + n
  | 0, w, w', h => by
      subst h
      rfl
  | _ + 1, _, _, ⟨_, hu, hc⟩ => by
      rw [Chain.depth hc, hu.1]
      omega

theorem Chain.comp : ∀ {n m : ℕ} {w v s : World σ N₀}, Chain n w v → Chain m v s →
    Chain (m + n) w s
  | 0, _, w, v, s, h, hm => by
      subst h
      exact hm
  | _ + 1, _, _, _, _, ⟨u, hu, hc⟩, hm => ⟨u, hu, Chain.comp hc hm⟩

/-- The views along a chain embed into the stages of its last world. -/
theorem Chain.le : ∀ {n : ℕ} {w w' : World σ N₀}, Chain n w w' → ∀ {Γ : Ctx} {i : ℕ × ℕ},
    Γ.Le (w.L.ctx i) → (Ctx.boxIter n Γ).Le (w'.L.ctx (childIter n i))
  | 0, w, w', h, _, _, e => by
      subst h
      exact e
  | _ + 1, _, _, ⟨_, hu, hc⟩, _, i, e => Chain.le hc (e.boxIn.trans (hu.boxIn_le i))

/-- ⭐Accessibility: a chain of proper steps — the empty chain under T, chains of two or more
    steps under 4. -/
def R (w w' : World σ N₀) : Prop :=
  ∃ n, Chain n w w' ∧ (n = 0 → ModalSys.T = true) ∧ (2 ≤ n → ModalSys.Four = true)

theorem R.refl (hT : ModalSys.T = true) (w : World σ N₀) : R w w :=
  ⟨0, rfl, fun _ => hT, fun h => absurd h (by omega)⟩

theorem R.of_acc {w w' : World σ N₀} (h : Acc' w w') : R w w' :=
  ⟨1, ⟨w', h, rfl⟩, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

theorem R.trans (hF : ModalSys.Four = true) {w v s : World σ N₀} : R w v → R v s → R w s
  | ⟨n, hn, h₀, _⟩, ⟨m, hm, _, _⟩ => ⟨m + n, hn.comp hm, fun h => h₀ (by omega), fun _ => hF⟩

/-- The successors of a world. -/
abbrev Succ (w : World σ N₀) : Type := Σ w' : World σ N₀, PLift (R w w')

/-- A successor is reached by a chain as long as the depth difference. -/
theorem Succ.chain {w : World σ N₀} (w' : Succ w) :
    Chain (w'.1.depth - w.depth) w w'.1 ∧ (w'.1.depth - w.depth = 0 → ModalSys.T = true) ∧
      (2 ≤ w'.1.depth - w.depth → ModalSys.Four = true) := by
  obtain ⟨n, hn, h₀, h₂⟩ := w'.2.down
  have e : w'.1.depth - w.depth = n := by
    rw [hn.depth]
    omega
  rw [e]
  exact ⟨hn, h₀, h₂⟩

/-- A successor at the same depth is the world itself. -/
theorem Succ.self {w : World σ N₀} (w' : Succ w) (h : w'.1.depth - w.depth = 0) :
    ModalSys.T = true ∧ w'.1 = w := by
  obtain ⟨hc, h₀, _⟩ := w'.chain
  rw [h] at hc
  exact ⟨h₀ h, hc⟩

/-- A successor one level deeper is proper. -/
theorem Succ.acc {w : World σ N₀} (w' : Succ w) (h : w'.1.depth - w.depth = 1) : Acc' w w'.1 := by
  have hc := w'.chain.1
  rw [h] at hc
  obtain ⟨u, hu, rfl⟩ := hc
  exact hu

/-- A successor more than one level deeper exists only under 4. -/
theorem Succ.four {w : World σ N₀} (w' : Succ w) {d : ℕ} (h : w'.1.depth - w.depth = d + 1) :
    d ≠ 0 → ModalSys.Four = true :=
  fun hd => w'.chain.2.2 (by omega)

theorem Succ.chainLe {w : World σ N₀} (w' : Succ w) {d : ℕ} (h : w'.1.depth - w.depth = d + 1)
    {Γ : Ctx} {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) :
    (Ctx.boxIter (d + 1) Γ).Le (w'.1.L.ctx (childIter (d + 1) i)) := by
  have hc := w'.chain.1
  rw [h] at hc
  exact hc.le e

/-- A far successor is a successor of a proper successor. -/
theorem Succ.split {w : World σ N₀} (w' : Succ w) {d : ℕ} (h : w'.1.depth - w.depth = d + 2) :
    ∃ (u : World σ N₀) (_ : Acc' w u) (_ : R u w'.1), w'.1.depth - u.depth = d + 1 := by
  obtain ⟨hc, _, h₂⟩ := w'.chain
  rw [h] at hc
  obtain ⟨u, hu, hc'⟩ := hc
  refine ⟨u, hu, ⟨d + 1, hc', fun h => absurd h (by omega), fun _ => h₂ (by omega)⟩, ?_⟩
  rw [hc'.depth, hu.1]
  omega

/-- ⭐The extent of the possible object named by `x`: the proper successors with the `◇_x` view
    that hold everything `□_x`-necessary here and, under strong T, the world itself when `x` is
    realised. -/
def extent (w : World σ N₀) (x : VarSymb) : Set (Succ w) :=
  {w' | (w'.1.depth = w.depth + 1 ∧ DiaView x w w'.1 ∧ BoxxContents x w w'.1) ∨
    (w'.1 = w ∧ w.Realised x)}

/-- A member of the extent is the world itself or one level deeper. -/
theorem extent_cases {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x) :
    (w'.1.depth - w.depth = 1 ∧ DiaView x w w'.1 ∧ BoxxContents x w w'.1) ∨
      (w'.1.depth - w.depth = 0 ∧ w'.1 = w ∧ w.Realised x) := by
  rcases hw' with ⟨hd, hv, hb⟩ | ⟨he, hr⟩
  · exact Or.inl ⟨by omega, hv, hb⟩
  · exact Or.inr ⟨by rw [he]; omega, he, hr⟩

/-- A member of the extent one level deeper is a proper one. -/
theorem extent_proper {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth ≠ 0) :
    w'.1.depth - w.depth = 1 ∧ DiaView x w w'.1 ∧ BoxxContents x w w'.1 := by
  rcases extent_cases hw' with h | ⟨h, _⟩
  · exact h
  · exact absurd h hd

/-- A member of the extent at this depth is the world itself, and then `x` is realised. -/
theorem extent_self {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth = 0) : w'.1 = w ∧ w.Realised x := by
  rcases extent_cases hw' with ⟨h, _⟩ | ⟨_, h⟩
  · omega
  · exact h

theorem extent_dist {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth ≠ 0) : w'.1.depth - w.depth = 1 :=
  (extent_proper hw' hd).1

theorem extent_acc {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth ≠ 0) : Acc' w w'.1 :=
  w'.acc (extent_dist hw' hd)

theorem extent_le {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth ≠ 0) (i : ℕ × ℕ) :
    ((w.L.ctx i).diaIn x).Le (w'.1.L.ctx (childStage i)) :=
  (extent_proper hw' hd).2.1.le (le_max_left _ _) (le_max_right _ _) 0

/-- The world itself is in the extent of a realised address. -/
theorem self_mem_extent {w : World σ N₀} {x : VarSymb} (h : w.Realised x) :
    (⟨w, ⟨R.refl h.T w⟩⟩ : Succ w) ∈ extent w x :=
  Or.inr ⟨rfl, h⟩

end Canon

end V12M
