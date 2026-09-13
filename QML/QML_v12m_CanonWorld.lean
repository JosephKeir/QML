import QML.QML_v12m_HenkinFinal
import QML.QML_v12m_Soundness

/-!
# QML v12m — the canonical model: worlds and accessibility

A **world** is a world language with a maximal consistent theory that has witnesses for its
existentials and counter-instances for its failing universals.  Its own variables are named by
its modal depth (`names N₀ d n = N₀ + ⟪d, n⟫`), so the variables of a world reached through a
modality are fresh for the world it was reached from.

* `BoxView w w'` / `DiaView x w w'`: the base of `w'` is the `□` / `◇_x` view of `w`'s language;
* `Acc' w w'`: `w'` is one level deeper, has one of the views, and holds everything necessary at
  `w` — the **proper** successors;
* `R w w'`: a proper successor, or under T the world itself.  A successor at the same depth is the
  world itself (`Succ.self`); any other is proper (`Succ.acc`).
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

/-- For now the canonical model covers the systems without weak 4. -/
class ModalSys.NoFour : Prop where
  noFour : ModalSys.Four = false

theorem ModalSys.NoFour.absurd [ModalSys.NoFour] (hF : ModalSys.Four = true) : False := by
  rw [ModalSys.NoFour.noFour] at hF
  cases hF

theorem CtxExpr.noProjLast : ∀ e : CtxExpr, e.denote.NoProjLast
  | .empty => fun _ _ h => by simp [CtxExpr.denote, Ctx.empty] at h
  | .insertFree e _ T => (CtxExpr.noProjLast e).insert _ T
  | .boxIn _ => Ctx.noProjLast_boxIn _
  | .diaIn _ x => Ctx.noProjLast_diaIn _ x

/-- Presented contexts have no visible address ending in a projection. -/
theorem Ctx.Presented.noProjLast (Γ : Ctx) [h : Γ.Presented] : Γ.NoProjLast :=
  h.denote_eq ▸ h.expr.noProjLast

namespace Canon

variable (σ : Signature) (N₀ : ℕ)

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

variable {σ N₀}

namespace World

/-- Names of deeper worlds are fresh at every stage. -/
theorem fresh_deeper (w : World σ N₀) {d : ℕ} (hd : w.depth < d) (n : ℕ) (i : ℕ × ℕ) :
    (w.L.ctx i).RootFresh (.free (names N₀ d n)) :=
  w.L.fresh_ctx_of (fun m => w.hfresh m d n hd.le)
    (fun n' => by
      rw [w.hρ]
      exact names_ne (Nat.ne_of_lt hd)) i

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

/-- ⭐Accessibility: a proper successor, or under T the world itself. -/
def R (w w' : World σ N₀) : Prop := Acc' w w' ∨ (ModalSys.T = true ∧ w' = w)

/-- The successors of a world. -/
abbrev Succ (w : World σ N₀) : Type := {w' : World σ N₀ // R w w'}

/-- A successor at another depth is proper. -/
theorem Succ.acc {w : World σ N₀} (w' : Succ w) (h : w'.1.depth ≠ w.depth) : Acc' w w'.1 :=
  w'.2.resolve_right fun ⟨_, e⟩ => h (congrArg World.depth e)

/-- A successor at the same depth is the world itself. -/
theorem Succ.self {w : World σ N₀} (w' : Succ w) (h : w'.1.depth = w.depth) :
    ModalSys.T = true ∧ w'.1 = w :=
  w'.2.resolve_left fun ha => by
    have := ha.1
    omega

/-- ⭐The extent of the possible object named by `x`. -/
def extent (w : World σ N₀) (x : VarSymb) : Set (Succ w) :=
  {w' | w'.1.depth = w.depth + 1 ∧ DiaView x w w'.1 ∧ BoxxContents x w w'.1}

theorem extent_depth {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x) :
    w'.1.depth ≠ w.depth := by
  have := hw'.1
  omega

/-- The stage of a successor that contains the modal views of stage `i`. -/
def childStage (i : ℕ × ℕ) : ℕ × ℕ := (max i.1 i.2, 0)

theorem Acc'.boxIn_le {w w' : World σ N₀} (h : Acc' w w') (i : ℕ × ℕ) :
    (w.L.ctx i).boxIn.Le (w'.L.ctx (childStage i)) := by
  rcases h.2.1 with hv | ⟨x, hv⟩
  · exact hv.le (le_max_left _ _) (le_max_right _ _) 0
  · exact hv.le_boxIn (le_max_left _ _) (le_max_right _ _) 0

theorem extent_le {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (i : ℕ × ℕ) : ((w.L.ctx i).diaIn x).Le (w'.1.L.ctx (childStage i)) :=
  hw'.2.1.le (le_max_left _ _) (le_max_right _ _) 0

end Canon

end V12M
