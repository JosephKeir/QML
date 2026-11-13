import QML.QML_v12m_OCanonView
import QML.QML_v12m_CanonExist

/-!
# QML v12m — the canonical tree with `Opt` on: children

Under `Opt` there is one kind of child (docs §12.22, "Revised"): the `□` view of the parent with the
witnesses **present at the child** opened.  A `◇_x` child is the case where `◇⁰_x χ` is wanted
(`◇_x χ ⊣⊢ ◇ ◇⁰_x χ`, the bridge), so the `□`-failure construction is the only one.

* `presentList w P m`: the witnesses of the `□` view of stage `(m, m)` with `P`, as a list.
* `openLang w P`: the child's language, the `□` views with those witnesses opened.
* Two passes.  The first is the existing `□`-failure world (`Canon.boxWorld`); its theory decides
  every witness's presence (`present`).  The second starts from the first's theory at the base
  stages, carried into the opened language (`openStart`); it is consistent because opening a
  present witness is conservative (`Proof.unopens`).
-/

namespace V12M

/- M1's construction is for K and D with `Opt` on: T off (`ModalSys.NoT`) until M2 step 6
   generalises it, so the class is in scope throughout. -/
set_option linter.unusedSectionVars false

variable [ModalSys] [ModalSys.NoT]

namespace OCanon

open Canon

variable {σ : Signature} {N₀ : ℕ}

/-- The `□` view of a world's diagonal stage. -/
abbrev bview (w : World σ N₀) (m : ℕ) : Ctx := (w.L.ctx (m, m)).boxIn

theorem bview_le (w : World σ N₀) {m m' : ℕ} (h : m ≤ m') : (bview w m).Le (bview w m') :=
  (w.L.le_diag (k := m') (i := (m, m)) h h).boxIn

/-- The witnesses of a stage's `□` view are finitely many. -/
theorem wit_finite (w : World σ N₀) (m : ℕ) (P : VarSymb → Prop) :
    {y | (∃ X, (bview w m).wit y = some X) ∧ P y}.Finite :=
  (Ctx.Fin.reach (Ctx.Presented.fin (w.L.ctx (m, m)))).subset fun y hy => by
    obtain ⟨⟨X, hX⟩, -⟩ := hy
    change ((w.L.ctx (m, m)).ref y).isSome
    rw [(Ctx.boxIn_wit.mp hX).2]
    rfl

/-- The witnesses of the `□` view of stage `(m, m)` with `P`, as a list. -/
noncomputable def presentList (w : World σ N₀) (P : VarSymb → Prop) (m : ℕ) : List VarSymb :=
  (wit_finite w m P).toFinset.toList

theorem mem_presentList {w : World σ N₀} {P : VarSymb → Prop} {m : ℕ} {y : VarSymb} :
    y ∈ presentList w P m ↔ (∃ X, (bview w m).wit y = some X) ∧ P y := by
  rw [presentList, Finset.mem_toList, Set.Finite.mem_toFinset]
  rfl

theorem presentList_mono {w : World σ N₀} {P : VarSymb → Prop} {m m' : ℕ} (h : m ≤ m')
    {y : VarSymb} (hy : y ∈ presentList w P m) : y ∈ presentList w P m' := by
  obtain ⟨⟨X, hX⟩, hP⟩ := mem_presentList.mp hy
  exact mem_presentList.mpr ⟨⟨X, (bview_le w h).wit y X hX⟩, hP⟩

/-- ⭐**The child's language**: the `□` views of the parent's stages with the witnesses `P`
    opened. -/
noncomputable def openLang (w : World σ N₀) (P : VarSymb → Prop) : WorldLang where
  base m := (bview w m).optIns (presentList w P m)
  base_le m := Ctx.optIns_le (bview_le w (Nat.le_succ m)) fun _ hy =>
    presentList_mono (Nat.le_succ m) hy
  basePres m := Ctx.presentedOptIns (presentList w P m)
  τ := fun _ => .VTypeOne
  ρ := names N₀ (w.depth + 1)
  ρ_inj := names_injective _ _
  fresh m n := ((childNames_fresh w m n).boxIn).optIns _

theorem openLang_base (w : World σ N₀) (P : VarSymb → Prop) (m : ℕ) :
    (openLang w P).base m = (bview w m).optIns (presentList w P m) := rfl

omit [ModalSys] in
/-- Choosing preimages of a list. -/
theorem exists_list_map {α β : Type} {P : α → Prop} (f : α → β) :
    ∀ Δ : List β, (∀ δ ∈ Δ, ∃ x, P x ∧ f x = δ) →
      ∃ Δ₀ : List α, (∀ x ∈ Δ₀, P x) ∧ ∀ δ ∈ Δ, δ ∈ Δ₀.map f
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: Δ, h => by
      obtain ⟨Δ₀, h₀, h₁⟩ := exists_list_map f Δ fun d hd => h d (List.mem_cons_of_mem _ hd)
      obtain ⟨x, hx, rfl⟩ := h δ List.mem_cons_self
      refine ⟨x :: Δ₀, fun y hy => ?_, fun d hd => ?_⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact h₀ y hy
      · rcases List.mem_cons.mp hd with rfl | hd
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h₁ d hd)

/-- ⭐**Proper accessibility under `Opt`**: one level deeper and built as a successor; the base is
    the parent's `□` view with the same witnesses, each of them either opened (its content
    declared) or absent by the theory; and everything necessary at the parent holds. -/
structure AccO (hO : ModalSys.Opt = true) (w w' : World σ N₀) : Prop where
  depth : w'.depth = w.depth + 1
  parent : w'.parent = some w
  le : ∀ m, (bview w m).Le (w'.L.base m)
  wit : ∀ m y, (w'.L.base m).wit y = (bview w m).wit y
  decide : ∀ m y X (hX : (bview w m).wit y = some X),
    w'.L.base m (.step y .dia) = some X ∨
      (⟨(m, 0), (WFF.optx hO .arrow y ⟨X, (wit m y).trans hX⟩ .top).neg⟩ :
        w'.L.sys.Sentence σ) ∈ w'.T
  box : BoxContents w w'

/-- A stage's `□` view sits in a proper successor's child stage. -/
theorem AccO.boxIn_le {hO : ModalSys.Opt = true} {w w' : World σ N₀} (h : AccO hO w w')
    (i : ℕ × ℕ) : (w.L.ctx i).boxIn.Le (w'.L.ctx (childStage i)) :=
  (le_diag_max w i).boxIn.trans ((h.le _).trans (w'.L.base_le_ctx _ 0))

section Pass

variable (hO : ModalSys.Opt = true) [Countable σ.FuncSyms] [Countable σ.RelSyms]
  (w : World σ N₀) {i : ℕ × ℕ} (χ : WFF σ (w.L.ctx i).boxIn 0)
  (hχ : (⟨i, .box χ⟩ : w.L.sys.Sentence σ) ∉ w.T)

/-- ⭐**Presence, as the first pass decides it**: the first pass is the plain `□`-failure world
    (`Canon.boxWorld`), whose theory decides `◇⁰_y ⊤` for every witness `y`. -/
def present (y : VarSymb) : Prop :=
  ∃ (m : ℕ) (hy : ∃ X, (bview w m).wit y = some X),
    (⟨(m, 0), WFF.optx hO .arrow y hy .top⟩ : (boxWorld w χ hχ).L.sys.Sentence σ) ∈
      (boxWorld w χ hχ).T

/-- Presence does not depend on the stage it is read at. -/
theorem present_at {y : VarSymb} {m : ℕ} (hy : ∃ X, (bview w m).wit y = some X)
    (hp : present hO w χ hχ y) :
    (⟨(m, 0), WFF.optx hO .arrow y hy .top⟩ : (boxWorld w χ hχ).L.sys.Sentence σ) ∈
      (boxWorld w χ hχ).T := by
  obtain ⟨m₀, _, hm₀⟩ := hp
  have h₁ := (World.mem_lift (w := boxWorld w χ hχ)
    (show ((m₀, 0) : ℕ × ℕ) ≤ (max m m₀, 0) from ⟨le_max_right _ _, le_rfl⟩)).mp hm₀
  exact (World.mem_lift (w := boxWorld w χ hχ)
    (show ((m, 0) : ℕ × ℕ) ≤ (max m m₀, 0) from ⟨le_max_left _ _, le_rfl⟩)).mpr h₁

/-- The second pass's start: the first pass's theory at the base stages, in the opened
    language. -/
def openStart : Set (((openLang w (present hO w χ hχ)).pre []).Sentence σ) :=
  {s | ∃ ψ : WFF σ (bview w s.1) 0,
    (⟨(s.1, 0), ψ⟩ : (boxWorld w χ hχ).L.sys.Sentence σ) ∈ (boxWorld w χ hχ).T ∧
      s.2 = WFF.mono (Ctx.le_optIns _ _) ψ}

/-- ⭐**The second pass's start is consistent**: a contradiction in the opened language is one in
    the first pass's, once its present witnesses are known present (`Proof.unopens`). -/
theorem openStart_consistent : StageSys.Consistent (openStart hO w χ hχ) := by
  intro m
  rintro ⟨Δ, hΔ, ⟨p⟩⟩
  have key : ∀ δ ∈ Δ, ∃ ψ : WFF σ (bview w m) 0,
      (⟨(m, 0), ψ⟩ : (boxWorld w χ hχ).L.sys.Sentence σ) ∈ (boxWorld w χ hχ).T ∧
        WFF.mono (Ctx.le_optIns _ (presentList w (present hO w χ hχ) m)) ψ = δ := by
    intro δ hδ
    obtain ⟨s, ⟨ψ, hψ, hs⟩, hle, rfl⟩ := hΔ δ hδ
    refine ⟨_, (World.mem_lift (w := boxWorld w χ hχ)
      (show ((s.1, 0) : ℕ × ℕ) ≤ (m, 0) from ⟨hle, le_rfl⟩)).mp hψ, ?_⟩
    rw [hs]
    change _ = WFF.mono _ (WFF.mono _ ψ)
    rw [WFF.mono_mono, WFF.mono_mono]
  obtain ⟨Δ₀, h₀, h₁⟩ := exists_list_map _ Δ key
  obtain ⟨q⟩ := Provable.mono h₁ ⟨p⟩
  have q' := Proof.unopens hO (Γ := bview w m) (Δ := Δ₀)
    (presentList w (present hO w χ hχ) m) (fun y hy => (mem_presentList.mp hy).1) q
  refine (boxWorld w χ hχ).mcs.bot_not_mem (i := (m, 0))
    (World.mem_of_provable (w := boxWorld w χ hχ) (fun ψ hψ => ?_) ⟨q'⟩)
  rcases List.mem_append.mp hψ with h | h
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
    obtain ⟨⟨X, hX⟩, hp⟩ := mem_presentList.mp hy
    rw [Proof.presence_eq hO hX]
    exact present_at hO w χ hχ ⟨X, hX⟩ hp
  · exact h₀ ψ h

/-- ⭐**The child**: the second pass, over the opened language. -/
noncomputable def child : World σ N₀ :=
  World.ofHenkin (w.depth + 1) (openLang w (present hO w χ hχ)) (fun _ => rfl)
    (fun m _ n hd => ((w.fresh_deeper hd n (m, m)).boxIn).optIns _)
    (openStart hO w χ hχ) (openStart_consistent hO w χ hχ) (some w)

/-- What the first pass has at a base stage, the child has, opened. -/
theorem child_of_first {m : ℕ} {ψ : WFF σ (bview w m) 0}
    (h : (⟨(m, 0), ψ⟩ : (boxWorld w χ hχ).L.sys.Sentence σ) ∈ (boxWorld w χ hχ).T) :
    (⟨(m, 0), WFF.mono (Ctx.le_optIns _ (presentList w (present hO w χ hχ) m)) ψ⟩ :
      (child hO w χ hχ).L.sys.Sentence σ) ∈ (child hO w χ hχ).T :=
  WorldLang.subset_finalT (openStart hO w χ hχ) ⟨ψ, h, rfl⟩

/-- ⭐The child is a proper successor. -/
theorem child_acc : AccO hO w (child hO w χ hχ) where
  depth := rfl
  parent := rfl
  le _ := Ctx.le_optIns _ _
  wit _ y := Ctx.optIns_wit _ _ y
  decide m y X hX := by
    by_cases hp : present hO w χ hχ y
    · exact Or.inl (Ctx.optIns_content (mem_presentList.mpr ⟨⟨X, hX⟩, hp⟩) hX)
    · right
      have hn : (⟨(m, 0), WFF.optx hO .arrow y ⟨X, hX⟩ .top⟩ :
          (boxWorld w χ hχ).L.sys.Sentence σ) ∉ (boxWorld w χ hχ).T :=
        fun h => hp ⟨m, ⟨X, hX⟩, h⟩
      exact child_of_first hO w χ hχ (((boxWorld w χ hχ).mcs.neg_mem_iff).mpr hn)
  box := by
    intro i' ψ j h hmem
    have hk := child_of_first hO w χ hχ
      ((boxWorld_acc w χ hχ).2.2.1 i' ψ (max i'.1 i'.2, 0) (le_diag_max w i').boxIn hmem)
    rw [WFF.mono_mono] at hk
    exact World.mem_mono_congr (child hO w χ hχ) h _ hk

/-- ⭐The child refutes `χ`. -/
theorem child_not :
    (⟨childStage i, WFF.mono ((child_acc hO w χ hχ).boxIn_le i) χ⟩ :
      (child hO w χ hχ).L.sys.Sentence σ) ∉ (child hO w χ hχ).T := by
  intro hin
  have hneg := WorldLang.subset_finalT (boxStart w χ)
    (Or.inr rfl : (⟨max i.1 i.2, WFF.mono (le_diag_max w i).boxIn χ.neg⟩ :
      ((boxLang w).pre []).Sentence σ) ∈ boxStart w χ)
  have hc : (⟨(max i.1 i.2, 0), (WFF.mono (Ctx.le_optIns _
      (presentList w (present hO w χ hχ) _)) (WFF.mono (le_diag_max w i).boxIn χ)).neg⟩ :
      (child hO w χ hχ).L.sys.Sentence σ) ∈ (child hO w χ hχ).T :=
    child_of_first hO w χ hχ hneg
  rw [WFF.mono_mono] at hc
  exact ((child hO w χ hχ).mcs.neg_mem_iff.mp hc) hin

include hχ in
/-- ⭐**A non-necessary formula fails at some proper successor**, under `Opt`. -/
theorem exists_box_failO :
    ∃ (w' : World σ N₀) (ha : AccO hO w w'),
      (⟨childStage i, WFF.mono (ha.boxIn_le i) χ⟩ : w'.L.sys.Sentence σ) ∉ w'.T :=
  ⟨child hO w χ hχ, child_acc hO w χ hχ, child_not hO w χ hχ⟩

end Pass

/-- ⭐Under D every world has a proper successor (`D_box` refutes `□⊥`). -/
theorem exists_succO (hO : ModalSys.Opt = true) [Countable σ.FuncSyms] [Countable σ.RelSyms]
    (hD : ModalSys.D = true) (w : World σ N₀) : ∃ w' : World σ N₀, AccO hO w w' := by
  have hnot : (⟨(0, 0), .box .bot⟩ : w.L.sys.Sentence σ) ∉ w.T := fun h =>
    w.mcs.bot_not_mem (World.mem_of_provable (Δ := [.box .bot])
      (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact h)
      ⟨Proof.D_box hD (Proof.lookup List.mem_cons_self)⟩)
  obtain ⟨w', ha, -⟩ := exists_box_failO hO w (i := (0, 0)) .bot hnot
  exact ⟨w', ha⟩

end OCanon

end V12M
