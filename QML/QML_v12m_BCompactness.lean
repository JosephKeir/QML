import QML.QML_v12m_BFlat
import QML.QML_v12m_Compactness

/-!
# QML v12m — strong completeness and compactness for weak B

* ⭐`model_existenceB`: every consistent set of formulas in a presented context is satisfiable.  At a
  world language this is the canonical model over a maximal consistent extension of the set, at its
  root; a presentation is reduced to that case by its flattening, along which consistency and
  satisfiability both travel (`Flat.setConsistent`, `Flat.setSatisfiable`).
* ⭐`strong_completenessB`: a formula true in every model of a set of premises is derivable from
  finitely many of them.
* ⭐`compactnessB`: a set is satisfiable when each of its finite subsets is.

Unlike the staged construction, no reserved names are needed: the network makes its own.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoTFour]

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoTFour] in
theorem setConsistent_iff {Γ : Ctx} {S : Set (WFF σ Γ 0)} :
    WFF.SetConsistent S ↔ Theory.Consistent S :=
  ⟨fun h ⟨L, hL, p⟩ => h L hL p, fun h L hL p => h ⟨L, hL, p⟩⟩

/-! ## Model existence -/

/-- ⭐**Model existence at a world language**: the canonical model over a maximal consistent
    extension satisfies the set at its root. -/
theorem model_existenceB_ctxOf (hB : ModalSys.B = true) {l₀ : List VarType}
    {S : Set (WFF σ (ctxOf l₀) 0)} (hS : WFF.SetConsistent S) : WFF.SetSatisfiable S := by
  obtain ⟨hSM, hM₀⟩ := complete_spec (setConsistent_iff.mp hS)
  let B := bdata hB hM₀
  let s : B.W := B.actual
  have hle : (ctxOf l₀).Le ((B.w s).ctx 0) :=
    ctxOf_le_of_suffix (lang_suffix hB hM₀ (Nat.zero_le _) trivial)
  have hag : Model.Env.Agree hle (fun v T hv => B.canonEnv s 0 v T (hle v T hv))
      (B.canonEnv s 0) := fun _ _ _ => rfl
  have hg := (ext_net hB hM₀ (Nat.zero_le (birth (complete S) s.2 + 0))).grows [] trivial
  refine ⟨B.model, s, fun v T hv => B.canonEnv s 0 v T (hle v T hv), fun ψ hψ => ?_⟩
  refine (Model.sat_mono hag ψ).mp ((BData.truth s 0 _).mpr ?_)
  exact hg.sub ψ (show ψ ∈ ((net (complete S) 0).st []).M from hSM hψ)

/-! ## Along a flattening -/

omit [ModalSys] [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoTFour] in
/-- A list of images has a list of preimages. -/
theorem list_preimage {α β : Type} {f : α → β} {P : Set α} :
    ∀ L : List β, (∀ y ∈ L, ∃ x ∈ P, y = f x) →
      ∃ M : List α, (∀ x ∈ M, x ∈ P) ∧ M.map f = L
  | [], _ => ⟨[], by simp, rfl⟩
  | y :: L, h => by
      obtain ⟨x, hx, rfl⟩ := h y List.mem_cons_self
      obtain ⟨M, hM, hML⟩ := list_preimage L fun z hz => h z (List.mem_cons_of_mem _ hz)
      refine ⟨x :: M, fun z hz => ?_, by simp [hML]⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hx
      · exact hM z hz

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoTFour] in
/-- Consistency travels along a translation. -/
theorem Flat.setConsistent {Γ Δ : Ctx} (F : Flat σ Γ Δ) {S : Set (WFF σ Γ 0)}
    (hS : WFF.SetConsistent S) : WFF.SetConsistent (F.tr '' S) := by
  intro L hL p
  obtain ⟨M, hM, rfl⟩ := list_preimage (f := F.tr) (P := S) L fun y hy => by
    obtain ⟨ψ, hψ, rfl⟩ := hL y hy
    exact ⟨ψ, hψ, rfl⟩
  refine hS M hM (F.prov ?_)
  rwa [F.bot]

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoTFour] in
/-- Satisfiability travels back along a translation. -/
theorem Flat.setSatisfiable {Γ Δ : Ctx} (F : Flat σ Γ Δ) {S : Set (WFF σ Γ 0)}
    (h : WFF.SetSatisfiable (F.tr '' S)) : WFF.SetSatisfiable S := by
  obtain ⟨M, w, env, hsat⟩ := h
  exact ⟨M, w, F.env env, fun ψ hψ => (F.sat env ψ).mp (hsat _ ⟨ψ, hψ, rfl⟩)⟩

/-- ⭐**Model existence** in every presented context whose presentation is fresh. -/
theorem model_existenceB (hB : ModalSys.B = true) (e : CtxExpr) (he : e.Fresh)
    {S : Set (WFF σ e.denote 0)} (hS : WFF.SetConsistent S) : WFF.SetSatisfiable S :=
  letI : e.denote.Presented := ⟨e, rfl⟩
  ((e.chain he).2.toFlat).setSatisfiable
    (model_existenceB_ctxOf hB (((e.chain he).2.toFlat).setConsistent hS))

/-! ## Strong completeness and compactness -/

/-- ⭐**Strong completeness for weak B**: a formula true in every model, world and environment
    satisfying a set of premises is derivable from finitely many of them. -/
theorem strong_completenessB (hB : ModalSys.B = true) (e : CtxExpr) (he : e.Fresh)
    {S : Set (WFF σ e.denote 0)} {φ : WFF σ e.denote 0}
    (hval : ∀ (M : Model.{0, 0} σ) {w : M.frame.W} (env : M.Env e.denote w),
      (∀ ψ ∈ S, M.sat env ψ) → M.sat env φ) :
    ∃ Δ : List (WFF σ e.denote 0), (∀ ψ ∈ Δ, ψ ∈ S) ∧ Provable Δ φ := by
  by_contra hno
  have hcons : WFF.SetConsistent (insert φ.neg S) := by
    intro Δ hΔ p
    refine hno ⟨Δ.filter (· ≠ φ.neg), fun ψ hψ => ?_, Provable.byContra (Provable.mono ?_ p)⟩
    · obtain ⟨hψΔ, hne⟩ := List.mem_filter.mp hψ
      exact (Set.mem_insert_iff.mp (hΔ ψ hψΔ)).resolve_left (by simpa using hne)
    · intro θ hθ
      by_cases h : θ = φ.neg
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hθ, by simpa using h⟩)
  obtain ⟨M, w, env, hsat⟩ := model_existenceB hB e he hcons
  exact hsat φ.neg (Set.mem_insert _ _)
    (hval M env fun ψ hψ => hsat ψ (Set.mem_insert_of_mem _ hψ))

/-- ⭐**Compactness for weak B**: a set of formulas is satisfiable when every finite subset is —
    in models of any universe. -/
theorem compactnessB (hB : ModalSys.B = true) (e : CtxExpr) (he : e.Fresh)
    {S : Set (WFF σ e.denote 0)}
    (hfin : ∀ Δ : List (WFF σ e.denote 0), (∀ ψ ∈ Δ, ψ ∈ S) →
      ∃ (M : Model.{u, v} σ) (w : M.frame.W) (env : M.Env e.denote w), ∀ ψ ∈ Δ, M.sat env ψ) :
    WFF.SetSatisfiable S := by
  letI : e.denote.Presented := ⟨e, rfl⟩
  refine model_existenceB hB e he fun Δ hΔ ⟨p⟩ => ?_
  obtain ⟨M, w, env, hsat⟩ := hfin Δ hΔ
  exact Model.soundness p M env (Ctx.Presented.noProjLast _) hsat

end BArrow

end V12M
