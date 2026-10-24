import QML.QML_v12m_GCompleteness
import QML.QML_v12m_BCompactness

/-!
# QML v12m — the growing tree: every presented context, strong completeness, compactness

`completenessG` speaks of a world language `ctxOf l`.  A presented context may show view items;
it is flattened into a world language as for B (`BFlat`), with the growing tree's child edge as
the pair for each view.

* `gpair`: the child edge and its pull-back (`sim_gchild_pull`), a `Pair` for the `□` view and for
  a `◇_x` view alike.  Under 4 a `□` view also shows kept items, which is why B's own pair
  (`pairBox`, 4 off) does not serve.
* `CtxExpr.gchain`: every well-formed presentation flattens into a world language.
* ⭐`completenessG_presented`, ⭐`model_existenceG`, ⭐`strong_completenessG`, ⭐`compactnessG`.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature}

/-! ## The child edge as a pair -/

/-- ⭐**The child edge, as a pair**: the child's map, and its pull-back. -/
noncomputable def gpair (hF : ModalSys.Four = true) (l : List VarType) (k : Option VarSymb)
    (X : VarType) (hk : KContent (ctxOf l) k X) :
    Pair σ ((ctxOf l).kView k) (ctxOf (childL l k X)) where
  ι := eIdx (ofRen (gchildMap l k))
  ι' := gpullIdx l k X
  ι₃ := id
  θ := eS σ (ctxOf (childL l k X)) (ofRen (gchildMap l k))
  θ' := gpullS hF σ l k X hk
  θ₃ := Subst.idS σ ((ctxOf l).kView k)
  hθ := ok_eS_kView (entOk_ofRen (itemOk_gchild hF l hk))
  hc := coh_eS_kView (entOk_ofRen (itemOk_gchild hF l hk))
  hθ' := ok_gpullS hF l k X hk
  hc' := coh_gpullS hF l k X hk
  hθ₃ := Subst.ok_idS
  hc₃ := Subst.coh_idS
  sim := sim_gchild_pull hF l hk
  simId := fun _ _ _ => .refl _

/-- ⭐**Every well-formed presentation flattens into a world language**, as for B: a declared
    root by `Chain.insertRoot`, a view by the chain pushed under it and then the child edge. -/
noncomputable def _root_.V12M.CtxExpr.gchain (hF : ModalSys.Four = true) :
    (e : CtxExpr) → e.Fresh → e.Views → Σ l : List VarType, Chain σ e.denote (ctxOf l)
  | .empty, _, _ => ⟨[], .nil ⟨.empty, trivial, rfl⟩⟩
  | .insertFree e u T, h, hv =>
      ⟨T :: (e.gchain hF h.1 hv).1,
        (e.gchain hF h.1 hv).2.insertRoot T u (e.gchain hF h.1 hv).1.length h.2
          (ctxOf_fresh le_rfl)⟩
  | .boxIn e, h, hv =>
      ⟨(e.gchain hF h hv).1.map VarType.gc,
        ((e.gchain hF h hv).2.box).snoc
          (gpair hF _ none .VTypeOne (kContent_none _ _)) inferInstance⟩
  | .diaIn e _, h, hv =>
      ⟨((e.gchain hF h hv.1).2.witness hv.2.choose_spec).choose ::
          (e.gchain hF h hv.1).1.map VarType.gc,
        ((e.gchain hF h hv.1).2.dia hv.2.choose_spec).snoc
          (gpair hF _ (some _) _ fun _ e' => by
            cases e'
            exact ((e.gchain hF h hv.1).2.witness hv.2.choose_spec).choose_spec)
          inferInstance⟩

/-! ## Completeness in every presented context -/

variable [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoT] [ModalSys.NoSym]

/-- Completeness for 4 in any context flattened into a world language. -/
theorem completenessG_flat (hF : ModalSys.Four = true) {Γ : Ctx} {l : List VarType}
    (F : Flat σ Γ (ctxOf l)) (hnp : Γ.NoProjLast) {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0}
    (hval : ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W}
      (env : M.Env Γ w), Γ.NoProjLast →
      (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ := by
  refine F.prov (completenessG hF ?_)
  intro M hM w e _ hΔ
  rw [F.sat]
  exact hval M hM _ hnp fun ψ hψ => (F.sat e ψ).mp (hΔ _ (List.mem_map_of_mem hψ))

/-- ⭐**Completeness for 4 in every presented context** whose views are at declared witnesses
    (T and B off; D and strong 4 free). -/
theorem completenessG_presented (hF : ModalSys.Four = true) (e : CtxExpr) (he : e.Wf)
    {Δ : List (WFF σ e.denote 0)} {φ : WFF σ e.denote 0}
    (hval : ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W}
      (env : M.Env e.denote w),
      e.denote.NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ :=
  letI : e.denote.Presented := ⟨e, he.1, rfl⟩
  completenessG_flat hF (e.gchain hF he.1 he.2).2.toFlat (Ctx.Presented.noProjLast _) hval

/-! ## Model existence, strong completeness, compactness -/

/-- Model existence at a world language: the canonical model over a maximal consistent
    extension satisfies the set at its root. -/
theorem model_existenceG_ctxOf (hF : ModalSys.Four = true) {l₀ : List VarType}
    {S : Set (WFF σ (ctxOf l₀) 0)} (hS : WFF.SetConsistent S) : WFF.SetSatisfiable S := by
  obtain ⟨hSM, hM₀⟩ := complete_spec (setConsistent_iff.mp hS)
  obtain ⟨hle, htruth, hmem₀⟩ := exists_canonG hF hM₀
  have hag : Model.Env.Agree hle (fun v T hv => gcanonEnv hM₀ (groot hF _) 0 v T (hle v T hv))
      (gcanonEnv hM₀ (groot hF _) 0) := fun _ _ _ => rfl
  exact ⟨gmodel hF hM₀, gmodel_indInvariant hF hM₀, groot hF _,
    fun v T hv => gcanonEnv hM₀ (groot hF _) 0 v T (hle v T hv),
    fun ψ hψ => (Model.sat_mono hag ψ).mp ((htruth _).mpr (hmem₀ ψ (hSM hψ)))⟩

/-- ⭐**Model existence** for 4 in every presented context whose presentation is
    well-formed. -/
theorem model_existenceG (hF : ModalSys.Four = true) (e : CtxExpr) (he : e.Wf)
    {S : Set (WFF σ e.denote 0)} (hS : WFF.SetConsistent S) : WFF.SetSatisfiable S :=
  letI : e.denote.Presented := ⟨e, he.1, rfl⟩
  ((e.gchain hF he.1 he.2).2.toFlat).setSatisfiable
    (model_existenceG_ctxOf hF (((e.gchain hF he.1 he.2).2.toFlat).setConsistent hS))

/-- ⭐**Strong completeness for 4**: a formula true in every model, world and environment
    satisfying a set of premises is derivable from finitely many of them. -/
theorem strong_completenessG (hF : ModalSys.Four = true) (e : CtxExpr) (he : e.Wf)
    {S : Set (WFF σ e.denote 0)} {φ : WFF σ e.denote 0}
    (hval : ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W} (env : M.Env e.denote w),
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
  obtain ⟨M, hM, w, env, hsat⟩ := model_existenceG hF e he hcons
  exact hsat φ.neg (Set.mem_insert _ _)
    (hval M hM env fun ψ hψ => hsat ψ (Set.mem_insert_of_mem _ hψ))

/-- ⭐**Compactness for 4**: a set of formulas is satisfiable when every finite subset is — in
    models of any universe. -/
theorem compactnessG (hF : ModalSys.Four = true) (e : CtxExpr) (he : e.Wf)
    {S : Set (WFF σ e.denote 0)}
    (hfin : ∀ Δ : List (WFF σ e.denote 0), (∀ ψ ∈ Δ, ψ ∈ S) →
      ∃ (M : Model.{u, v} σ) (_ : M.IndInvariant) (w : M.frame.W) (env : M.Env e.denote w),
        ∀ ψ ∈ Δ, M.sat env ψ) :
    WFF.SetSatisfiable S := by
  letI : e.denote.Presented := ⟨e, he.1, rfl⟩
  refine model_existenceG hF e he fun Δ hΔ ⟨p⟩ => ?_
  obtain ⟨M, hM, w, env, hsat⟩ := hfin Δ hΔ
  exact Model.soundness p M hM env (Ctx.Presented.tame _) (Ctx.Presented.noProjLast _) hsat

end GArrow

end V12M
