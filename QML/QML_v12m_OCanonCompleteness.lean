import QML.QML_v12m_OCanonTruth

/-!
# QML v12m — completeness with `Opt` on (K and D)

The root is built as a child is (`OCanonChild`), in two passes over the user's context `Γ`: the
first is the plain Henkin world refuting the sequent, whose theory decides which of `Γ`'s witnesses
are present; the second opens those (finitely many: `Ctx.Presented.wit_finite`) and starts from the
first pass's theory, consistent because opening a present witness is conservative
(`Proof.unopens`).  The root then decides its witnesses (`DecidesO`), so the truth lemma holds
there, and the canonical environment read back over `Γ` refutes the sequent.

⭐`OCanon.completeness`: with `Opt` on, a sequent in a presented context that holds in every model
is provable — in every system `Opt` allows (K and D, weak and strong D).
-/

namespace V12M

variable [ModalSys]

/-- The witnesses of a presented context are finitely many: a view's are the reachable possible
    addresses below it. -/
theorem CtxExpr.wit_finite : ∀ e : CtxExpr, {y | ∃ X, e.denote.wit y = some X}.Finite
  | .empty => Set.finite_empty.subset fun _ ⟨_, h⟩ => by cases h
  | .insertFree e _ _ => CtxExpr.wit_finite e
  | .boxIn e => (Ctx.Fin.reach (CtxExpr.fin e)).subset fun y ⟨_, hX⟩ => by
      change (e.denote.ref y).isSome
      rw [(Ctx.boxIn_wit.mp hX).2]
      rfl
  | .diaIn e _ => (Ctx.Fin.reach (CtxExpr.fin e)).subset fun y ⟨_, hX⟩ => by
      change (e.denote.ref y).isSome
      rw [(Ctx.boxIn_wit.mp hX).2]
      rfl
  | .optIn e k y => by
      change {z | ∃ X, (e.denote.optInK k y).wit z = some X}.Finite
      rw [Ctx.optInK_wit]; exact CtxExpr.wit_finite e

theorem Ctx.Presented.wit_finite (Γ : Ctx) [h : Γ.Presented] :
    {y | ∃ X, Γ.wit y = some X}.Finite :=
  h.denote_eq ▸ CtxExpr.wit_finite h.expr

namespace OCanon

open Canon

/-- The witnesses of a presented context with `P`, as a list. -/
noncomputable def witList (Γ : Ctx) [Γ.Presented] (P : VarSymb → Prop) : List VarSymb :=
  ((Ctx.Presented.wit_finite Γ).subset fun _ hy => hy.1 :
    {y | (∃ X, Γ.wit y = some X) ∧ P y}.Finite).toFinset.toList

theorem mem_witList {Γ : Ctx} [Γ.Presented] {P : VarSymb → Prop} {y : VarSymb} :
    y ∈ witList Γ P ↔ (∃ X, Γ.wit y = some X) ∧ P y := by
  rw [witList, Finset.mem_toList, Set.Finite.mem_toFinset]
  rfl

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms] (hO : ModalSys.Opt = true)

include hO in
/-- ⭐**Completeness with `Opt` on**: a sequent in a presented context that holds in every model,
    at every world, in every environment, is provable. -/
theorem completeness {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0}
    (hval : ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W} (env : M.Env Γ w),
      Γ.NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ := by
  by_contra hnp
  have hfresh : ∀ d n, Γ.RootFresh (.free (Canon.names (Ctx.Presented.bound Γ) d n)) :=
    fun _ _ => Ctx.Presented.fresh_bound _ (Nat.le_add_right _ _)
  -- the first pass: the plain world refuting the sequent
  let L₀ : WorldLang := WorldLang.const Γ (fun _ => .VTypeOne)
    (Canon.names (Ctx.Presented.bound Γ) 0) (Canon.names_injective _ _) (hfresh 0)
  let S₀ : Set ((L₀.pre []).Sentence σ) := {s | ∃ ψ ∈ Δ, s = ⟨0, ψ⟩} ∪ {⟨0, φ.neg⟩}
  have hS₀ : StageSys.Consistent S₀ := by
    rintro m ⟨Δ', hΔ', p⟩
    refine hnp (Provable.byContra (Provable.mono (fun δ hδ => ?_) p))
    obtain ⟨s, hs, hle, rfl⟩ := hΔ' δ hδ
    rcases hs with ⟨ψ, hψ, rfl⟩ | hs
    · convert (List.mem_cons_of_mem φ.neg hψ : ψ ∈ φ.neg :: Δ) using 1
      exact WFF.mono_refl _ _
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      convert (List.mem_cons_self : φ.neg ∈ φ.neg :: Δ) using 1
      exact WFF.mono_refl _ _
  let w₁ : Canon.World σ (Ctx.Presented.bound Γ) :=
    Canon.World.ofHenkin 0 L₀ (fun _ => rfl) (fun _ d n _ => hfresh d n) S₀ hS₀ none
  -- presence, as the first pass decides it
  let P : VarSymb → Prop := fun y => ∃ hy : ∃ X, Γ.wit y = some X,
    (⟨(0, 0), WFF.optx hO .arrow y hy .top⟩ : w₁.L.sys.Sentence σ) ∈ w₁.T
  let Lr := witList Γ P
  have hlift : ∀ m : ℕ, ((0, 0) : ℕ × ℕ) ≤ (m, 0) := fun _ => ⟨Nat.zero_le _, le_rfl⟩
  -- the second pass: the present witnesses opened
  let L₁ : WorldLang := WorldLang.const (Γ.optIns Lr) (fun _ => .VTypeOne)
    (Canon.names (Ctx.Presented.bound Γ) 0) (Canon.names_injective _ _)
    (fun n => (hfresh 0 n).optIns Lr)
  let S₁ : Set ((L₁.pre []).Sentence σ) :=
    {s | ∃ ψ : WFF σ Γ 0, (⟨(s.1, 0), ψ⟩ : w₁.L.sys.Sentence σ) ∈ w₁.T ∧
      s.2 = WFF.mono (Ctx.le_optIns Γ Lr) ψ}
  have hS₁ : StageSys.Consistent S₁ := by
    intro m
    rintro ⟨Δ', hΔ', ⟨p⟩⟩
    have key : ∀ δ ∈ Δ', ∃ ψ : WFF σ Γ 0,
        (⟨(m, 0), ψ⟩ : w₁.L.sys.Sentence σ) ∈ w₁.T ∧
          WFF.mono (Ctx.le_optIns Γ Lr) ψ = δ := by
      intro δ hδ
      obtain ⟨s, ⟨ψ, hψ, hs⟩, hle, rfl⟩ := hΔ' δ hδ
      refine ⟨_, (World.mem_lift (w := w₁)
        (show ((s.1, 0) : ℕ × ℕ) ≤ (m, 0) from ⟨hle, le_rfl⟩)).mp hψ, ?_⟩
      rw [hs]
      change _ = WFF.mono _ (WFF.mono _ ψ)
      rw [WFF.mono_mono, WFF.mono_mono]
    obtain ⟨Δ₀, h₀, h₁⟩ := exists_list_map _ Δ' key
    obtain ⟨q⟩ := Provable.mono h₁ ⟨p⟩
    have q' := Proof.unopens hO (Γ := Γ) (Δ := Δ₀) Lr (fun y hy => (mem_witList.mp hy).1) q
    refine w₁.mcs.bot_not_mem (i := (m, 0))
      (World.mem_of_provable (w := w₁) (fun ψ hψ => ?_) ⟨q'⟩)
    rcases List.mem_append.mp hψ with h | h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
      obtain ⟨⟨X, hX⟩, ⟨_, hp⟩⟩ := mem_witList.mp hy
      rw [Proof.presence_eq hO hX]
      exact (World.mem_lift (w := w₁) (hlift m)).mp hp
    · exact h₀ ψ h
  let w₀ : Canon.World σ (Ctx.Presented.bound Γ) :=
    Canon.World.ofHenkin 0 L₁ (fun _ => rfl) (fun _ d n _ => (hfresh d n).optIns Lr) S₁ hS₁ none
  have hfirst : ∀ {m : ℕ} {ψ : WFF σ Γ 0}, (⟨(m, 0), ψ⟩ : w₁.L.sys.Sentence σ) ∈ w₁.T →
      (⟨(m, 0), WFF.mono (Ctx.le_optIns Γ Lr) ψ⟩ : w₀.L.sys.Sentence σ) ∈ w₀.T :=
    fun h => WorldLang.subset_finalT S₁ ⟨_, h, rfl⟩
  -- the root decides its witnesses
  have hdec : DecidesO hO w₀ := by
    intro m y X hX
    have hXΓ : Γ.wit y = some X := (Ctx.optIns_wit Γ Lr y).symm.trans hX
    by_cases hp : P y
    · exact Or.inl (Ctx.optIns_content (mem_witList.mpr ⟨⟨X, hXΓ⟩, hp⟩) hXΓ)
    · right
      have hn : (⟨(m, 0), WFF.optx hO .arrow y ⟨X, hXΓ⟩ .top⟩ : w₁.L.sys.Sentence σ) ∉ w₁.T :=
        fun h => hp ⟨⟨X, hXΓ⟩, (World.mem_lift (w := w₁) (hlift m)).mpr h⟩
      exact hfirst (w₁.mcs.neg_mem_iff.mpr hn)
  -- the canonical environment read back over `Γ`
  have hle : Γ.Le (w₀.L.ctx (0, 0)) := Ctx.le_optIns Γ Lr
  have hag := Model.Env.agree_restrict hle (canonEnvO hO w₀ w₀ (0, 0))
  have hwag : ModalSys.Opt = true → Model.Env.WitAgree hle
      ((canonEnvO hO w₀ w₀ (0, 0)).restrict hle) (canonEnvO hO w₀ w₀ (0, 0)) :=
    fun _ _ _ _ => rfl
  have hsat := hval (model hO w₀) (indInvariant hO w₀) (w := w₀)
    ((canonEnvO hO w₀ w₀ (0, 0)).restrict hle) (Ctx.Presented.noProjLast Γ)
    (fun ψ hψ => (Model.sat_mono hag ψ hwag).mp ((truth hO w₀ hdec (0, 0) _).mpr
      (hfirst (WorldLang.subset_finalT S₀ (Or.inl ⟨ψ, hψ, rfl⟩)))))
  have hmem := (truth hO w₀ hdec (0, 0) _).mp ((Model.sat_mono hag φ hwag).mpr hsat)
  have hneg := hfirst (WorldLang.subset_finalT (L := L₀) S₀ (m := 0) (φ := φ.neg) (Or.inr rfl))
  exact (w₀.mcs.neg_mem_iff.mp hneg) hmem

include hO in
/-- ⭐**Soundness and completeness with `Opt` on**: over a countable signature, a sequent in a
    presented context is provable exactly when it holds in every model. -/
theorem provable_iff_valid {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} :
    Provable Δ φ ↔ ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W} (env : M.Env Γ w),
      Γ.NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ :=
  ⟨fun ⟨p⟩ M hM _ env hnp =>
    Model.soundness p M hM env (Ctx.Presented.tame Γ) hnp
      (env.openedT_off fun h => absurd (ModalSys.noOpt_of_T h.1) (by rw [hO]; decide)),
    completeness hO⟩

end OCanon

end V12M
