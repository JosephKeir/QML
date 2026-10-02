import QML.QML_v12m_CanonInd

/-!
# QML v12m — the truth lemma and completeness

* ⭐`Canon.truth`: at every world and stage of the canonical model, the canonical environment
  satisfies exactly the formulas of the world's theory.  By induction on the size of the formula
  (which substitution and collapsing do not change): atoms and equations by the truth lemma for
  terms, the connectives by maximality, the quantifiers by definability of every object and the
  witnesses, `□` by the necessary contents and `exists_box_fail` — at the world itself under T by
  `Model.sat_boxHere` and the rule `T_box`, at a far successor under 4 by `four_box`, the necessary
  contents of the first step and `Model.sat_shift_twoBox` — `◇_x` by `exists_dia` and the
  `□_x`-necessary contents of the extent.
* ⭐`completeness`: over a countable signature, a sequent in a presented context valid in every
  model is provable.
* ⭐`provable_iff_valid`: with soundness.
-/

namespace V12M

variable [ModalSys]

/-! ## Size -/

/-- The size of the defined equality at a type.  `eqRec A t s` is assembled from `A` alone — `.eq`
    at base, `.and` at a product, `.box` under `□`, `□_x` at `◇` — so its size is a function of the
    type and not of the terms (⭐`WFF.size_eqRec`).  This is what lets `WFF.size` give a `Here`
    formula room for the equation its functionality concludes, so that the truth lemma's `here` case
    may appeal to its own induction hypothesis at that equation rather than to a separate
    faithfulness lemma. -/
def VarType.eqRecSize : VarType → ℕ
  | .Var => 0
  | .VTypeOne => 0
  | .VTypeProd A B => A.eqRecSize + B.eqRecSize + 1
  | .VTypeBox A => A.eqRecSize + 1
  | .VTypeDia A => A.eqRecSize + 3

/-- The size of a formula, ignoring its terms. -/
def WFF.size {σ : Signature} : {Γ : Ctx} → {d : ℕ} → WFF σ Γ d → ℕ
  | _, _, .atom _ => 0
  | _, _, .eq _ _ => 0
  | _, _, .top => 0
  | _, _, .bot => 0
  | _, _, .and φ ψ => φ.size + ψ.size + 1
  | _, _, .or φ ψ => φ.size + ψ.size + 1
  | _, _, .imp φ ψ => φ.size + ψ.size + 1
  | _, _, .all _ φ => φ.size + 1
  | _, _, .ex _ φ => φ.size + 1
  | _, _, .box φ => φ.size + 1
  | _, _, .dia _ _ φ => φ.size + 1
  | _, _, .here (A := A) _ _ _ => A.eqRecSize + 1

/-- ⭐The size of an equality is the size of its type: nothing in `eqRec`'s clauses looks at the
    terms.  So the `here` clause of `WFF.size` above dominates the equation `Proof.here_fun`
    concludes. -/
theorem WFF.size_eqRec {σ : Signature} : {Γ : Ctx} → {d : ℕ} → (A : VarType) → {a : Ann A} →
    (t s : Term σ Γ A a) → (eqRec A t s : WFF σ Γ d).size = A.eqRecSize
  | _, _, .Var, .var, t, s => by rw [eqRec_Var t s]; rfl
  | _, _, .VTypeOne, .one, .unit, .unit => rfl
  | _, _, .VTypeProd A B, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ => by
      change (WFF.and (eqRec A t₁ s₁) (eqRec B t₂ s₂)).size = _
      simp only [WFF.size, WFF.size_eqRec A t₁ s₁, WFF.size_eqRec B t₂ s₂, VarType.eqRecSize]
  | _, _, .VTypeBox A, .box _, .boxtm t, .boxtm s => by
      change (WFF.box (eqRec A t s)).size = _
      simp only [WFF.size, WFF.size_eqRec A t s, VarType.eqRecSize]
  | _, _, .VTypeDia A, .dia x _, .diatm _ hx t, .diatm _ _ s => by
      change (WFF.boxx x hx (eqRec A t s)).size = _
      simp only [WFF.size, WFF.size_eqRec A t s, VarType.eqRecSize]

theorem WFF.size_mono {σ : Signature} : ∀ {Γ Γ' : Ctx} {d : ℕ} (h : Γ.Le Γ') (φ : WFF σ Γ d),
    (WFF.mono h φ).size = φ.size
  | _, _, _, _, .atom _ => rfl
  | _, _, _, _, .eq _ _ => rfl
  | _, _, _, _, .top => rfl
  | _, _, _, _, .bot => rfl
  | _, _, _, h, .and φ ψ => congrArg₂ (· + · + 1) (WFF.size_mono h φ) (WFF.size_mono h ψ)
  | _, _, _, h, .or φ ψ => congrArg₂ (· + · + 1) (WFF.size_mono h φ) (WFF.size_mono h ψ)
  | _, _, _, h, .imp φ ψ => congrArg₂ (· + · + 1) (WFF.size_mono h φ) (WFF.size_mono h ψ)
  | _, _, _, h, .all T φ => congrArg (· + 1) (WFF.size_mono (h.insert _ T) φ)
  | _, _, _, h, .ex T φ => congrArg (· + 1) (WFF.size_mono (h.insert _ T) φ)
  | _, _, _, h, .box φ => congrArg (· + 1) (WFF.size_mono h.boxIn φ)
  | _, _, _, h, .dia x _ φ => congrArg (· + 1) (WFF.size_mono (h.diaIn x) φ)
  | _, _, _, _, .here _ _ _ => rfl

theorem WFF.size_subst {σ : Signature} : ∀ {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d d' : ℕ}
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom d)
    (hΔ : Δ.SlotsFrom d') (φ : WFF σ Γ d), (WFF.subst ι θ hθ hc hΓ hΔ φ).size = φ.size
  | _, _, _, _, _, _, _, _, _, _, .atom _ => rfl
  | _, _, _, _, _, _, _, _, _, _, .eq _ _ => rfl
  | _, _, _, _, _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .and φ ψ =>
      congrArg₂ (· + · + 1) (WFF.size_subst θ hθ hc hΓ hΔ φ) (WFF.size_subst θ hθ hc hΓ hΔ ψ)
  | _, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .or φ ψ =>
      congrArg₂ (· + · + 1) (WFF.size_subst θ hθ hc hΓ hΔ φ) (WFF.size_subst θ hθ hc hΓ hΔ ψ)
  | _, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .imp φ ψ =>
      congrArg₂ (· + · + 1) (WFF.size_subst θ hθ hc hΓ hΔ φ) (WFF.size_subst θ hθ hc hΓ hΔ ψ)
  | _, _, _, _, _, _, _, _, _, _, .all _ φ => congrArg (· + 1) (WFF.size_subst _ _ _ _ _ φ)
  | _, _, _, _, _, _, _, _, _, _, .ex _ φ => congrArg (· + 1) (WFF.size_subst _ _ _ _ _ φ)
  | _, _, _, _, _, _, _, _, _, _, .box φ => congrArg (· + 1) (WFF.size_subst _ _ _ _ _ φ)
  | _, _, _, _, _, _, _, _, _, _, .dia _ _ φ => congrArg (· + 1) (WFF.size_subst _ _ _ _ _ φ)
  | _, _, _, _, _, _, _, _, _, _, .here _ _ _ => rfl

theorem WFF.size_instantiate {σ : Signature} {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {T : VarType}
    {a : Ann T} (t : Term σ Γ T a) (φ : WFF σ (Γ.insert (.bnd d) T) (d + 1)) :
    (WFF.instantiate hs t φ).size = φ.size :=
  WFF.size_subst _ _ _ _ _ φ

theorem WFF.size_collapse {σ : Signature} : ∀ {k : ℕ} {Γ₁ Γ₂ : Ctx} {d : ℕ}
    (h : Ctx.Collapses k Γ₁ Γ₂) (hs : Γ₁.SlotsFrom d) (φ : WFF σ Γ₁ d),
    (WFF.collapse h hs φ).size = φ.size
  | _, _, _, _, _, _, .atom _ => rfl
  | _, _, _, _, _, _, .eq _ _ => rfl
  | _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, h, hs, .and φ ψ =>
      congrArg₂ (· + · + 1) (WFF.size_collapse h hs φ) (WFF.size_collapse h hs ψ)
  | _, _, _, _, h, hs, .or φ ψ =>
      congrArg₂ (· + · + 1) (WFF.size_collapse h hs φ) (WFF.size_collapse h hs ψ)
  | _, _, _, _, h, hs, .imp φ ψ =>
      congrArg₂ (· + · + 1) (WFF.size_collapse h hs φ) (WFF.size_collapse h hs ψ)
  | _, _, _, _, _, _, .all _ φ => congrArg (· + 1) (WFF.size_collapse _ _ φ)
  | _, _, _, _, _, _, .ex _ φ => congrArg (· + 1) (WFF.size_collapse _ _ φ)
  | _, _, _, _, _, _, .box φ => congrArg (· + 1) (WFF.size_collapse _ _ φ)
  | _, _, _, _, _, _, .dia _ _ φ => congrArg (· + 1) (WFF.size_collapse _ _ φ)
  | _, _, _, _, _, _, .here _ _ _ => rfl

theorem WFF.size_shift {σ : Signature} : ∀ {k : ℕ} {Γ₁ Γ₂ : Ctx} {d : ℕ}
    (h : Ctx.Shifts k Γ₁ Γ₂) (hs : Γ₁.SlotsFrom d) (φ : WFF σ Γ₁ d),
    (WFF.shift h hs φ).size = φ.size
  | _, _, _, _, _, _, .atom _ => rfl
  | _, _, _, _, _, _, .eq _ _ => rfl
  | _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, h, hs, .and φ ψ =>
      congrArg₂ (· + · + 1) (WFF.size_shift h hs φ) (WFF.size_shift h hs ψ)
  | _, _, _, _, h, hs, .or φ ψ =>
      congrArg₂ (· + · + 1) (WFF.size_shift h hs φ) (WFF.size_shift h hs ψ)
  | _, _, _, _, h, hs, .imp φ ψ =>
      congrArg₂ (· + · + 1) (WFF.size_shift h hs φ) (WFF.size_shift h hs ψ)
  | _, _, _, _, _, _, .all _ φ => congrArg (· + 1) (WFF.size_shift _ _ φ)
  | _, _, _, _, _, _, .ex _ φ => congrArg (· + 1) (WFF.size_shift _ _ φ)
  | _, _, _, _, _, _, .box φ => congrArg (· + 1) (WFF.size_shift _ _ φ)
  | _, _, _, _, _, _, .dia _ _ φ => congrArg (· + 1) (WFF.size_shift _ _ φ)
  | _, _, _, _, _, _, .here _ _ _ => rfl

/-- Abstracting a witness is a substitution, so it leaves the logical structure alone. -/
theorem WFF.size_diaAbs {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (c : ℕ) {A : VarType}
    (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    (χ : WFF σ (Γ.diaIn (.root (.free c))) 0) : (WFF.diaAbs c hcA hfr χ).size = χ.size :=
  WFF.size_subst _ _ _ _ _ χ

theorem WFF.size_hereRead {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true)
    {A : VarType} {a : Ann A} (t : Term σ Γ A a) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    (WFF.hereRead hT t ψ).size = ψ.size :=
  (WFF.size_instantiate _ _ _).trans (WFF.size_collapse _ _ ψ)

/-- ⭐So does realising one: `WFF.size` counts connectives, and the realisation only substitutes
    terms.  This is what keeps the truth lemma's induction going through the realised case, where
    the formula grows but its logical structure does not. -/
theorem WFF.size_realiseAt {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true) (c : ℕ)
    {A : VarType} (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    {a₀ : Ann A} (t₀ : Term σ Γ A a₀) (χ : WFF σ (Γ.diaIn (.root (.free c))) 0) :
    (WFF.realiseAt hT c hcA hfr t₀ χ).size = χ.size :=
  (WFF.size_hereRead hT t₀ _).trans (WFF.size_diaAbs c hcA hfr χ)

/-- The same at an arbitrary declared address. -/
theorem WFF.size_diaAbsA {σ : Signature} {Γ : Ctx} [Γ.Presented] (x : VarSymb) {A : VarType}
    (hxA : Γ.ref x = some (.VTypeDia A)) (χ : WFF σ (Γ.diaIn x) 0) :
    (WFF.diaAbsA x hxA χ).size = χ.size :=
  WFF.size_subst _ _ _ _ _ χ

/-- ⭐And realising at an arbitrary address keeps the logical size, which is what keeps the truth
    lemma's induction going through the realised case. -/
theorem WFF.size_realiseAtA {σ : Signature} {Γ : Ctx} [Γ.Presented] (hT : ModalSys.T = true)
    (x : VarSymb) {A : VarType} (hxA : Γ.ref x = some (.VTypeDia A)) {a₀ : Ann A}
    (t₀ : Term σ Γ A a₀) (χ : WFF σ (Γ.diaIn x) 0) :
    (WFF.realiseAtA hT x hxA t₀ χ).size = χ.size :=
  (WFF.size_hereRead hT t₀ _).trans (WFF.size_diaAbsA x hxA χ)

/-! ## Helpers -/

theorem Model.Env.Agree.refl' {σ : Signature} {M : Model.{u, v} σ} {Γ : Ctx} {w : M.frame.W}
    (env : M.Env Γ w) : Model.Env.Agree (Ctx.Le.refl Γ) env env :=
  fun _ _ _ => rfl

/-- `¬◇_x χ ⊢ □_x ¬χ`. -/
def Proof.boxx_neg_of_not_dia {σ : Signature} {Γ : Ctx} (x : VarSymb)
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (χ : WFF σ (Γ.diaIn x) 0) :
    Proof σ Γ [(WFF.dia x hx χ).neg] (WFF.boxx x hx χ.neg) :=
  .imp_intro (.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
    (Proof.ofSubset (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | h
        · exact List.mem_cons_self
        · simp at h)
      (Proof.K_dia (Δ₁ := []) (Δ₂ := []) (ψ := χ.neg.neg) (φ := χ) x hx
        (Proof.byContra (.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
          (Proof.lookup List.mem_cons_self))))))

namespace Canon

variable {σ : Signature} {N₀ : ℕ} (w₀ : World σ N₀) [Countable σ.FuncSyms] [Countable σ.RelSyms]
  [ModalSys.NoB]

/-- The truth lemma for atoms. -/
theorem relSat_canon : ∀ {Γ : Ctx} {n : ℕ} (ρ : Rel σ Γ n) {w : World σ N₀} {i : ℕ × ℕ}
    {e : Γ.Le (w.L.ctx i)} {env : (model w₀).Env Γ w},
    Model.Env.Agree e env (canonEnv w₀ w i) →
    ∀ (args : Fin n → w.D) (ts : Fin n → Term σ Γ .Var .var),
      (∀ k, args k = w.cls i (Term.mono e (ts k))) →
      (Model.relSat env ρ args ↔
        (⟨i, WFF.mono e (.atom ((Spine.ofFn ts).fillR ρ))⟩ : w.L.sys.Sentence σ) ∈ w.T)
  | _, _, .R ⟨r, rfl⟩, w, i, e, _, _, args, ts, hts => by
      change canonRel w r (fun k => args (Fin.cast rfl k)) ↔ _
      rw [WFF.mono_fillR, Spine.mono_ofFn,
        show (fun k => args (Fin.cast rfl k)) = fun k => w.cls i (Term.mono e (ts k)) from
          funext fun k => hts k,
        canonRel_cls]
      rfl
  | _, _, .eval ρ t, w, i, e, env, hag, args, ts, hts => by
      change Model.relSat env ρ (Fin.cons (Model.interp env t) args) ↔ _
      have h0 : Model.interp env t = w.cls i (Term.mono e t) :=
        (interp_canon w₀ t hag).trans (rden_var_mono e t)
      rw [relSat_canon ρ hag (Fin.cons (Model.interp env t) args) (Fin.cons t ts)
        (fun k => by cases k using Fin.cases <;> simp [h0, hts]), Spine.ofFn_cons]
      rfl

/-- ⭐The realised case of the truth lemma's `◇` step: at the world itself, a formula holding in
    the witness's view holds of the realising term (`Model.sat_realiseAt`), and what the theory
    says about the realising term it says about the witness (`RealDatum.spec`).  The induction
    hypothesis is needed only at formulas of the same logical size (`WFF.size_realiseAt`). -/
theorem dia_mem_of_sat_self {w : World σ N₀} {i : ℕ × ℕ} {x : VarSymb}
    (dat : RealDatum σ w.L w.T x)
    (hdeclI : (w.L.ctx i).ref x = some (.VTypeDia dat.A))
    (hreal : w.real x = some dat) {X : VarType}
    (h : (w.L.ctx i).ref x = some (.VTypeDia X)) (hx : ∃ Y, (w.L.ctx i).ref x = some (.VTypeDia Y))
    (χ : WFF σ ((w.L.ctx i).diaIn x) 0)
    (IH : ∀ ψ : WFF σ (w.L.ctx (i ⊔ dat.i₀)) 0, ψ.size = χ.size →
      ((model w₀).sat (canonEnv w₀ w (i ⊔ dat.i₀)) ψ ↔
        (⟨i ⊔ dat.i₀, ψ⟩ : w.L.sys.Sentence σ) ∈ w.T))
    (hmem : (⟨w, ⟨R.refl dat.hT w⟩⟩ : Succ w) ∈ ((model w₀).posEval ((canonEnv w₀ w i).ref x h)).1)
    (hsat : (model w₀).sat
      ((canonEnv w₀ w i).diaPush x h ⟨⟨w, ⟨R.refl dat.hT w⟩⟩, hmem⟩) χ) :
    (⟨i, WFF.dia x hx χ⟩ : w.L.sys.Sentence σ) ∈ w.T := by
  have hXA : X = dat.A := by
    have h1 := h
    rw [hdeclI] at h1
    simp only [Option.some.injEq, VarType.VTypeDia.injEq] at h1
    exact h1.symm
  subst hXA
  have hj : i ≤ i ⊔ dat.i₀ := le_sup_left
  have hdecl := dat.hdeclOf (i ⊔ dat.i₀) ⟨dat.A, (w.L.ctx_le hj).ref hdeclI⟩
  have hagj : Model.Env.Agree (w.L.ctx_le hj) (canonEnv w₀ w i) (canonEnv w₀ w (i ⊔ dat.i₀)) :=
    canonEnv_le w₀ w hj
  have hm' : (⟨w, ⟨R.refl dat.hT w⟩⟩ : Succ w) ∈
      ((model w₀).posEval ((canonEnv w₀ w (i ⊔ dat.i₀)).ref x hdecl)).1 := by
    rw [canonEnv_extent]
    exact self_mem_extent (World.realised_of_real hreal)
  have hcont : ((model w₀).posEval
        ((canonEnv w₀ w (i ⊔ dat.i₀)).ref x hdecl)).2
          ⟨⟨w, ⟨R.refl dat.hT w⟩⟩, hm'⟩ =
      Model.interp (canonEnv w₀ w (i ⊔ dat.i₀))
        (Term.mono (w.L.ctx_le (le_sup_right : dat.i₀ ≤ i ⊔ dat.i₀)) dat.t₀) := by
    have hpq := canonEnv_ref w₀ w (i ⊔ dat.i₀) x hdecl
    rw [Model.posEval_snd_congr hpq ⟨⟨w, ⟨R.refl dat.hT w⟩⟩, hm'⟩ (hpq ▸ hm'),
      Model.interp_mono (canonEnv_le w₀ w (le_sup_right : dat.i₀ ≤ i ⊔ dat.i₀)) dat.t₀,
      interp_canon w₀ dat.t₀ (Model.Env.Agree.refl' _)]
    exact toDom_congr w₀ (rden_eta_of_real hreal hdecl) _ _
  have hsatR := (Model.sat_realiseAtA dat.hT (canonEnv w₀ w (i ⊔ dat.i₀)) (w.noProjLast _) hdecl
    (Term.mono (w.L.ctx_le le_sup_right) dat.t₀) hm' hcont
    (WFF.mono ((w.L.ctx_le hj).diaIn x) χ)).mpr
    ((Model.sat_mono (Model.Env.diaPush_agree hagj h
      ⟨⟨w, ⟨R.refl dat.hT w⟩⟩, hmem⟩ hm') χ).mpr hsat)
  have hdia := dat.spec w.mcs (i ⊔ dat.i₀) le_sup_right hdecl _
    ((IH _ (by rw [WFF.size_realiseAtA, WFF.size_mono])).mp hsatR)
  have hmem' := World.mem_mono_congr w (Ctx.Le.refl _) (w.L.ctx_le hj)
    (ψ := WFF.dia x hx χ) hdia
  rwa [WFF.mono_refl] at hmem'

theorem truth_lt : ∀ (n : ℕ) (w : World σ N₀) (i : ℕ × ℕ) (φ : WFF σ (w.L.ctx i) 0), φ.size < n →
    ((model w₀).sat (canonEnv w₀ w i) φ ↔ (⟨i, φ⟩ : w.L.sys.Sentence σ) ∈ w.T)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, w, i, φ, hφ => by
      cases φ with
      | atom ρ =>
          change Model.relSat (canonEnv w₀ w i) ρ Fin.elim0 ↔ _
          rw [relSat_canon w₀ ρ (Model.Env.Agree.refl' _) Fin.elim0 Fin.elim0 (fun k => k.elim0)]
          change (⟨i, WFF.mono (Ctx.Le.refl _) (.atom ρ)⟩ : w.L.sys.Sentence σ) ∈ w.T ↔ _
          rw [WFF.mono_refl]
      | eq t s =>
          change Model.interp (canonEnv w₀ w i) t = Model.interp (canonEnv w₀ w i) s ↔ _
          rw [interp_canon w₀ t (Model.Env.Agree.refl' _),
            interp_canon w₀ s (Model.Env.Agree.refl' _)]
          change rden w i (Ctx.Le.refl _) t = rden w i (Ctx.Le.refl _) s ↔ _
          rw [rden_var_cls, rden_var_cls, World.cls_eq_iff (le_refl i) (le_refl i)]
          change (⟨i, .eq (Term.mono (w.L.ctx_le (le_refl i)) t)
            (Term.mono (w.L.ctx_le (le_refl i)) s)⟩ : w.L.sys.Sentence σ) ∈ w.T ↔ _
          rw [Term.mono_refl, Term.mono_refl]
      | top => exact ⟨fun _ => w.mcs.top_mem, fun _ => trivial⟩
      | bot => exact ⟨False.elim, fun h => w.mcs.bot_not_mem h⟩
      | and φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change _ ∧ _ ↔ _
          rw [truth_lt n w i φ h₁, truth_lt n w i ψ h₂, w.mcs.and_mem_iff]
      | or φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change _ ∨ _ ↔ _
          rw [truth_lt n w i φ h₁, truth_lt n w i ψ h₂, w.mcs.or_mem_iff]
      | imp φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (_ → _) ↔ _
          rw [truth_lt n w i φ h₁, truth_lt n w i ψ h₂, w.mcs.imp_mem_iff]
      | all A ψ =>
          have hψ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (∀ o : (model w₀).frame.Dom A w,
            (model w₀).sat ((canonEnv w₀ w i).extend (.bnd 0) o) ψ) ↔ _
          constructor
          · intro hsat
            by_contra hnot
            obtain ⟨i', hi, a, t, hmem⟩ := w.allW hnot
            have hs₁ := (Model.sat_mono (Model.Env.extend_agree (canonEnv_le w₀ w hi) (.bnd 0)
              (Model.interp (canonEnv w₀ w i') t)) ψ).mpr (hsat _)
            have hs₂ := (Model.sat_instantiate (canonEnv w₀ w i') (w.noProjLast i')
              Ctx.NoSlots.slots t _).mpr hs₁
            have hs₃ := (truth_lt n w i' _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mp hs₂
            exact (w.mcs.neg_mem_iff.mp hmem) hs₃
          · intro hmem o
            obtain ⟨i', a, t', ht'⟩ := definable_fromDom w₀ A w o
            have hK : i ≤ i ⊔ i' := le_sup_left
            have hK' : i' ≤ i ⊔ i' := le_sup_right
            have ho : Model.interp (canonEnv w₀ w (i ⊔ i')) (w.liftT hK' t') = o :=
              (interp_canon w₀ _ (Model.Env.Agree.refl' _)).trans
                ((toDom_congr w₀ ((rden_mono _ t' w _ _).trans
                  ((rden_congr t' w _ i' _ _).trans ht')) _ _).trans (toDom_fromDom w₀ A w o))
            have hinst : (⟨i ⊔ i', WFF.instantiate Ctx.NoSlots.slots (w.liftT hK' t')
                (WFF.mono ((w.L.ctx_le hK).insert (.bnd 0) A) ψ)⟩ : w.L.sys.Sentence σ) ∈ w.T :=
              World.mem_of_provable
                (Δ := [WFF.all A (WFF.mono ((w.L.ctx_le hK).insert (.bnd 0) A) ψ)])
                (fun χ hχ => by
                  rw [List.mem_singleton.mp hχ]
                  exact (World.mem_lift hK).mp hmem)
                ⟨Proof.all_elim A (w.liftT hK' t') (Proof.lookup List.mem_cons_self)⟩
            have hs := (truth_lt n w (i ⊔ i') _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mpr hinst
            have hs₁ := (Model.sat_instantiate (canonEnv w₀ w (i ⊔ i')) (w.noProjLast _)
              Ctx.NoSlots.slots (w.liftT hK' t') _).mp hs
            rw [ho] at hs₁
            exact (Model.sat_mono (Model.Env.extend_agree (canonEnv_le w₀ w hK) (.bnd 0) o)
              ψ).mp hs₁
      | ex A ψ =>
          have hψ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (∃ o : (model w₀).frame.Dom A w,
            (model w₀).sat ((canonEnv w₀ w i).extend (.bnd 0) o) ψ) ↔ _
          constructor
          · rintro ⟨o, hsat⟩
            obtain ⟨i', a, t', ht'⟩ := definable_fromDom w₀ A w o
            have hK : i ≤ i ⊔ i' := le_sup_left
            have hK' : i' ≤ i ⊔ i' := le_sup_right
            have ho : Model.interp (canonEnv w₀ w (i ⊔ i')) (w.liftT hK' t') = o :=
              (interp_canon w₀ _ (Model.Env.Agree.refl' _)).trans
                ((toDom_congr w₀ ((rden_mono _ t' w _ _).trans
                  ((rden_congr t' w _ i' _ _).trans ht')) _ _).trans (toDom_fromDom w₀ A w o))
            have hs₁ := (Model.sat_mono (Model.Env.extend_agree (canonEnv_le w₀ w hK) (.bnd 0) o)
              ψ).mpr hsat
            rw [← ho] at hs₁
            have hs₂ := (Model.sat_instantiate (canonEnv w₀ w (i ⊔ i')) (w.noProjLast _)
              Ctx.NoSlots.slots (w.liftT hK' t') _).mpr hs₁
            have hmemK := (truth_lt n w (i ⊔ i') _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mp hs₂
            exact (World.mem_lift hK).mpr (World.mem_of_provable
              (Δ := [WFF.instantiate Ctx.NoSlots.slots (w.liftT hK' t')
                (WFF.mono ((w.L.ctx_le hK).insert (.bnd 0) A) ψ)])
              (fun χ hχ => by
                rw [List.mem_singleton.mp hχ]
                exact hmemK)
              ⟨Proof.ex_intro A (w.liftT hK' t') (Proof.lookup List.mem_cons_self)⟩)
          · intro hmem
            obtain ⟨i', hi, a, t, hmem'⟩ := w.exW_term hmem
            refine ⟨Model.interp (canonEnv w₀ w i') t, ?_⟩
            have hs := (truth_lt n w i' _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mpr hmem'
            have hs₁ := (Model.sat_instantiate (canonEnv w₀ w i') (w.noProjLast i')
              Ctx.NoSlots.slots t _).mp hs
            exact (Model.sat_mono (Model.Env.extend_agree (canonEnv_le w₀ w hi) (.bnd 0) _)
              ψ).mp hs₁
      | box χ =>
          have hχs : χ.size < n := by simp only [WFF.size] at hφ; omega
          change (∀ w' : (model w₀).frame.Acc w,
            (model w₀).sat ((canonEnv w₀ w i).boxPush w') χ) ↔ _
          have key : ∀ (w' : Succ w) (hd : w'.1.depth - w.depth = 1),
              (model w₀).sat ((canonEnv w₀ w i).boxPush w') χ ↔
                (⟨childStage i, WFF.mono ((w'.acc hd).boxIn_le i) χ⟩ :
                  w'.1.L.sys.Sentence σ) ∈ w'.1.T :=
            fun w' hd => (Model.sat_mono (boxPush_agree_canon w₀ w i w' hd) χ).symm.trans
              (truth_lt n w'.1 (childStage i) _ (by rw [WFF.size_mono]; exact hχs))
          -- Far successors, by the distance: `four_box`, then the necessary contents of the
          -- first step.
          have far : ∀ (d : ℕ) (w : World σ N₀) (i : ℕ × ℕ) (χ : WFF σ (w.L.ctx i).boxIn 0),
              χ.size < n → (⟨i, .box χ⟩ : w.L.sys.Sentence σ) ∈ w.T →
              ∀ (w' : Succ w), w'.1.depth - w.depth = d + 1 →
                (model w₀).sat ((canonEnv w₀ w i).boxPush w') χ := by
            intro d
            induction d with
            | zero =>
                intro w i χ hχs hmem w' hd
                exact (Model.sat_mono (boxPush_agree_canon w₀ w i w' hd) χ).mp
                  ((truth_lt n w'.1 (childStage i) _ (by rw [WFF.size_mono]; exact hχs)).mpr
                    ((w'.acc hd).2.2 i χ (childStage i) _ hmem))
            | succ d ih =>
                intro w i χ hχs hmem w' hd
                obtain ⟨u, hu, hr, hd'⟩ := w'.split hd
                have hF : ModalSys.Four = true := w'.four hd (Nat.succ_ne_zero d)
                have hu1 : (⟨u, ⟨R.of_acc hu⟩⟩ : Succ w).1.depth - w.depth = 1 := by
                  have := hu.1
                  change u.depth - w.depth = 1
                  omega
                have h4 : (⟨i, .box (.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF _)
                    Ctx.NoSlots.slots χ))⟩ : w.L.sys.Sentence σ) ∈ w.T :=
                  World.mem_of_provable (Δ := [.box χ])
                    (fun ψ hψ => by
                      rw [List.mem_singleton.mp hψ]
                      exact hmem)
                    ⟨Proof.four_box hF (Proof.lookup List.mem_cons_self)⟩
                have hsat := ih u (childStage i)
                  (WFF.mono (hu.boxIn_le i).boxIn
                    (WFF.shift (Ctx.shifts_boxIn_boxIn hF _) Ctx.NoSlots.slots χ))
                  (by rw [WFF.size_mono, WFF.size_shift]; exact hχs)
                  (hu.2.2 i _ (childStage i) (hu.boxIn_le i) h4) ⟨w'.1, ⟨hr⟩⟩ hd'
                have hsat₂ := (Model.sat_mono (Model.Env.boxPush_agree
                  (boxPush_agree_canon w₀ w i ⟨u, ⟨R.of_acc hu⟩⟩ hu1) ⟨w'.1, ⟨hr⟩⟩) _).mp hsat
                exact (Model.sat_shift_twoBox hF (canonEnv w₀ w i) Ctx.NoSlots.slots χ
                  ⟨u, ⟨R.of_acc hu⟩⟩ ⟨w'.1, ⟨hr⟩⟩).mp hsat₂
          constructor
          · intro hsat
            by_contra hnot
            obtain ⟨w', ha, hw'⟩ := exists_box_fail w χ hnot
            have hd : w'.depth - w.depth = 1 := by
              have := ha.1
              omega
            exact hw' ((key ⟨w', ⟨R.of_acc ha⟩⟩ hd).mp (hsat ⟨w', ⟨R.of_acc ha⟩⟩))
          · intro hmem w'
            rcases hd : w'.1.depth - w.depth with _ | d
            · obtain ⟨w₁, hw₁⟩ := w'
              obtain ⟨hT, hw⟩ := Succ.self ⟨w₁, hw₁⟩ hd
              change w₁ = w at hw
              subst hw
              refine (Model.sat_boxHere hT (canonEnv w₀ _ i) Ctx.NoSlots.slots χ).mp
                ((truth_lt n _ i _ ?_).mpr ?_)
              · rw [WFF.size_collapse]
                exact hχs
              · exact World.mem_of_provable (Δ := [.box χ])
                  (fun ψ hψ => by
                    rw [List.mem_singleton.mp hψ]
                    exact hmem)
                  ⟨Proof.T_box hT (Proof.lookup List.mem_cons_self)⟩
            · exact far d w i χ hχs hmem w' hd
      | dia x hx χ =>
          have hχs : χ.size < n := by simp only [WFF.size] at hφ; omega
          change (∃ (X : VarType) (h : (w.L.ctx i).ref x = some (.VTypeDia X))
            (w' : ((model w₀).posEval ((canonEnv w₀ w i).ref x h)).1),
              (model w₀).sat ((canonEnv w₀ w i).diaPush x h w') χ) ↔ _
          have key : ∀ {X : VarType} (h : (w.L.ctx i).ref x = some (.VTypeDia X))
              (w' : ((model w₀).posEval ((canonEnv w₀ w i).ref x h)).1)
              (hd : w'.1.1.depth - w.depth ≠ 0),
              (model w₀).sat ((canonEnv w₀ w i).diaPush x h w') χ ↔
                (⟨childStage i, WFF.mono (extent_le (canonEnv_extent w₀ w i h ▸ w'.2) hd i) χ⟩ :
                  w'.1.1.L.sys.Sentence σ) ∈ w'.1.1.T :=
            fun h w' hd => (Model.sat_mono (diaPush_agree_canon w₀ w i h w' hd) χ).symm.trans
              (truth_lt n w'.1.1 (childStage i) _ (by rw [WFF.size_mono]; exact hχs))
          constructor
          · rintro ⟨X, h, w', hsat⟩
            have hw' : w'.1 ∈ extent w x := canonEnv_extent w₀ w i h ▸ w'.2
            by_cases hd : w'.1.1.depth - w.depth ≠ 0
            · by_contra hnot
              have hbx : (⟨i, WFF.boxx x hx χ.neg⟩ : w.L.sys.Sentence σ) ∈ w.T :=
                World.mem_of_provable (Δ := [(WFF.dia x hx χ).neg])
                  (fun ψ hψ => by
                    rw [List.mem_singleton.mp hψ]
                    exact w.mcs.neg_mem_iff.mpr hnot)
                  ⟨Proof.boxx_neg_of_not_dia x hx χ⟩
              have hneg := (extent_proper hw' hd).2.2 i hx χ.neg (childStage i)
                (extent_le hw' hd i) hbx
              exact (w'.1.1.mcs.neg_mem_iff.mp hneg) ((key h w' hd).mp hsat)
            · obtain ⟨hweq, hrx⟩ := extent_self hw' (not_not.mp hd)
              obtain ⟨⟨w₁, hR⟩, hmem⟩ := w'
              change w₁ = w at hweq
              subst hweq
              exact dia_mem_of_sat_self w₀ hrx.data (hrx.data.declType i ⟨X, h⟩)
                (World.real_of_realised hrx) h hx χ
                (fun ψ hψ => truth_lt n _ _ ψ (by rw [hψ]; exact hχs)) hmem hsat
          · intro hmem
            obtain ⟨X, h⟩ : ∃ X, (w.L.ctx i).ref x = some (.VTypeDia X) := hx
            obtain ⟨w', hw', hd, hmem'⟩ := exists_dia w x ⟨X, h⟩ χ hmem
            exact ⟨X, h, ⟨w', (canonEnv_extent w₀ w i h).symm ▸ hw'⟩, (key h _ hd).mpr hmem'⟩
      | here hT s t =>
          cases s with
          | diatm x hx bd =>
              exact here_truth w₀ hT hx bd t (fun K _ u u' => truth_lt n w K _ (by
                rw [WFF.size_eqRec]; simp only [WFF.size] at hφ; omega))

/-- ⭐**The truth lemma.** -/
theorem truth (w : World σ N₀) (i : ℕ × ℕ) (φ : WFF σ (w.L.ctx i) 0) :
    (model w₀).sat (canonEnv w₀ w i) φ ↔ (⟨i, φ⟩ : w.L.sys.Sentence σ) ∈ w.T :=
  truth_lt w₀ (φ.size + 1) w i φ (Nat.lt_succ_self _)

/-- ⭐⭐**The canonical model is a model proper** (docs §10.33, item 7 of §10.34).  Over a tame
    context an environment is the canonical one at a stage, read through a substitution
    (`substEnv_repSubst`); so a slot formula with an object in its slot is true exactly when the
    substituted slot formula, instantiated at a representative of the object, is in the theory
    (`sat_subst`, `sat_instantiate`, the truth lemma).  Related objects have representatives
    interchangeable in every slot formula (`DTerm.Rel`), so the two memberships agree. -/
theorem indInvariant : (model w₀).IndInvariant := by
  intro Γ _ htame hnp w env A φ o o' hInd
  obtain ⟨hfin, d, hd⟩ := htame
  have hθ := repSubst_ok w₀ env hfin
  have hc := repSubst_coh w₀ env hfin hd
  have h0 : (w.L.ctx (repSup w₀ env hfin)) (.root (.bnd 0)) = none :=
    (Ctx.NoSlots.slots (Γ := w.L.ctx (repSup w₀ env hfin))).root
  let φ' : WFF σ ((w.L.ctx (repSup w₀ env hfin)).insert (.bnd 0) A) 1 :=
    WFF.subst (VarSymb.shiftSlot (repIdx w₀ env hfin) 0 0)
      ((repSubst w₀ env hfin).under 0 0 A h0) (Subst.ok_under hθ A h0)
      (Subst.coh_under hθ hc Ctx.NoSlots.slots A h0)
      (Ctx.NoSlots.slots.insert A) ((Ctx.NoSlots.slots).insert A) φ
  have key : ∀ (o₁ : (model w₀).frame.Dom A w) (s : DTerm w A),
      rden w s.i (Ctx.Le.refl _) s.t = fromDom w₀ A w o₁ →
      ∀ (K' : ℕ × ℕ) (hK : repSup w₀ env hfin ≤ K') (hs : s.i ≤ K'),
        ((model w₀).sat (env.extend (.bnd 0) o₁) φ ↔
          (⟨K', WFF.instantiate Ctx.NoSlots.slots (s.lift K' hs)
            (WFF.mono ((w.L.ctx_le hK).insert (.bnd 0) A) φ')⟩ : w.L.sys.Sentence σ) ∈ w.T) := by
    intro o₁ s hs₁ K' hK hs
    have hval : Model.interp (canonEnv w₀ w K') (s.lift K' hs) = o₁ := by
      rw [interp_canon w₀ _ (fun _ _ _ => rfl)]
      refine Eq.trans ?_ (toDom_fromDom w₀ A w o₁)
      exact toDom_congr w₀ ((rden_lift hs s.t).trans hs₁) _ _
    calc (model w₀).sat (env.extend (.bnd 0) o₁) φ
        ↔ (model w₀).sat ((Model.substEnv (repSubst w₀ env hfin) hθ hnp
            (canonEnv w₀ w (repSup w₀ env hfin))).extend (.bnd 0) o₁) φ := by
          rw [substEnv_repSubst w₀ env hfin hnp]
      _ ↔ (model w₀).sat (Model.substEnv ((repSubst w₀ env hfin).under 0 0 A h0)
            (Subst.ok_under hθ A h0) (hnp.insert (.bnd 0) A)
            ((canonEnv w₀ w (repSup w₀ env hfin)).extend (.bnd 0) o₁)) φ := by
          rw [Model.substEnv_under]
      _ ↔ (model w₀).sat ((canonEnv w₀ w (repSup w₀ env hfin)).extend (.bnd 0) o₁) φ' :=
          (Model.sat_subst _ _ _ _ _ _ _ φ).symm
      _ ↔ (model w₀).sat ((canonEnv w₀ w K').extend (.bnd 0) o₁)
            (WFF.mono ((w.L.ctx_le hK).insert (.bnd 0) A) φ') :=
          (Model.sat_mono (Model.Env.extend_agree (canonEnv_le w₀ w hK) (.bnd 0) o₁) φ').symm
      _ ↔ (model w₀).sat (canonEnv w₀ w K') (WFF.instantiate Ctx.NoSlots.slots (s.lift K' hs)
            (WFF.mono ((w.L.ctx_le hK).insert (.bnd 0) A) φ')) := by
          rw [Model.sat_instantiate (canonEnv w₀ w K') (w.noProjLast K'), hval]
      _ ↔ _ := truth w₀ w K' _
  obtain ⟨s, s', hs, hs', hrel⟩ := hInd
  have hK : repSup w₀ env hfin ≤ repSup w₀ env hfin ⊔ (s.i ⊔ s'.i) := le_sup_left
  have h₁ : s.i ≤ repSup w₀ env hfin ⊔ (s.i ⊔ s'.i) := le_sup_left.trans le_sup_right
  have h₂ : s'.i ≤ repSup w₀ env hfin ⊔ (s.i ⊔ s'.i) := le_sup_right.trans le_sup_right
  rw [key o s hs _ hK h₁, key o' s' hs' _ hK h₂]
  exact hrel _ h₁ h₂ _

end Canon

/-! ## Completeness -/

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoB]

/-- ⭐**Completeness**: a sequent in a presented context that holds in every model, at every
    world, in every environment, is provable. -/
theorem completeness {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0}
    (hval : ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W} (env : M.Env Γ w),
      Γ.NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ := by
  by_contra hnp
  have hfresh : ∀ d n, Γ.RootFresh (.free (Canon.names (Ctx.Presented.bound Γ) d n)) :=
    fun _ _ => Ctx.Presented.fresh_bound _ (Nat.le_add_right _ _)
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
  let w₀ : Canon.World σ (Ctx.Presented.bound Γ) :=
    Canon.World.ofHenkin 0 L₀ (fun _ => rfl) (fun _ d n _ => hfresh d n) S₀ hS₀
  have hsat := hval (Canon.model w₀) (Canon.indInvariant w₀) (w := w₀)
    (Canon.canonEnv w₀ w₀ (0, 0))
    (Ctx.Presented.noProjLast Γ)
    (fun ψ hψ => (Canon.truth w₀ w₀ (0, 0) ψ).mpr
      (WorldLang.subset_finalT S₀ (Or.inl ⟨ψ, hψ, rfl⟩)))
  have hmem := (Canon.truth w₀ w₀ (0, 0) φ).mp hsat
  have hneg := WorldLang.subset_finalT (L := L₀) S₀ (m := 0) (φ := φ.neg) (Or.inr rfl)
  exact (w₀.mcs.neg_mem_iff.mp hneg) hmem

/-- ⭐**Soundness and completeness**: over a countable signature, a sequent in a presented context
    is provable exactly when it holds in every model. -/
theorem provable_iff_valid {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} :
    Provable Δ φ ↔ ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W} (env : M.Env Γ w),
      Γ.NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ :=
  ⟨fun ⟨p⟩ M hM _ env => Model.soundness p M hM env (Ctx.Presented.tame Γ), completeness⟩

end V12M
