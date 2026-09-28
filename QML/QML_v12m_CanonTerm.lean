import QML.QML_v12m_CanonModel
import QML.QML_v12m_SemAbs

/-!
# QML v12m — the canonical model: the truth lemma for terms

The **canonical environment** at stage `i` of a world gives every visible address the frame object
of its η-expansion (`canonEnv`); so does its reading of every reachable address (`canonEnv_ref`;
under T `u.here` reads the necessary object `u` at the world itself, which is the collapsed
η-expansion).  Entering a modality at a proper successor from it agrees with the canonical
environment of the successor (`boxPush_agree_canon`, `diaPush_agree_canon`).

⭐`interp_canon`: in any environment agreeing with the canonical one, a term's value is its
denotation.  At the world itself a necessary term's value is its collapsed body's
(`Model.interp_collapse`), and at a far successor its shifted body's value from a proper successor
on the way (`interp_box_far`, by the distance); so the induction is on the size of terms, which
collapsing and shifting keep.
-/

namespace V12M

variable [ModalSys]

theorem Model.Env.Agree.trans {σ : Signature} {M : Model.{u, v} σ} {Γ₁ Γ₂ Γ₃ : Ctx}
    {h₁ : Γ₁.Le Γ₂} {h₂ : Γ₂.Le Γ₃} {w : M.frame.W} {e₁ : M.Env Γ₁ w} {e₂ : M.Env Γ₂ w}
    {e₃ : M.Env Γ₃ w} (a : Model.Env.Agree h₁ e₁ e₂) (b : Model.Env.Agree h₂ e₂ e₃) :
    Model.Env.Agree (h₁.trans h₂) e₁ e₃ :=
  fun v T hv => (a v T hv).trans (b v T (h₁ v T hv))

theorem Spine.ofFn_cons {σ : Signature} {Δ : Ctx} {n : ℕ} (t : Term σ Δ .Var .var)
    (ts : Fin n → Term σ Δ .Var .var) :
    Spine.ofFn (Fin.cons t ts : Fin (n + 1) → Term σ Δ .Var .var) = .cons t (Spine.ofFn ts) := by
  change Spine.cons ((Fin.cons t ts : Fin (n + 1) → Term σ Δ .Var .var) 0)
    (Spine.ofFn fun k => (Fin.cons t ts : Fin (n + 1) → Term σ Δ .Var .var) k.succ) = _
  simp only [Fin.cons_zero, Fin.cons_succ]

/-! ## Sizes of terms -/

mutual
  /-- The size of a function term. -/
  def Func.size {σ : Signature} : {Γ : Ctx} → {n : ℕ} → Func σ Γ n → ℕ
    | _, _, .F _ => 0
    | _, _, .eval g t => Func.size g + Term.size t + 1

  /-- The size of a term. -/
  def Term.size {σ : Signature} : {Γ : Ctx} → {T : VarType} → {a : Ann T} → Term σ Γ T a → ℕ
    | _, _, _, .var _ _ => 0
    | _, _, _, .func f => Func.size f + 1
    | _, _, _, .unit => 0
    | _, _, _, .pair s t => Term.size s + Term.size t + 1
    | _, _, _, .boxtm t => Term.size t + 1
    | _, _, _, .diatm _ _ t => Term.size t + 1
end

mutual
  theorem Func.size_collapse {σ : Signature} : ∀ {k : ℕ} {Γ₁ Γ₂ : Ctx}
      (h : Ctx.Collapses k Γ₁ Γ₂) {n : ℕ} (f : Func σ Γ₁ n), (Func.collapse h f).size = f.size
    | _, _, _, _, _, .F _ => rfl
    | _, _, _, h, _, .eval g t => by
        change (Func.collapse h g).size + (Term.collapse h t).size + 1 = g.size + t.size + 1
        rw [Func.size_collapse h g, Term.size_collapse h t]

  theorem Term.size_collapse {σ : Signature} : ∀ {k : ℕ} {Γ₁ Γ₂ : Ctx}
      (h : Ctx.Collapses k Γ₁ Γ₂) {T : VarType} {a : Ann T} (t : Term σ Γ₁ T a),
      (Term.collapse h t).size = t.size
    | _, _, _, _, _, _, .var _ _ => rfl
    | _, _, _, h, _, _, .func f => congrArg (· + 1) (Func.size_collapse h f)
    | _, _, _, _, _, _, .unit => rfl
    | _, _, _, h, _, _, .pair s t =>
        congrArg₂ (· + · + 1) (Term.size_collapse h s) (Term.size_collapse h t)
    | _, _, _, h, _, _, .boxtm t => congrArg (· + 1) (Term.size_collapse h.boxIn t)
    | _, _, _, h, _, _, .diatm x _ t => congrArg (· + 1) (Term.size_collapse (h.diaIn x) t)
end

mutual
  theorem Func.size_shift {σ : Signature} : ∀ {k : ℕ} {Γ₁ Γ₂ : Ctx}
      (h : Ctx.Shifts k Γ₁ Γ₂) {n : ℕ} (f : Func σ Γ₁ n), (Func.shift h f).size = f.size
    | _, _, _, _, _, .F _ => rfl
    | _, _, _, h, _, .eval g t => by
        change (Func.shift h g).size + (Term.shift h t).size + 1 = g.size + t.size + 1
        rw [Func.size_shift h g, Term.size_shift h t]

  theorem Term.size_shift {σ : Signature} : ∀ {k : ℕ} {Γ₁ Γ₂ : Ctx}
      (h : Ctx.Shifts k Γ₁ Γ₂) {T : VarType} {a : Ann T} (t : Term σ Γ₁ T a),
      (Term.shift h t).size = t.size
    | _, _, _, _, _, _, .var _ _ => rfl
    | _, _, _, h, _, _, .func f => congrArg (· + 1) (Func.size_shift h f)
    | _, _, _, _, _, _, .unit => rfl
    | _, _, _, h, _, _, .pair s t =>
        congrArg₂ (· + · + 1) (Term.size_shift h s) (Term.size_shift h t)
    | _, _, _, h, _, _, .boxtm t => congrArg (· + 1) (Term.size_shift h.boxIn t)
    | _, _, _, h, _, _, .diatm x _ t => congrArg (· + 1) (Term.size_shift (h.diaIn x) t)
end

namespace Canon

variable {σ : Signature} {N₀ : ℕ} (w₀ : World σ N₀)

omit w₀ in
theorem World.noProjLast (w : World σ N₀) (i : ℕ × ℕ) : (w.L.ctx i).NoProjLast :=
  Ctx.Presented.noProjLast _

variable [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoB]

/-- ⭐The canonical environment: every visible address denotes its η-expansion. -/
noncomputable def canonEnv (w : World σ N₀) (i : ℕ × ℕ) : (model w₀).Env (w.L.ctx i) w :=
  fun v T hv => toDom w₀ T w
    (rden w i (Ctx.Le.refl _) (Term.eta v T ((Ctx.ref_nonproj _ (w.noProjLast i v T hv)).trans hv)))
    (definable_rden _ _)

/-- Every reachable address reads as its η-expansion. -/
theorem canonEnv_ref (w : World σ N₀) (i : ℕ × ℕ) :
    ∀ (v : VarSymb) {T : VarType} (h : (w.L.ctx i).ref v = some T),
      (canonEnv w₀ w i).ref v h =
        toDom w₀ T w (rden w i (Ctx.Le.refl _) (Term.eta v T h)) (definable_rden _ _)
  | .root _, _, _ => rfl
  | .step v s, T, h => by
      by_cases hs : s.isProj = true
      · rw [Model.Env.ref, dif_pos hs]
        split
        · rename_i U hU
          rw [canonEnv_ref w i v hU]
          have hT : U.step s = some T := by
            rw [Ctx.ref_step_proj _ _ hs, hU] at h
            exact h
          cases s with
          | fst =>
              cases U <;> simp only [VarType.step, reduceCtorEq, Option.some.injEq] at hT
              subst hT
              rfl
          | snd =>
              cases U <;> simp only [VarType.step, reduceCtorEq, Option.some.injEq] at hT
              subst hT
              rfl
          | here =>
              cases U <;> simp only [VarType.step, reduceCtorEq] at hT
              rename_i A
              obtain ⟨hT₁, rfl⟩ := VarType.step_here hT
              change toDom w₀ _ w (rden w i (Ctx.Le.refl _)
                (.boxtm (Term.eta v.inner _ (Ctx.ref_inner hU))) ⟨w, _⟩) _ = _
              exact toDom_congr w₀
                ((rden_boxtm_self (Ctx.Le.refl _) (Term.eta v.inner _ (Ctx.ref_inner hU))
                  ⟨w, ⟨R.refl hT₁ w⟩⟩ (Nat.sub_self _)).trans
                  (rden_sigma _ ((Term.collapse_eta _ _ _ _).trans
                    (Term.eta_congr (VarSymb.inner_collapse_zero v) _ _ _)))) _ _
          | box => cases hs
          | dia => cases hs
          | keep => cases hs
        · rename_i hU
          rw [Ctx.ref_step_proj _ _ hs, hU] at h
          cases h
      · rw [Model.Env.ref, dif_neg hs]
        rfl

/-- ⭐**The truth lemma for an address, outright.**  `Model.interp_eta` says an address's
    η-expansion denotes the address, and `canonEnv_ref` says the canonical environment's value there
    is its denotation — so no induction is needed, at any stage and any type.  This is what lets a
    realisation *named by an address* be read without the stage-led induction, and hence without any
    order between the naming and the witness. -/
theorem interp_canon_eta (w : World σ N₀) (k : ℕ × ℕ) (y : VarSymb) {A : VarType}
    (hy : (w.L.ctx k).ref y = some A) :
    Model.interp (canonEnv w₀ w k) (Term.eta y A hy) =
      toDom w₀ A w (rden w k (Ctx.Le.refl _) (Term.eta y A hy)) (definable_rden _ _) :=
  (Model.interp_eta (canonEnv w₀ w k) y hy).trans (canonEnv_ref w₀ w k y hy)

theorem canonEnv_extent (w : World σ N₀) (i : ℕ × ℕ) {x : VarSymb} {X : VarType}
    (hr : (w.L.ctx i).ref x = some (.VTypeDia X)) :
    ((model w₀).posEval ((canonEnv w₀ w i).ref x hr)).1 = extent w x := by
  rw [canonEnv_ref]
  rfl

/-- The canonical environment at a later stage agrees with the one at an earlier stage: both read
    an address as its η-expansion, and that does not depend on the stage it is read at. -/
theorem canonEnv_le (w : World σ N₀) {i j : ℕ × ℕ} (hij : i ≤ j) :
    Model.Env.Agree (w.L.ctx_le hij) (canonEnv w₀ w i) (canonEnv w₀ w j) :=
  fun _ _ _ => toDom_congr w₀ (rden_eta_le (w.L.ctx_le hij) _ _ _ _ _ _) _ _

/-- Pushing the canonical environment into `□` at a proper successor agrees with the
    successor's. -/
theorem boxPush_agree_canon (w : World σ N₀) (i : ℕ × ℕ) (w' : Succ w)
    (hd : w'.1.depth - w.depth = 1) :
    Model.Env.Agree ((w'.acc hd).boxIn_le i) ((canonEnv w₀ w i).boxPush w')
      (canonEnv w₀ w'.1 (childStage i)) := by
  intro v T hv
  match v with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hv
      change (model w₀).necEval ((canonEnv w₀ w i).ref u (Ctx.boxIn_step_box hv)) w' = _
      rw [canonEnv_ref]
      change toDom w₀ T w'.1 (rden w i (Ctx.Le.refl _)
        (.boxtm (Term.eta u.inner T (Ctx.ref_inner hu))) w') _ = _
      exact toDom_congr w₀ ((rden_boxtm_acc _ _ w' hd).trans
        ((rden_sigma _ (Term.eta_congr (VarSymb.inner_box hk) T _ (Ctx.ref_boxIn_of hk hu))).trans
          (rden_eta_le ((w'.acc hd).boxIn_le i) _ _ _ _ _ _))) _ _
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep hv
      change (model w₀).necEval ((ops w₀).necDup hF ((canonEnv w₀ w i).ref u hu)) w' = _
      rw [canonEnv_ref]
      change toDom w₀ (.VTypeBox A) w'.1
        (rawEval (.dup hF) w (rden w i (Ctx.Le.refl _) (Term.eta u (.VTypeBox A) hu)) w') _ = _
      refine toDom_congr w₀ ?_ _ _
      rw [← rden_applyG (.dup hF) (Term.eta u (.VTypeBox A) hu) w i (Ctx.Le.refl _)]
      change rden w i (Ctx.Le.refl _) (.boxtm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _)
        (Term.eta u.inner A (Ctx.ref_inner hu))))) w' = _
      rw [rden_boxtm_acc _ _ w' hd]
      exact (rden_sigma _ (sig_boxtm ((Term.shift_eta _ _ _ _).trans
        (Term.eta_congr (VarSymb.inner_shift_zero u) _ _
          (Ctx.ref_inner (Ctx.ref_keep_of hF hu)))))).trans
        (rden_eta_le ((w'.acc hd).boxIn_le i) _ _ _ _ (Ctx.ref_keep_of hF hu) _)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

/-- Pushing the canonical environment into `◇_x` agrees with the successor's. -/
theorem diaPush_agree_canon (w : World σ N₀) (i : ℕ × ℕ) {x : VarSymb} {X : VarType}
    (hr : (w.L.ctx i).ref x = some (.VTypeDia X))
    (w' : ((model w₀).posEval ((canonEnv w₀ w i).ref x hr)).1)
    (hd : w'.1.1.depth - w.depth ≠ 0) :
    Model.Env.Agree (extent_le (canonEnv_extent w₀ w i hr ▸ w'.2) hd i)
      ((canonEnv w₀ w i).diaPush x hr w') (canonEnv w₀ w'.1.1 (childStage i)) := by
  have hw : w'.1 ∈ extent w x := canonEnv_extent w₀ w i hr ▸ w'.2
  intro v T hv
  match v with
  | .step u .dia =>
      have hux : u = x := by
        change (if u = x then (match (w.L.ctx i).ref x with
          | some (.VTypeDia X) => some X | _ => none) else none) = some T at hv
        split_ifs at hv with hux
        exact hux
      subst hux
      have hTX : X = T := Ctx.diaIn_step_dia hr hv
      subst hTX
      have hpq := canonEnv_ref w₀ w i u hr
      have hm : w'.1 ∈ ((model w₀).posEval (toDom w₀ (.VTypeDia X) w
          (rden w i (Ctx.Le.refl _) (Term.eta u (.VTypeDia X) hr)) (definable_rden _ _))).1 :=
        hpq ▸ w'.2
      change ((model w₀).posEval ((canonEnv w₀ w i).ref u hr)).2 w' = _
      rw [Model.posEval_snd_congr hpq w' hm]
      refine toDom_congr w₀ ?_ _ _
      exact (rden_diatm_acc' (Ctx.Le.refl _) ⟨X, hr⟩
          (Term.eta (.step u .dia) X (Ctx.ref_diaIn_of hr)) w'.1 hm hd (extent_le hw hd i)).trans
        (rden_eta_le (extent_le hw hd i) _ _ _ _ _ _)
  | .step u .box =>
      exact boxPush_agree_canon w₀ w i w'.1 (extent_dist hw hd) (.step u .box) T hv
  | .step u .keep =>
      exact boxPush_agree_canon w₀ w i w'.1 (extent_dist hw hd) (.step u .keep) T hv
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

/-- Under 4, the value of a necessary term at a successor `d + 1` levels deeper is its
    denotation there, given the truth lemma for terms no larger than its body. -/
theorem interp_box_far (S : ℕ) {A : VarType}
    (IH : ∀ {Γ : Ctx} {a : Ann A} (t : Term σ Γ A a), t.size ≤ S →
      ∀ {w : World σ N₀} {i : ℕ × ℕ} (_hi : i.2 = 0) {e : Γ.Le (w.L.ctx i)}
      {env : (model w₀).Env Γ w},
      Model.Env.Agree e env (canonEnv w₀ w i) →
      Model.interp env t = toDom w₀ A w (rden w i e t) (definable_rden e t)) :
    ∀ (d : ℕ) {Γ : Ctx} {a : Ann A} (t : Term σ Γ.boxIn A a), t.size ≤ S →
      ∀ {w : World σ N₀} {i : ℕ × ℕ} {e : Γ.Le (w.L.ctx i)} {env : (model w₀).Env Γ w},
      Model.Env.Agree e env (canonEnv w₀ w i) → ∀ (w' : Succ w), w'.1.depth - w.depth = d + 1 →
      Model.interp (env.boxPush w') t =
        toDom w₀ A w'.1 (rden w i e (.boxtm t) w')
          (definable_box_apply (definable_rden e (.boxtm t)) w')
  | 0, _, _, t, ht, w, i, e, env, hag, w', hd =>
      (IH t ht rfl ((Model.Env.boxPush_agree hag w').trans
        (boxPush_agree_canon w₀ w i w' hd))).trans
        (toDom_congr w₀ (rden_boxtm_acc e t w' hd).symm _ _)
  | d + 1, Γ, _, t, ht, w, i, e, env, hag, w', hd => by
      obtain ⟨u, hu, hr, hd'⟩ := w'.split hd
      have hF : ModalSys.Four = true := w'.four hd (Nat.succ_ne_zero d)
      have hu1 : (⟨u, ⟨R.of_acc hu⟩⟩ : Succ w).1.depth - w.depth = 1 := by
        have := hu.1
        change u.depth - w.depth = 1
        omega
      have hag' := (Model.Env.boxPush_agree hag (⟨u, ⟨R.of_acc hu⟩⟩ : Succ w)).trans
        (boxPush_agree_canon w₀ w i ⟨u, ⟨R.of_acc hu⟩⟩ hu1)
      refine (Model.interp_shift (Model.Env.shiftAgree_twoBox hF env
        (⟨u, ⟨R.of_acc hu⟩⟩ : Succ w) ⟨w'.1, ⟨hr⟩⟩) t).symm.trans ?_
      refine (interp_box_far S IH d (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) t)
        (by rw [Term.size_shift]; exact ht) hag' ⟨w'.1, ⟨hr⟩⟩ hd').trans ?_
      exact toDom_congr w₀ (rden_boxtm_step hF e t w' hu hr (by omega)).symm _ _

/-- The size of a type: the middle component of the truth lemma's measure.  A `◇` term recurses at
    its body, of the type inside, so within a stage the recursion is on the type first and the size
    second — as `rden`'s own recursion is. -/
def VarType.tsize : VarType → ℕ
  | .Var => 0
  | .VTypeOne => 0
  | .VTypeProd A B => VarType.tsize A + VarType.tsize B + 1
  | .VTypeBox A => VarType.tsize A + 1
  | .VTypeDia A => VarType.tsize A + 1

/-- ⭐The realised case of the truth lemma, with its two recursive calls taken as hypotheses: one at
    the realising term `dat.t₀` (`hIHt₀`), and one at the realisation of the body, which is of the
    type inside the `◇` (`IH`).  The stage the body's call is made at is `i ⊔ dat.i₀`, so whatever
    the induction demands of the stages it recurses at is a parameter here (`StageOK`, `hsup`): a
    stage-led measure asks for `k.2 ≤ i.2`, and one led by the type asks for nothing.

    The realisation is `Term.realiseAtA`, whose semantics (`Model.interp_realiseAtA`) is to read the
    body in the environment pushed into the witness's view at the world itself; what the witness's
    content is there is what the world names (`rden_eta_of_real`). -/
theorem interp_dia_self_core {A : VarType} {a : Ann A} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ}
    {x : VarSymb} (dat : RealDatum σ w.L w.T x)
    (hdeclI : (w.L.ctx i).ref x = some (.VTypeDia dat.A))
    (hIHt₀ : Model.interp (canonEnv w₀ w dat.i₀) dat.t₀ =
      toDom w₀ dat.A w (rden w dat.i₀ (Ctx.Le.refl _) dat.t₀) (definable_rden _ dat.t₀))
    {StageOK : ℕ × ℕ → Prop} (hsup : StageOK (i ⊔ dat.i₀))
    (IH : ∀ {Γ' : Ctx} {b : Ann A} (s : Term σ Γ' A b) {k : ℕ × ℕ}, StageOK k →
      ∀ {e' : Γ'.Le (w.L.ctx k)} {env' : (model w₀).Env Γ' w},
      Model.Env.Agree e' env' (canonEnv w₀ w k) →
      Model.interp env' s = toDom w₀ A w (rden w k e' s) (definable_rden e' s))
    {e : Γ.Le (w.L.ctx i)} {env : (model w₀).Env Γ w}
    (hag : Model.Env.Agree e env (canonEnv w₀ w i))
    {X : VarType} (hx : Γ.ref x = some (.VTypeDia X))
    (hreal : w.real x = some dat)
    (hdecl : (w.L.ctx (i ⊔ dat.i₀)).ref x = some (.VTypeDia dat.A))
    (hle : (Γ.diaIn x).Le ((w.L.ctx (i ⊔ dat.i₀)).diaIn x))
    (hT : ModalSys.T = true)
    (hmem : (⟨w, ⟨R.refl hT w⟩⟩ : Succ w) ∈ ((model w₀).posEval (env.ref x hx)).1)
    (t : Term σ (Γ.diaIn x) A a) :
    Model.interp (env.diaPush x hx ⟨⟨w, ⟨R.refl hT w⟩⟩, hmem⟩) t =
      toDom w₀ A w (rden w (i ⊔ dat.i₀) (Ctx.Le.refl _)
        (Term.realiseAtA hT x hdecl (Term.mono (w.L.ctx_le le_sup_right) dat.t₀)
          (Term.mono hle t))) (definable_rden _ _) := by
  have hXA : X = dat.A := by
    have h1 := e.ref hx
    rw [hdeclI] at h1
    simp only [Option.some.injEq, VarType.VTypeDia.injEq] at h1
    exact h1.symm
  subst hXA
  have hj : i ≤ i ⊔ dat.i₀ := le_sup_left
  have hagj : Model.Env.Agree (e.trans (w.L.ctx_le hj)) env (canonEnv w₀ w (i ⊔ dat.i₀)) :=
    hag.trans (canonEnv_le w₀ w hj)
  have hm' : (⟨w, ⟨R.refl hT w⟩⟩ : Succ w) ∈
      ((model w₀).posEval ((canonEnv w₀ w (i ⊔ dat.i₀)).ref x hdecl)).1 := by
    rw [canonEnv_extent]
    exact self_mem_extent (World.realised_of_real hreal)
  have hcont : ((model w₀).posEval
        ((canonEnv w₀ w (i ⊔ dat.i₀)).ref x hdecl)).2 ⟨⟨w, ⟨R.refl hT w⟩⟩, hm'⟩ =
      Model.interp (canonEnv w₀ w (i ⊔ dat.i₀))
        (Term.mono (w.L.ctx_le (le_sup_right : dat.i₀ ≤ i ⊔ dat.i₀)) dat.t₀) := by
    have hpq := canonEnv_ref w₀ w (i ⊔ dat.i₀) x hdecl
    rw [Model.posEval_snd_congr hpq ⟨⟨w, ⟨R.refl hT w⟩⟩, hm'⟩ (hpq ▸ hm'),
      Model.interp_mono (canonEnv_le w₀ w (le_sup_right : dat.i₀ ≤ i ⊔ dat.i₀)) dat.t₀,
      hIHt₀]
    exact toDom_congr w₀ (rden_eta_of_real hreal hdecl) _ _
  refine (Model.interp_mono
    (Model.Env.diaPush_agree hagj hx ⟨⟨w, ⟨R.refl hT w⟩⟩, hmem⟩ hm') t).symm.trans ?_
  refine (Model.interp_realiseAtA hT (canonEnv w₀ w (i ⊔ dat.i₀)) (w.noProjLast _) hdecl
    (Term.mono (w.L.ctx_le le_sup_right) dat.t₀) hm' hcont
    _).symm.trans ?_
  exact IH _ hsup (fun _ _ _ => rfl)


/-- ⭐The realised case as the induction now uses it.  The realising term is the content
    **address's** η-expansion, so its own value is read outright (`interp_canon_eta`): there is no
    recursive call at the content, and hence nothing the induction has to know about the stage the
    content lives at — which is what takes the stage out of the measure below (§2d, step 3). -/
theorem interp_dia_self {A : VarType} {a : Ann A} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ}
    {x : VarSymb} (dat : RealDatum σ w.L w.T x)
    (hdeclI : (w.L.ctx i).ref x = some (.VTypeDia dat.A))
    (IH : ∀ {Γ' : Ctx} {b : Ann A} (s : Term σ Γ' A b) {k : ℕ × ℕ},
      ∀ {e' : Γ'.Le (w.L.ctx k)} {env' : (model w₀).Env Γ' w},
      Model.Env.Agree e' env' (canonEnv w₀ w k) →
      Model.interp env' s = toDom w₀ A w (rden w k e' s) (definable_rden e' s))
    {e : Γ.Le (w.L.ctx i)} {env : (model w₀).Env Γ w}
    (hag : Model.Env.Agree e env (canonEnv w₀ w i))
    {X : VarType} (hx : Γ.ref x = some (.VTypeDia X))
    (hreal : w.real x = some dat)
    (hdecl : (w.L.ctx (i ⊔ dat.i₀)).ref x = some (.VTypeDia dat.A))
    (hle : (Γ.diaIn x).Le ((w.L.ctx (i ⊔ dat.i₀)).diaIn x))
    (hT : ModalSys.T = true)
    (hmem : (⟨w, ⟨R.refl hT w⟩⟩ : Succ w) ∈ ((model w₀).posEval (env.ref x hx)).1)
    (t : Term σ (Γ.diaIn x) A a) :
    Model.interp (env.diaPush x hx ⟨⟨w, ⟨R.refl hT w⟩⟩, hmem⟩) t =
      toDom w₀ A w (rden w (i ⊔ dat.i₀) (Ctx.Le.refl _)
        (Term.realiseAtA hT x hdecl (Term.mono (w.L.ctx_le le_sup_right) dat.t₀)
          (Term.mono hle t))) (definable_rden _ _) :=
  interp_dia_self_core w₀ dat hdeclI
    (interp_canon_eta w₀ w dat.i₀ dat.b₀ dat.hb₀)
    (StageOK := fun _ => True) trivial
    (fun {_Γ'} {_b} s {_k} _ {_e'} {_env'} hag' => IH s hag')
    hag hx hreal hdecl hle hT hmem t

/-! ## The truth lemma for terms

Base terms come first, and on their own: the value of a base term is a class of base terms, and the
only addresses it can read are the world's own roots, whose canonical values are classes.  So this
pair recurses on **size alone** — no stage, no type.  `interp_canon` below recurses on the type and
then the size, and on nothing else: a realisation's content is an address, read outright by
`interp_canon_eta`, so no call is ever made at an unrelated type and no stage order is needed.
-/

mutual
  theorem interpFunc_canon : ∀ {Γ : Ctx} {n : ℕ} (g : Func σ Γ n) {w : World σ N₀}
      {i : ℕ × ℕ} {e : Γ.Le (w.L.ctx i)} {env : (model w₀).Env Γ w},
      Model.Env.Agree e env (canonEnv w₀ w i) →
      ∀ (args : Fin n → w.D) (ts : Fin n → Term σ Γ .Var .var),
        (∀ k, args k = w.cls i (Term.mono e (ts k))) →
        Model.interpFunc env g args = w.cls i (Term.mono e (.func ((Spine.ofFn ts).fill g)))
    | _, _, .F ⟨f, rfl⟩, w, i, e, env, _, args, ts, hts => by
        change canonFunc w f (fun k => args (Fin.cast rfl k)) = _
        rw [Term.mono_fill, Spine.mono_ofFn,
          show (fun k => args (Fin.cast rfl k)) = fun k => w.cls i (Term.mono e (ts k)) from
            funext fun k => hts k,
          canonFunc_cls]
        rfl
    | _, _, .eval g t, w, i, e, env, hag, args, ts, hts => by
        change Model.interpFunc env g (Fin.cons (Model.interp env t) args) = _
        have h0 : Model.interp env t = w.cls i (Term.mono e t) :=
          (interp_canon_base t hag).trans (rden_var_mono e t)
        rw [interpFunc_canon g hag (Fin.cons (Model.interp env t) args) (Fin.cons t ts)
          (fun k => by cases k using Fin.cases <;> simp [h0, hts]), Spine.ofFn_cons]
        rfl
    termination_by _ _ g => g.size
    decreasing_by
      all_goals simp only [Func.size]
      all_goals omega

  /-- ⭐**The truth lemma for base terms**: in an environment agreeing with the canonical one, a base
      term's value is its denotation.  Only `var` and `func` build a base term. -/
  theorem interp_canon_base : ∀ {Γ : Ctx} (t : Term σ Γ .Var .var) {w : World σ N₀}
      {i : ℕ × ℕ} {e : Γ.Le (w.L.ctx i)} {env : (model w₀).Env Γ w},
      Model.Env.Agree e env (canonEnv w₀ w i) →
      Model.interp env t = toDom w₀ .Var w (rden w i e t) (definable_rden e t)
    | _, .var v hv, w, i, e, env, hag => by
        change env.ref v hv = _
        rw [Model.Env.ref_agree hag v hv, canonEnv_ref]
        rfl
    | _, .func f, _, _, _, env, hag => by
        change Model.interpFunc env f Fin.elim0 = _
        exact interpFunc_canon f hag Fin.elim0 Fin.elim0 (fun k => k.elim0)
    termination_by _ t => t.size
    decreasing_by
      all_goals simp only [Term.size]
      all_goals omega
end

/-! ## The realised case when the content is base-typed

The same for a datum whose content happens to be base-typed: its realising term is a base term, so
`interp_canon_base` gives its value outright, with no call at the content and nothing asked of the
stages.  Kept alongside the address reading (`interp_dia_self`) because the truth lemma for
`WFF.here` states the realisation predicate at base type.
-/

/-- `interp_canon_base` at a type that is only provably `Var`. -/
theorem interp_canon_base_of : ∀ {A : VarType}, A = .Var → ∀ {a : Ann A} {Γ : Ctx}
    (t : Term σ Γ A a) {w : World σ N₀} {i : ℕ × ℕ} {e : Γ.Le (w.L.ctx i)}
    {env : (model w₀).Env Γ w}, Model.Env.Agree e env (canonEnv w₀ w i) →
    Model.interp env t = toDom w₀ A w (rden w i e t) (definable_rden e t)
  | _, rfl, .var, _, t, _, _, _, _, hag => interp_canon_base w₀ t hag

/-- ⭐The realised case at base content: no `IHt₀`, and no condition on the stages the induction
    recurses at. -/
theorem interp_dia_self_base {A : VarType} {a : Ann A} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ}
    {x : VarSymb} (dat : RealDatum σ w.L w.T x) (hA : dat.A = .Var)
    (hdeclI : (w.L.ctx i).ref x = some (.VTypeDia dat.A))
    (IH : ∀ {Γ' : Ctx} {b : Ann A} (s : Term σ Γ' A b) {k : ℕ × ℕ},
      ∀ {e' : Γ'.Le (w.L.ctx k)} {env' : (model w₀).Env Γ' w},
      Model.Env.Agree e' env' (canonEnv w₀ w k) →
      Model.interp env' s = toDom w₀ A w (rden w k e' s) (definable_rden e' s))
    {e : Γ.Le (w.L.ctx i)} {env : (model w₀).Env Γ w}
    (hag : Model.Env.Agree e env (canonEnv w₀ w i))
    {X : VarType} (hx : Γ.ref x = some (.VTypeDia X))
    (hreal : w.real x = some dat)
    (hdecl : (w.L.ctx (i ⊔ dat.i₀)).ref x = some (.VTypeDia dat.A))
    (hle : (Γ.diaIn x).Le ((w.L.ctx (i ⊔ dat.i₀)).diaIn x))
    (hT : ModalSys.T = true)
    (hmem : (⟨w, ⟨R.refl hT w⟩⟩ : Succ w) ∈ ((model w₀).posEval (env.ref x hx)).1)
    (t : Term σ (Γ.diaIn x) A a) :
    Model.interp (env.diaPush x hx ⟨⟨w, ⟨R.refl hT w⟩⟩, hmem⟩) t =
      toDom w₀ A w (rden w (i ⊔ dat.i₀) (Ctx.Le.refl _)
        (Term.realiseAtA hT x hdecl (Term.mono (w.L.ctx_le le_sup_right) dat.t₀)
          (Term.mono hle t))) (definable_rden _ _) :=
  interp_dia_self_core w₀ dat hdeclI
    (interp_canon_base_of w₀ hA dat.t₀ (fun _ _ _ => rfl))
    (StageOK := fun _ => True) trivial
    (fun {_Γ'} {_b} s {_k} _ {_e'} {_env'} hag' => IH s hag')
    hag hx hreal hdecl hle hT hmem t

mutual
  /-- ⭐In an environment agreeing with the canonical one, a term's value is its denotation. -/
  theorem interp_canon : ∀ {Γ : Ctx} {A : VarType} {a : Ann A} (t : Term σ Γ A a)
      {w : World σ N₀} {i : ℕ × ℕ} {e : Γ.Le (w.L.ctx i)} {env : (model w₀).Env Γ w},
      Model.Env.Agree e env (canonEnv w₀ w i) →
      Model.interp env t = toDom w₀ A w (rden w i e t) (definable_rden e t)
    | _, _, _, .var v hv, _, _, _, _, hag => interp_canon_base w₀ (Term.var v hv) hag
    | _, _, _, .func f, _, _, _, _, hag => interp_canon_base w₀ (Term.func f) hag
    | _, _, _, .unit, _, _, _, _, _ => rfl
    | _, _, _, .pair s t, _, _, _, _, hag => Prod.ext (interp_canon s hag) (interp_canon t hag)
    | Γ, _, _, .boxtm t, w, i, e, env, hag => by
        apply (model w₀).nec_inj
        funext w'
        rw [Model.box_beta]
        change Model.interp (env.boxPush w') t = toDom w₀ _ w'.1 (rden w i e (.boxtm t) w') _
        rcases hd : w'.1.depth - w.depth with _ | d
        · obtain ⟨w₁, hw₁⟩ := w'
          obtain ⟨hT, hw⟩ := Succ.self ⟨w₁, hw₁⟩ hd
          change w₁ = w at hw
          subst hw
          exact ((Model.interp_collapse (Model.Env.collapseAgree_self hT env) t).symm.trans
            (interp_canon (Term.collapse (Ctx.collapses_boxIn_self hT Γ) t) hag)).trans
            (toDom_congr w₀ (rden_boxtm_self e t _ hd).symm _ _)
        · exact interp_box_far w₀ t.size
            (fun {_Γ} {_a} t' _ht' {_w} {_i} hi {_e} {_env} hag' => interp_canon t' hag') d t
            le_rfl hag w' hd
    | _, _, _, .diatm x hx t, w, i, e, env, hag => by
        obtain ⟨X, hr⟩ := hx
        apply (model w₀).pos_inj
        rw [Model.dia_beta env ⟨X, hr⟩ hr t]
        have hpq₀ : env.ref x hr = (canonEnv w₀ w i).ref x (e.ref hr) :=
          Model.Env.ref_agree hag x hr
        have hpq := hpq₀.trans (canonEnv_ref w₀ w i x (e.ref hr))
        refine Model.posSec_ext hpq _ _ fun w' => ?_
        have hm : w'.1 ∈ ((model w₀).posEval ((canonEnv w₀ w i).ref x (e.ref hr))).1 :=
          hpq₀ ▸ w'.2
        by_cases hd : (w'.1.1 : World σ N₀).depth - w.depth ≠ 0
        · simp only [toDom, rden, dif_neg hd]
          exact interp_canon t ((Model.Env.diaPush_agree hag hr w' hm).trans
            (diaPush_agree_canon w₀ w i (e.ref hr) ⟨w'.1, hm⟩ hd))
        · have hd0 : (w'.1.1 : World σ N₀).depth - w.depth = 0 := not_not.mp hd
          obtain ⟨hweq, hrx⟩ := extent_self (canonEnv_extent w₀ w i (e.ref hr) ▸ hm) hd0
          obtain ⟨⟨w₁, hR⟩, hmem⟩ := w'
          change w₁ = w at hweq
          subst hweq
          have hmx : (⟨w₁, hR⟩ : Succ w₁) ∈ extent w₁ x :=
            canonEnv_extent w₀ w₁ i (e.ref hr) ▸ hm
          refine Eq.trans ?_ (toDom_congr w₀
            (rden_diatm_self e ⟨X, hr⟩ t ⟨⟨w₁, hR⟩, hmx⟩ hd0).symm (definable_rden _ _)
            (definable_dia_apply (definable_rden e (Term.diatm x ⟨X, hr⟩ t)) ⟨⟨w₁, hR⟩, hmx⟩))
          exact interp_dia_self w₀ hrx.data
            (hrx.data.declType i ⟨X, e.ref hr⟩)
            (fun {_Γ} {_b} s {_k} {_e} {_env} hag' => interp_canon s hag')
            hag hr (World.real_of_realised hrx) (realisedDecl hrx e ⟨X, hr⟩)
            (realisedLe w₁ hrx e) hrx.T hmem t
    termination_by _ A _ t => (VarType.tsize A, t.size)
    decreasing_by
      all_goals simp only [Prod.lex_def, Term.size, Term.size_collapse, VarType.tsize]
      all_goals omega
end

end Canon

end V12M
