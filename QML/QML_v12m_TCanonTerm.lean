import QML.QML_v12m_TCanonModel
import QML.QML_v12m_CanonTerm
import QML.QML_v12m_SemReadNames

/-!
# QML v12m — the canonical tree with `Opt` on, T included: the truth lemma for terms

The generalisation of `OCanonTerm` (docs §12.36, step 5).  The **canonical environment** at stage
`i` of a world gives every visible address the frame object of its η-expansion, and a witness is
present exactly when its content is declared at the stage, with that content as its value.

New with T:
* the `here` projection of a necessary address is its value at the self arrow (`canonEnvO_ref`);
* ⭐`canon_selfContent`: a witness realised at the world itself has there, as its content, the value
  of its **identity name** (the η-expansion collapsed and read at the name is the name's);
* ⭐`interp_canonO` at the self arrow: a necessary term through the collapse
  (`Model.interp_collapse`), a possible term through the collapse onto the identity view and the
  reading at the name (`Model.interp_readNames`).  The induction is on the type first, as in the
  `Opt`-off tree: every self case recurses at a smaller type.
-/

namespace V12M

set_option linter.unusedSectionVars false

variable [ModalSys]

omit [ModalSys] in
/-- Stages add only roots: a step address other than an identity content reads as in the
    base. -/
theorem Ctx.stage_step {B : Ctx} {τ : ℕ → VarType} {ρ : ℕ → ℕ} :
    ∀ (k : ℕ) (v : VarSymb) (s : Step), s ≠ .at → B.stage τ ρ k (.step v s) = B (.step v s)
  | 0, _, _, _ => rfl
  | k + 1, v, s, hs => by
      change (Ctx.insert (B.stage τ ρ k) (.free (ρ k)) (τ k)) (.step v s) = _
      rw [Ctx.insert_ne (fun h => by cases h) (by cases s <;> first | rfl | exact absurd rfl hs)]
      exact Ctx.stage_step k v s hs

omit [ModalSys] in
/-- Stages keep the witnesses. -/
theorem Ctx.stage_wit {B : Ctx} {τ : ℕ → VarType} {ρ : ℕ → ℕ} :
    ∀ (k : ℕ) (y : VarSymb), (B.stage τ ρ k).wit y = B.wit y
  | 0, _ => rfl
  | k + 1, y => Ctx.stage_wit k y

namespace OCanon

open Canon

variable {σ : Signature} {N₀ : ℕ}

theorem ctx_step (w : World σ N₀) (i : ℕ × ℕ) (v : VarSymb) {s : Step} (hs : s ≠ .at) :
    w.L.ctx i (.step v s) = w.L.base i.1 (.step v s) :=
  Ctx.stage_step _ v s hs

theorem ctx_wit (w : World σ N₀) (i : ℕ × ℕ) (y : VarSymb) :
    (w.L.ctx i).wit y = (w.L.base i.1).wit y :=
  Ctx.stage_wit _ y

/-- ⭐**Declared at one stage, declared at all**, in a world deciding its witnesses. -/
theorem DecidesO.ctx_stable {hO : ModalSys.Opt = true} {w : World σ N₀} (hdec : DecidesO hO w)
    {i j : ℕ × ℕ} {y : VarSymb} {X : VarType} (hy : (w.L.ctx i).wit y = some X)
    (h : w.L.ctx j (.step y .dia) = some X) : w.L.ctx i (.step y .dia) = some X := by
  rw [ctx_step (s := .dia) _ _ _ nofun] at h ⊢
  rw [ctx_wit] at hy
  exact hdec.stable h hy

variable (hO : ModalSys.Opt = true)

theorem rdenO_sigma {A : VarType} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i))
    {p q : Σ b : Ann A, Term σ Γ A b} (h : p = q) :
    rdenO hO w i e p.2 = rdenO hO w i e q.2 := by
  subst h
  rfl

/-- The denotations of the η-expansions of an address in two nested contexts agree. -/
theorem rdenO_eta_le {Γ₁ Γ₂ : Ctx} (h : Γ₁.Le Γ₂) {w : World σ N₀} {i j : ℕ × ℕ}
    (e₁ : Γ₁.Le (w.L.ctx i)) (e₂ : Γ₂.Le (w.L.ctx j)) (v : VarSymb) (T : VarType)
    (p₁ : Γ₁.ref v = some T) (p₂ : Γ₂.ref v = some T) :
    rdenO hO w i e₁ (Term.eta (σ := σ) v T p₁) = rdenO hO w j e₂ (Term.eta v T p₂) := by
  rw [show Term.eta (σ := σ) v T p₂ = Term.mono h (Term.eta v T p₁) from
    (Term.mono_eta h v T p₁).symm, rdenO_mono]
  exact rdenO_congr _ _ _ _ _ _

variable [Countable σ.FuncSyms] [Countable σ.RelSyms] (w₀ : World σ N₀)

/-- The canonical value of a visible address: its η-expansion's denotation. -/
noncomputable def canonVal (w : World σ N₀) (i : ℕ × ℕ) (v : VarSymb) (T : VarType)
    (hv : w.L.ctx i v = some T) : (frameO hO w₀).Dom T w :=
  toDomO hO w₀ T w (rdenO hO w i (Ctx.Le.refl _)
    (Term.eta v T ((Ctx.ref_nonproj _ (w.noProjLast i v T hv)).trans hv))) (definableO_rden _ _)

/-- ⭐**The canonical environment**: every visible address denotes its η-expansion, and a witness
    is present exactly when its content is declared, with that content as its value. -/
noncomputable def canonEnvO (w : World σ N₀) (i : ℕ × ℕ) :
    (modelT hO w₀).Env (w.L.ctx i) w where
  val := canonVal hO w₀ w i
  wit y X _ := ⟨w.L.ctx i (.step y .dia) = some X, fun hv => canonVal hO w₀ w i _ X hv⟩
  opened _ _ _ hv := ⟨hv, rfl⟩

/-- Every reachable address reads as its η-expansion.  Under T the `here` projection of a necessary
    address is its value at the self arrow, its η-expansion collapsed. -/
theorem canonEnvO_ref (w : World σ N₀) (i : ℕ × ℕ) :
    ∀ (v : VarSymb) {T : VarType} (h : (w.L.ctx i).ref v = some T),
      (canonEnvO hO w₀ w i).ref v h =
        toDomO hO w₀ T w (rdenO hO w i (Ctx.Le.refl _) (Term.eta v T h)) (definableO_rden _ _)
  | .root _, _, _ => rfl
  | .step v s, T, h => by
      by_cases hs : s.isStruct = true
      · rw [Model.Env.ref, dif_pos hs]
        split
        · rename_i U hU
          rw [canonEnvO_ref w i v hU]
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
              change toDomO hO w₀ _ w (rdenO hO w i (Ctx.Le.refl _)
                (.boxtm (Term.eta v.inner _ (Ctx.ref_inner hU))) (SuccO.selfArr hT₁ w)) _ = _
              exact toDomO_congr hO w₀
                ((rdenO_boxtm_self (Ctx.Le.refl _) (Term.eta v.inner _ (Ctx.ref_inner hU))
                  (SuccO.selfArr hT₁ w) (Nat.sub_self _)).trans
                  (rdenO_sigma hO _ ((Term.collapse_eta _ _ _ _).trans
                    (Term.eta_congr (VarSymb.inner_collapse_zero v) _ _ _)))) _ _
          | box => cases hs
          | dia => cases hs
          | keep => cases hs
          | «at» => cases hs
        · rename_i hU
          rw [Ctx.ref_step_proj _ _ hs, hU] at h
          cases h
      · rw [Model.Env.ref, dif_neg hs]
        rfl

/-- The extent of a canonical possible address is its extent in the tree. -/
theorem canonEnvO_extent (w : World σ N₀) (i : ℕ × ℕ) {x : VarSymb} {X : VarType}
    (hr : (w.L.ctx i).ref x = some (.VTypeDia X)) :
    ((modelT hO w₀).posEval ((canonEnvO hO w₀ w i).ref x hr)).1 = extentO w x := by
  rw [canonEnvO_ref]
  rfl

/-- The canonical environment at a later stage agrees with the one at an earlier stage. -/
theorem canonEnvO_le (w : World σ N₀) {i j : ℕ × ℕ} (hij : i ≤ j) :
    Model.Env.Agree (w.L.ctx_le hij) (canonEnvO hO w₀ w i) (canonEnvO hO w₀ w j) :=
  fun _ _ _ => toDomO_congr hO w₀ (rdenO_eta_le hO (w.L.ctx_le hij) _ _ _ _ _ _) _ _

/-- … and, in a world deciding its witnesses, in witnesses. -/
theorem canonEnvO_le_wit {w : World σ N₀} (hdec : DecidesO hO w) {i j : ℕ × ℕ} (hij : i ≤ j) :
    Model.Env.WitAgree (w.L.ctx_le hij) (canonEnvO hO w₀ w i) (canonEnvO hO w₀ w j) := by
  intro y X hy
  refine Part.ext' ⟨fun h => w.L.ctx_le hij _ _ h, fun h => hdec.ctx_stable hy h⟩
    fun _ _ => toDomO_congr hO w₀ (rdenO_eta_le hO (w.L.ctx_le hij) _ _ _ _ _ _) _ _

/-- Pushing the canonical environment into `□` at a child agrees with the child's. -/
theorem boxPush_agree_canonO (w : World σ N₀) (i : ℕ × ℕ) (a : SuccO hO w) (ha : AccO hO w a.1) :
    Model.Env.Agree (ha.boxIn_le i) ((canonEnvO hO w₀ w i).boxPush a)
      (canonEnvO hO w₀ a.1 (childStage i)) := by
  intro v T hv
  match v with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hv
      change (modelT hO w₀).necEval ((canonEnvO hO w₀ w i).ref u (Ctx.boxIn_step_box hv)) a = _
      rw [canonEnvO_ref]
      have hd : a.1.depth - w.depth ≠ 0 := ha.depth_ne
      refine toDomO_congr hO w₀ ((rdenO_boxtm_acc _ _ a hd).trans ((rdenO_sigma hO _
        (Term.eta_congr (VarSymb.inner_box hk) T _ (Ctx.ref_boxIn_of hk hu))).trans
          (rdenO_eta_le hO (ha.boxIn_le i) _ _ _ _ _ _))) _ _
  | .step _ .keep =>
      exact (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four (Ctx.boxIn_keep hv).1)).elim
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv
  | .step _ .at => cases hv

/-- ⭐**A witness read along the arrow to a child is present exactly when the child opened it**,
    with its content there. -/
theorem boxPush_witAgree_canonO (w : World σ N₀) (i : ℕ × ℕ) (a : SuccO hO w)
    (ha : AccO hO w a.1) :
    Model.Env.WitAgree (ha.boxIn_le i) ((canonEnvO hO w₀ w i).boxPush a)
      (canonEnvO hO w₀ a.1 (childStage i)) := by
  intro y X hy
  have hr : (w.L.ctx i).ref y = some (.VTypeDia X) := (Ctx.boxIn_wit.mp hy).2
  have hM : (w.L.ctx i).boxIn.Le (bview w (max i.1 i.2)) := (le_diag_max w i).boxIn
  have hd : a.1.depth - w.depth ≠ 0 := ha.depth_ne
  change (⟨a ∈ ((modelT hO w₀).posEval ((canonEnvO hO w₀ w i).ref y hr)).1,
    fun hm => ((modelT hO w₀).posEval ((canonEnvO hO w₀ w i).ref y hr)).2 ⟨a, hm⟩⟩ :
      Part ((frameO hO w₀).Dom X a.1)) = _
  rw [Model.posPart_congr (canonEnvO_ref hO w₀ w i y hr) a]
  refine Part.ext' ⟨fun hm => ha.opened_at (extentO_child hm hd).2 (hM.wit y X hy),
    fun hdc => Or.inl ⟨ha, max i.1 i.2, X, hM.wit y X hy, hdc⟩⟩ fun hm _ =>
      toDomO_congr hO w₀ ((rdenO_diatm_acc _ _ _ ⟨a, hm⟩ hd).trans
        (rdenO_eta_le hO (extentO_le ha (extentO_child hm hd).2 (Ctx.Le.refl _) ⟨X, hr⟩)
          _ _ _ _ _ _)) _ _

/-- Pushing the canonical environment into `◇_x` at a child that opened `x` agrees with the
    child's. -/
theorem diaPush_agree_canonO (w : World σ N₀) (i : ℕ × ℕ) {x : VarSymb} {X : VarType}
    (hr : (w.L.ctx i).ref x = some (.VTypeDia X))
    (a : ((modelT hO w₀).posEval ((canonEnvO hO w₀ w i).ref x hr)).1)
    (hw : a.1 ∈ extentO w x) (hd : a.1.1.depth - w.depth ≠ 0) :
    Model.Env.Agree (extentO_le (extentO_child hw hd).1 (extentO_child hw hd).2 (Ctx.Le.refl _)
        ⟨X, hr⟩)
      ((canonEnvO hO w₀ w i).diaPush x hr a) (canonEnvO hO w₀ a.1.1 (childStage i)) := by
  have hc := extentO_child hw hd
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
      have hpq := canonEnvO_ref hO w₀ w i u hr
      have hm : a.1 ∈ ((modelT hO w₀).posEval (toDomO hO w₀ (.VTypeDia X) w
          (rdenO hO w i (Ctx.Le.refl _) (Term.eta u (.VTypeDia X) hr))
          (definableO_rden _ _))).1 := by
        rw [← hpq]
        exact a.2
      change ((modelT hO w₀).posEval ((canonEnvO hO w₀ w i).ref u hr)).2 a = _
      rw [Model.posEval_snd_congr hpq a hm]
      exact toDomO_congr hO w₀ ((rdenO_diatm_acc _ _ _ ⟨a.1, hm⟩ hd).trans
        (rdenO_eta_le hO (extentO_le hc.1 hc.2 (Ctx.Le.refl _) ⟨X, hr⟩) _ _ _ _ _ _)) _ _
  | .step u .box =>
      exact boxPush_agree_canonO hO w₀ w i a.1 hc.1 (.step u .box) T hv
  | .step u .keep =>
      exact boxPush_agree_canonO hO w₀ w i a.1 hc.1 (.step u .keep) T hv
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv
  | .step _ .at => cases hv

/-! ## The self arrow -/

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem sig_readNames {ν : VarSymb → Option VarSymb} {k : ℕ} {Γ₁ Γ₂ : Ctx}
    (h : Ctx.ReadsNames ν k Γ₁ Γ₂) {T : VarType} {p q : Σ b : Ann T, Term σ Γ₁ T b}
    (e : p = q) :
    (⟨_, Term.readNames h p.2⟩ : Σ b, Term σ Γ₂ T b) = ⟨_, Term.readNames h q.2⟩ := by
  subst e
  rfl

/-- A canonical environment of a world declaring no identity reading respects its identity
    contents, vacuously. -/
theorem canonEnvO_openedT {w : World σ N₀} (hna : StagesNoAt w) (i : ℕ × ℕ) :
    (canonEnvO hO w₀ w i).OpenedT :=
  fun z _ _ hv => (hna i z _ hv).elim

/-- ⭐**A witness realised at the world itself has there the value of its identity name.**  The
    content of its η-expansion at the self arrow is the η-expansion collapsed (`x.dia` to `x.at`)
    and read at the name (`x.at` to the name). -/
theorem canon_selfContent {w : World σ N₀} {x : VarSymb} (hs : SelfIn hO w x) {j : ℕ × ℕ}
    (hj : hs.name.i₀ ≤ j)
    (hm : SuccO.selfArr hs.1 w ∈
      ((modelT hO w₀).posEval ((canonEnvO hO w₀ w j).ref x (hs.decl hj))).1) :
    ((modelT hO w₀).posEval ((canonEnvO hO w₀ w j).ref x (hs.decl hj))).2
        ⟨SuccO.selfArr hs.1 w, hm⟩ =
      (canonEnvO hO w₀ w j).ref (.root (.free hs.name.c)) (hs.declName hj) := by
  have hpq := canonEnvO_ref hO w₀ w j x (hs.decl hj)
  have hm' : SuccO.selfArr hs.1 w ∈ ((modelT hO w₀).posEval (toDomO hO w₀ _ w
      (rdenO hO w j (Ctx.Le.refl _) (Term.eta x _ (hs.decl hj))) (definableO_rden _ _))).1 := by
    rw [← hpq]
    exact hm
  rw [Model.posEval_snd_congr hpq _ hm', canonEnvO_ref hO w₀ w j (.root (.free hs.name.c))]
  have hd : (SuccO.selfArr (hO := hO) hs.1 w).1.depth - w.depth = 0 := Nat.sub_self _
  refine toDomO_congr hO w₀ ((rdenO_diatm_self (Ctx.Le.refl _) _ _
    ⟨SuccO.selfArr hs.1 w, hm'⟩ hd).trans ?_) _ _
  change rdenO hO w _ (Ctx.Le.refl _) (selfTermAt _ le_sup_right (Term.mono _
    (Term.eta (.step x .dia) hs.name.A _))).2 = _
  rw [Term.mono_eta]
  refine (rdenO_sigma hO _ (q := ⟨_, Term.eta (.root (.free hs.name.c)) hs.name.A
    (hs.declName le_sup_right)⟩) ?_).trans
    (rdenO_eta_le hO (w.L.ctx_le (sup_le le_rfl hj)) _ _ _ _ _ _)
  exact (sig_readNames _ (Term.collapse_eta _ _ _ _)).trans ((Term.readNames_eta _ _ _ _).trans
    (Term.eta_congr (by rw [VarSymb.collapse_dia_zero_opt hO,
      VarSymb.readNames_at_named (TCanon.nameAt_self x _)]) _ _ _))

/-- ⭐**A possible term's body at the self arrow**, given the truth lemma at the content type:
    weaken to the name's stage, collapse onto `x`'s identity view (`collapseAgree_diaIn_optInT`;
    the stage declares no identity reading, so the canonical environment respects its identity
    contents), read at the name (`interp_readNames`; the name's value is the content,
    `canon_selfContent`), and apply the truth lemma there. -/
theorem interp_dia_selfO {w : World σ N₀} {A : VarType}
    (IH : ∀ {Γ' : Ctx} {b : Ann A} (s : Term σ Γ' A b) {k : ℕ × ℕ} {e' : Γ'.Le (w.L.ctx k)}
      {env' : (modelT hO w₀).Env Γ' w}, Model.Env.Agree e' env' (canonEnvO hO w₀ w k) →
      Model.interp env' s = toDomO hO w₀ A w (rdenO hO w k e' s) (definableO_rden e' s))
    {Γ : Ctx} {i : ℕ × ℕ} {e : Γ.Le (w.L.ctx i)} {env : (modelT hO w₀).Env Γ w}
    (hag : Model.Env.Agree e env (canonEnvO hO w₀ w i)) {x : VarSymb} {X : VarType}
    (hr : Γ.ref x = some (.VTypeDia X)) (hs : SelfIn hO w x)
    (hm : SuccO.selfArr hs.1 w ∈ ((modelT hO w₀).posEval (env.ref x hr)).1) {a : Ann A}
    (t : Term σ (Γ.diaIn x) A a) :
    Model.interp (env.diaPush x hr ⟨SuccO.selfArr hs.1 w, hm⟩) t =
      toDomO hO w₀ A w (rdenO hO w (i ⊔ hs.name.i₀) (Ctx.Le.refl _) (selfTerm hs e t).2)
        (definableO_rden _ _) := by
  have eK : Γ.Le (w.L.ctx (i ⊔ hs.name.i₀)) := e.trans (w.L.ctx_le le_sup_left)
  have hagK : Model.Env.Agree eK env (canonEnvO hO w₀ w (i ⊔ hs.name.i₀)) :=
    hag.trans (canonEnvO_le hO w₀ w le_sup_left)
  have hxK : (w.L.ctx (i ⊔ hs.name.i₀)).ref x = some (.VTypeDia hs.name.A) :=
    hs.decl le_sup_right
  have hXA : X = hs.name.A := by
    have h₁ := eK.ref hr
    rw [hxK] at h₁
    cases h₁
    rfl
  subst hXA
  have hxT := Ctx.witT_of hs.1 hO hxK
  have hmK : SuccO.selfArr hs.1 w ∈
      ((modelT hO w₀).posEval ((canonEnvO hO w₀ w (i ⊔ hs.name.i₀)).ref x hxK)).1 := by
    rw [← Model.Env.ref_agree hagK x hr]
    exact hm
  have hd : ((canonEnvO hO w₀ w (i ⊔ hs.name.i₀)).witT x hxT).Dom := hmK
  have hop := canonEnvO_openedT hO w₀ hs.2.2 (i ⊔ hs.name.i₀)
  have R := TCanon.readsNameIn hs.1 hO (hs.2.2 _) hxK (hs.declName le_sup_right)
  have hRA : Model.Env.ReadAgree R
      ((canonEnvO hO w₀ w (i ⊔ hs.name.i₀)).optPushT x hxT hd)
      (canonEnvO hO w₀ w (i ⊔ hs.name.i₀)) := by
    refine Model.Env.ReadAgree.of_raw ?_
    intro v T hlp hv
    by_cases hvx : v = .step x .at
    · subst hvx
      have hTA : hs.name.A = T := by
        rw [Ctx.optInT_content hxT] at hv
        exact Option.some.inj hv
      subst hTA
      rw [Model.Env.ref_congr _ (VarSymb.readNames_at_named (TCanon.nameAt_self x hs.name.c)) _
        (hs.declName le_sup_right)]
      refine Eq.trans ?_ (canon_selfContent hO w₀ hs le_sup_right hmK)
      change (if hv' : VarSymb.step x .at = .step x .at then _ else _) = _
      rw [dif_pos rfl]
      rfl
    · have hv' : (w.L.ctx (i ⊔ hs.name.i₀)) v = some T := by rwa [Ctx.optInT_ne hvx] at hv
      rw [Model.Env.ref_congr _ (VarSymb.readNames_raw (hs.2.2 _) hlp hv') _
          ((Ctx.ref_nonproj _ hlp).trans hv'),
        Model.Env.ref_of_nonproj _ hlp _ hv']
      exact (Model.Env.agree_optPushT _ hop hxT hd v T hv').symm
  calc Model.interp (env.diaPush x hr ⟨SuccO.selfArr hs.1 w, hm⟩) t
      = Model.interp ((canonEnvO hO w₀ w (i ⊔ hs.name.i₀)).diaPush x hxK
          ⟨SuccO.selfArr hs.1 w, hmK⟩) (Term.mono (eK.diaIn x) t) :=
        (Model.interp_mono (Model.Env.diaPush_agree hagK hr ⟨_, hm⟩ hmK) t).symm
    _ = Model.interp ((canonEnvO hO w₀ w (i ⊔ hs.name.i₀)).optPushT x hxT hd)
          (Term.collapse (Ctx.collapses_diaIn_optInT hs.1 hO _ hxK) (Term.mono (eK.diaIn x) t)) :=
        (Model.interp_collapse (Model.Env.collapseAgree_diaIn_optInT hs.1 hO _ hop hxK hmK hd)
          _).symm
    _ = Model.interp (canonEnvO hO w₀ w (i ⊔ hs.name.i₀)) (Term.readNames R
          (Term.collapse (Ctx.collapses_diaIn_optInT hs.1 hO _ hxK) (Term.mono (eK.diaIn x) t))) :=
        (Model.interp_readNames hO hRA _).symm
    _ = _ := IH _ (fun _ _ _ => rfl)

/-! ## The truth lemma for terms -/

mutual
  theorem interpFunc_canonO : ∀ {Γ : Ctx} {n : ℕ} (g : Func σ Γ n) {w : World σ N₀}
      {i : ℕ × ℕ} {e : Γ.Le (w.L.ctx i)} {env : (modelT hO w₀).Env Γ w},
      Model.Env.Agree e env (canonEnvO hO w₀ w i) →
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
          (interp_canon_baseO t hag).trans (rdenO_var_mono e t)
        rw [interpFunc_canonO g hag (Fin.cons (Model.interp env t) args) (Fin.cons t ts)
          (fun k => by cases k using Fin.cases <;> simp [h0, hts]), Spine.ofFn_cons]
        rfl
    termination_by _ _ g => g.size
    decreasing_by
      all_goals simp only [Func.size]
      all_goals omega

  /-- The truth lemma for base terms. -/
  theorem interp_canon_baseO : ∀ {Γ : Ctx} (t : Term σ Γ .Var .var) {w : World σ N₀}
      {i : ℕ × ℕ} {e : Γ.Le (w.L.ctx i)} {env : (modelT hO w₀).Env Γ w},
      Model.Env.Agree e env (canonEnvO hO w₀ w i) →
      Model.interp env t = toDomO hO w₀ .Var w (rdenO hO w i e t) (definableO_rden e t)
    | _, .var v hv, w, i, e, env, hag => by
        change env.ref v hv = _
        rw [Model.Env.ref_agree hag v hv, canonEnvO_ref]
        rfl
    | _, .func f, _, _, _, env, hag => by
        change Model.interpFunc env f Fin.elim0 = _
        exact interpFunc_canonO f hag Fin.elim0 Fin.elim0 (fun k => k.elim0)
    termination_by _ t => t.size
    decreasing_by
      all_goals simp only [Term.size]
      all_goals omega
end

/-- ⭐**The truth lemma for terms**: in an environment agreeing with the canonical one, a term's
    value is its denotation — at the self arrow too. -/
theorem interp_canonO : ∀ {Γ : Ctx} {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    {w : World σ N₀} {i : ℕ × ℕ} {e : Γ.Le (w.L.ctx i)} {env : (modelT hO w₀).Env Γ w},
    Model.Env.Agree e env (canonEnvO hO w₀ w i) →
    Model.interp env t = toDomO hO w₀ A w (rdenO hO w i e t) (definableO_rden e t)
  | _, _, _, .var v hv, _, _, _, _, hag => interp_canon_baseO hO w₀ (Term.var v hv) hag
  | _, _, _, .func f, _, _, _, _, hag => interp_canon_baseO hO w₀ (Term.func f) hag
  | _, _, _, .unit, _, _, _, _, _ => rfl
  | _, _, _, .pair s t, _, _, _, _, hag => Prod.ext (interp_canonO s hag) (interp_canonO t hag)
  | Γ, _, _, .boxtm t, w, i, e, env, hag => by
      apply (modelT hO w₀).nec_inj
      funext a
      rw [Model.box_beta]
      change Model.interp (env.boxPush a) t = toDomO hO w₀ _ a.1 (rdenO hO w i e (.boxtm t) a) _
      by_cases hd : a.1.depth - w.depth = 0
      · obtain ⟨w₁, h₁⟩ := a
        obtain ⟨hT, hw⟩ := SuccO.self ⟨w₁, h₁⟩ hd
        change w₁ = w at hw
        subst hw
        exact ((Model.interp_collapse (Model.Env.collapseAgree_self hT env) t).symm.trans
          (interp_canonO (Term.collapse (Ctx.collapses_boxIn_self hT Γ) t) hag)).trans
          (toDomO_congr hO w₀ (rdenO_boxtm_self e t _ hd).symm _ _)
      · exact (interp_canonO t ((Model.Env.boxPush_agree hag a).trans
          (boxPush_agree_canonO hO w₀ w i a (SuccO.acc (hO := hO) a hd)))).trans
          (toDomO_congr hO w₀ (rdenO_boxtm_acc e t a hd).symm _ _)
  | _, _, _, .diatm x hx t, w, i, e, env, hag => by
      obtain ⟨X, hr⟩ := hx
      refine (modelT hO w₀).pos_inj ?_
        fun hS => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_shaped hS)).elim
      rw [Model.dia_beta env ⟨X, hr⟩ hr t]
      have hpq₀ : env.ref x hr = (canonEnvO hO w₀ w i).ref x (e.ref hr) :=
        Model.Env.ref_agree hag x hr
      have hpq := hpq₀.trans (canonEnvO_ref hO w₀ w i x (e.ref hr))
      refine Model.posSec_ext hpq _ _ fun a => ?_
      have hm : a.1 ∈ ((modelT hO w₀).posEval ((canonEnvO hO w₀ w i).ref x (e.ref hr))).1 := by
        rw [← hpq₀]
        exact a.2
      have hmx : a.1 ∈ extentO w x := by
        rw [← canonEnvO_extent hO w₀ w i (e.ref hr)]
        exact hm
      by_cases hd : a.1.1.depth - w.depth = 0
      · obtain ⟨⟨w₁, h₁⟩, ha⟩ := a
        obtain ⟨he, hs⟩ := extentO_self hmx hd
        change w₁ = w at he
        subst he
        exact (interp_dia_selfO hO w₀ (fun s _ _ _ hag' => interp_canonO s hag') hag hr hs ha
          t).trans (toDomO_congr hO w₀ (rdenO_diatm_self e ⟨X, hr⟩ t ⟨_, hmx⟩ hd).symm _ _)
      · exact (interp_canonO t ((Model.Env.diaPush_agree hag hr a hm).trans
          (diaPush_agree_canonO hO w₀ w i (e.ref hr) ⟨a.1, hm⟩ hmx hd))).trans
          (toDomO_congr hO w₀ (rdenO_diatm_acc e ⟨X, hr⟩ t ⟨a.1, hmx⟩ hd).symm _ _)
  termination_by _ A _ t => (VarType.tsize A, t.size)
  decreasing_by
    all_goals simp only [Prod.lex_def, Term.size, Term.size_collapse, VarType.tsize]
    all_goals omega

end OCanon

end V12M
