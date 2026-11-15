import QML.QML_v12m_TCanonTerm
import QML.QML_v12m_Completeness
import QML.QML_v12m_GK
import QML.QML_v12m_SemEqH

/-!
# QML v12m — the canonical tree with `Opt` on, T included: the truth lemma

The generalisation of `OCanonTruth` (docs §12.36).  Invariants at a world: it decides its witnesses
(`DecidesO`) and declares no identity reading (`StagesNoAt`); children inherit both
(`AccO.decides`, `SuccO.noAt`).  New cases:

* ⭐`identCase`, `◇⁰ᵀ_y χ`: where `y` is realised at the world, its identity view is read at the
  name (`TCanon.optT_named`, `TCanon.named_optT`), and the semantic side follows by **soundness**
  of those two derivations, the name sentence being true in the canonical environment
  (`sat_eqH`, `canon_selfContent`).  Where it is not, both sides are false.
* `□χ` at the self arrow: `T_box` and the collapse.
* `◇_x χ` at the self arrow: were `◇_x χ` missing, `¬ diaId χ` would be in the theory (the bridge,
  `T_box`, `WFF.collapse_fold`), against `identCase` at the collapsed body.
-/

namespace V12M

set_option linter.unusedSectionVars false

variable [ModalSys]

namespace OCanon

open Canon

variable {σ : Signature} {N₀ : ℕ}

variable (hO : ModalSys.Opt = true) [Countable σ.FuncSyms] [Countable σ.RelSyms]
  (w₀ : World σ N₀) [ModalSys.WeakTO]

/-- ⭐The canonical model with `Opt` on is a model proper: its `Ind` is equality. -/
theorem indInvariantT : (modelT hO w₀).IndInvariant :=
  Model.indInvariant_of_eq (fun _ _ h => h)
    fun hS => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_BStrong hS)).elim

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.WeakTO] in
/-- Weakening the name sentence. -/
theorem nameSent_mono {Γ Γ' : Ctx} (h : Γ.Le Γ') (hT : ModalSys.T = true) {x : VarSymb}
    {A : VarType} (hx : Γ.ref x = some (.VTypeDia A)) {a : Ann A} (t : Term σ Γ A a) :
    WFF.mono h (TCanon.nameSent hT hO hx t) = TCanon.nameSent hT hO (h.ref hx) (Term.mono h t) := by
  change WFF.optx hO .ident x _ (WFF.mono (h.optInK .ident x) (eqH hO A _ _)) =
    WFF.optx hO .ident x _ (eqH hO A (Term.eta (.step x .at) A _)
      (Term.mono (Ctx.le_optInT Γ' x) (Term.mono h t)))
  rw [eqH_mono, Term.mono_eta, Term.mono_mono, Term.mono_mono]

/-- ⭐**The name sentence is true**: at a stage past the name, `y` is realised at the world itself
    with its content `≡` to the name. -/
theorem sat_nameSent {w : World σ N₀} {y : VarSymb} (hs : SelfIn hO w y) {j : ℕ × ℕ}
    (hj : hs.name.i₀ ≤ j) :
    (modelT hO w₀).sat (canonEnvO hO w₀ w j)
      (TCanon.nameSent hs.1 hO (hs.decl hj)
        (Term.eta (.root (.free hs.name.c)) hs.name.A (hs.declName hj))) := by
  have hxT := Ctx.witT_of hs.1 hO (hs.decl hj)
  have hm : SuccO.selfArr hs.1 w ∈
      ((modelT hO w₀).posEval ((canonEnvO hO w₀ w j).ref y (hs.decl hj))).1 := by
    rw [canonEnvO_extent]
    exact Or.inr ⟨rfl, hs⟩
  have hd : ((canonEnvO hO w₀ w j).witT y hxT).Dom := hm
  refine ⟨hs.name.A, hxT, hd, ?_⟩
  rw [Model.sat_eqH hO]
  have hop := canonEnvO_openedT hO w₀ hs.2.2 j
  rw [Model.interp_eta, Model.interp_mono (Model.Env.agree_optPushT _ hop hxT hd),
    Model.interp_eta]
  refine Eq.trans ?_ (canon_selfContent hO w₀ hs hj hm)
  rw [Model.Env.ref_of_nonproj _ rfl _ (Ctx.optInT_content hxT)]
  change (if hv' : VarSymb.step y .at = .step y .at then _ else _) = _
  rw [dif_pos rfl]
  rfl

/-- ⭐**The identity case of the truth lemma**, given the truth lemma below a size bound. -/
theorem identCase (n : ℕ) {w : World σ N₀} (hna : StagesNoAt w)
    (IH : ∀ (i : ℕ × ℕ) (φ : WFF σ (w.L.ctx i) 0), φ.size < n →
      ((modelT hO w₀).sat (canonEnvO hO w₀ w i) φ ↔ (⟨i, φ⟩ : w.L.sys.Sentence σ) ∈ w.T))
    (hwit : ∀ {i j : ℕ × ℕ} (hij : i ≤ j),
      Model.Env.WitAgree (w.L.ctx_le hij) (canonEnvO hO w₀ w i) (canonEnvO hO w₀ w j))
    (i : ℕ × ℕ) {y : VarSymb} (hy : ∃ X, (w.L.ctx i).witK .ident y = some X)
    (χ : WFF σ ((w.L.ctx i).optInT y) 0) (hχ : χ.size < n) :
    (modelT hO w₀).sat (canonEnvO hO w₀ w i) (.optx hO .ident y hy χ) ↔
      (⟨i, .optx hO .ident y hy χ⟩ : w.L.sys.Sentence σ) ∈ w.T := by
  obtain ⟨X, hyT⟩ := hy
  obtain ⟨hT, -, hr⟩ := Ctx.witT_spec hyT
  by_cases hs : SelfIn hO w y
  swap
  · constructor
    · rintro ⟨X', h', hd, -⟩
      obtain rfl : X' = X := by
        have h₁ := (Ctx.witT_spec h').2.2
        rw [hr] at h₁
        cases h₁
        rfl
      have hm : SuccO.selfArr (hO := hO) hT w ∈ extentO (hO := hO) w y := by
        rw [← canonEnvO_extent hO w₀ w i hr]
        exact hd
      rcases hm with ⟨ha, _⟩ | ⟨_, hs'⟩
      · exact absurd (Nat.sub_self _) ha.depth_ne
      · exact (hs hs').elim
    · intro hmem
      exfalso
      refine hs ⟨hT, ⟨i, X, hr, World.mem_of_provable (Δ := [_])
        (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hmem) ⟨?_⟩⟩, hna⟩
      exact Proof.K_opt hO .ident y ⟨X, hyT⟩ (Δ₁ := []) (Δ₂ := []) (φ := .top) (ψ := χ)
        .top_intro
  -- `y` is realised here: read its identity view at the name
  have hK : i ≤ i ⊔ hs.name.i₀ := le_sup_left
  have hle := w.L.ctx_le hK
  have hrK : (w.L.ctx (i ⊔ hs.name.i₀)).ref y = some (.VTypeDia X) := hle.ref hr
  have hXA : X = hs.name.A := by
    have h₁ := hs.decl (le_sup_right : hs.name.i₀ ≤ i ⊔ hs.name.i₀)
    rw [hrK] at h₁
    cases h₁
    rfl
  subst hXA
  have hc' := w.fresh_deeper (Nat.lt_succ_self w.depth) 0 (i ⊔ hs.name.i₀)
  have hfree := hna (i ⊔ hs.name.i₀)
  set t := Term.eta (σ := σ) (.root (.free hs.name.c)) hs.name.A (hs.declName le_sup_right)
  set χK := WFF.mono (hle.optInT y) χ
  have hns := sat_nameSent hO w₀ hs (le_sup_right : hs.name.i₀ ≤ i ⊔ hs.name.i₀)
  have hnsm : (⟨i ⊔ hs.name.i₀, TCanon.nameSent hs.1 hO (hs.decl le_sup_right) t⟩ :
      w.L.sys.Sentence σ) ∈ w.T := by
    have h₀ := (World.mem_lift (w := w) (le_sup_right : hs.name.i₀ ≤ i ⊔ hs.name.i₀)).mp
      hs.name.nameSent_mem
    rw [nameSent_mono, Term.mono_eta] at h₀
    exact h₀
  have hxT := Ctx.witT_of hs.1 hO (hs.decl (le_sup_right : hs.name.i₀ ≤ i ⊔ hs.name.i₀))
  set Φt := WFF.instantiate Ctx.NoSlots.slots t
    (TCanon.readSlot hs.1 hO hfree (hs.decl le_sup_right) hc' χK) with hΦt
  have hsz : Φt.size < n := by
    simp only [hΦt, TCanon.readSlot, WFF.bindFree, WFF.renameRoot, WFF.size_instantiate,
      WFF.size_subst, WFF.size_readNames, χK, WFF.size_mono]
    exact hχ
  have hpre : ∀ φ : WFF σ (w.L.ctx (i ⊔ hs.name.i₀)) 0,
      (modelT hO w₀).sat (canonEnvO hO w₀ w (i ⊔ hs.name.i₀)) φ →
      ∀ ψ ∈ [TCanon.nameSent hs.1 hO (hs.decl le_sup_right) t, φ],
        (modelT hO w₀).sat (canonEnvO hO w₀ w (i ⊔ hs.name.i₀)) ψ := by
    intro φ hφ ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact hns
    · rw [List.mem_singleton.mp hψ]
      exact hφ
  have hmpre : ∀ φ : WFF σ (w.L.ctx (i ⊔ hs.name.i₀)) 0,
      (⟨i ⊔ hs.name.i₀, φ⟩ : w.L.sys.Sentence σ) ∈ w.T →
      ∀ ψ ∈ [TCanon.nameSent hs.1 hO (hs.decl le_sup_right) t, φ],
        (⟨i ⊔ hs.name.i₀, ψ⟩ : w.L.sys.Sentence σ) ∈ w.T := by
    intro φ hφ ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact hnsm
    · rw [List.mem_singleton.mp hψ]
      exact hφ
  have hsound := fun {Δ : List (WFF σ (w.L.ctx (i ⊔ hs.name.i₀)) 0)}
      {φ : WFF σ (w.L.ctx (i ⊔ hs.name.i₀)) 0} (p : Proof σ _ Δ φ) =>
    Model.soundness p (modelT hO w₀) (indInvariantT hO w₀) (canonEnvO hO w₀ w (i ⊔ hs.name.i₀))
      (Ctx.Presented.tame _) (w.noProjLast _) (canonEnvO_openedT hO w₀ hna _)
  calc (modelT hO w₀).sat (canonEnvO hO w₀ w i) (.optx hO .ident y ⟨_, hyT⟩ χ)
      ↔ (modelT hO w₀).sat (canonEnvO hO w₀ w (i ⊔ hs.name.i₀))
          (.optx hO .ident y ⟨_, hxT⟩ χK) :=
        (Model.sat_mono (canonEnvO_le hO w₀ w hK) (.optx hO .ident y ⟨_, hyT⟩ χ)
          (fun _ => hwit hK)).symm
    _ ↔ (modelT hO w₀).sat (canonEnvO hO w₀ w (i ⊔ hs.name.i₀)) Φt :=
        ⟨fun h => hsound (TCanon.optT_named hs.1 hO hfree (hs.decl le_sup_right) hc' χK t)
            (hpre _ h),
          fun h => hsound (TCanon.named_optT hs.1 hO hfree (hs.decl le_sup_right) hc' χK t)
            (hpre _ h)⟩
    _ ↔ (⟨i ⊔ hs.name.i₀, Φt⟩ : w.L.sys.Sentence σ) ∈ w.T := IH _ _ hsz
    _ ↔ (⟨i ⊔ hs.name.i₀, .optx hO .ident y ⟨_, hxT⟩ χK⟩ : w.L.sys.Sentence σ) ∈ w.T :=
        ⟨fun h => World.mem_of_provable (hmpre _ h)
            ⟨TCanon.named_optT hs.1 hO hfree (hs.decl le_sup_right) hc' χK t⟩,
          fun h => World.mem_of_provable (hmpre _ h)
            ⟨TCanon.optT_named hs.1 hO hfree (hs.decl le_sup_right) hc' χK t⟩⟩
    _ ↔ (⟨i, .optx hO .ident y ⟨_, hyT⟩ χ⟩ : w.L.sys.Sentence σ) ∈ w.T :=
        (World.mem_lift (w := w) (φ := .optx hO .ident y ⟨_, hyT⟩ χ) hK).symm

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.WeakTO] in
/-- ⭐Under T with `Opt`, at the self arrow the `◇_x` view's witnesses are the identity witnesses
    of `x`'s identity view: the collapse onto it respects witnesses. -/
theorem collapseOpt_diaIn_optInT_self {M : Model σ} (hT : ModalSys.T = true)
    {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W} (env : M.Env Γ w) (hop : env.OpenedT) {x : VarSymb}
    {X : VarType} (hr : Γ.ref x = some (.VTypeDia X))
    (hm : M.frame.reflAcc hT w ∈ (M.posEval (env.ref x hr)).1)
    (hd : (env.witT x (Ctx.witT_of hT hO hr)).Dom) :
    Model.Env.CollapseOpt (Ctx.collapses_diaIn_optInT hT hO Γ hr) 0 (env.diaPush x hr ⟨_, hm⟩)
      (env.optPushT x (Ctx.witT_of hT hO hr) hd) where
  zero y _ hy _ := Model.posPart_congr
    (Model.Env.ref_agree (Model.Env.agree_optPushT env hop _ hd) y (Ctx.boxIn_wit.mp hy).2) _
  succ _ _ _ k' hk := absurd hk.symm (Nat.succ_ne_zero k')
  opened := hop.optPushT _ hd
  slots := Ctx.NoSlots.slots

/-- The truth lemma for atoms. -/
theorem relSat_canonO : ∀ {Γ : Ctx} {n : ℕ} (ρ : Rel σ Γ n) {w : World σ N₀} {i : ℕ × ℕ}
    {e : Γ.Le (w.L.ctx i)} {env : (modelT hO w₀).Env Γ w},
    Model.Env.Agree e env (canonEnvO hO w₀ w i) →
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
        (interp_canonO hO w₀ t hag).trans (rdenO_var_mono e t)
      rw [relSat_canonO ρ hag (Fin.cons (Model.interp env t) args) (Fin.cons t ts)
        (fun k => by cases k using Fin.cases <;> simp [h0, hts]), Spine.ofFn_cons]
      rfl

omit [ModalSys] in
/-- With a witness's content declared, its view sits inside the context. -/
theorem optIn_le_of_declared {Γ : Ctx} {y : VarSymb} {X : VarType} (hy : Γ.wit y = some X)
    (hd : Γ (.step y .dia) = some X) : (Γ.optIn y).Le Γ :=
  Ctx.optIns_le_of (L := [y]) (Ctx.Le.refl Γ) fun z hz Z hZ => by
    rw [List.mem_singleton.mp hz] at hZ ⊢
    rw [hy] at hZ
    cases hZ
    exact hd

/-- ⭐**The truth lemma, below a size bound.** -/
theorem truth_ltO : ∀ (n : ℕ) (w : World σ N₀), DecidesO hO w → StagesNoAt w →
    ∀ (i : ℕ × ℕ)
    (φ : WFF σ (w.L.ctx i) 0), φ.size < n →
    ((modelT hO w₀).sat (canonEnvO hO w₀ w i) φ ↔ (⟨i, φ⟩ : w.L.sys.Sentence σ) ∈ w.T)
  | 0, _, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, w, hdec, hna, i, φ, hφ => by
      cases φ with
      | atom ρ =>
          change Model.relSat (canonEnvO hO w₀ w i) ρ Fin.elim0 ↔ _
          rw [relSat_canonO hO w₀ ρ (Model.Env.Agree.refl' _) Fin.elim0 Fin.elim0
            (fun k => k.elim0)]
          change (⟨i, WFF.mono (Ctx.Le.refl _) (.atom ρ)⟩ : w.L.sys.Sentence σ) ∈ w.T ↔ _
          rw [WFF.mono_refl]
      | eq t s =>
          change Model.interp (canonEnvO hO w₀ w i) t =
            Model.interp (canonEnvO hO w₀ w i) s ↔ _
          rw [interp_canonO hO w₀ t (Model.Env.Agree.refl' _),
            interp_canonO hO w₀ s (Model.Env.Agree.refl' _)]
          change rdenO hO w i (Ctx.Le.refl _) t = rdenO hO w i (Ctx.Le.refl _) s ↔ _
          rw [rdenO_var_cls, rdenO_var_cls, World.cls_eq_iff (le_refl i) (le_refl i)]
          change (⟨i, .eq (Term.mono (w.L.ctx_le (le_refl i)) t)
            (Term.mono (w.L.ctx_le (le_refl i)) s)⟩ : w.L.sys.Sentence σ) ∈ w.T ↔ _
          rw [Term.mono_refl, Term.mono_refl]
      | top => exact ⟨fun _ => w.mcs.top_mem, fun _ => trivial⟩
      | bot => exact ⟨False.elim, fun h => w.mcs.bot_not_mem h⟩
      | and φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change _ ∧ _ ↔ _
          rw [truth_ltO n w hdec hna i φ h₁, truth_ltO n w hdec hna i ψ h₂, w.mcs.and_mem_iff]
      | or φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change _ ∨ _ ↔ _
          rw [truth_ltO n w hdec hna i φ h₁, truth_ltO n w hdec hna i ψ h₂, w.mcs.or_mem_iff]
      | imp φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (_ → _) ↔ _
          rw [truth_ltO n w hdec hna i φ h₁, truth_ltO n w hdec hna i ψ h₂, w.mcs.imp_mem_iff]
      | all A ψ =>
          have hψ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (∀ o : (modelT hO w₀).frame.Dom A w,
            (modelT hO w₀).sat ((canonEnvO hO w₀ w i).extend (.bnd 0) o) ψ) ↔ _
          constructor
          · intro hsat
            by_contra hnot
            obtain ⟨i', hi, a, t, hmem⟩ := w.allW hnot
            have hs₁ := (Model.sat_mono (Model.Env.extend_agree (canonEnvO_le hO w₀ w hi) (.bnd 0)
              (Model.interp (canonEnvO hO w₀ w i') t)) ψ
              (fun _ => canonEnvO_le_wit hO w₀ hdec hi)).mpr (hsat _)
            have hs₂ := (Model.sat_instantiate (canonEnvO hO w₀ w i') (w.noProjLast i')
              Ctx.NoSlots.slots t _
              (fun _ _ => canonEnvO_openedT hO w₀ hna _)).mpr hs₁
            have hs₃ := (truth_ltO n w hdec hna i' _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mp hs₂
            exact (w.mcs.neg_mem_iff.mp hmem) hs₃
          · intro hmem o
            obtain ⟨i', a, t', ht'⟩ := definableO_fromDom hO w₀ A w o
            have hK : i ≤ i ⊔ i' := le_sup_left
            have hK' : i' ≤ i ⊔ i' := le_sup_right
            have ho : Model.interp (canonEnvO hO w₀ w (i ⊔ i')) (w.liftT hK' t') = o :=
              (interp_canonO hO w₀ _ (Model.Env.Agree.refl' _)).trans
                ((toDomO_congr hO w₀ ((rdenO_mono _ t' w _ _).trans
                  ((rdenO_congr t' w _ i' _ _).trans ht')) _ _).trans
                  (toDomO_fromDomO hO w₀ A w o))
            have hinst : (⟨i ⊔ i', WFF.instantiate Ctx.NoSlots.slots (w.liftT hK' t')
                (WFF.mono ((w.L.ctx_le hK).insert (.bnd 0) A) ψ)⟩ : w.L.sys.Sentence σ) ∈ w.T :=
              World.mem_of_provable
                (Δ := [WFF.all A (WFF.mono ((w.L.ctx_le hK).insert (.bnd 0) A) ψ)])
                (fun χ hχ => by
                  rw [List.mem_singleton.mp hχ]
                  exact (World.mem_lift hK).mp hmem)
                ⟨Proof.all_elim A (w.liftT hK' t') (Proof.lookup List.mem_cons_self)⟩
            have hs := (truth_ltO n w hdec hna (i ⊔ i') _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mpr hinst
            have hs₁ := (Model.sat_instantiate (canonEnvO hO w₀ w (i ⊔ i')) (w.noProjLast _)
              Ctx.NoSlots.slots (w.liftT hK' t') _
              (fun _ _ => canonEnvO_openedT hO w₀ hna _)).mp hs
            rw [ho] at hs₁
            exact (Model.sat_mono (Model.Env.extend_agree (canonEnvO_le hO w₀ w hK) (.bnd 0) o)
              ψ (fun _ => canonEnvO_le_wit hO w₀ hdec hK)).mp hs₁
      | ex A ψ =>
          have hψ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (∃ o : (modelT hO w₀).frame.Dom A w,
            (modelT hO w₀).sat ((canonEnvO hO w₀ w i).extend (.bnd 0) o) ψ) ↔ _
          constructor
          · rintro ⟨o, hsat⟩
            obtain ⟨i', a, t', ht'⟩ := definableO_fromDom hO w₀ A w o
            have hK : i ≤ i ⊔ i' := le_sup_left
            have hK' : i' ≤ i ⊔ i' := le_sup_right
            have ho : Model.interp (canonEnvO hO w₀ w (i ⊔ i')) (w.liftT hK' t') = o :=
              (interp_canonO hO w₀ _ (Model.Env.Agree.refl' _)).trans
                ((toDomO_congr hO w₀ ((rdenO_mono _ t' w _ _).trans
                  ((rdenO_congr t' w _ i' _ _).trans ht')) _ _).trans
                  (toDomO_fromDomO hO w₀ A w o))
            have hs₁ := (Model.sat_mono (Model.Env.extend_agree (canonEnvO_le hO w₀ w hK) (.bnd 0)
              o) ψ (fun _ => canonEnvO_le_wit hO w₀ hdec hK)).mpr hsat
            rw [← ho] at hs₁
            have hs₂ := (Model.sat_instantiate (canonEnvO hO w₀ w (i ⊔ i')) (w.noProjLast _)
              Ctx.NoSlots.slots (w.liftT hK' t') _
              (fun _ _ => canonEnvO_openedT hO w₀ hna _)).mpr hs₁
            have hmemK := (truth_ltO n w hdec hna (i ⊔ i') _
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
            refine ⟨Model.interp (canonEnvO hO w₀ w i') t, ?_⟩
            have hs := (truth_ltO n w hdec hna i' _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mpr hmem'
            have hs₁ := (Model.sat_instantiate (canonEnvO hO w₀ w i') (w.noProjLast i')
              Ctx.NoSlots.slots t _
              (fun _ _ => canonEnvO_openedT hO w₀ hna _)).mp hs
            exact (Model.sat_mono (Model.Env.extend_agree (canonEnvO_le hO w₀ w hi) (.bnd 0) _)
              ψ (fun _ => canonEnvO_le_wit hO w₀ hdec hi)).mp hs₁
      | box χ =>
          have hχs : χ.size < n := by simp only [WFF.size] at hφ; omega
          change (∀ a : (modelT hO w₀).frame.Acc w,
            (modelT hO w₀).sat ((canonEnvO hO w₀ w i).boxPush a) χ) ↔ _
          have key : ∀ (a : SuccO hO w) (ha : AccO hO w a.1), StagesNoAt a.1 →
              ((modelT hO w₀).sat ((canonEnvO hO w₀ w i).boxPush a) χ ↔
                (⟨childStage i, WFF.mono (ha.boxIn_le i) χ⟩ :
                  a.1.L.sys.Sentence σ) ∈ a.1.T) :=
            fun a ha hn => (Model.sat_mono (boxPush_agree_canonO hO w₀ w i a ha) χ
              (fun _ => boxPush_witAgree_canonO hO w₀ w i a ha)).symm.trans
              (truth_ltO n a.1 ha.decides hn (childStage i) _
                (by rw [WFF.size_mono]; exact hχs))
          constructor
          · intro hsat
            by_contra hnot
            obtain ⟨w', ha, hn, hw'⟩ := exists_box_failT hO w χ hnot
            exact hw' ((key (SuccO.child ha hn) ha (hn hna)).mp (hsat (SuccO.child ha hn)))
          · intro hmem a
            by_cases hd : a.1.depth - w.depth = 0
            · obtain ⟨w₁, h₁⟩ := a
              obtain ⟨hT, hw⟩ := SuccO.self (hO := hO) ⟨w₁, h₁⟩ hd
              change w₁ = w at hw
              subst hw
              refine (Model.sat_collapse Ctx.NoSlots.slots (Model.Env.collapseAgree_self hT _) χ
                (fun _ => Model.Env.collapseOpt_self hT _ (canonEnvO_openedT hO w₀ hna i)
                  Ctx.NoSlots.slots)).mp ?_
              refine (truth_ltO n w₁ hdec hna i _ (by rw [WFF.size_collapse]; exact hχs)).mpr ?_
              exact World.mem_of_provable (Δ := [_])
                (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hmem)
                ⟨Proof.T_box hT (Proof.lookup List.mem_cons_self)⟩
            · exact (key a (SuccO.acc (hO := hO) a hd) (SuccO.noAt (hO := hO) a hd hna)).mpr
                ((SuccO.acc (hO := hO) a hd).box i χ (childStage i) _ hmem)
      | dia x hx χ =>
          have hχs : χ.size < n := by simp only [WFF.size] at hφ; omega
          change (∃ (X : VarType) (h : (w.L.ctx i).ref x = some (.VTypeDia X))
            (a : ((modelT hO w₀).posEval ((canonEnvO hO w₀ w i).ref x h)).1),
              (modelT hO w₀).sat ((canonEnvO hO w₀ w i).diaPush x h a) χ) ↔ _
          constructor
          · rintro ⟨X, h, a, hsat⟩
            have hm : a.1 ∈ extentO w x := by
              rw [← canonEnvO_extent hO w₀ w i h]
              exact a.2
            by_contra hnot
            -- `□¬◇⁰_x χ`, by the bridge
            have hwit : (w.L.ctx i).boxIn.wit x = some X := Ctx.boxIn_wit.mpr ⟨hO, h⟩
            have hnd : (⟨i, WFF.diaOpt hO x hx χ⟩ : w.L.sys.Sentence σ) ∉ w.T := fun hd =>
              hnot (World.mem_of_provable (Δ := [_])
                (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hd)
                ⟨Proof.opt_dia hO x hx (Proof.lookup List.mem_cons_self)⟩)
            have hbox : (⟨i, .box (WFF.optx hO .arrow x ⟨X, hwit⟩
                (WFF.mono (Ctx.le_diaIn_boxIn_optIn hO h) χ)).neg⟩ :
                w.L.sys.Sentence σ) ∈ w.T := by
              by_contra hb
              exact hnd (w.mcs.neg_mem_iff.mpr hb)
            by_cases hd : a.1.1.depth - w.depth = 0
            · -- the self member: `¬ diaId χ`, against `identCase` at the collapsed body
              obtain ⟨⟨w₁, h₁⟩, ha⟩ := a
              obtain ⟨he, hs⟩ := extentO_self hm hd
              change w₁ = w at he
              subst he
              have hT := hs.1
              have hxT := Ctx.witT_of hT hO h
              have hcol := World.mem_of_provable (w := w₁) (Δ := [_])
                (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hbox)
                ⟨Proof.T_box hT (Proof.lookup List.mem_cons_self)⟩
              have hfold := WFF.collapse_fold hT hO x hx χ
              change (⟨i, (WFF.collapse (Ctx.collapses_boxIn_self hT _) Ctx.NoSlots.slots
                (WFF.optx hO .arrow x (hx.imp fun _ h => Ctx.boxIn_wit.mpr ⟨hO, h⟩)
                  (WFF.mono (hx.elim fun _ h => Ctx.le_diaIn_boxIn_optIn hO h) χ))).neg⟩ :
                w₁.L.sys.Sentence σ) ∈ w₁.T at hcol
              rw [hfold] at hcol
              have hdT : ((canonEnvO hO w₀ w₁ i).witT x hxT).Dom := ha
              have hid := identCase hO w₀ n hna (fun i' φ hφ' => truth_ltO n w₁ hdec hna i' φ hφ')
                (fun hij => canonEnvO_le_wit hO w₀ hdec hij) i ⟨X, hxT⟩
                (WFF.collapse (Ctx.collapses_diaIn_optInT hT hO _ h) Ctx.NoSlots.slots χ)
                (by rw [WFF.size_collapse]; exact hχs)
              refine (w₁.mcs.neg_mem_iff.mp hcol) (hid.mp ⟨X, hxT, hdT, ?_⟩)
              exact (Model.sat_collapse Ctx.NoSlots.slots
                (Model.Env.collapseAgree_diaIn_optInT hT hO _ (canonEnvO_openedT hO w₀ hna i) h
                  ha hdT) χ
                (fun _ => collapseOpt_diaIn_optInT_self hO hT _ (canonEnvO_openedT hO w₀ hna i) h
                  ha hdT)).mpr hsat
            · have hc := extentO_child hm hd
              have hχ' := (Model.sat_mono (diaPush_agree_canonO hO w₀ w i h a hm hd) χ
                (fun _ => boxPush_witAgree_canonO hO w₀ w i a.1 hc.1)).mpr hsat
              have hχ'' := (truth_ltO n a.1.1 hc.1.decides (SuccO.noAt (hO := hO) a.1 hd hna)
                (childStage i) _ (by rw [WFF.size_mono]; exact hχs)).mp hχ'
              have hcb := hc.1.box i _ (childStage i) (hc.1.boxIn_le i) hbox
              -- `x` is opened at the member, so `◇⁰_x χ` holds there
              have hM : (w.L.ctx i).boxIn.Le (bview w (max i.1 i.2)) := (le_diag_max w i).boxIn
              have hw' : (a.1.1.L.ctx (childStage i)).wit x = some X :=
                (hc.1.wit _ x).trans (hM.wit x X hwit)
              have hd' : a.1.1.L.ctx (childStage i) (.step x .dia) = some X :=
                hc.1.opened_at hc.2 (hM.wit x X hwit)
              have hre := World.mem_of_provable (Δ := [_])
                (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hχ'')
                ⟨Proof.opt_reopen hO .arrow x ⟨X, hw', hd'⟩ (Proof.lookup List.mem_cons_self)⟩
              refine (a.1.1.mcs.neg_mem_iff.mp hcb) ?_
              change (⟨childStage i, WFF.optx hO .arrow x _ (WFF.mono _ (WFF.mono _ χ))⟩ :
                a.1.1.L.sys.Sentence σ) ∈ a.1.1.T
              rw [WFF.mono_mono]
              rw [WFF.mono_mono] at hre
              exact hre
          · intro hmem
            obtain ⟨X, h⟩ := hx
            obtain ⟨a, ha, ho, hn, hmem'⟩ := exists_diaO hO w ⟨X, h⟩ χ hmem
            have hm : SuccO.child (hO := hO) ha hn ∈ extentO w x := Or.inl ⟨ha, ho⟩
            have hm' : SuccO.child (hO := hO) ha hn ∈
                ((modelT hO w₀).posEval ((canonEnvO hO w₀ w i).ref x h)).1 := by
              rw [canonEnvO_extent]
              exact hm
            refine ⟨X, h, ⟨_, hm'⟩, ?_⟩
            have hd : (SuccO.child (hO := hO) ha hn).1.depth - w.depth ≠ 0 := ha.depth_ne
            exact (Model.sat_mono (diaPush_agree_canonO hO w₀ w i h ⟨_, hm'⟩ hm hd) χ
              (fun _ => boxPush_witAgree_canonO hO w₀ w i _ ha)).mp
              ((truth_ltO n a ha.decides (hn hna) (childStage i) _
                (by rw [WFF.size_mono]; exact hχs)).mpr hmem')
      | optx hO' k y hy χ =>
          have hχs : χ.size < n := by simp only [WFF.size] at hφ; omega
          cases k
          case ident =>
            exact identCase hO w₀ n hna (fun i' φ hφ' => truth_ltO n w hdec hna i' φ hφ')
              (fun hij => canonEnvO_le_wit hO w₀ hdec hij) i hy χ hχs
          change (∃ (X : VarType) (h : (w.L.ctx i).wit y = some X)
            (hd : ((canonEnvO hO w₀ w i).wit y X h).Dom),
              (modelT hO w₀).sat ((canonEnvO hO w₀ w i).optPush y h hd) χ) ↔ _
          -- where the content is declared, the view is the stage itself
          have key : ∀ {X : VarType} (h : (w.L.ctx i).wit y = some X)
              (hd : w.L.ctx i (.step y .dia) = some X),
              ((modelT hO w₀).sat ((canonEnvO hO w₀ w i).optPush y h hd) χ ↔
                (⟨i, WFF.mono (optIn_le_of_declared h hd) χ⟩ : w.L.sys.Sentence σ) ∈ w.T) ∧
              ((⟨i, WFF.optx hO' .arrow y hy χ⟩ : w.L.sys.Sentence σ) ∈ w.T ↔
                (⟨i, WFF.mono (optIn_le_of_declared h hd) χ⟩ : w.L.sys.Sentence σ) ∈ w.T) := by
            intro X h hd
            have hle := optIn_le_of_declared h hd
            have hag : Model.Env.Agree hle ((canonEnvO hO w₀ w i).optPush y h hd)
                (canonEnvO hO w₀ w i) := by
              intro v T hv
              by_cases hvy : v = .step y .dia
              · subst hvy
                have hXT : X = T := by
                  rw [Ctx.optIn_content h] at hv
                  exact Option.some.inj hv
                subst hXT
                change (if hv' : VarSymb.step y .dia = .step y .dia then _ else _) = _
                rw [dif_pos rfl]
                rfl
              · change (if hv' : v = .step y .dia then _ else _) = _
                rw [dif_neg hvy]
            refine ⟨(Model.sat_mono hag χ (fun _ _ _ _ => rfl)).symm.trans
              (truth_ltO n w hdec hna i _ (by rw [WFF.size_mono]; exact hχs)), ?_⟩
            have hform :
                WFF.optx hO .arrow y ⟨X, h⟩ (WFF.mono (Ctx.le_optIn _ y) (WFF.mono hle χ)) =
                WFF.optx hO' .arrow y hy χ := by
              rw [WFF.mono_mono, WFF.mono_refl]
            constructor
            · intro hm
              refine World.mem_of_provable (Δ := [_])
                (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hm)
                ⟨Proof.opt_out hO .arrow y ⟨X, h⟩ (Proof.lookup ?_)⟩
              rw [hform]
              exact List.mem_cons_self
            · intro hm
              have hre := World.mem_of_provable (Δ := [_])
                (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hm)
                ⟨Proof.opt_reopen hO .arrow y ⟨X, h, hd⟩ (Proof.lookup List.mem_cons_self)⟩
              rw [hform] at hre
              exact hre
          constructor
          · rintro ⟨X, h, hd, hsat⟩
            exact ((key h hd).2).mpr (((key h hd).1).mp hsat)
          · intro hmem
            obtain ⟨X, h⟩ := hy
            -- the theory decides `y`; `◇⁰_y χ` rules out its absence
            have hdecl : w.L.ctx i (.step y .dia) = some X := by
              have hb : (w.L.base i.1).wit y = some X := (ctx_wit w i y).symm.trans h
              rcases hdec i.1 y X hb with hd | hneg
              · rw [ctx_step (s := .dia) _ _ _ nofun]
                exact hd
              · exfalso
                have hneg' := (World.mem_lift (w := w)
                  (show ((i.1, 0) : ℕ × ℕ) ≤ i from ⟨le_rfl, Nat.zero_le _⟩)).mp hneg
                refine w.mcs.bot_not_mem (i := i) (World.mem_of_provable (Δ := [_, _])
                  (fun ψ hψ => ?_) ⟨.imp_elim (Proof.lookup List.mem_cons_self)
                    (Proof.weak _ (Proof.K_opt hO .arrow y ⟨X, h⟩ (Δ₁ := []) (Δ₂ := []) (φ := .top)
                      (ψ := χ) .top_intro))⟩)
                rcases List.mem_cons.mp hψ with rfl | hψ
                · exact hneg'
                · rw [List.mem_singleton.mp hψ]
                  exact hmem
            exact ⟨X, h, hdecl, ((key h hdecl).1).mpr (((key h hdecl).2).mp hmem)⟩
      | here _ _ _ hO'' => exact (ModalSys.opt_absurd hO hO'').elim
      | back hB _ _ _ => exact (ModalSys.opt_absurd hO (ModalSys.noOpt_of_BStrong hB)).elim
      | retS hB _ _ _ => exact (ModalSys.opt_absurd hO (ModalSys.noOpt_of_BStrong hB)).elim
      | retxS hB _ _ _ _ _ => exact (ModalSys.opt_absurd hO (ModalSys.noOpt_of_BStrong hB)).elim
      | link hV _ _ _ => exact (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Five hV)).elim
      | linkx hV _ _ _ _ _ => exact (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Five hV)).elim


/-- ⭐**The truth lemma** with `Opt` on, T included, at a world deciding its witnesses and
    declaring no identity reading. -/
theorem truth {w : World σ N₀} (hdec : DecidesO hO w) (hna : StagesNoAt w) (i : ℕ × ℕ)
    (φ : WFF σ (w.L.ctx i) 0) :
    (modelT hO w₀).sat (canonEnvO hO w₀ w i) φ ↔ (⟨i, φ⟩ : w.L.sys.Sentence σ) ∈ w.T :=
  truth_ltO hO w₀ (φ.size + 1) w hdec hna i φ (Nat.lt_succ_self _)

end OCanon

end V12M
