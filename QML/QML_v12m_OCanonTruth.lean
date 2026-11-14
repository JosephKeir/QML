import QML.QML_v12m_OCanonTerm
import QML.QML_v12m_Completeness

/-!
# QML v12m — the canonical tree with `Opt` on: the truth lemma

⭐`OCanon.truth`: at a world that decides its witnesses (`DecidesO`; every child does), a formula
holds in the canonical environment exactly when it is in the theory.  The new cases:

* `□`: the children are exactly the arrows; a non-necessary formula fails at a child
  (`exists_box_failO`).
* `◇_x`: into a member of `x`'s extent.  One way is `exists_diaO`.  The other goes through the
  bridge: were `◇_x χ` missing, `□¬◇⁰_x χ` would be in the theory, so the member would have
  `¬◇⁰_x χ`, which reopening `x` there refutes.
* `◇⁰_y`: a witness is present in the canonical environment exactly when its content is declared;
  the world decides it, so where it is not declared the theory says `¬◇⁰_y ⊤`.  Where it is,
  `◇⁰_y χ` is `χ` read in the stage itself (`Proof.opt_reopen`, `Proof.opt_out`).
-/

namespace V12M

/- M1's construction is for K and D with `Opt` on: T off (`ModalSys.NoT`) until M2 step 6
   generalises it, so the class is in scope throughout. -/
set_option linter.unusedSectionVars false

variable [ModalSys] [ModalSys.NoT]

namespace OCanon

open Canon

variable {σ : Signature} {N₀ : ℕ}

variable (hO : ModalSys.Opt = true) [Countable σ.FuncSyms] [Countable σ.RelSyms]
  (w₀ : World σ N₀)

/-- The truth lemma for atoms. -/
theorem relSat_canonO : ∀ {Γ : Ctx} {n : ℕ} (ρ : Rel σ Γ n) {w : World σ N₀} {i : ℕ × ℕ}
    {e : Γ.Le (w.L.ctx i)} {env : (model hO w₀).Env Γ w},
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
theorem truth_ltO : ∀ (n : ℕ) (w : World σ N₀), DecidesO hO w → ∀ (i : ℕ × ℕ)
    (φ : WFF σ (w.L.ctx i) 0), φ.size < n →
    ((model hO w₀).sat (canonEnvO hO w₀ w i) φ ↔ (⟨i, φ⟩ : w.L.sys.Sentence σ) ∈ w.T)
  | 0, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, w, hdec, i, φ, hφ => by
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
          rw [truth_ltO n w hdec i φ h₁, truth_ltO n w hdec i ψ h₂, w.mcs.and_mem_iff]
      | or φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change _ ∨ _ ↔ _
          rw [truth_ltO n w hdec i φ h₁, truth_ltO n w hdec i ψ h₂, w.mcs.or_mem_iff]
      | imp φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (_ → _) ↔ _
          rw [truth_ltO n w hdec i φ h₁, truth_ltO n w hdec i ψ h₂, w.mcs.imp_mem_iff]
      | all A ψ =>
          have hψ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (∀ o : (model hO w₀).frame.Dom A w,
            (model hO w₀).sat ((canonEnvO hO w₀ w i).extend (.bnd 0) o) ψ) ↔ _
          constructor
          · intro hsat
            by_contra hnot
            obtain ⟨i', hi, a, t, hmem⟩ := w.allW hnot
            have hs₁ := (Model.sat_mono (Model.Env.extend_agree (canonEnvO_le hO w₀ w hi) (.bnd 0)
              (Model.interp (canonEnvO hO w₀ w i') t)) ψ
              (fun _ => canonEnvO_le_wit hO w₀ hdec hi)).mpr (hsat _)
            have hs₂ := (Model.sat_instantiate (canonEnvO hO w₀ w i') (w.noProjLast i')
              Ctx.NoSlots.slots t _).mpr hs₁
            have hs₃ := (truth_ltO n w hdec i' _
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
            have hs := (truth_ltO n w hdec (i ⊔ i') _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mpr hinst
            have hs₁ := (Model.sat_instantiate (canonEnvO hO w₀ w (i ⊔ i')) (w.noProjLast _)
              Ctx.NoSlots.slots (w.liftT hK' t') _).mp hs
            rw [ho] at hs₁
            exact (Model.sat_mono (Model.Env.extend_agree (canonEnvO_le hO w₀ w hK) (.bnd 0) o)
              ψ (fun _ => canonEnvO_le_wit hO w₀ hdec hK)).mp hs₁
      | ex A ψ =>
          have hψ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (∃ o : (model hO w₀).frame.Dom A w,
            (model hO w₀).sat ((canonEnvO hO w₀ w i).extend (.bnd 0) o) ψ) ↔ _
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
              Ctx.NoSlots.slots (w.liftT hK' t') _).mpr hs₁
            have hmemK := (truth_ltO n w hdec (i ⊔ i') _
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
            have hs := (truth_ltO n w hdec i' _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mpr hmem'
            have hs₁ := (Model.sat_instantiate (canonEnvO hO w₀ w i') (w.noProjLast i')
              Ctx.NoSlots.slots t _).mp hs
            exact (Model.sat_mono (Model.Env.extend_agree (canonEnvO_le hO w₀ w hi) (.bnd 0) _)
              ψ (fun _ => canonEnvO_le_wit hO w₀ hdec hi)).mp hs₁
      | box χ =>
          have hχs : χ.size < n := by simp only [WFF.size] at hφ; omega
          change (∀ a : (model hO w₀).frame.Acc w,
            (model hO w₀).sat ((canonEnvO hO w₀ w i).boxPush a) χ) ↔ _
          have key : ∀ a : SuccO hO w,
              (model hO w₀).sat ((canonEnvO hO w₀ w i).boxPush a) χ ↔
                (⟨childStage i, WFF.mono (a.2.down.boxIn_le i) χ⟩ :
                  a.1.L.sys.Sentence σ) ∈ a.1.T :=
            fun a => (Model.sat_mono (boxPush_agree_canonO hO w₀ w i a) χ
              (fun _ => boxPush_witAgree_canonO hO w₀ w i a)).symm.trans
              (truth_ltO n a.1 a.2.down.decides (childStage i) _
                (by rw [WFF.size_mono]; exact hχs))
          constructor
          · intro hsat
            by_contra hnot
            obtain ⟨w', ha, hw'⟩ := exists_box_failO hO w χ hnot
            exact hw' ((key ⟨w', ⟨ha⟩⟩).mp (hsat ⟨w', ⟨ha⟩⟩))
          · intro hmem a
            exact (key a).mpr (a.2.down.box i χ (childStage i) _ hmem)
      | dia x hx χ =>
          have hχs : χ.size < n := by simp only [WFF.size] at hφ; omega
          change (∃ (X : VarType) (h : (w.L.ctx i).ref x = some (.VTypeDia X))
            (a : ((model hO w₀).posEval ((canonEnvO hO w₀ w i).ref x h)).1),
              (model hO w₀).sat ((canonEnvO hO w₀ w i).diaPush x h a) χ) ↔ _
          have key : ∀ {X : VarType} (h : (w.L.ctx i).ref x = some (.VTypeDia X))
              (a : ((model hO w₀).posEval ((canonEnvO hO w₀ w i).ref x h)).1),
              (model hO w₀).sat ((canonEnvO hO w₀ w i).diaPush x h a) χ ↔
                (⟨childStage i, WFF.mono (extentO_le (canonEnvO_extent hO w₀ w i h ▸ a.2)
                  (Ctx.Le.refl _) ⟨X, h⟩) χ⟩ : a.1.1.L.sys.Sentence σ) ∈ a.1.1.T :=
            fun h a => (Model.sat_mono (diaPush_agree_canonO hO w₀ w i h a) χ
              (fun _ => boxPush_witAgree_canonO hO w₀ w i a.1)).symm.trans
              (truth_ltO n a.1.1 a.1.2.down.decides (childStage i) _
                (by rw [WFF.size_mono]; exact hχs))
          constructor
          · rintro ⟨X, h, a, hsat⟩
            have hm : a.1 ∈ extentO w x := canonEnvO_extent hO w₀ w i h ▸ a.2
            have hχ' := (key h a).mp hsat
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
            have hc := a.1.2.down.box i _ (childStage i) (a.1.2.down.boxIn_le i) hbox
            -- `x` is opened at the member, so `◇⁰_x χ` holds there
            have hM : (w.L.ctx i).boxIn.Le (bview w (max i.1 i.2)) := (le_diag_max w i).boxIn
            have hw' : (a.1.1.L.ctx (childStage i)).wit x = some X :=
              (a.1.2.down.wit _ x).trans (hM.wit x X hwit)
            have hd' : a.1.1.L.ctx (childStage i) (.step x .dia) = some X :=
              a.1.2.down.opened_at hm (hM.wit x X hwit)
            have hre := World.mem_of_provable (Δ := [_])
              (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hχ')
              ⟨Proof.opt_reopen hO .arrow x ⟨X, hw', hd'⟩ (Proof.lookup List.mem_cons_self)⟩
            refine (a.1.1.mcs.neg_mem_iff.mp hc) ?_
            change (⟨childStage i, WFF.optx hO .arrow x _ (WFF.mono _ (WFF.mono _ χ))⟩ :
              a.1.1.L.sys.Sentence σ) ∈ a.1.1.T
            rw [WFF.mono_mono]
            rw [WFF.mono_mono] at hre
            exact hre
          · intro hmem
            obtain ⟨X, h⟩ := hx
            obtain ⟨a, ha, hmem'⟩ := exists_diaO hO w ⟨X, h⟩ χ hmem
            exact ⟨X, h, ⟨a, (canonEnvO_extent hO w₀ w i h).symm ▸ ha⟩, (key h _).mpr hmem'⟩
      | optx hO' k y hy χ =>
          obtain rfl : k = .arrow := by
            cases k <;> first | rfl | exact (hy.elim fun _ h => ModalSys.NoT.absurd (Ctx.witT_spec
                h).1).elim
          have hχs : χ.size < n := by simp only [WFF.size] at hφ; omega
          change (∃ (X : VarType) (h : (w.L.ctx i).wit y = some X)
            (hd : ((canonEnvO hO w₀ w i).wit y X h).Dom),
              (model hO w₀).sat ((canonEnvO hO w₀ w i).optPush y h hd) χ) ↔ _
          -- where the content is declared, the view is the stage itself
          have key : ∀ {X : VarType} (h : (w.L.ctx i).wit y = some X)
              (hd : w.L.ctx i (.step y .dia) = some X),
              ((model hO w₀).sat ((canonEnvO hO w₀ w i).optPush y h hd) χ ↔
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
              (truth_ltO n w hdec i _ (by rw [WFF.size_mono]; exact hχs)), ?_⟩
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
      | here hT _ _ _ => exact (ModalSys.NoT.absurd hT).elim
      | back hB _ _ _ => exact (ModalSys.opt_absurd hO (ModalSys.noOpt_of_BStrong hB)).elim
      | retS hB _ _ _ => exact (ModalSys.opt_absurd hO (ModalSys.noOpt_of_BStrong hB)).elim
      | retxS hB _ _ _ _ _ => exact (ModalSys.opt_absurd hO (ModalSys.noOpt_of_BStrong hB)).elim
      | link hV _ _ _ => exact (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Five hV)).elim
      | linkx hV _ _ _ _ _ => exact (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Five hV)).elim

/-- ⭐**The truth lemma** with `Opt` on, at a world deciding its witnesses. -/
theorem truth {w : World σ N₀} (hdec : DecidesO hO w) (i : ℕ × ℕ) (φ : WFF σ (w.L.ctx i) 0) :
    (model hO w₀).sat (canonEnvO hO w₀ w i) φ ↔ (⟨i, φ⟩ : w.L.sys.Sentence σ) ∈ w.T :=
  truth_ltO hO w₀ (φ.size + 1) w hdec i φ (Nat.lt_succ_self _)

/-- ⭐The canonical model with `Opt` on is a model proper: its `Ind` is equality. -/
theorem indInvariant : (model hO w₀).IndInvariant :=
  Model.indInvariant_of_eq (fun _ _ h => h)
    fun hS => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_BStrong hS)).elim

end OCanon

end V12M
