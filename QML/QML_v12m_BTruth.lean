import QML.QML_v12m_BHere
import QML.QML_v12m_Completeness

/-!
# QML v12m — B's canonical model: the truth lemma

⭐`BData.truth`: at every world and stage, the canonical environment satisfies exactly the formulas
of the world's theory.  By induction on the size of the formula, which substitution does not
change.  Atoms and equations by the truth lemma for terms, the connectives by maximality, the
quantifiers by definability and the Henkin witnesses (`BWorld.exW`, `BWorld.allW`).  The modal
steps are where the arrows do their work: pushing the canonical environment along an arrow is
the target's canonical environment read through the arrow (`boxPush_canon`, `diaPush_canon`), so by
`Model.sat_subst` the view satisfies `χ` exactly when the target's theory contains `χ` translated
along the arrow — which transfer (`tr`, `trX`) and existence (`ex`, `exX`) settle.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

namespace BData

variable [ModalSys.NoFour] {B : BData σ}

/-- The truth lemma for atoms. -/
theorem relSat_canon : ∀ {Γ : Ctx} {n : ℕ} (ρ : Rel σ Γ n) {s : B.W} {i : ℕ}
    {e : Γ.Le ((B.w s).ctx i)} {env : B.model.Env Γ s},
    Model.Env.Agree e env (B.canonEnv s i) →
    ∀ (args : Fin n → (B.w s).D) (ts : Fin n → Term σ Γ .Var .var),
      (∀ k, args k = (B.w s).cls i (Term.mono e (ts k))) →
      (Model.relSat env ρ args ↔
        WFF.mono e (.atom ((Spine.ofFn ts).fillR ρ)) ∈ (B.w s).M i)
  | _, _, .R ⟨r, rfl⟩, s, i, e, _, _, args, ts, hts => by
      change (B.w s).canonRel r (fun k => args (Fin.cast rfl k)) ↔ _
      rw [WFF.mono_fillR, Spine.mono_ofFn,
        show (fun k => args (Fin.cast rfl k)) = fun k => (B.w s).cls i (Term.mono e (ts k)) from
          funext fun k => hts k,
        BWorld.canonRel_cls]
      rfl
  | _, _, .eval ρ t, s, i, e, env, hag, args, ts, hts => by
      change Model.relSat env ρ (Fin.cons (Model.interp env t) args) ↔ _
      have h0 : Model.interp env t = (B.w s).cls i (Term.mono e t) :=
        (interp_canon t hag).trans (rden_var_mono e t)
      rw [relSat_canon ρ hag (Fin.cons (Model.interp env t) args) (Fin.cons t ts)
        (fun k => by cases k using Fin.cases <;> simp [h0, hts]), Spine.ofFn_cons]
      rfl

/-- A denotable object is the value of a term at a later stage. -/
theorem interp_lift {A : VarType} {s : B.W} {i i' : ℕ} {a : Ann A}
    {t' : Term σ ((B.w s).ctx i') A a} {o : B.model.frame.Dom A s}
    (ht' : B.rden s i' (Ctx.Le.refl _) t' = B.fromDom A s o) (hK : i' ≤ i) :
    Model.interp (B.canonEnv s i) ((B.w s).liftT hK t') = o :=
  (interp_canon _ (Model.Env.Agree.refl' _)).trans
    ((toDom_congr ((rden_mono _ t' s _ _).trans ((rden_congr t' s _ i' _ _).trans ht')) _
      _).trans (B.toDom_fromDom A s o))

/-- ⭐The realised case of the truth lemma's `◇` step, along a world's own arrow, as in the tree
    (`Canon.dia_mem_of_sat_self`): a formula holding in the witness's view there holds of the
    realising term (`Model.sat_realiseAtA`), and what the theory says about the realising term it
    says about the witness (`RealDatum.spec`).  The induction hypothesis is needed only at formulas
    of the same logical size (`WFF.size_realiseAtA`). -/
theorem dia_mem_of_sat_self {s : B.W} {i : ℕ} {x : VarSymb} (hr : (B.w s).Realised x)
    {X : VarType} (h : ((B.w s).ctx i).ref x = some (.VTypeDia X))
    (hx : ∃ Y, ((B.w s).ctx i).ref x = some (.VTypeDia Y))
    (χ : WFF σ (((B.w s).ctx i).diaIn x) 0)
    (IH : ∀ ψ : WFF σ ((B.w s).ctx (max i hr.data.i₀)) 0, ψ.size = χ.size →
      (B.model.sat (B.canonEnv s (max i hr.data.i₀)) ψ ↔ ψ ∈ (B.w s).M (max i hr.data.i₀)))
    (hmem : B.model.frame.reflAcc hr.T s ∈ (B.model.posEval ((B.canonEnv s i).ref x h)).1)
    (hsat : B.model.sat ((B.canonEnv s i).diaPush x h ⟨B.model.frame.reflAcc hr.T s, hmem⟩) χ) :
    WFF.dia x hx χ ∈ (B.w s).M i := by
  have hXA : X = hr.data.A := by
    have h1 := (hr.data.hdeclOf i ⟨X, h⟩).symm.trans h
    simp only [Option.some.injEq, VarType.VTypeDia.injEq] at h1
    exact h1.symm
  subst hXA
  set K := max i hr.data.i₀
  have hj : i ≤ K := le_max_left _ _
  have hdecl : ((B.w s).ctx K).ref x = some (.VTypeDia hr.data.A) :=
    hr.data.hdeclOf K ⟨_, ((B.w s).le hj).ref h⟩
  have hagj : Model.Env.Agree ((B.w s).le hj) (B.canonEnv s i) (B.canonEnv s K) :=
    canonEnv_le s hj
  have hm' : B.model.frame.reflAcc hr.T s ∈
      (B.model.posEval ((B.canonEnv s K).ref x hdecl)).1 := by
    rw [canonEnv_extent]
    exact Or.inr ⟨B.irrefl s, hr⟩
  have hcont : (B.model.posEval ((B.canonEnv s K).ref x hdecl)).2
        ⟨B.model.frame.reflAcc hr.T s, hm'⟩ =
      Model.interp (B.canonEnv s K)
        (Term.mono ((B.w s).le (le_max_right _ _ : hr.data.i₀ ≤ K)) hr.data.t₀) := by
    have hpq := canonEnv_ref s K x hdecl
    rw [Model.posEval_snd_congr hpq ⟨B.model.frame.reflAcc hr.T s, hm'⟩ (hpq ▸ hm'),
      Model.interp_mono (canonEnv_le s (le_max_right _ _ : hr.data.i₀ ≤ K)) hr.data.t₀,
      interp_canon_eta s hr.data.i₀ hr.data.b₀ hr.data.hb₀]
    exact toDom_congr (rden_eta_real hr hdecl _) _ _
  have hsatR := (Model.sat_realiseAtA hr.T (B.canonEnv s K) (noProjLast s K) hdecl
    (Term.mono ((B.w s).le (le_max_right _ _)) hr.data.t₀) hm' hcont
    (WFF.mono (((B.w s).le hj).diaIn x) χ)).mpr
    ((Model.sat_mono (Model.Env.diaPush_agree hagj h
      ⟨B.model.frame.reflAcc hr.T s, hmem⟩ hm') χ).mpr hsat)
  have hdia := hr.data.spec (B.w s).mcsT K (le_max_right _ _) hdecl _
    ((IH _ (by rw [WFF.size_realiseAtA, WFF.size_mono])).mp hsatR)
  have hmem' := (BWorld.mem_mono_congr (w := B.w s) (Ctx.Le.refl _) ((B.w s).le hj)
    (φ := WFF.dia x hx χ)).mpr hdia
  rwa [WFF.mono_refl] at hmem'

/-- ⭐**A `Back` atom of the theory is true** (strong B): the canonical `Ret` is read off the
    atoms, so the atom is its own witness. -/
theorem sat_back_of_mem (hB : ModalSys.BStrong = true) {s : B.W} {i : ℕ} {L : BLeg}
    {A : VarType} {b : Ann (L.carrier A)} {a : Ann A} (c : Term σ ((B.w s).ctx i) (L.carrier A) b)
    (t : Term σ ((B.w s).ctx i) A a) (h : WFF.back hB L c t ∈ (B.w s).M i) :
    B.model.sat (B.canonEnv s i) (WFF.back hB L c t : WFF σ _ 0) := by
  change B.model.Backs L _ _
  rw [backs_iff, interp_canon c (Model.Env.Agree.refl' _),
    interp_canon t (Model.Env.Agree.refl' _)]
  exact Or.inr ⟨hB, i, L, b, c, a, t, h, rfl, rfl⟩

variable (B) in
/-- What the truth lemma's induction step needs at the size of `φ`: the lemma below it. -/
def TruthBelow {s : B.W} {i : ℕ} (φ : WFF σ ((B.w s).ctx i) 0) : Prop :=
  ∀ (s' : B.W) (K : ℕ) (ψ : WFF σ ((B.w s').ctx K) 0), ψ.size < φ.size →
    (B.model.sat (B.canonEnv s' K) ψ ↔ ψ ∈ (B.w s').M K)

variable (B) in
/-- ⭐**The truth lemma's strong B cases** (`Back` and the returning possibilities), given the
    lemma below them.  Abstracted so that the truth lemma stays here; the limit of a strong
    chain has them (`bdataS_strongTruth`). -/
structure StrongTruth (hS : ModalSys.BStrong = true) : Prop where
  back : ∀ {s : B.W} {i : ℕ} {L : BLeg} {A : VarType} {b : Ann (L.carrier A)} {a : Ann A}
    (c : Term σ ((B.w s).ctx i) (L.carrier A) b) (t : Term σ ((B.w s).ctx i) A a),
    B.TruthBelow (WFF.back hS L c t : WFF σ _ 0) →
      (B.model.sat (B.canonEnv s i) (WFF.back hS L c t : WFF σ _ 0) ↔
        (WFF.back hS L c t : WFF σ _ 0) ∈ (B.w s).M i)
  retS : ∀ {s : B.W} {i : ℕ} {S : RShape} {a : Ann S.flat} (t : Term σ ((B.w s).ctx i) S.flat a)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) S.ty) 1),
    B.TruthBelow (WFF.retS hS S t Φ : WFF σ _ 0) →
      (B.model.sat (B.canonEnv s i) (WFF.retS hS S t Φ : WFF σ _ 0) ↔
        (WFF.retS hS S t Φ : WFF σ _ 0) ∈ (B.w s).M i)
  retxS : ∀ {s : B.W} {i : ℕ} {y : VarSymb} (hy : ∃ Y, ((B.w s).ctx i).ref y = some (.VTypeDia Y))
    {S : RShape} {a : Ann S.flat} (t : Term σ ((B.w s).ctx i) S.flat a)
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) S.ty) 1),
    B.TruthBelow (WFF.retxS hS y hy S t Φ : WFF σ _ 0) →
      (B.model.sat (B.canonEnv s i) (WFF.retxS hS y hy S t Φ : WFF σ _ 0) ↔
        (WFF.retxS hS y hy S t Φ : WFF σ _ 0) ∈ (B.w s).M i)

variable (hST : ∀ hS : ModalSys.BStrong = true, B.StrongTruth hS)
include hST

theorem truth_lt :
    ∀ (n : ℕ) (s : B.W) (i : ℕ) (φ : WFF σ ((B.w s).ctx i) 0), φ.size < n →
    (B.model.sat (B.canonEnv s i) φ ↔ φ ∈ (B.w s).M i)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, i, φ, hφ => by
      cases φ with
      | atom ρ =>
          change Model.relSat (B.canonEnv s i) ρ Fin.elim0 ↔ _
          rw [relSat_canon ρ (Model.Env.Agree.refl' _) Fin.elim0 Fin.elim0 (fun k => k.elim0)]
          change WFF.mono (Ctx.Le.refl _) (.atom ρ) ∈ (B.w s).M i ↔ _
          rw [WFF.mono_refl]
      | eq t u =>
          change Model.interp (B.canonEnv s i) t = Model.interp (B.canonEnv s i) u ↔ _
          rw [interp_canon t (Model.Env.Agree.refl' _), interp_canon u (Model.Env.Agree.refl' _)]
          change B.rden s i (Ctx.Le.refl _) t = B.rden s i (Ctx.Le.refl _) u ↔ _
          rw [rden_var_cls, rden_var_cls, BWorld.cls_eq_iff (le_refl i) (le_refl i)]
          change WFF.eq (Term.mono ((B.w s).le (le_refl i)) t)
            (Term.mono ((B.w s).le (le_refl i)) u) ∈ (B.w s).M i ↔ _
          rw [Term.mono_refl, Term.mono_refl]
      | top => exact ⟨fun _ => ((B.w s).mcs i).top_mem, fun _ => trivial⟩
      | bot => exact ⟨False.elim, fun h => ((B.w s).mcs i).bot_not_mem h⟩
      | here hT S t =>
          cases S with
          | diatm x hx bd =>
              exact here_truth hT hx bd t (fun K _ u u' => truth_lt n s K _ (by
                rw [WFF.size_eqRec]; simp only [WFF.size] at hφ; omega))
      | back hB L c t =>
          exact (hST hB).back c t fun s' K ψ h => truth_lt n s' K ψ (by omega)
      | retS hB S t Φ =>
          exact (hST hB).retS t Φ fun s' K ψ h => truth_lt n s' K ψ (by omega)
      | retxS hB y hy S t Φ =>
          exact (hST hB).retxS hy t Φ fun s' K ψ h => truth_lt n s' K ψ (by omega)
      | and φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change _ ∧ _ ↔ _
          rw [truth_lt n s i φ h₁, truth_lt n s i ψ h₂, ((B.w s).mcs i).and_mem_iff]
      | or φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change _ ∨ _ ↔ _
          rw [truth_lt n s i φ h₁, truth_lt n s i ψ h₂, ((B.w s).mcs i).or_mem_iff]
      | imp φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (_ → _) ↔ _
          rw [truth_lt n s i φ h₁, truth_lt n s i ψ h₂, ((B.w s).mcs i).imp_mem_iff]
      | all A ψ =>
          have hψ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (∀ o : B.model.frame.Dom A s,
            B.model.sat ((B.canonEnv s i).extend (.bnd 0) o) ψ) ↔ _
          constructor
          · intro hsat
            by_contra hnot
            obtain ⟨i', hi, a, t, hmem⟩ := (B.w s).allW (((B.w s).mcs i).neg_mem_iff.mpr hnot)
            have hs₁ := (Model.sat_mono (Model.Env.extend_agree (canonEnv_le s hi) (.bnd 0)
              (Model.interp (B.canonEnv s i') t)) ψ).mpr (hsat _)
            have hs₂ := (Model.sat_instantiate (B.canonEnv s i') (noProjLast s i')
              Ctx.NoSlots.slots t _).mpr hs₁
            have hs₃ := (truth_lt n s i' _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mp hs₂
            exact (((B.w s).mcs i').neg_mem_iff.mp hmem) hs₃
          · intro hmem o
            obtain ⟨i', a, t', ht'⟩ := B.definable_fromDom A s o
            have hK : i ≤ i ⊔ i' := le_sup_left
            have hK' : i' ≤ i ⊔ i' := le_sup_right
            have hinst : WFF.instantiate Ctx.NoSlots.slots ((B.w s).liftT hK' t')
                (WFF.mono (((B.w s).le hK).insert (.bnd 0) A) ψ) ∈ (B.w s).M (i ⊔ i') :=
              BWorld.mem_of_provable
                (Δ := [WFF.all A (WFF.mono (((B.w s).le hK).insert (.bnd 0) A) ψ)])
                (fun χ hχ => by
                  rw [List.mem_singleton.mp hχ]
                  exact (BWorld.mem_lift hK).mp hmem)
                ⟨Proof.all_elim A ((B.w s).liftT hK' t') (Proof.lookup List.mem_cons_self)⟩
            have hs := (truth_lt n s (i ⊔ i') _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mpr hinst
            have hs₁ := (Model.sat_instantiate (B.canonEnv s (i ⊔ i')) (noProjLast s _)
              Ctx.NoSlots.slots ((B.w s).liftT hK' t') _).mp hs
            rw [interp_lift ht' hK'] at hs₁
            exact (Model.sat_mono (Model.Env.extend_agree (canonEnv_le s hK) (.bnd 0) o)
              ψ).mp hs₁
      | ex A ψ =>
          have hψ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (∃ o : B.model.frame.Dom A s,
            B.model.sat ((B.canonEnv s i).extend (.bnd 0) o) ψ) ↔ _
          constructor
          · rintro ⟨o, hsat⟩
            obtain ⟨i', a, t', ht'⟩ := B.definable_fromDom A s o
            have hK : i ≤ i ⊔ i' := le_sup_left
            have hK' : i' ≤ i ⊔ i' := le_sup_right
            have hs₁ := (Model.sat_mono (Model.Env.extend_agree (canonEnv_le s hK) (.bnd 0) o)
              ψ).mpr hsat
            rw [← interp_lift ht' hK'] at hs₁
            have hs₂ := (Model.sat_instantiate (B.canonEnv s (i ⊔ i')) (noProjLast s _)
              Ctx.NoSlots.slots ((B.w s).liftT hK' t') _).mpr hs₁
            have hmemK := (truth_lt n s (i ⊔ i') _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mp hs₂
            exact (BWorld.mem_lift hK).mpr (BWorld.mem_of_provable
              (Δ := [WFF.instantiate Ctx.NoSlots.slots ((B.w s).liftT hK' t')
                (WFF.mono (((B.w s).le hK).insert (.bnd 0) A) ψ)])
              (fun χ hχ => by
                rw [List.mem_singleton.mp hχ]
                exact hmemK)
              ⟨Proof.ex_intro A ((B.w s).liftT hK' t') (Proof.lookup List.mem_cons_self)⟩)
          · intro hmem
            obtain ⟨i', hi, a, t, hmem'⟩ := (B.w s).exW_term hmem
            refine ⟨Model.interp (B.canonEnv s i') t, ?_⟩
            have hs := (truth_lt n s i' _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mpr hmem'
            have hs₁ := (Model.sat_instantiate (B.canonEnv s i') (noProjLast s i')
              Ctx.NoSlots.slots t _).mp hs
            exact (Model.sat_mono (Model.Env.extend_agree (canonEnv_le s hi) (.bnd 0) _)
              ψ).mp hs₁
      | box χ =>
          have hχs : χ.size < n := by simp only [WFF.size] at hφ; omega
          change (∀ a : B.Acc s, B.model.sat ((B.canonEnv s i).boxPush a) χ) ↔ _
          have key : ∀ (a : B.Acc s) (hR : B.R s a.1),
              B.model.sat ((B.canonEnv s i).boxPush a) χ ↔
                WFF.subst (arrowIdx (B.img s a.1)) (arrowS σ _ (B.img s a.1))
                  (ok_arrowS (B.imgOk hR i)) (coh_arrowS (B.imgOk hR i))
                  Ctx.NoSlots.slots Ctx.NoSlots.slots χ ∈ (B.w a.1).M (B.stg s a.1 i) := by
            intro a hR
            rw [boxPush_canon s i a hR]
            exact (Model.sat_subst _ _ (coh_arrowS (B.imgOk hR i)) Ctx.NoSlots.slots
              Ctx.NoSlots.slots _ _ χ).symm.trans
              (truth_lt n a.1 _ _ (by rw [WFF.size_subst]; exact hχs))
          constructor
          · intro hsat
            by_contra hnot
            obtain ⟨t, h, hneg⟩ := B.ex s i χ hnot
            exact ((B.w t).mcs _).neg_mem_iff.mp hneg
              ((key ⟨t, ⟨Or.inl h⟩⟩ h).mp (hsat ⟨t, ⟨Or.inl h⟩⟩))
          · intro hmem a
            obtain ⟨t, ⟨ha⟩⟩ := a
            rcases ha with hR | ⟨hT, hst⟩
            · exact (key ⟨t, ⟨Or.inl hR⟩⟩ hR).mpr (B.tr hR i χ hmem)
            · -- the world's own arrow: `T_box`, and the collapse
              subst hst
              refine (Model.sat_boxHere hT (B.canonEnv _ i) Ctx.NoSlots.slots χ).mp
                ((truth_lt n _ i _ (by rw [WFF.size_collapse]; exact hχs)).mpr ?_)
              exact BWorld.mem_of_provable (Δ := [.box χ])
                (fun ψ hψ => by
                  rw [List.mem_singleton.mp hψ]
                  exact hmem)
                ⟨Proof.T_box hT (Proof.lookup List.mem_cons_self)⟩
      | dia x hx χ =>
          have hχs : χ.size < n := by simp only [WFF.size] at hφ; omega
          change (∃ (X : VarType) (h : ((B.w s).ctx i).ref x = some (.VTypeDia X))
            (a : (B.model.posEval ((B.canonEnv s i).ref x h)).1),
              B.model.sat ((B.canonEnv s i).diaPush x h a) χ) ↔ _
          have key : ∀ {X : VarType} (h : ((B.w s).ctx i).ref x = some (.VTypeDia X))
              (a : (B.model.posEval ((B.canonEnv s i).ref x h)).1)
              (hk : B.kd s a.1.1 = some (x, X)),
              B.model.sat ((B.canonEnv s i).diaPush x h a) χ ↔
                WFF.subst (arrowXIdx (B.img s a.1.1) x (B.cx s a.1.1))
                  (arrowXS σ _ (B.img s a.1.1) x (B.cx s a.1.1))
                  (ok_arrowXS (B.imgOk (B.kdR hk) i) h (B.hcx hk i))
                  (coh_arrowXS (B.imgOk (B.kdR hk) i) h (B.hcx hk i))
                  Ctx.NoSlots.slots Ctx.NoSlots.slots χ ∈ (B.w a.1.1).M (B.stg s a.1.1 i) := by
            intro X h a hk
            rw [diaPush_canon s i h a ⟨_, hk⟩]
            exact (Model.sat_subst _ _ (coh_arrowXS (B.imgOk (B.kdR hk) i) h (B.hcx hk i))
              Ctx.NoSlots.slots Ctx.NoSlots.slots _ _ χ).symm.trans
              (truth_lt n a.1.1 _ _ (by rw [WFF.size_subst]; exact hχs))
          constructor
          · rintro ⟨X, h, a, hsat⟩
            rcases (canonEnv_extent s i h ▸ a.2 : a.1 ∈ B.extent s x) with ⟨X', hk⟩ | ⟨hnR, hr⟩
            swap
            · -- the world's own arrow: the witness is realised
              obtain ⟨-, hst⟩ := self_of_not_R hnR
              obtain ⟨⟨t, ⟨ht⟩⟩, hmem⟩ := a
              change s = t at hst
              subst hst
              exact dia_mem_of_sat_self hr h hx χ
                (fun ψ hψ => truth_lt n _ _ ψ (by rw [hψ]; exact hχs)) hmem hsat
            obtain rfl := B.hxX hk i X h
            by_contra hnot
            have hbx : WFF.boxx x hx χ.neg ∈ (B.w s).M i :=
              BWorld.mem_of_provable (Δ := [(WFF.dia x hx χ).neg])
                (fun ψ hψ => by
                  rw [List.mem_singleton.mp hψ]
                  exact ((B.w s).mcs i).neg_mem_iff.mpr hnot)
                ⟨Proof.boxx_neg_of_not_dia x hx χ⟩
            have hneg := B.trX hk i h χ.neg hbx
            exact ((B.w a.1.1).mcs _).neg_mem_iff.mp hneg ((key h a hk).mp hsat)
          · intro hmem
            obtain ⟨X, h⟩ : ∃ X, ((B.w s).ctx i).ref x = some (.VTypeDia X) := hx
            obtain ⟨t, hk, hm⟩ := B.exX s i x X h χ hmem
            have hmt : (⟨t, ⟨Or.inl (B.kdR hk)⟩⟩ : B.Acc s) ∈
                (B.model.posEval ((B.canonEnv s i).ref x h)).1 := by
              rw [canonEnv_extent]
              exact Or.inl ⟨X, hk⟩
            exact ⟨X, h, ⟨_, hmt⟩, (key h ⟨_, hmt⟩ hk).mpr hm⟩

/-- ⭐**The truth lemma** for B's canonical model. -/
theorem truth (s : B.W) (i : ℕ) (φ : WFF σ ((B.w s).ctx i) 0) :
    B.model.sat (B.canonEnv s i) φ ↔ φ ∈ (B.w s).M i :=
  truth_lt hST (φ.size + 1) s i φ (Nat.lt_succ_self _)

end BData

end BArrow

end V12M
