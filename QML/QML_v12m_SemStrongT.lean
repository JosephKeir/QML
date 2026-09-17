import QML.QML_v12m_SatInst
import QML.QML_v12m_Proof

/-!
# QML v12m — semantics of strong T

Strong T gives every object *some* possible object realised at the current world
(`Model.posRet_exists`), with the object as its content there.  So a `□`-view formula with a hole,
read at the current world with a term in its hole (`WFF.hereRead`), holds exactly when the same
formula holds in the `◇` view of that possible object with its content in the hole
(`WFF.viewRead`).

* `Env.diaPush_ret`: at the realised world the pushed environment agrees with the environment
  pushed into `□` at the current world — the `◇` counterpart of `Env.collapseAgree_self`.
* ⭐`sat_ret`: the two readings agree, which is the semantic content of the rule `T_dia`.
-/

namespace V12M

variable [ModalSys]

namespace Model

variable {σ : Signature} {M : Model.{u} σ}

/-- The environment pushed into `◇_c` at the world where the witness is realised agrees, on the
    `□` part, with the environment pushed into `□` at the current world. -/
theorem Env.diaPush_ret {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {c : ℕ}
    (hc : Γ.RootFresh (.free c)) {A : VarType} (p : M.frame.Dom (.VTypeDia A) w)
    (h : M.frame.R w w)
    (hr : (Γ.insert (.free c) (.VTypeDia A)).ref (.root (.free c)) = some (.VTypeDia A))
    (hmem : (⟨w, h⟩ : M.frame.Acc w) ∈
      (M.posEval ((env.extend (.free c) p).ref (.root (.free c)) hr)).1) :
    Env.Agree ((Ctx.le_insert hc.root (.VTypeDia A)).boxIn.trans
        (Ctx.le_boxIn_diaIn _ (.root (.free c))))
      (env.boxPush ⟨w, h⟩)
      ((env.extend (.free c) p).diaPush (.root (.free c)) hr ⟨⟨w, h⟩, hmem⟩) := by
  intro v T hv
  match v with
  | .step u .box =>
      have hu := Ctx.boxIn_step_box hv
      have hu' : (Γ.insert (.free c) (.VTypeDia A)).ref u = some (.VTypeBox T) :=
        (Ctx.ref_insert_ne _ (fun he => by
          rw [Ctx.ref_none_of_rootFresh hc u he] at hu
          cases hu)).trans hu
      change M.necEval (env.ref u hu) ⟨w, h⟩ =
        M.necEval ((env.extend (.free c) p).ref u hu') ⟨w, h⟩
      rw [Env.ref_extend_ne env p hu' hu (fun he => by
        rw [Ctx.ref_none_of_rootFresh hc u he] at hu
        cases hu)]
  | .step u .keep =>
      obtain ⟨hF, hu, B, rfl⟩ := Ctx.boxIn_keep hv
      have hu' : (Γ.insert (.free c) (.VTypeDia A)).ref u = some (.VTypeBox B) :=
        (Ctx.ref_insert_ne _ (fun he => by
          rw [Ctx.ref_none_of_rootFresh hc u he] at hu
          cases hu)).trans hu
      change M.necEval (GFunc.eval M.ops (GFunc.keep (σ := σ) hF ⟨B, rfl⟩) w
          (env.ref u hu)) ⟨w, h⟩ =
        M.necEval (GFunc.eval M.ops (GFunc.keep (σ := σ) hF ⟨B, rfl⟩) w
          ((env.extend (.free c) p).ref u hu')) ⟨w, h⟩
      rw [Env.ref_extend_ne env p hu' hu (fun he => by
        rw [Ctx.ref_none_of_rootFresh hc u he] at hu
        cases hu)]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

/-- ⭐Strong T: what holds of `t` here holds of the witness content in the `◇` view of the
    possible object realised here. -/
theorem sat_ret (hT : ModalSys.T = true) {Γ : Ctx} [Γ.NoSlots]
    {w : M.frame.W} (env : M.Env Γ w) (hnp : Γ.NoProjLast) {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) (c : ℕ) (hc : Γ.RootFresh (.free c))
    (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) (p : M.frame.Dom (.VTypeDia A) w)
    (hrefl : M.frame.R w w) (hmem : (⟨w, hrefl⟩ : M.frame.Acc w) ∈ (M.posEval p).1)
    (hcont : (M.posEval p).2 ⟨⟨w, hrefl⟩, hmem⟩ = interp env t) :
    M.sat env (WFF.hereRead hT t ψ) →
    M.sat (env.extend (.free c) p)
      (.dia (.root (.free c)) ⟨A, Ctx.ref_insert_root Γ (.free c) (.VTypeDia A)⟩
        (WFF.viewRead c hc A ψ)) := by
  intro hhere
  -- The `↓` side: instantiate, then collapse onto the `□` view at the current world.
  have hbox : M.sat ((env.boxPush ⟨w, M.frame.refl hT w⟩).extend (.bnd 0) (interp env t)) ψ := by
    have h₁ := (sat_instantiate env hnp Ctx.NoSlots.slots t _).mp hhere
    exact (sat_collapse ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A)
      ((Env.collapseAgree_self hT env).extend
        ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) (interp env t)) ψ).mp h₁
  -- The witness is given: realised at the current world, with `t`'s value as its content.
  set env' : M.Env (Γ.insert (.free c) (.VTypeDia A)) w := env.extend (.free c) p with henv'
  have hrc : (Γ.insert (.free c) (.VTypeDia A)).ref (.root (.free c)) = some (.VTypeDia A) :=
    Ctx.ref_insert_root Γ (.free c) (.VTypeDia A)
  have hpe : env'.ref (.root (.free c)) hrc = p := Env.extend_root env (.free c) p hrc
  have hmem' : (⟨w, hrefl⟩ : M.frame.Acc w) ∈ (M.posEval (env'.ref (.root (.free c)) hrc)).1 := by
    rw [hpe]
    exact hmem
  refine ⟨A, hrc, ⟨⟨w, hrefl⟩, hmem'⟩, ?_⟩
  -- The `↑` side: the hole takes the witness content, which is `t`'s value.
  have hval : (env'.diaPush (.root (.free c)) hrc ⟨⟨w, hrefl⟩, hmem'⟩).ref
      (.step (.root (.free c)) .dia) (Ctx.ref_diaIn_of hrc) = interp env t := by
    rw [Env.ref, dif_neg (by decide : ¬ Step.dia.isProj = true)]
    simp only [Env.diaPush]
    rw [posEval_snd_congr hpe ⟨⟨w, hrefl⟩, hmem'⟩ hmem]
    exact hcont
  have henvs : Env.restrict ((Ctx.le_insert hc.root (.VTypeDia A)).boxIn.trans
        (Ctx.le_boxIn_diaIn _ (.root (.free c))))
      (env'.diaPush (.root (.free c)) hrc ⟨⟨w, hrefl⟩, hmem'⟩) = env.boxPush ⟨w, hrefl⟩ := by
    funext v T hv
    exact (Env.diaPush_ret env hc p hrefl hrc hmem' v T hv).symm
  refine (sat_renameRoot _ (Ctx.noProjLast_boxIn Γ) (.bnd 0)
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) _ _ _ _ Ctx.NoSlots.slots ψ).mpr ?_
  rw [hval, henvs]
  exact hbox

/-- Extending by two distinct roots in either order gives agreeing environments. -/
theorem Env.extend_swap_agree {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {r r' : Root}
    (hne : r ≠ r') {T T' : VarType} (o : M.frame.Dom T w) (o' : M.frame.Dom T' w) :
    Env.Agree (Ctx.insert_swap_le hne T T') ((env.extend r o).extend r' o')
      ((env.extend r' o').extend r o) := by
  have hne' : VarSymb.root r' ≠ .root r := fun h => hne (VarSymb.root.inj h).symm
  intro v U hv
  by_cases h₁ : v = .root r'
  · subst h₁
    have hU : T' = U := by simpa [Ctx.insert] using hv
    subst hU
    rw [Env.extend_root, Env.extend_ne _ _ _ _ hne' (by simp [Ctx.insert]), Env.extend_root]
  · by_cases h₂ : v = .root r
    · subst h₂
      have hU : T = U := by simpa [Ctx.insert, hne'.symm] using hv
      subst hU
      rw [Env.extend_ne _ _ _ _ hne'.symm (by simp [Ctx.insert]), Env.extend_root,
        Env.extend_root]
    · have hv' : Γ v = some U := by simpa [Ctx.insert, h₁, h₂] using hv
      rw [Env.extend_ne _ _ _ _ h₁ (by simpa [Ctx.insert, h₂] using hv'),
        Env.extend_ne _ _ _ _ h₂ hv',
        Env.extend_ne _ _ _ _ h₂ (by simpa [Ctx.insert, h₁] using hv'),
        Env.extend_ne _ _ _ _ h₁ hv']

/-- ⭐At the world where the witness is realised, a hole formula read in the `◇` view holds exactly
    when it holds here with `t` in its hole.  This is `sat_ret` as an equivalence, at that one
    member of the extent: the canonical model's truth lemma needs both directions. -/
theorem sat_viewRead_ret (hT : ModalSys.T = true) {Γ : Ctx} [Γ.NoSlots]
    {w : M.frame.W} (env : M.Env Γ w) (hnp : Γ.NoProjLast) {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) (c : ℕ) (hc : Γ.RootFresh (.free c))
    (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) (p : M.frame.Dom (.VTypeDia A) w)
    (hrefl : M.frame.R w w) (hmem : (⟨w, hrefl⟩ : M.frame.Acc w) ∈ (M.posEval p).1)
    (hcont : (M.posEval p).2 ⟨⟨w, hrefl⟩, hmem⟩ = interp env t)
    (hmem' : (⟨w, hrefl⟩ : M.frame.Acc w) ∈
      (M.posEval ((env.extend (.free c) p).ref (.root (.free c))
        (Ctx.ref_insert_root Γ (.free c) (.VTypeDia A)))).1) :
    M.sat ((env.extend (.free c) p).diaPush (.root (.free c))
        (Ctx.ref_insert_root Γ (.free c) (.VTypeDia A)) ⟨⟨w, hrefl⟩, hmem'⟩)
      (WFF.viewRead c hc A ψ) ↔ M.sat env (WFF.hereRead hT t ψ) := by
  have hrc : (Γ.insert (.free c) (.VTypeDia A)).ref (.root (.free c)) = some (.VTypeDia A) :=
    Ctx.ref_insert_root Γ (.free c) (.VTypeDia A)
  have hpe : (env.extend (.free c) p).ref (.root (.free c)) hrc = p :=
    Env.extend_root env (.free c) p hrc
  have hval : ((env.extend (.free c) p).diaPush (.root (.free c)) hrc ⟨⟨w, hrefl⟩, hmem'⟩).ref
      (.step (.root (.free c)) .dia) (Ctx.ref_diaIn_of hrc) = interp env t := by
    rw [Env.ref, dif_neg (by decide : ¬ Step.dia.isProj = true)]
    simp only [Env.diaPush]
    rw [posEval_snd_congr hpe ⟨⟨w, hrefl⟩, hmem'⟩ hmem]
    exact hcont
  have henvs : Env.restrict ((Ctx.le_insert hc.root (.VTypeDia A)).boxIn.trans
        (Ctx.le_boxIn_diaIn _ (.root (.free c))))
      ((env.extend (.free c) p).diaPush (.root (.free c)) hrc ⟨⟨w, hrefl⟩, hmem'⟩) =
      env.boxPush ⟨w, hrefl⟩ := by
    funext v T hv
    exact (Env.diaPush_ret env hc p hrefl hrc hmem' v T hv).symm
  refine (sat_renameRoot _ (Ctx.noProjLast_boxIn Γ) (.bnd 0)
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) _ _ _ _ Ctx.NoSlots.slots ψ).trans
    ?_
  rw [hval, henvs]
  refine Iff.symm ((sat_instantiate env hnp Ctx.NoSlots.slots t _).trans ?_)
  exact sat_collapse ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A)
    ((Env.collapseAgree_self hT env).extend
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) (interp env t)) ψ

/-- ⭐Strong T, with a parameter: a witness realised here with `t`'s value as its content satisfies
    the hypothesis `WFF.retHyp` for every value of the parameter.  The witness is chosen before the
    parameter — it depends only on `t`'s value — which is why the rule's `∃x ∀y` form is sound. -/
theorem sat_retHyp (hT : ModalSys.T = true) {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W}
    (env : M.Env Γ w) (hnp : Γ.NoProjLast) {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    (c y : ℕ) (hc : Γ.RootFresh (.free c)) (hy : Γ.RootFresh (.free y)) (hyc : y ≠ c)
    (B : VarType) (ψ : WFF σ ((Γ.insert (.free y) B).boxIn.insert (.bnd 0) A) 1)
    (p : M.frame.Dom (.VTypeDia A) w) (hrefl : M.frame.R w w)
    (hmem : (⟨w, hrefl⟩ : M.frame.Acc w) ∈ (M.posEval p).1)
    (hcont : (M.posEval p).2 ⟨⟨w, hrefl⟩, hmem⟩ = interp env t) :
    M.sat (env.extend (.free c) p) (WFF.retHyp hT t c y hc hy hyc B ψ) := by
  have hne : Root.free y ≠ Root.free c := fun h => hyc (Root.free.inj h)
  have hcy : (Γ.insert (.free y) B).RootFresh (.free c) := hc.insert_ne hne B
  intro b
  refine (sat_bindFree (env.extend (.free c) p) (hnp.insert _ _) y
    (hy.insert_ne hne.symm (.VTypeDia A)) Ctx.NoSlots.slots B b _).mpr ?_
  refine (sat_mono (Env.extend_swap_agree env hne b p) _).mpr ?_
  intro hhere
  have hhere' := (sat_weaken (env.extend (.free y) b) hcy.root p _).mp hhere
  exact sat_ret hT (env.extend (.free y) b) (hnp.insert _ _) (Term.mono (Ctx.le_insert hy.root B) t)
    c hcy ψ p hrefl hmem
    (hcont.trans (interp_mono (Env.agree_extend env hy.root b) t).symm) hhere'

end Model

end V12M
