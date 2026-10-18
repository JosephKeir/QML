import QML.QML_v12m_BBackLimit

/-!
# QML v12m — a body along `◇_x` as a view body (strong B with T)

`Proof.ret_hereXC`/`ret_hereXWC` conclude at a **view body** `WFF.viewBody hx bd χ`: a hole
formula `χ` over the `□` view, read along `◇_x` with the content `bd` and the bound item paired in
its hole.  The own arrow's truth cases along a witness need every body along `◇_x` in that form.
As `WFF.diaAbsA` does for a formula of the view (`QML_v12m_Abs`), `WFF.bodyAbsA` abstracts a body:
the content `x.dia` to the hole's first component, the bound item to its second, the `□`-view
entries kept.

* ⭐`Subst.bodyAbsA`, its index map `VarSymb.bodyAbsAddr`, `ok_bodyAbsA`, `coh_bodyAbsA`;
* ⭐`WFF.viewBody_bodyAbsA`: the round trip at the content itself.
-/

namespace V12M

variable [ModalSys]

namespace VarSymb

/-- The address map of the body abstraction: below `x.dia` to the hole's first component, the
    bound item's addresses to its second, everything else kept. -/
def bodyAbsAddr (x : VarSymb) (v : VarSymb) : VarSymb :=
  match belowDia x v with
  | some p => (VarSymb.step (.root (.bnd 0)) .fst).ext p
  | none => if v.rt = .bnd 0 then (VarSymb.step (.root (.bnd 0)) .snd).ext v.path else v

end VarSymb

namespace Subst

variable {σ : Signature}

/-- ⭐**The abstraction of a body along `◇_x`**: the content `x.dia` to the hole's first
    component, the bound item to its second, the `□`-view entries kept. -/
def bodyAbsA (σ : Signature) (Δ : Ctx) (x : VarSymb) : Subst σ Δ := fun v =>
  match v with
  | .root (.bnd 0) => .ren (.step (.root (.bnd 0)) .snd)
  | .step u .dia => if u = x then .ren (.step (.root (.bnd 0)) .fst) else .hide
  | .step u .box => .ren (.step u .box)
  | .step u .keep => .ren (.step u .keep)
  | _ => .hide

variable {Γ : Ctx} [Γ.NoSlots] {x : VarSymb} {A T : VarType}

omit [Γ.NoSlots] in
/-- Away from the slot and the content, the body abstraction is `diaAbsA`'s. -/
theorem bodyAbsA_eq_ren {Δ : Ctx} {v : VarSymb} (hv : ∀ r : Root, v ≠ .root r)
    (hd : VarSymb.belowDia x v = none) (h : diaAbsA σ Δ x v = .ren v) :
    bodyAbsA σ Δ x v = .ren v := by
  match v with
  | .root r => exact absurd rfl (hv r)
  | .step u .dia =>
      have hu : u ≠ x := fun e => by
        subst e
        rw [VarSymb.belowDia_dia] at hd
        cases hd
      change (if u = x then _ else _) = _
      rw [if_neg hu]
      change (if u = x then _ else _) = _ at h
      rw [if_neg hu] at h
      exact h
  | .step _ .box => exact h
  | .step _ .keep => exact h
  | .step _ .fst => exact h
  | .step _ .snd => exact h
  | .step _ .here => exact h

/-- ⭐Well-typedness of the body abstraction. -/
theorem ok_bodyAbsA (hxA : Γ.ref x = some (.VTypeDia A))
    (hnb : ∀ p : List Step, Γ.ref ((VarSymb.step x .dia).ext p) = none) :
    Ok ((Γ.diaIn x).insert (.bnd 0) T)
      (bodyAbsA σ (Γ.boxIn.insert (.bnd 0) (.VTypeProd A T)) x) := by
  have h₀ : Γ.boxIn (.root (.bnd 0)) = none := (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root
  intro v U hlp hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = U := by simpa [Ctx.insert] using hv
    exact Ctx.ref_snd_of (Ctx.ref_insert_root _ (.bnd 0) _)
  · have hv' : (Γ.diaIn x) v = some U := by simpa [Ctx.insert, hvr] using hv
    rcases diaIn_casesA (σ := σ) hxA hnb hv' with ⟨rfl, rfl⟩ | ⟨hbl, hb, hen, hroot⟩
    · change (if x = x then SubE.ren (.step (.root (.bnd 0)) .fst) else .hide).OkRef _
      rw [if_pos rfl]
      exact Ctx.ref_fst_of (Ctx.ref_insert_root _ (.bnd 0) _)
    · rw [bodyAbsA_eq_ren hroot hbl (hen (Γ.boxIn.insert (.bnd 0) (.VTypeProd A T)))]
      change (Γ.boxIn.insert (.bnd 0) (.VTypeProd A T)).ref v = some U
      exact (Ctx.ref_nonproj _ hlp).trans (Ctx.le_insert h₀ _ v U hb)

/-- ⭐Coherence of the body abstraction: as `coh_diaAbsA`, with the bound item's addresses under
    the hole's second component (no address of the view has the slot's root). -/
theorem coh_bodyAbsA (hxA : Γ.ref x = some (.VTypeDia A))
    (hnb : ∀ p : List Step, Γ.ref ((VarSymb.step x .dia).ext p) = none)
    (hvf : Γ.ViewFresh) :
    Coh (VarSymb.bodyAbsAddr x) ((Γ.diaIn x).insert (.bnd 0) T)
      (bodyAbsA σ (Γ.boxIn.insert (.bnd 0) (.VTypeProd A T)) x) := by
  refine coh_of (ok_bodyAbsA hxA hnb) ?_
  have hx0 : x.rt ≠ .bnd 0 :=
    Ctx.ref_rt_ne ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) hxA
  intro v U hlp hv p
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    change (VarSymb.step (.root (.bnd 0)) .snd).ext p = _
    have hb : VarSymb.belowDia x ((VarSymb.root (.bnd 0)).ext p) = none := by
      cases hq : VarSymb.belowDia x ((VarSymb.root (.bnd 0)).ext p) with
      | none => rfl
      | some q =>
          exfalso
          apply hx0
          have h := congrArg VarSymb.rt (VarSymb.belowDia_eq hq)
          rw [VarSymb.ext_rt, VarSymb.ext_rt] at h
          exact h.symm
    unfold VarSymb.bodyAbsAddr
    rw [hb]
    dsimp only
    rw [if_pos (by rw [VarSymb.ext_rt]; rfl), VarSymb.ext_path]
    rfl
  · have hv' : (Γ.diaIn x) v = some U := by simpa [Ctx.insert, hvr] using hv
    rcases diaIn_casesA (σ := σ) hxA hnb hv' with ⟨rfl, rfl⟩ | ⟨hbl, hb, hen, hroot⟩
    · change (if x = x then SubE.ren (.step (.root (.bnd 0)) .fst) else .hide).idxAlong p = _
      rw [if_pos rfl]
      unfold VarSymb.bodyAbsAddr
      rw [VarSymb.belowDia_dia_ext]
      rfl
    · rw [bodyAbsA_eq_ren hroot hbl (hen (Γ.boxIn.insert (.bnd 0) (.VTypeProd A T)))]
      change v.ext p = _
      have hnone : VarSymb.belowDia x (v.ext p) = none := by
        cases hq : VarSymb.belowDia x (v.ext p) with
        | none => rfl
        | some q =>
            exfalso
            obtain ⟨p', hp'⟩ := VarSymb.belowDia_ext_of_none p hbl hq
            rcases List.eq_nil_or_concat p' with rfl | ⟨p'', s, rfl⟩
            · rw [show VarSymb.ext v [] = v from rfl] at hp'
              rw [hp'] at hb
              cases hb
            · rw [List.concat_eq_append, VarSymb.ext_snoc] at hp'
              injection hp' with hvx _
              have hbv : Γ.boxIn.ref v ≠ none := by
                rw [Ctx.ref_nonproj _ hlp, hb]
                exact fun hcon => by cases hcon
              have hx := hvf v p'' hbv
              rw [hvx, hxA] at hx
              cases hx
      have hrt : v.rt ≠ .bnd 0 := Ctx.ref_rt_ne
        ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0))
        ((Ctx.ref_nonproj _ hlp).trans hb)
      unfold VarSymb.bodyAbsAddr
      rw [hnone]
      dsimp only
      rw [if_neg (by rw [VarSymb.ext_rt]; exact hrt)]

end Subst

/-- ⭐**A body along `◇_x` abstracted** into a hole formula over the `□` view, whose hole pairs the
    content with the bound item. -/
def WFF.bodyAbsA {σ : Signature} {Γ : Ctx} [hp : Γ.Presented] (x : VarSymb) {A T : VarType}
    (hxA : Γ.ref x = some (.VTypeDia A)) (Φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) :
    WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeProd A T)) 1 :=
  WFF.subst (VarSymb.bodyAbsAddr x) (Subst.bodyAbsA σ _ x)
    (Subst.ok_bodyAbsA hxA (hp.not_below hxA rfl))
    (Subst.coh_bodyAbsA hxA (hp.not_below hxA rfl) hp.viewFresh)
    ((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert T)
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert _) Φ

/-- ⭐**The round trip**: every body along `◇_x` is the view body of its abstraction, at the
    content itself. -/
theorem WFF.viewBody_bodyAbsA {σ : Signature} {Γ : Ctx} [hp : Γ.Presented] (x : VarSymb)
    {A T : VarType} (hxA : Γ.ref x = some (.VTypeDia A))
    (Φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) :
    WFF.viewBody ⟨A, hxA⟩ (Term.eta (.step x .dia) A (Ctx.ref_diaIn_of hxA))
      (WFF.bodyAbsA x hxA Φ) = Φ := by
  unfold WFF.viewBody WFF.bodyRepl
  dsimp only [OutLeg.lift]
  unfold WFF.bodyAbsA
  rw [WFF.subst_mono]
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ Subst.ok_idS Subst.coh_idS _ _ _ ?_ Φ).trans
    (WFF.subst_id Subst.ok_idS Subst.coh_idS _ Φ)
  refine Subst.sim_of fun v U hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = U := by simpa [Ctx.insert] using hv
    dsimp only [Subst.comp, Subst.bodyAbsA, Subst.idS, SubE.comp]
    rw [Subst.at_proj _ _ rfl, Subst.at_nonproj _ rfl, Subst.set_root]
    exact .ren_eta _ _
  · have hv' : (Γ.diaIn x) v = some U := by simpa [Ctx.insert, hvr] using hv
    rcases Subst.diaIn_casesA (σ := σ) hxA (hp.not_below hxA rfl) hv' with
      ⟨rfl, rfl⟩ | ⟨hbl, hb, hen, hroot⟩
    · dsimp only [Subst.comp, Subst.bodyAbsA, Subst.idS]
      rw [if_pos rfl]
      dsimp only [SubE.comp]
      rw [Subst.at_proj _ _ rfl, Subst.at_nonproj _ rfl, Subst.set_root]
      change SubE.Sim _ _ (.tm (Term.mono _ (Term.eta _ _ _)))
      rw [Term.mono_eta]
      exact .ren_eta _ _
    · dsimp only [Subst.comp, Subst.idS]
      rw [Subst.bodyAbsA_eq_ren hroot hbl (hen _)]
      dsimp only [SubE.comp]
      rw [Subst.at_nonproj _ hlp, Subst.set_ne _ _ (hroot (.bnd 0))]
      exact .refl _

namespace Model

variable {σ : Signature} {M : Model σ} {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W}

/-- `sat_viewBody_here` at an explicit declaration `h` of the witness, as the truth lemma has it. -/
theorem sat_viewBody_here' (env : M.Env Γ w) (hT : ModalSys.T = true) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {Y : VarType} (h : Γ.ref x = some (.VTypeDia Y))
    {X T : VarType} {a₁ : Ann X}
    (bd : Term σ (Γ.diaIn x) X a₁) (χ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeProd X T)) 1)
    (hm : M.frame.reflAcc hT w ∈ (M.posEval (env.ref x h)).1)
    (e : M.frame.Dom T w) :
    M.sat ((env.diaPush x h ⟨M.frame.reflAcc hT w, hm⟩).extend (.bnd 0) e)
        (WFF.viewBody hx bd χ) ↔
      M.sat ((env.boxPush (M.frame.reflAcc hT w)).extend (T := .VTypeProd X T) (.bnd 0)
        (interp (env.diaPush x h ⟨M.frame.reflAcc hT w, hm⟩) bd, e)) χ := by
  set en := env.diaPush x h ⟨M.frame.reflAcc hT w, hm⟩
  unfold WFF.viewBody
  rw [sat_bodyRepl (Ctx.noProjLast_diaIn Γ x)]
  have hpair : interp (en.extend (.bnd 0) e)
      (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root T) bd)
        (Term.eta (.root (.bnd 0)) T (Ctx.ref_insert_root (Γ.diaIn x) (.bnd 0) T))) =
      ((interp en bd, e) : M.frame.Dom (.VTypeProd X T) w) := by
    change (interp _ (Term.mono _ bd), interp _ (Term.eta _ _ _)) = _
    rw [interp_mono (Env.agree_extend en (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root e),
      interp_eta]
    exact congrArg _ (Env.extend_root _ _ _ _)
  rw [hpair]
  exact sat_mono (Env.extend_agree (Env.diaPush_boxIn env h
    ⟨M.frame.reflAcc hT w, hm⟩) (.bnd 0) _) χ

end Model

end V12M
