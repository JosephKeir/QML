import QML.QML_v12m_ReadNames
import QML.QML_v12m_SubstShift

/-!
# QML v12m — substituting into a formula read at names

Substituting into a formula read at names is substituting into the formula, by the entries the
substitution has at the renamed addresses (`Subst.PreRead`), up to η — as `WFF.subst_shift` is for
shifting.  This is the round trip of docs §12.36: a formula read at a fresh name, then the name
sent back to the content it names, is the formula again (`WFF.readNames_roundTrip`, in the next
file).

* `Subst.PreRead ν k Γ Ψ Ψ'`: `Ψ` at a renamed address agrees with `Ψ'` at the address; the
  witnesses one level out likewise; and at level 0 a named witness's name is sent where `Ψ'` sends
  the witness's identity content.
* `preRead_of`, `preRead_box`, `preRead_dia`, `preRead_under`, `preRead_optIn`, `preRead_optInT`.
* ⭐`Term.subst_readNames`, ⭐`WFF.subst_readNames`.
-/

namespace V12M

variable [ModalSys]

namespace Subst

variable {σ : Signature} {Δ : Ctx} {ν : VarSymb → Option VarSymb}

/-- `Ψ` substitutes each address read at the names as `Ψ'` substitutes the address, up to η; the
    witnesses one level out likewise; and a named witness's name as its identity content. -/
structure PreRead (ν : VarSymb → Option VarSymb) (k : ℕ) (Γ : Ctx) (Ψ Ψ' : Subst σ Δ) :
    Prop where
  ty : ∀ v T, Γ.ref v = some T → SubE.Sim T (Ψ.at (v.readNames ν k)) (Ψ'.at v)
  wit : ModalSys.Opt = true → ∀ y X, Γ.wit y = some X →
    WitE.Sim X (Ψ.wit (y.readNamesW ν k)) (Ψ'.wit y)
  named : k = 0 → ∀ y n X, ν y = some n → Γ.ref y = some (.VTypeDia X) →
    SubE.Sim X ((Ψ.at n).mono (Ctx.le_optInT Δ ((Ψ'.at y).idxAlong [])))
      ((Ψ'.at y).atBody ((Ψ'.at y).idxAlong []))

theorem preRead_of {k : ℕ} {Γ : Ctx} {Ψ Ψ' : Subst σ Δ}
    (hvis : ∀ v T, v.lastProj = false → Γ v = some T →
      SubE.Sim T (Ψ.at (v.readNames ν k)) (Ψ' v))
    (hwit : ModalSys.Opt = true → ∀ y X, Γ.wit y = some X →
      WitE.Sim X (Ψ.wit (y.readNamesW ν k)) (Ψ'.wit y))
    (hnamed : k = 0 → ∀ y n X, ν y = some n → Γ.ref y = some (.VTypeDia X) →
      SubE.Sim X ((Ψ.at n).mono (Ctx.le_optInT Δ ((Ψ'.at y).idxAlong [])))
        ((Ψ'.at y).atBody ((Ψ'.at y).idxAlong []))) :
    PreRead ν k Γ Ψ Ψ' := by
  refine ⟨?_, hwit, hnamed⟩
  intro v
  induction v with
  | root r => intro T hv; exact hvis _ _ rfl hv
  | step v s ih =>
      intro T hv
      by_cases hs : s.isStruct = true
      · rw [Ctx.ref_step_proj _ _ hs] at hv
        cases hU : Γ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U =>
            rw [hU] at hv
            rw [VarSymb.readNames_struct hs]
            change SubE.Sim T (if s.isStruct then (Ψ.at (v.readNames ν k)).proj s else Ψ _)
              (if s.isStruct then (Ψ'.at v).proj s else Ψ' _)
            rw [if_pos hs, if_pos hs]
            exact (ih U hU).proj_step hs hv
      · have hlp : (VarSymb.step v s).lastProj = false := Bool.eq_false_iff.mpr hs
        rw [at_nonproj Ψ' hlp]
        exact hvis _ _ hlp (by rwa [Ctx.ref_step_nonproj _ _ hs] at hv)

theorem preRead_box {k : ℕ} {Γ : Ctx} {Ψ Ψ' : Subst σ Δ} (hp : PreRead ν k Γ Ψ Ψ') :
    PreRead ν (k + 1) Γ.boxIn Ψ.box Ψ'.box := by
  refine preRead_of ?_ (fun hO y X hy => ?_) (fun h0 => absurd h0 (by omega))
  · intro v T _ hv
    match v with
    | .step u .box =>
        have hu := Ctx.boxIn_step_box hv
        rw [VarSymb.readNames_level_succ rfl, at_nonproj _ rfl]
        exact (hp.ty u _ hu).unbox
    | .step u .keep =>
        obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep hv
        rw [VarSymb.readNames_level_succ rfl, at_nonproj _ rfl]
        exact (hp.ty u _ hu).keepE' hF hk
    | .root _ => cases hv
    | .step _ .fst => cases hv
    | .step _ .snd => cases hv
    | .step _ .dia => cases hv
    | .step _ .here => cases hv
    | .step _ .at => cases hv
  · obtain ⟨-, hr⟩ := Ctx.boxIn_wit.mp hy
    exact (hp.ty y _ hr).toWit hO

theorem preRead_dia {k : ℕ} {Γ : Ctx} {Ψ Ψ' : Subst σ Δ} (hp : PreRead ν k Γ Ψ Ψ')
    {x ιx : VarSymb} (hw : (Ψ.at (x.readNames ν k)).idxAlong [] = ιx) :
    PreRead ν (k + 1) (Γ.diaIn x) (Ψ.dia (x.readNames ν k) ιx) (Ψ'.dia x ιx) := by
  refine preRead_of ?_ (fun hO y X hy => ?_) (fun h0 => absurd h0 (by omega))
  · intro v T _ hv
    match v with
    | .step u .dia =>
        change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
          else none) = some T at hv
        split_ifs at hv with hux
        subst hux
        cases hx : Γ.ref u with
        | none => rw [hx] at hv; cases hv
        | some U =>
            rw [hx] at hv
            cases U <;> try cases hv
            rw [VarSymb.readNames_level_succ rfl, at_nonproj _ rfl]
            change SubE.Sim _ (if u.readNames ν k = u.readNames ν k then
              (Ψ.at (u.readNames ν k)).diaBody ιx else SubE.hide)
              (if u = u then (Ψ'.at u).diaBody ιx else SubE.hide)
            rw [if_pos rfl, if_pos rfl]
            exact (hp.ty u _ hx).diaBody hw
    | .step u .box =>
        have hu := Ctx.boxIn_step_box (Γ := Γ) hv
        rw [VarSymb.readNames_level_succ rfl, at_nonproj _ rfl]
        exact (hp.ty u _ hu).unbox.mono _
    | .step u .keep =>
        obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep (Γ := Γ) hv
        rw [VarSymb.readNames_level_succ rfl, at_nonproj _ rfl]
        exact ((hp.ty u _ hu).keepE' hF hk).mono _
    | .root _ => cases hv
    | .step _ .fst => cases hv
    | .step _ .snd => cases hv
    | .step _ .here => cases hv
    | .step _ .at => cases hv
  · obtain ⟨-, hr⟩ := (Ctx.boxIn_wit (Γ := Γ)).mp hy
    exact ((hp.ty y _ hr).toWit hO).mono (Ctx.le_boxIn_diaIn Δ ιx)

theorem preRead_under {k : ℕ} {Γ : Ctx} {Ψ Ψ' : Subst σ Δ} (hp : PreRead ν k Γ Ψ Ψ') {d d' : ℕ}
    (hΓ : Γ.SlotsFrom d) (hn : ∀ y n, ν y = some n → n.rt ≠ .bnd d)
    (hdom : ∀ y n, ν y = some n → y.rt ≠ .bnd d) (T : VarType)
    (h : Δ (.root (.bnd d')) = none) :
    PreRead ν k (Γ.insert (.bnd d) T) (Ψ.under d d' T h) (Ψ'.under d d' T h) := by
  refine preRead_of ?_ (fun hO y X hy => (hp.wit hO y X hy).mono (Ctx.le_insert h T))
    (fun h0 y n X hyn hy => ?_)
  · intro v U hlp hv
    by_cases hvr : v = .root (.bnd d)
    · subst hvr
      change SubE.Sim U ((Ψ.under d d' T h).at (.root (.bnd d)))
        ((Ψ'.under d d' T h) (.root (.bnd d)))
      rw [show (Ψ.under d d' T h).at (.root (.bnd d)) = .ren (.root (.bnd d')) from if_pos rfl,
        show Ψ'.under d d' T h (.root (.bnd d)) = .ren (.root (.bnd d')) from if_pos rfl]
      exact .refl _
    · have hv' : Γ v = some U := Ctx.insert_ne_some hv hvr
      have hrt : v.rt ≠ .bnd d := fun he => by
        rw [hΓ v d he le_rfl] at hv'
        cases hv'
      rw [at_under_ne Ψ T h (VarSymb.readNames_rt_ne hn v hrt),
        show Ψ'.under d d' T h v = (Ψ' v).mono (Ctx.le_insert h T) from if_neg hvr]
      have h₁ := hp.ty v U ((Ctx.ref_nonproj Γ hlp).trans hv')
      rw [at_nonproj Ψ' hlp] at h₁
      exact h₁.mono _
  · have hyr := hdom y n hyn
    rw [Ctx.ref_insert_ne T hyr] at hy
    have H := (hp.named h0 y n X hyn hy).mono
      ((Ctx.le_insert h T).optInT ((Ψ'.at y).idxAlong []))
    rw [SubE.atBody_mono (Ctx.le_insert h T), SubE.mono_mono] at H
    rw [at_under_ne Ψ T h (hn y n hyn), at_under_ne Ψ' T h hyr, SubE.idxAlong_mono,
      SubE.mono_mono]
    exact H

theorem preRead_optIn {k : ℕ} {Γ Γ₂ : Ctx} {ι ι' : VarSymb → VarSymb} {Ψ Ψ' : Subst σ Δ}
    (h : Ctx.ReadsNames ν k Γ Γ₂) (hc : Coh ι Γ₂ Ψ) (hc' : Coh ι' Γ Ψ')
    (hp : PreRead ν k Γ Ψ Ψ') (hO : ModalSys.Opt = true) {y : VarSymb} {X : VarType}
    (hy : Γ.wit y = some X) {z : VarSymb} (hz : (Ψ'.wit y).idxAlong [] = z) :
    PreRead ν k (Γ.optIn y) (Ψ.optIn (y.readNamesW ν k) z) (Ψ'.optIn y z) := by
  have hz₂ : (Ψ.wit (y.readNamesW ν k)).idxAlong [] = z := ((hp.wit hO y X hy).idx).trans hz
  refine preRead_of ?_ (fun hO' y' X' hy' => (hp.wit hO' y' X' hy').mono (Ctx.le_optIn Δ z))
    (fun h0 y' n X' hyn hy' => ?_)
  · intro v T hlp hv
    by_cases hc0 : v = .step y .dia
    · subst hc0
      rw [Ctx.optIn_content hy] at hv
      cases hv
      have e : (VarSymb.step y .dia).readNames ν k = .step (y.readNamesW ν k) .dia := by
        cases k with
        | zero => exact VarSymb.readNames_level_zero rfl
        | succ k => exact VarSymb.readNames_level_succ rfl
      rw [e, at_nonproj _ rfl, optIn_content, optIn_content]
      exact (hp.wit hO y _ hy).optBody hz₂
    · rw [Ctx.optIn_ne hc0] at hv
      have hv' := (Ctx.ref_nonproj Γ hlp).trans hv
      rw [optIn_ne Ψ' z hc0, at_optIn_of hc hO (h.wit y X hy) hz₂ _ T (h v T hv')]
      have h₁ := hp.ty v T hv'
      rw [at_nonproj Ψ' hlp] at h₁
      exact h₁.mono _
  · obtain ⟨X'', hX'', hn⟩ := h.named h0 y' n hyn
    rw [(Ctx.le_optIn Γ y).ref hX''] at hy'
    cases hy'
    have H := (hp.named h0 y' n _ hyn hX'').mono
      ((Ctx.le_optIn Δ z).optInT ((Ψ'.at y').idxAlong []))
    rw [SubE.atBody_mono (Ctx.le_optIn Δ z), SubE.mono_mono] at H
    rw [at_optIn_of hc hO (h.wit y X hy) hz₂ n _ hn, at_optIn_of hc' hO hy hz y' _ hX'',
      SubE.idxAlong_mono, SubE.mono_mono]
    exact H

theorem preRead_optInT {k : ℕ} {Γ Γ₂ : Ctx} {ι ι' : VarSymb → VarSymb} {Ψ Ψ' : Subst σ Δ}
    (h : Ctx.ReadsNames ν k Γ Γ₂) (hc : Coh ι Γ₂ Ψ) (hc' : Coh ι' Γ Ψ')
    (hp : PreRead ν k Γ Ψ Ψ') {y : VarSymb} {X : VarType} (hy : Γ.witT y = some X)
    {z : VarSymb} (hz : (Ψ'.at y).idxAlong [] = z) :
    PreRead ν k (Γ.optInT y) (Ψ.optInT (y.readNames ν k) z) (Ψ'.optInT y z) := by
  obtain ⟨hT, hO, hr⟩ := Ctx.witT_spec hy
  have hz₂ : (Ψ.at (y.readNames ν k)).idxAlong [] = z := ((hp.ty y _ hr).idx).trans hz
  have hyT₂ := h.witT hy
  refine preRead_of ?_ (fun hO' y' X' hy' => (hp.wit hO' y' X' hy').mono (Ctx.le_optInT Δ z))
    (fun h0 y' n X' hyn hy' => ?_)
  · intro v T hlp hv
    by_cases hc0 : v = .step y .at
    · subst hc0
      rw [Ctx.optInT_content hy] at hv
      cases hv
      rw [optInT_content]
      by_cases hk : k = 0 ∧ (ν y).isSome
      · obtain ⟨rfl, hs⟩ := hk
        obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
        rw [VarSymb.readNames_at_named hn]
        obtain ⟨X', hX', hnT⟩ := h.named rfl y n hn
        rw [hr] at hX'
        cases hX'
        rw [at_optInT_of hc hyT₂ hz₂ n _ hnT]
        have H := hp.named rfl y n _ hn hr
        rw [hz] at H
        exact H
      · have e : (VarSymb.step y .at).readNames ν k = .step (y.readNames ν k) .at := by
          cases k with
          | zero =>
              have hnone : ν y = none := by
                cases hv : ν y with
                | none => rfl
                | some _ => exact absurd ⟨rfl, by rw [hv]; rfl⟩ hk
              exact VarSymb.readNames_at_unnamed hnone
          | succ k => exact VarSymb.readNames_at_succ
        rw [e, at_nonproj _ rfl, optInT_content]
        exact (hp.ty y _ hr).atBody hT hO hz₂
    · rw [Ctx.optInT_ne hc0] at hv
      have hv' := (Ctx.ref_nonproj Γ hlp).trans hv
      rw [optInT_ne Ψ' z hc0, at_optInT_of hc hyT₂ hz₂ _ T (h v T hv')]
      have h₁ := hp.ty v T hv'
      rw [at_nonproj Ψ' hlp] at h₁
      exact h₁.mono _
  · obtain ⟨X'', hX'', hn⟩ := h.named h0 y' n hyn
    rw [(Ctx.le_optInT Γ y).ref hX''] at hy'
    cases hy'
    have H := (hp.named h0 y' n _ hyn hX'').mono
      ((Ctx.le_optInT Δ z).optInT ((Ψ'.at y').idxAlong []))
    rw [SubE.atBody_mono (Ctx.le_optInT Δ z), SubE.mono_mono] at H
    rw [at_optInT_of hc hyT₂ hz₂ n _ hn, at_optInT_of hc' hy hz y' _ hX'',
      SubE.idxAlong_mono, SubE.mono_mono]
    exact H

end Subst

section SubstReadNames

variable {σ : Signature} {ν : VarSymb → Option VarSymb}

mutual
  theorem Func.subst_readNames {k : ℕ} {ι ι' : VarSymb → VarSymb} {Γ Γ₂ Δ : Ctx}
      (h : Ctx.ReadsNames ν k Γ Γ₂) (Ψ : Subst σ Δ) (hΨ : Subst.Ok Γ₂ Ψ)
      (hc : Subst.Coh ι Γ₂ Ψ) (Ψ' : Subst σ Δ) (hΨ' : Subst.Ok Γ Ψ') (hc' : Subst.Coh ι' Γ Ψ')
      (hp : Subst.PreRead ν k Γ Ψ Ψ') :
      {n : ℕ} → (f : Func σ Γ n) →
      Func.subst ι Ψ hΨ hc (Func.readNames h f) = Func.subst ι' Ψ' hΨ' hc' f
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.subst ι Ψ hΨ hc (Func.readNames h g))
            (Term.subst ι Ψ hΨ hc (Term.readNames h t)) =
          Func.eval (Func.subst ι' Ψ' hΨ' hc' g) (Term.subst ι' Ψ' hΨ' hc' t)
        rw [Func.subst_readNames h Ψ hΨ hc Ψ' hΨ' hc' hp g,
          eq_of_heq (Sigma.mk.inj (Term.subst_readNames h Ψ hΨ hc Ψ' hΨ' hc' hp t)).2]
    termination_by structural _ f => f

  /-- ⭐**Substituting into a term read at names** is substituting into the term, by the entries
      at the renamed addresses. -/
  theorem Term.subst_readNames {k : ℕ} {ι ι' : VarSymb → VarSymb} {Γ Γ₂ Δ : Ctx}
      (h : Ctx.ReadsNames ν k Γ Γ₂) (Ψ : Subst σ Δ) (hΨ : Subst.Ok Γ₂ Ψ)
      (hc : Subst.Coh ι Γ₂ Ψ) (Ψ' : Subst σ Δ) (hΨ' : Subst.Ok Γ Ψ') (hc' : Subst.Coh ι' Γ Ψ')
      (hp : Subst.PreRead ν k Γ Ψ Ψ') :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ T a) →
      (⟨_, Term.subst ι Ψ hΨ hc (Term.readNames h t)⟩ : Σ b, Term σ Δ T b) =
        ⟨_, Term.subst ι' Ψ' hΨ' hc' t⟩
    | _, _, .var v hv => congrArg (Sigma.mk _) ((hp.ty v _ hv).toVar _ _)
    | _, _, .func f => by
        change (⟨_, Term.func (Func.subst ι Ψ hΨ hc (Func.readNames h f))⟩ :
            Σ b, Term σ Δ .Var b) = ⟨_, Term.func (Func.subst ι' Ψ' hΨ' hc' f)⟩
        rw [Func.subst_readNames h Ψ hΨ hc Ψ' hΨ' hc' hp f]
    | _, _, .unit => rfl
    | _, _, .pair s t =>
        sig_pair (Term.subst_readNames h Ψ hΨ hc Ψ' hΨ' hc' hp s)
          (Term.subst_readNames h Ψ hΨ hc Ψ' hΨ' hc' hp t)
    | _, _, .boxtm t =>
        sig_boxtm (Term.subst_readNames h.boxIn Ψ.box (Subst.ok_box hΨ) (Subst.coh_box hΨ hc)
          Ψ'.box (Subst.ok_box hΨ') (Subst.coh_box hΨ' hc') (Subst.preRead_box hp) t)
    | _, _, .diatm x hx t => by
        have hw : (Ψ.at (x.readNames ν k)).idxAlong [] = ι (x.readNames ν k) :=
          hx.elim fun _ hX => hc _ _ (h x _ hX) []
        have hw' : (Ψ'.at x).idxAlong [] = ι' x := hx.elim fun _ hX => hc' x _ hX []
        have hι : ι (x.readNames ν k) = ι' x :=
          hx.elim fun _ hX => hw.symm.trans (((hp.ty x _ hX).idx).trans hw')
        have key : ∀ (y y' : VarSymb) (_hy : y = y')
            (hwy : (Ψ.at (x.readNames ν k)).idxAlong [] = y)
            (P : ∃ Y, Δ.ref y = some (.VTypeDia Y))
            (p : Subst.Ok (Γ₂.diaIn (x.readNames ν k)) (Ψ.dia (x.readNames ν k) y))
            (q : Subst.Coh ι (Γ₂.diaIn (x.readNames ν k)) (Ψ.dia (x.readNames ν k) y))
            (P' : ∃ Y, Δ.ref y' = some (.VTypeDia Y))
            (p' : Subst.Ok (Γ.diaIn x) (Ψ'.dia x y'))
            (q' : Subst.Coh ι' (Γ.diaIn x) (Ψ'.dia x y')),
            (⟨_, Term.diatm y P (Term.subst ι (Ψ.dia (x.readNames ν k) y) p q
                (Term.readNames (h.diaIn x) t))⟩ : Σ b, Term σ Δ _ b) =
              ⟨_, Term.diatm y' P' (Term.subst ι' (Ψ'.dia x y') p' q' t)⟩ := by
          intro y y' hy hwy P p q P' p' q'
          subst hy
          exact sig_diatm (Term.subst_readNames (h.diaIn x) _ p q _ p' q'
            (Subst.preRead_dia hp hwy) t)
        exact key _ _ hι hw _ _ _ _ _ _
    termination_by structural _ _ t => t
end

theorem Rel.subst_readNames {k : ℕ} {ι ι' : VarSymb → VarSymb} {Γ Γ₂ Δ : Ctx}
    (h : Ctx.ReadsNames ν k Γ Γ₂) (Ψ : Subst σ Δ) (hΨ : Subst.Ok Γ₂ Ψ) (hc : Subst.Coh ι Γ₂ Ψ)
    (Ψ' : Subst σ Δ) (hΨ' : Subst.Ok Γ Ψ') (hc' : Subst.Coh ι' Γ Ψ')
    (hp : Subst.PreRead ν k Γ Ψ Ψ') :
    {n : ℕ} → (ρ : Rel σ Γ n) →
    Rel.subst ι Ψ hΨ hc (Rel.readNames h ρ) = Rel.subst ι' Ψ' hΨ' hc' ρ
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.subst ι Ψ hΨ hc (Rel.readNames h ρ))
          (Term.subst ι Ψ hΨ hc (Term.readNames h t)) =
        Rel.eval (Rel.subst ι' Ψ' hΨ' hc' ρ) (Term.subst ι' Ψ' hΨ' hc' t)
      rw [Rel.subst_readNames h Ψ hΨ hc Ψ' hΨ' hc' hp ρ,
        eq_of_heq (Sigma.mk.inj (Term.subst_readNames h Ψ hΨ hc Ψ' hΨ' hc' hp t)).2]

/-- ⭐**Substituting into a formula read at names** is substituting into the formula, by the
    entries at the renamed addresses; the names and the named witnesses avoid the slots. -/
theorem WFF.subst_readNames (hν : ∀ y n, ν y = some n → ∀ e, n.rt ≠ .bnd e)
    (hdom : ∀ y n, ν y = some n → ∀ e, y.rt ≠ .bnd e) :
    {k : ℕ} → {ι ι' : VarSymb → VarSymb} → {Γ Γ₂ Δ : Ctx} → {d d' : ℕ} →
    (h : Ctx.ReadsNames ν k Γ Γ₂) → (hΓ : Γ.SlotsFrom d) → (hΓ₂ : Γ₂.SlotsFrom d) →
    (Ψ : Subst σ Δ) → (hΨ : Subst.Ok Γ₂ Ψ) → (hc : Subst.Coh ι Γ₂ Ψ) →
    (Ψ' : Subst σ Δ) → (hΨ' : Subst.Ok Γ Ψ') → (hc' : Subst.Coh ι' Γ Ψ') →
    (hΔ : Δ.SlotsFrom d') → Subst.PreRead ν k Γ Ψ Ψ' → (φ : WFF σ Γ d) →
    WFF.subst ι Ψ hΨ hc hΓ₂ hΔ (WFF.readNames hν h hΓ φ) = WFF.subst ι' Ψ' hΨ' hc' hΓ hΔ φ
  | _, _, _, _, _, _, _, _, h, _, _, Ψ, hΨ, hc, Ψ', hΨ', hc', _, hp, .atom ρ =>
      congrArg WFF.atom (Rel.subst_readNames h Ψ hΨ hc Ψ' hΨ' hc' hp ρ)
  | _, _, _, _, _, _, _, _, h, _, _, Ψ, hΨ, hc, Ψ', hΨ', hc', _, hp, .eq t s =>
      congrArg₂ WFF.eq
        (eq_of_heq (Sigma.mk.inj (Term.subst_readNames h Ψ hΨ hc Ψ' hΨ' hc' hp t)).2)
        (eq_of_heq (Sigma.mk.inj (Term.subst_readNames h Ψ hΨ hc Ψ' hΨ' hc' hp s)).2)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, _, _, _, _, h, hΓ, hΓ₂, Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp, .and φ ψ =>
      congrArg₂ WFF.and (WFF.subst_readNames hν hdom h hΓ hΓ₂ Ψ hΨ hc Ψ' hΨ' hc' hΔ hp φ)
        (WFF.subst_readNames hν hdom h hΓ hΓ₂ Ψ hΨ hc Ψ' hΨ' hc' hΔ hp ψ)
  | _, _, _, _, _, _, _, _, h, hΓ, hΓ₂, Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp, .or φ ψ =>
      congrArg₂ WFF.or (WFF.subst_readNames hν hdom h hΓ hΓ₂ Ψ hΨ hc Ψ' hΨ' hc' hΔ hp φ)
        (WFF.subst_readNames hν hdom h hΓ hΓ₂ Ψ hΨ hc Ψ' hΨ' hc' hΔ hp ψ)
  | _, _, _, _, _, _, _, _, h, hΓ, hΓ₂, Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp, .imp φ ψ =>
      congrArg₂ WFF.imp (WFF.subst_readNames hν hdom h hΓ hΓ₂ Ψ hΨ hc Ψ' hΨ' hc' hΔ hp φ)
        (WFF.subst_readNames hν hdom h hΓ hΓ₂ Ψ hΨ hc Ψ' hΨ' hc' hΔ hp ψ)
  | _, _, _, _, _, _, d, d', h, hΓ, hΓ₂, Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp, .all T φ =>
      congrArg (WFF.all T) (WFF.subst_readNames hν hdom
        (h.insert (hΓ.rootFresh le_rfl) (fun y n hy => hν y n hy d) T) (hΓ.insert T)
        (hΓ₂.insert T) (Ψ.under d d' T hΔ.root) (Subst.ok_under hΨ T hΔ.root)
        (Subst.coh_under hΨ hc hΓ₂ T hΔ.root) (Ψ'.under d d' T hΔ.root)
        (Subst.ok_under hΨ' T hΔ.root) (Subst.coh_under hΨ' hc' hΓ T hΔ.root) (hΔ.insert T)
        (Subst.preRead_under hp hΓ (fun y n hy => hν y n hy d) (fun y n hy => hdom y n hy d) T
          hΔ.root) φ)
  | _, _, _, _, _, _, d, d', h, hΓ, hΓ₂, Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp, .ex T φ =>
      congrArg (WFF.ex T) (WFF.subst_readNames hν hdom
        (h.insert (hΓ.rootFresh le_rfl) (fun y n hy => hν y n hy d) T) (hΓ.insert T)
        (hΓ₂.insert T) (Ψ.under d d' T hΔ.root) (Subst.ok_under hΨ T hΔ.root)
        (Subst.coh_under hΨ hc hΓ₂ T hΔ.root) (Ψ'.under d d' T hΔ.root)
        (Subst.ok_under hΨ' T hΔ.root) (Subst.coh_under hΨ' hc' hΓ T hΔ.root) (hΔ.insert T)
        (Subst.preRead_under hp hΓ (fun y n hy => hν y n hy d) (fun y n hy => hdom y n hy d) T
          hΔ.root) φ)
  | _, _, _, _, _, _, _, _, h, hΓ, hΓ₂, Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp, .box φ =>
      congrArg WFF.box (WFF.subst_readNames hν hdom h.boxIn hΓ.boxIn hΓ₂.boxIn Ψ.box
        (Subst.ok_box hΨ) (Subst.coh_box hΨ hc) Ψ'.box (Subst.ok_box hΨ') (Subst.coh_box hΨ' hc')
        hΔ.boxIn (Subst.preRead_box hp) φ)
  | k, ι, ι', Γ, Γ₂, Δ, _, d', h, hΓ, hΓ₂, Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp, .dia x hx φ => by
      have hw : (Ψ.at (x.readNames ν k)).idxAlong [] = ι (x.readNames ν k) :=
        hx.elim fun _ hX => hc _ _ (h x _ hX) []
      have hw' : (Ψ'.at x).idxAlong [] = ι' x := hx.elim fun _ hX => hc' x _ hX []
      have hι : ι (x.readNames ν k) = ι' x :=
        hx.elim fun _ hX => hw.symm.trans (((hp.ty x _ hX).idx).trans hw')
      have key : ∀ (y y' : VarSymb) (_hy : y = y')
          (hwy : (Ψ.at (x.readNames ν k)).idxAlong [] = y)
          (P : ∃ Y, Δ.ref y = some (.VTypeDia Y))
          (p : Subst.Ok (Γ₂.diaIn (x.readNames ν k)) (Ψ.dia (x.readNames ν k) y))
          (q : Subst.Coh ι (Γ₂.diaIn (x.readNames ν k)) (Ψ.dia (x.readNames ν k) y))
          (hΔy : (Δ.diaIn y).SlotsFrom d')
          (P' : ∃ Y, Δ.ref y' = some (.VTypeDia Y))
          (p' : Subst.Ok (Γ.diaIn x) (Ψ'.dia x y')) (q' : Subst.Coh ι' (Γ.diaIn x) (Ψ'.dia x y'))
          (hΔy' : (Δ.diaIn y').SlotsFrom d'),
          (WFF.dia y P (WFF.subst ι (Ψ.dia (x.readNames ν k) y) p q
              (hΓ₂.diaIn (x.readNames ν k)) hΔy
              (WFF.readNames hν (h.diaIn x) (hΓ.diaIn x) φ)) : WFF σ Δ d') =
            WFF.dia y' P' (WFF.subst ι' (Ψ'.dia x y') p' q' (hΓ.diaIn x) hΔy' φ) := by
        intro y y' hy hwy P p q hΔy P' p' q' hΔy'
        subst hy
        exact congrArg (WFF.dia y _) (WFF.subst_readNames hν hdom (h.diaIn x) (hΓ.diaIn x)
          (hΓ₂.diaIn (x.readNames ν k)) _ p q _ p' q' hΔy (Subst.preRead_dia hp hwy) φ)
      exact key _ _ hι hw _ _ _ _ _ _ _ _
  | k, ι, ι', Γ, Γ₂, Δ, _, d', h, hΓ, hΓ₂, Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp,
      .optx hO .arrow y hy φ => by
      obtain ⟨X, hX⟩ := id hy
      have hw : (Ψ.wit (y.readNamesW ν k)).idxAlong [] = ι (y.readNamesW ν k) :=
        hc.wit hO _ X (h.wit y X hX) []
      have hw' : (Ψ'.wit y).idxAlong [] = ι' y := hc'.wit hO y X hX []
      have hι : ι (y.readNamesW ν k) = ι' y :=
        hw.symm.trans (((hp.wit hO y X hX).idx).trans hw')
      have key : ∀ (z z' : VarSymb) (_hz : z = z') (hwz : (Ψ'.wit y).idxAlong [] = z')
          (P : ∃ Y, Δ.wit z = some Y)
          (p : Subst.Ok (Γ₂.optIn (y.readNamesW ν k)) (Ψ.optIn (y.readNamesW ν k) z))
          (q : Subst.Coh ι (Γ₂.optIn (y.readNamesW ν k)) (Ψ.optIn (y.readNamesW ν k) z))
          (hΔz : (Δ.optIn z).SlotsFrom d')
          (P' : ∃ Y, Δ.wit z' = some Y)
          (p' : Subst.Ok (Γ.optIn y) (Ψ'.optIn y z'))
          (q' : Subst.Coh ι' (Γ.optIn y) (Ψ'.optIn y z'))
          (hΔz' : (Δ.optIn z').SlotsFrom d'),
          (WFF.optx hO .arrow z P (WFF.subst ι (Ψ.optIn (y.readNamesW ν k) z) p q
              (hΓ₂.optIn (y.readNamesW ν k)) hΔz
              (WFF.readNames hν (h.optIn hX) (hΓ.optIn y) φ)) : WFF σ Δ d') =
            WFF.optx hO .arrow z' P' (WFF.subst ι' (Ψ'.optIn y z') p' q' (hΓ.optIn y) hΔz' φ) := by
        intro z z' hz hwz P p q hΔz P' p' q' hΔz'
        subst hz
        exact congrArg (WFF.optx hO .arrow z _) (WFF.subst_readNames hν hdom (h.optIn hX)
          (hΓ.optIn y) (hΓ₂.optIn _) _ p q _ p' q' hΔz
          (Subst.preRead_optIn h hc hc' hp hO hX hwz) φ)
      exact key _ _ hι hw' _ _ _ _ _ _ _ _
  | k, ι, ι', Γ, Γ₂, Δ, _, d', h, hΓ, hΓ₂, Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp,
      .optx hO .ident y hy φ => by
      obtain ⟨X, hX⟩ := id hy
      obtain ⟨-, -, hr⟩ := Ctx.witT_spec hX
      have hw : (Ψ.at (y.readNames ν k)).idxAlong [] = ι (y.readNames ν k) :=
        hc _ _ (h y _ hr) []
      have hw' : (Ψ'.at y).idxAlong [] = ι' y := hc' y _ hr []
      have hι : ι (y.readNames ν k) = ι' y := hw.symm.trans (((hp.ty y _ hr).idx).trans hw')
      have key : ∀ (z z' : VarSymb) (_hz : z = z') (hwz : (Ψ'.at y).idxAlong [] = z')
          (P : ∃ Y, Δ.witT z = some Y)
          (p : Subst.Ok (Γ₂.optInT (y.readNames ν k)) (Ψ.optInT (y.readNames ν k) z))
          (q : Subst.Coh ι (Γ₂.optInT (y.readNames ν k)) (Ψ.optInT (y.readNames ν k) z))
          (hΔz : (Δ.optInT z).SlotsFrom d')
          (P' : ∃ Y, Δ.witT z' = some Y)
          (p' : Subst.Ok (Γ.optInT y) (Ψ'.optInT y z'))
          (q' : Subst.Coh ι' (Γ.optInT y) (Ψ'.optInT y z'))
          (hΔz' : (Δ.optInT z').SlotsFrom d'),
          (WFF.optx hO .ident z P (WFF.subst ι (Ψ.optInT (y.readNames ν k) z) p q
              (hΓ₂.optInT (y.readNames ν k)) hΔz
              (WFF.readNames hν (h.optInT hX) (hΓ.optInT y) φ)) : WFF σ Δ d') =
            WFF.optx hO .ident z' P'
              (WFF.subst ι' (Ψ'.optInT y z') p' q' (hΓ.optInT y) hΔz' φ) := by
        intro z z' hz hwz P p q hΔz P' p' q' hΔz'
        subst hz
        exact congrArg (WFF.optx hO .ident z _) (WFF.subst_readNames hν hdom (h.optInT hX)
          (hΓ.optInT y) (hΓ₂.optInT _) _ p q _ p' q' hΔz
          (Subst.preRead_optInT h hc hc' hp hX hwz) φ)
      exact key _ _ hι hw' _ _ _ _ _ _ _ _
  | _, _, _, _, _, _, _, _, h, _, _, Ψ, hΨ, hc, Ψ', hΨ', hc', _, hp, .here hT s t hO =>
      WFF.here_congr hT (Term.subst_readNames h Ψ hΨ hc Ψ' hΨ' hc' hp s)
        (Term.subst_readNames h Ψ hΨ hc Ψ' hΨ' hc' hp t)
  | _, _, _, _, _, _, _, _, h, _, _, Ψ, hΨ, hc, Ψ', hΨ', hc', _, hp, .back hB L s t =>
      WFF.back_congr hB L (Term.subst_readNames h Ψ hΨ hc Ψ' hΨ' hc' hp s)
        (Term.subst_readNames h Ψ hΨ hc Ψ' hΨ' hc' hp t)
  | _, _, _, _, _, _, d, d', h, hΓ, hΓ₂, Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp, .retS hB S t Φ =>
      WFF.retS_congr hB S (Term.subst_readNames h Ψ hΨ hc Ψ' hΨ' hc' hp t)
        (WFF.subst_readNames hν hdom (h.boxIn.insert (hΓ.boxIn.rootFresh le_rfl)
          (fun y n hy => hν y n hy d) _) (hΓ.boxIn.insert _)
          (hΓ₂.boxIn.insert _) (Ψ.box.under d d' _ hΔ.boxIn.root)
          (Subst.ok_under (Subst.ok_box hΨ) _ hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hΨ) (Subst.coh_box hΨ hc) hΓ₂.boxIn _ hΔ.boxIn.root)
          (Ψ'.box.under d d' _ hΔ.boxIn.root) (Subst.ok_under (Subst.ok_box hΨ') _ hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hΨ') (Subst.coh_box hΨ' hc') hΓ.boxIn _ hΔ.boxIn.root)
          (hΔ.boxIn.insert _) (Subst.preRead_under (Subst.preRead_box hp) hΓ.boxIn
            (fun y n hy => hν y n hy d) (fun y n hy => hdom y n hy d) _ hΔ.boxIn.root) Φ)
  | k, ι, ι', Γ, Γ₂, Δ, d, d', h, hΓ, hΓ₂, Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp,
      .retxS hB y hy S t Φ => by
      have hw : (Ψ.at (y.readNames ν k)).idxAlong [] = ι (y.readNames ν k) :=
        hy.elim fun _ hY => hc _ _ (h y _ hY) []
      have hw' : (Ψ'.at y).idxAlong [] = ι' y := hy.elim fun _ hY => hc' y _ hY []
      have hι : ι (y.readNames ν k) = ι' y :=
        hy.elim fun _ hY => hw.symm.trans (((hp.ty y _ hY).idx).trans hw')
      have key : ∀ (z z' : VarSymb) (_hz : z = z')
          (hwz : (Ψ.at (y.readNames ν k)).idxAlong [] = z)
          (P : ∃ Y, Δ.ref z = some (.VTypeDia Y)) (hΔz : (Δ.diaIn z).SlotsFrom d')
          (p : Subst.Ok ((Γ₂.diaIn (y.readNames ν k)).insert (.bnd d) S.ty)
            ((Ψ.dia (y.readNames ν k) z).under d d' _ hΔz.root))
          (q : Subst.Coh (VarSymb.shiftSlot ι d d')
            ((Γ₂.diaIn (y.readNames ν k)).insert (.bnd d) S.ty)
            ((Ψ.dia (y.readNames ν k) z).under d d' _ hΔz.root))
          (P' : ∃ Y, Δ.ref z' = some (.VTypeDia Y)) (hΔz' : (Δ.diaIn z').SlotsFrom d')
          (p' : Subst.Ok ((Γ.diaIn y).insert (.bnd d) S.ty)
            ((Ψ'.dia y z').under d d' _ hΔz'.root))
          (q' : Subst.Coh (VarSymb.shiftSlot ι' d d') ((Γ.diaIn y).insert (.bnd d) S.ty)
            ((Ψ'.dia y z').under d d' _ hΔz'.root)),
          (WFF.retxS hB z P S (Term.subst ι Ψ hΨ hc (Term.readNames h t))
              (WFF.subst (VarSymb.shiftSlot ι d d')
                ((Ψ.dia (y.readNames ν k) z).under d d' _ hΔz.root)
                p q ((hΓ₂.diaIn (y.readNames ν k)).insert _) (hΔz.insert _)
                (WFF.readNames hν ((h.diaIn y).insert ((hΓ.diaIn y).rootFresh le_rfl)
                  (fun y n hy => hν y n hy d) _) ((hΓ.diaIn y).insert _) Φ)) : WFF σ Δ d') =
            WFF.retxS hB z' P' S (Term.subst ι' Ψ' hΨ' hc' t)
              (WFF.subst (VarSymb.shiftSlot ι' d d') ((Ψ'.dia y z').under d d' _ hΔz'.root)
                p' q' ((hΓ.diaIn y).insert _) (hΔz'.insert _) Φ) := by
        intro z z' hz hwz P hΔz p q P' hΔz' p' q'
        subst hz
        exact WFF.retxS_congr hB _ _ S (Term.subst_readNames h Ψ hΨ hc Ψ' hΨ' hc' hp t)
          (WFF.subst_readNames hν hdom ((h.diaIn y).insert ((hΓ.diaIn y).rootFresh le_rfl)
            (fun y n hy => hν y n hy d) _)
            ((hΓ.diaIn y).insert _) ((hΓ₂.diaIn (y.readNames ν k)).insert _) _ p q _ p' q'
            (hΔz.insert _) (Subst.preRead_under (Subst.preRead_dia hp hwz) (hΓ.diaIn y)
              (fun y n hy => hν y n hy d) (fun y n hy => hdom y n hy d) _ hΔz.root) Φ)
      exact key _ _ hι hw _ (hΔ.diaIn _) _ _ _ (hΔ.diaIn _) _ _
  | _, _, _, _, _, _, d, d', h, hΓ, hΓ₂, Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp, .link hV hF t Φ =>
      WFF.link_congr hV hF (Term.subst_readNames h Ψ hΨ hc Ψ' hΨ' hc' hp t)
        (WFF.subst_readNames hν hdom (h.boxIn.insert (hΓ.boxIn.rootFresh le_rfl)
          (fun y n hy => hν y n hy d) _) (hΓ.boxIn.insert _)
          (hΓ₂.boxIn.insert _) (Ψ.box.under d d' _ hΔ.boxIn.root)
          (Subst.ok_under (Subst.ok_box hΨ) _ hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hΨ) (Subst.coh_box hΨ hc) hΓ₂.boxIn _ hΔ.boxIn.root)
          (Ψ'.box.under d d' _ hΔ.boxIn.root) (Subst.ok_under (Subst.ok_box hΨ') _ hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hΨ') (Subst.coh_box hΨ' hc') hΓ.boxIn _ hΔ.boxIn.root)
          (hΔ.boxIn.insert _) (Subst.preRead_under (Subst.preRead_box hp) hΓ.boxIn
            (fun y n hy => hν y n hy d) (fun y n hy => hdom y n hy d) _ hΔ.boxIn.root) Φ)
  | k, ι, ι', Γ, Γ₂, Δ, d, d', h, hΓ, hΓ₂, Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp,
      .linkx hV hF y hy (D := D) t Φ => by
      have hw : (Ψ.at (y.readNames ν k)).idxAlong [] = ι (y.readNames ν k) :=
        hy.elim fun _ hY => hc _ _ (h y _ hY) []
      have hw' : (Ψ'.at y).idxAlong [] = ι' y := hy.elim fun _ hY => hc' y _ hY []
      have hι : ι (y.readNames ν k) = ι' y :=
        hy.elim fun _ hY => hw.symm.trans (((hp.ty y _ hY).idx).trans hw')
      have key : ∀ (z z' : VarSymb) (_hz : z = z')
          (hwz : (Ψ.at (y.readNames ν k)).idxAlong [] = z)
          (P : ∃ Y, Δ.ref z = some (.VTypeDia Y)) (hΔz : (Δ.diaIn z).SlotsFrom d')
          (p : Subst.Ok ((Γ₂.diaIn (y.readNames ν k)).insert (.bnd d) D.ty)
            ((Ψ.dia (y.readNames ν k) z).under d d' _ hΔz.root))
          (q : Subst.Coh (VarSymb.shiftSlot ι d d')
            ((Γ₂.diaIn (y.readNames ν k)).insert (.bnd d) D.ty)
            ((Ψ.dia (y.readNames ν k) z).under d d' _ hΔz.root))
          (P' : ∃ Y, Δ.ref z' = some (.VTypeDia Y)) (hΔz' : (Δ.diaIn z').SlotsFrom d')
          (p' : Subst.Ok ((Γ.diaIn y).insert (.bnd d) D.ty)
            ((Ψ'.dia y z').under d d' _ hΔz'.root))
          (q' : Subst.Coh (VarSymb.shiftSlot ι' d d') ((Γ.diaIn y).insert (.bnd d) D.ty)
            ((Ψ'.dia y z').under d d' _ hΔz'.root)),
          (WFF.linkx hV hF z P (Term.subst ι Ψ hΨ hc (Term.readNames h t))
              (WFF.subst (VarSymb.shiftSlot ι d d')
                ((Ψ.dia (y.readNames ν k) z).under d d' _ hΔz.root)
                p q ((hΓ₂.diaIn (y.readNames ν k)).insert _) (hΔz.insert _)
                (WFF.readNames hν ((h.diaIn y).insert ((hΓ.diaIn y).rootFresh le_rfl)
                  (fun y n hy => hν y n hy d) _) ((hΓ.diaIn y).insert _) Φ)) : WFF σ Δ d') =
            WFF.linkx hV hF z' P' (Term.subst ι' Ψ' hΨ' hc' t)
              (WFF.subst (VarSymb.shiftSlot ι' d d') ((Ψ'.dia y z').under d d' _ hΔz'.root)
                p' q' ((hΓ.diaIn y).insert _) (hΔz'.insert _) Φ) := by
        intro z z' hz hwz P hΔz p q P' hΔz' p' q'
        subst hz
        exact WFF.linkx_congr hV hF _ _ (Term.subst_readNames h Ψ hΨ hc Ψ' hΨ' hc' hp t)
          (WFF.subst_readNames hν hdom ((h.diaIn y).insert ((hΓ.diaIn y).rootFresh le_rfl)
            (fun y n hy => hν y n hy d) _)
            ((hΓ.diaIn y).insert _) ((hΓ₂.diaIn (y.readNames ν k)).insert _) _ p q _ p' q'
            (hΔz.insert _) (Subst.preRead_under (Subst.preRead_dia hp hwz) (hΓ.diaIn y)
              (fun y n hy => hν y n hy d) (fun y n hy => hdom y n hy d) _ hΔz.root) Φ)
      exact key _ _ hι hw _ (hΔ.diaIn _) _ _ _ (hΔ.diaIn _) _ _

end SubstReadNames

end V12M
