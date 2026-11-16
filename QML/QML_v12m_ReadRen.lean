import QML.QML_v12m_TCanonRead
import QML.QML_v12m_ReadNamesFunc

/-!
# QML v12m — reading at a fresh root, then renaming it, is reading at the name

The canonical model reads an identity view at a **declared** name `d` (`TCanon.readsNameIn`),
the theory at a **fresh** root `c`, bound and instantiated (`TCanon.readSlot`, `optT_named`):
`[c ↦ d] (R_{x→c} χ)`.  The two agree (docs §12.36, strong T, option R).  It is not a
substitution identity — `R_{x→d}` sends `x.at` to `d` and `x` to itself, which no coherent
substitution does — so it is proved directly, for terms, as `Term.subst_readNames` is but with
the reading at `d` as the target:

* `Subst.ReadRen νc νd k Γ θ`: `θ` sends each address read at `νc` to the address read at `νd`;
  closed under `□` and `◇` views (`readRen_box`, `readRen_dia`).
* ⭐`Term.subst_readRen`: then `θ` after reading at `νc` is reading at `νd`.
* ⭐`WFF.readNames_eqH`: reading at names commutes with `≡`.
-/

namespace V12M

set_option linter.unusedSectionVars false

variable [ModalSys]

namespace Subst

variable {σ : Signature} {Δ : Ctx} {νc νd : VarSymb → Option VarSymb}

/-- `θ` sends each address read at `νc` to the same address read at `νd`, up to η. -/
def ReadRen (νc νd : VarSymb → Option VarSymb) (k : ℕ) (Γ : Ctx) (θ : Subst σ Δ) : Prop :=
  ∀ v T, Γ.ref v = some T → SubE.Sim T (θ.at (v.readNames νc k)) (.ren (v.readNames νd k))

/-- Declared addresses suffice: projections follow. -/
theorem readRen_of {k : ℕ} {Γ : Ctx} {θ : Subst σ Δ}
    (hvis : ∀ v T, v.lastProj = false → Γ v = some T →
      SubE.Sim T (θ.at (v.readNames νc k)) (.ren (v.readNames νd k))) :
    ReadRen νc νd k Γ θ := by
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
            rw [VarSymb.readNames_struct hs, VarSymb.readNames_struct hs]
            change SubE.Sim T (if s.isStruct then (θ.at (v.readNames νc k)).proj s else θ _)
              ((SubE.ren (v.readNames νd k)).proj s)
            rw [if_pos hs]
            exact (ih U hU).proj_step hs hv
      · have hlp : (VarSymb.step v s).lastProj = false := Bool.eq_false_iff.mpr hs
        exact hvis _ _ hlp (by rwa [Ctx.ref_step_nonproj _ _ hs] at hv)

theorem optAbs (hO : ModalSys.Opt = true) (h : ModalSys.Opt = false) : False := by
  rw [hO] at h
  cases h

theorem keepOnly_false (hO : ModalSys.Opt = true) : ModalSys.keepOnly = false := by
  cases hk : ModalSys.keepOnly
  · rfl
  · exact (optAbs hO
      (ModalSys.noOpt_of_Four (ModalSys.keepOnly_flags hk).2)).elim

theorem readRen_box (hO : ModalSys.Opt = true) {k : ℕ} {Γ : Ctx} {θ : Subst σ Δ}
    (hp : ReadRen νc νd k Γ θ) : ReadRen νc νd (k + 1) Γ.boxIn θ.box := by
  refine readRen_of fun v T _ hv => ?_
  match v with
  | .step u .box =>
      have hu := Ctx.boxIn_step_box hv
      rw [VarSymb.readNames_level_succ rfl, VarSymb.readNames_level_succ rfl, at_nonproj _ rfl]
      have h := (hp u _ hu).unbox
      change SubE.Sim T _ (.ren (u.readNames νd k).inner) at h
      rwa [VarSymb.inner_box (keepOnly_false hO)] at h
  | .step u .keep =>
      obtain ⟨hF, -, -⟩ := Ctx.boxIn_keep hv
      exact (optAbs hO (ModalSys.noOpt_of_Four hF)).elim
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv
  | .step _ .at => cases hv

theorem readRen_dia (hO : ModalSys.Opt = true) {k : ℕ} {Γ : Ctx} {θ : Subst σ Δ}
    (hp : ReadRen νc νd k Γ θ) {x : VarSymb}
    (hw : (θ.at (x.readNames νc k)).idxAlong [] = x.readNames νd k) :
    ReadRen νc νd (k + 1) (Γ.diaIn x) (θ.dia (x.readNames νc k) (x.readNames νd k)) := by
  refine readRen_of fun v T _ hv => ?_
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
          rw [VarSymb.readNames_level_succ rfl, VarSymb.readNames_level_succ rfl,
            at_nonproj _ rfl]
          change SubE.Sim _ (if u.readNames νc k = u.readNames νc k then
            (θ.at (u.readNames νc k)).diaBody (u.readNames νd k) else SubE.hide)
            ((SubE.ren (u.readNames νd k)).diaBody (u.readNames νd k))
          rw [if_pos rfl]
          exact (hp u _ hx).diaBody hw
  | .step u .box =>
      have hu := Ctx.boxIn_step_box (Γ := Γ) hv
      rw [VarSymb.readNames_level_succ rfl, VarSymb.readNames_level_succ rfl, at_nonproj _ rfl]
      have h := ((hp u _ hu).unbox).mono (Ctx.le_boxIn_diaIn Δ (x.readNames νd k))
      change SubE.Sim T _ (.ren (u.readNames νd k).inner) at h
      rwa [VarSymb.inner_box (keepOnly_false hO)] at h
  | .step u .keep =>
      obtain ⟨hF, -, -⟩ := Ctx.boxIn_keep (Γ := Γ) hv
      exact (optAbs hO (ModalSys.noOpt_of_Four hF)).elim
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv
  | .step _ .at => cases hv

end Subst

variable {σ : Signature} {νc νd : VarSymb → Option VarSymb}

mutual
  theorem Func.subst_readRen (hO : ModalSys.Opt = true) {k : ℕ} {ι : VarSymb → VarSymb}
      {Γ Γ₂ Δ : Ctx} (hcR : Ctx.ReadsNames νc k Γ Γ₂) (hdR : Ctx.ReadsNames νd k Γ Δ)
      (θ : Subst σ Δ) (hθ : Subst.Ok Γ₂ θ) (hc : Subst.Coh ι Γ₂ θ)
      (hp : Subst.ReadRen νc νd k Γ θ) :
      {n : ℕ} → (f : Func σ Γ n) →
      Func.subst ι θ hθ hc (Func.readNames hcR f) = Func.readNames hdR f
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.subst ι θ hθ hc (Func.readNames hcR g))
            (Term.subst ι θ hθ hc (Term.readNames hcR t)) =
          Func.eval (Func.readNames hdR g) (Term.readNames hdR t)
        rw [Func.subst_readRen hO hcR hdR θ hθ hc hp g,
          eq_of_heq (Sigma.mk.inj (Term.subst_readRen hO hcR hdR θ hθ hc hp t)).2]
    termination_by structural _ f => f

  /-- ⭐**Substituting into a term read at `νc`** by a substitution that renames the `νc` reading
      to the `νd` one is reading at `νd`. -/
  theorem Term.subst_readRen (hO : ModalSys.Opt = true) {k : ℕ} {ι : VarSymb → VarSymb}
      {Γ Γ₂ Δ : Ctx} (hcR : Ctx.ReadsNames νc k Γ Γ₂) (hdR : Ctx.ReadsNames νd k Γ Δ)
      (θ : Subst σ Δ) (hθ : Subst.Ok Γ₂ θ) (hc : Subst.Coh ι Γ₂ θ)
      (hp : Subst.ReadRen νc νd k Γ θ) :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ T a) →
      (⟨_, Term.subst ι θ hθ hc (Term.readNames hcR t)⟩ : Σ b, Term σ Δ T b) =
        ⟨_, Term.readNames hdR t⟩
    | _, _, .var v hv => congrArg (Sigma.mk _) ((hp v _ hv).toVar _ _)
    | _, _, .func f => by
        change (⟨_, Term.func (Func.subst ι θ hθ hc (Func.readNames hcR f))⟩ :
            Σ b, Term σ Δ .Var b) = ⟨_, Term.func (Func.readNames hdR f)⟩
        rw [Func.subst_readRen hO hcR hdR θ hθ hc hp f]
    | _, _, .unit => rfl
    | _, _, .pair s t =>
        sig_pair (Term.subst_readRen hO hcR hdR θ hθ hc hp s)
          (Term.subst_readRen hO hcR hdR θ hθ hc hp t)
    | _, _, .boxtm t =>
        sig_boxtm (Term.subst_readRen hO hcR.boxIn hdR.boxIn θ.box (Subst.ok_box hθ)
          (Subst.coh_box hθ hc) (Subst.readRen_box hO hp) t)
    | _, _, .diatm x hx t => by
        have hw : (θ.at (x.readNames νc k)).idxAlong [] = ι (x.readNames νc k) :=
          hx.elim fun _ hX => hc _ _ (hcR x _ hX) []
        have hι : ι (x.readNames νc k) = x.readNames νd k :=
          hx.elim fun _ hX => hw.symm.trans (hp x _ hX).idx
        have key : ∀ (y : VarSymb) (_hy : y = x.readNames νd k)
            (hwy : (θ.at (x.readNames νc k)).idxAlong [] = y)
            (P : ∃ Y, Δ.ref y = some (.VTypeDia Y))
            (p : Subst.Ok (Γ₂.diaIn (x.readNames νc k)) (θ.dia (x.readNames νc k) y))
            (q : Subst.Coh ι (Γ₂.diaIn (x.readNames νc k)) (θ.dia (x.readNames νc k) y))
            (P' : ∃ Y, Δ.ref (x.readNames νd k) = some (.VTypeDia Y)),
            (⟨_, Term.diatm y P (Term.subst ι (θ.dia (x.readNames νc k) y) p q
                (Term.readNames (hcR.diaIn x) t))⟩ : Σ b, Term σ Δ _ b) =
              ⟨_, Term.diatm (x.readNames νd k) P' (Term.readNames (hdR.diaIn x) t)⟩ := by
          intro y hy hwy P p q P'
          subst hy
          exact sig_diatm (Term.subst_readRen hO (hcR.diaIn x) (hdR.diaIn x) _ p q
            (Subst.readRen_dia hO hp hwy) t)
        exact key _ hι hw _ _ _ _
    termination_by structural _ _ t => t
end

/-- ⭐**Reading at names commutes with `≡`.** -/
theorem WFF.readNames_eqH (hO : ModalSys.Opt = true) {ν : VarSymb → Option VarSymb}
    (hν : ∀ y n, ν y = some n → ∀ e, n.rt ≠ .bnd e) : {k : ℕ} → {Γ₁ Γ₂ : Ctx} → {d : ℕ} →
    (h : Ctx.ReadsNames ν k Γ₁ Γ₂) → (hs : Γ₁.SlotsFrom d) → (T : VarType) → {a b : Ann T} →
    (t : Term σ Γ₁ T a) → (s : Term σ Γ₁ T b) →
    WFF.readNames hν h hs (eqH hO T t s : WFF σ Γ₁ d) =
      eqH hO T (Term.readNames h t) (Term.readNames h s)
  | _, _, _, _, h, hs, .Var, .var, .var, t, s =>
      (congrArg (WFF.readNames hν h hs) (eqH_Var hO t s)).trans (eqH_Var hO _ _).symm
  | _, _, _, _, _, _, .VTypeOne, .one, .one, .unit, .unit => rfl
  | _, _, _, _, h, hs, .VTypeProd A B, .prod _ _, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ => by
      change WFF.and (WFF.readNames hν h hs (eqH hO A t₁ s₁))
        (WFF.readNames hν h hs (eqH hO B t₂ s₂)) = _
      rw [WFF.readNames_eqH hO hν h hs A, WFF.readNames_eqH hO hν h hs B]
      rfl
  | _, _, _, _, h, hs, .VTypeBox A, .box _, .box _, .boxtm t, .boxtm s => by
      change WFF.box (WFF.readNames hν h.boxIn hs.boxIn (eqH hO A t s)) = _
      rw [WFF.readNames_eqH hO hν h.boxIn hs.boxIn A]
      rfl
  | k, Γ₁, Γ₂, _, h, hs, .VTypeDia A, .dia x _, .dia x' _, .diatm _ hx t, .diatm _ hx' s => by
      obtain ⟨X, hX⟩ := Ctx.boxIn_wit_of hO hx
      obtain ⟨X', hX'⟩ := Ctx.boxIn_wit_of hO hx'
      have H : Ctx.ReadsNames ν (k + 1) ((Γ₁.boxIn.optIn x).optIn x')
          ((Γ₂.boxIn.optIn (x.readNames ν k)).optIn (x'.readNames ν k)) :=
        (h.boxIn.optIn hX).optIn ((Ctx.le_optIn _ x).wit _ _ hX')
      have hxc : ∃ Y, Γ₂.ref (x.readNames ν k) = some (.VTypeDia Y) :=
        hx.imp fun _ hY => h x _ hY
      have hxc' : ∃ Y, Γ₂.ref (x'.readNames ν k) = some (.VTypeDia Y) :=
        hx'.imp fun _ hY => h x' _ hY
      have ht : Term.readNames H (Term.mono (Ctx.le_optIn _ x')
            (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx) t)) =
          Term.mono (Ctx.le_optIn _ (x'.readNames ν k))
            (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hxc) (Term.readNames (h.diaIn x) t)) := by
        rw [Term.mono_mono, Term.mono_mono, Term.readNames_mono (h.diaIn x) H _
          ((Ctx.le_diaIn_boxIn_optIn' hO hxc).trans (Ctx.le_optIn _ _))]
      have hs' : Term.readNames H (Term.mono ((Ctx.le_optIn _ x).optIn x')
            (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx') s)) =
          Term.mono ((Ctx.le_optIn _ (x.readNames ν k)).optIn (x'.readNames ν k))
            (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hxc') (Term.readNames (h.diaIn x') s)) := by
        rw [Term.mono_mono, Term.mono_mono, Term.readNames_mono (h.diaIn x') H _
          ((Ctx.le_diaIn_boxIn_optIn' hO hxc').trans ((Ctx.le_optIn _ _).optIn _))]
      change WFF.box (WFF.imp (WFF.or _ _) (WFF.optx hO .arrow _ _ (WFF.optx hO .arrow _ _
        (WFF.readNames hν H _ (eqH hO A _ _))))) = _
      rw [WFF.readNames_eqH hO hν H _ A, ht, hs']
      rfl


/-! ## At level 0: the fresh root sent to the name -/

namespace TCanon

/-- ⭐At level 0, sending the fresh root `c` to the name `d` renames the reading at `c` to the
    reading at `d`. -/
theorem readRen_name (hT : ModalSys.T = true) (hO : ModalSys.Opt = true) {Γ : Ctx}
    (hfree : Γ.NoTopAt) {x : VarSymb} {A : VarType} (hx : Γ.ref x = some (.VTypeDia A))
    {c d : ℕ} (hc : Γ.RootFresh (.free c)) (hd : Γ.ref (.root (.free d)) = some A) :
    Subst.ReadRen (nameAt x c) (nameAt x d) 0 (Γ.optInT x)
      (Subst.single (σ := σ) (.free c) (.tm (Term.eta (.root (.free d)) A hd))) := by
  have hxT := Ctx.witT_of hT hO hx
  refine Subst.readRen_of fun v T hlp hv => ?_
  by_cases hvx : v = .step x .at
  · subst hvx
    rw [Ctx.optInT_content hxT] at hv
    cases hv
    rw [VarSymb.readNames_at_named (nameAt_self x c), VarSymb.readNames_at_named (nameAt_self x d),
      Subst.at_single_root]
    exact .eta_ren _ _
  · rw [Ctx.optInT_ne hvx] at hv
    rw [VarSymb.readNames_raw hfree hlp hv, VarSymb.readNames_raw hfree hlp hv,
      Subst.single_at_ne (fun he => by rw [hc v he] at hv; cases hv)]
    exact .refl _

/-- ⭐**The fresh reading, instantiated at the name, is the reading at the name**, for terms. -/
theorem subst_readName (hT : ModalSys.T = true) (hO : ModalSys.Opt = true) {Γ : Ctx}
    (hfree : Γ.NoTopAt) {x : VarSymb} {A : VarType} (hx : Γ.ref x = some (.VTypeDia A))
    {c d : ℕ} (hc : Γ.RootFresh (.free c)) (hd : Γ.ref (.root (.free d)) = some A)
    {B : VarType} {a : Ann B} (t : Term σ (Γ.optInT x) B a) :
    (⟨_, Term.subst (Subst.singleIdx (.free c) (.tm (Term.eta (.root (.free d)) A hd)))
      (Subst.single (.free c) (.tm (Term.eta (.root (.free d)) A hd)))
      (Subst.ok_single (Ctx.Le.refl Γ) rfl) (Subst.coh_single hc (Ctx.Le.refl Γ) rfl)
      (Term.readNames (readsName hT hO hfree hx hc) t)⟩ : Σ b, Term σ Γ B b) =
    ⟨_, Term.readNames (readsNameIn hT hO hfree hx hd) t⟩ :=
  Term.subst_readRen hO _ _ _ _ _ (readRen_name hT hO hfree hx hc hd) t

/-- Reading at a name declared in the context itself. -/
theorem readsSelf {Γ : Ctx} (hfree : Γ.NoTopAt) {x : VarSymb} {A : VarType}
    (hx : Γ.ref x = some (.VTypeDia A)) {d : ℕ} (hd : Γ.ref (.root (.free d)) = some A) :
    Ctx.ReadsNames (nameAt x d) 0 Γ Γ := by
  refine Ctx.ReadsNames.of_raw (fun v T hlp hv => ?_) (fun y X hy => hy) (fun _ y n hyn => ?_)
  · rw [VarSymb.readNames_raw hfree hlp hv, Ctx.ref_nonproj Γ hlp]
    exact hv
  · obtain ⟨rfl, rfl⟩ := nameAt_eq hyn
    exact ⟨A, hx, hd⟩

/-- A term of the context itself, read at the name, is itself. -/
theorem readName_mono (hT : ModalSys.T = true) (hO : ModalSys.Opt = true) {Γ : Ctx}
    (hfree : Γ.NoTopAt) {x : VarSymb} {A : VarType} (hx : Γ.ref x = some (.VTypeDia A))
    {d : ℕ} (hd : Γ.ref (.root (.free d)) = some A) {B : VarType} {b : Ann B}
    (u : Term σ Γ B b) :
    (⟨_, Term.readNames (readsNameIn hT hO hfree hx hd) (Term.mono (Ctx.le_optInT Γ x) u)⟩ :
      Σ b, Term σ Γ B b) = ⟨_, u⟩ := by
  have h0 := readsSelf hfree hx hd
  have e1 := Term.readNames_noAt h0 (Ctx.Le.refl Γ) (Ctx.RefFix.of_noTopAt hfree) u
  rw [Term.mono_refl] at e1
  rw [Term.readNames_mono h0 (readsNameIn hT hO hfree hx hd) (Ctx.le_optInT Γ x)
    (Ctx.Le.refl Γ) u, Term.mono_refl]
  exact e1

/-- ⭐**A term of `x`'s identity view is `≡` there to its reading at the name**:
    `◇⁰ᵀ_x (x.at ≡ d) ⊢ ◇⁰ᵀ_x (t ≡ (R_{x→d} t)↑)`, by `named_optT`, whose premise is `u ≡ u`. -/
def selfEq (hT : ModalSys.T = true) (hO : ModalSys.Opt = true) {Γ : Ctx} [Γ.Presented]
    (hfree : Γ.NoTopAt) {x : VarSymb} {A : VarType} (hx : Γ.ref x = some (.VTypeDia A))
    {c d : ℕ} (hc : Γ.RootFresh (.free c)) (hd : Γ.ref (.root (.free d)) = some A)
    {B : VarType} {a : Ann B} (t : Term σ (Γ.optInT x) B a) :
    Proof σ Γ [nameSent hT hO hx (Term.eta (.root (.free d)) A hd)]
      (.optx hO .ident x ⟨A, Ctx.witT_of hT hO hx⟩ (eqH hO B t
        (Term.mono (Ctx.le_optInT Γ x) (Term.readNames (readsNameIn hT hO hfree hx hd) t)))) := by
  set u := Term.readNames (readsNameIn hT hO hfree hx hd) t
  set χ : WFF σ (Γ.optInT x) 0 := eqH hO B t (Term.mono (Ctx.le_optInT Γ x) u) with hχ
  have key : WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free d)) A hd)
      (readSlot hT hO hfree hx hc χ) = eqH hO B u u := by
    have e1 := WFF.instantiate_bindFree (Ctx.Le.refl Γ) c hc (Term.eta (.root (.free d)) A hd)
      (WFF.readNames nameAt_rt (readsName hT hO hfree hx hc) Ctx.NoSlots.slots χ)
    rw [WFF.mono_refl] at e1
    change WFF.instantiate Ctx.NoSlots.slots _ (WFF.bindFree c hc Ctx.NoSlots.slots A
      (WFF.readNames nameAt_rt (readsName hT hO hfree hx hc) Ctx.NoSlots.slots χ)) = _
    rw [e1, hχ, WFF.readNames_eqH hO, WFF.subst_eqH hO]
    exact eqH_congr hO (subst_readName hT hO hfree hx hc hd t)
      ((subst_readName hT hO hfree hx hc hd _).trans (readName_mono hT hO hfree hx hd u))
  have p := named_optT hT hO hfree hx hc χ (Term.eta (.root (.free d)) A hd)
  have q : Proof σ Γ [nameSent hT hO hx (Term.eta (.root (.free d)) A hd)]
      (WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free d)) A hd)
        (readSlot hT hO hfree hx hc χ)) :=
    Proof.conv key.symm (Proof.eqH_refl hO B u)
  refine .imp_elim (.imp_intro (Proof.ofSubset (fun ψ hψ => ?_) p)) q
  rcases List.mem_cons.mp hψ with rfl | h
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · rw [List.mem_singleton.mp h]
    exact List.mem_cons_self

/-- Two hypotheses discharged by proofs. -/
def cut2 {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ₁ φ₂ ψ : WFF σ Γ 0} (p : Proof σ Γ [φ₁, φ₂] ψ)
    (h₁ : Proof σ Γ Δ φ₁) (h₂ : Proof σ Γ Δ φ₂) : Proof σ Γ Δ ψ :=
  .imp_elim (.imp_elim (Proof.ofSubset (fun _ h => by simp at h) (.imp_intro (.imp_intro p))) h₂)
    h₁

/-- ⭐**Inside two identity views**: `P ≡ P'` in both, `P ≡ u` in the first and `P' ≡ u'` in the
    second give `u ≡ u'` outside. -/
def selfCombine (hO : ModalSys.Opt = true) {Γ : Ctx} [Γ.Presented] {x x' : VarSymb}
    (hy : ∃ X, Γ.witK .ident x = some X) (hy' : ∃ X, Γ.witK .ident x' = some X)
    (hy'' : ∃ X, (Γ.optInK .ident x).witK .ident x' = some X)
    {B : VarType} {a a' b b' : Ann B} (P : Term σ (Γ.optInT x) B a)
    (P' : Term σ (Γ.optInT x') B a') (u : Term σ Γ B b) (u' : Term σ Γ B b') :
    Proof σ Γ [.optx hO .ident x hy (.optx hO .ident x' hy''
          (eqH hO B (Term.mono (Ctx.le_optInT _ x') P)
            (Term.mono ((Ctx.le_optInT Γ x).optInT x') P'))),
        .optx hO .ident x hy (eqH hO B P (Term.mono (Ctx.le_optInT Γ x) u)),
        .optx hO .ident x' hy' (eqH hO B P' (Term.mono (Ctx.le_optInT Γ x') u'))]
      (eqH hO B u u') := by
  -- inside both views
  have inner2 : Proof σ ((Γ.optInT x).optInT x')
      [WFF.and (eqH hO B (Term.mono (Ctx.le_optInT _ x') P)
          (Term.mono ((Ctx.le_optInT Γ x).optInT x') P'))
        (WFF.mono ((Ctx.le_optInT Γ x).optInT x')
          (eqH hO B P' (Term.mono (Ctx.le_optInT Γ x') u'))),
        WFF.mono (Ctx.le_optInK (Γ.optInT x) .ident x')
          (eqH hO B P (Term.mono (Ctx.le_optInT Γ x) u))]
      (WFF.mono (Ctx.le_optInK (Γ.optInT x) .ident x')
        (WFF.mono (Ctx.le_optInT Γ x) (eqH hO B u u'))) := by
    refine Proof.conv ?_ (Proof.eqH_trans hO B (Proof.eqH_trans hO B
      (Proof.eqH_symm hO B (Proof.conv (eqH_mono hO _ B _ _)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))))
      (Proof.and_elim_l (Proof.lookup List.mem_cons_self)))
      (Proof.conv (eqH_mono hO _ B _ _) (Proof.and_elim_r (Proof.lookup List.mem_cons_self))))
    simp only [eqH_mono, Term.mono_mono]
  -- inside the first view
  have inner1 : Proof σ (Γ.optInT x)
      [WFF.and (.optx hO .ident x' hy''
          (eqH hO B (Term.mono (Ctx.le_optInT _ x') P)
            (Term.mono ((Ctx.le_optInT Γ x).optInT x') P')))
        (eqH hO B P (Term.mono (Ctx.le_optInT Γ x) u)),
        WFF.mono (Ctx.le_optInK Γ .ident x)
          (.optx hO .ident x' hy' (eqH hO B P' (Term.mono (Ctx.le_optInT Γ x') u')))]
      (WFF.mono (Ctx.le_optInK Γ .ident x) (eqH hO B u u')) := by
    have f := Proof.opt_fun hO .ident x' hy''
      (eqH hO B (Term.mono (Ctx.le_optInT _ x') P)
        (Term.mono ((Ctx.le_optInT Γ x).optInT x') P'))
      (WFF.mono ((Ctx.le_optInT Γ x).optInT x')
        (eqH hO B P' (Term.mono (Ctx.le_optInT Γ x') u')))
    have k := Proof.K_opt hO .ident x' hy''
      (Δ₁ := [eqH hO B P (Term.mono (Ctx.le_optInT Γ x) u)]) (Δ₂ := []) inner2
    exact Proof.opt_out hO .ident x' hy''
      (cut2 k (cut2 f (Proof.and_elim_l (Proof.lookup List.mem_cons_self))
          (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))
        (Proof.and_elim_r (Proof.lookup List.mem_cons_self)))
  have f0 := Proof.opt_fun hO .ident x hy
    (.optx hO .ident x' hy'' (eqH hO B (Term.mono (Ctx.le_optInT _ x') P)
      (Term.mono ((Ctx.le_optInT Γ x).optInT x') P')))
    (eqH hO B P (Term.mono (Ctx.le_optInT Γ x) u))
  have k0 := Proof.K_opt hO .ident x hy
    (Δ₁ := [.optx hO .ident x' hy' (eqH hO B P' (Term.mono (Ctx.le_optInT Γ x') u'))])
    (Δ₂ := []) inner1
  exact Proof.opt_out hO .ident x hy
    (cut2 k0 (cut2 f0 (Proof.lookup List.mem_cons_self)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))
      (Proof.lookup (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))

end TCanon

end V12M
