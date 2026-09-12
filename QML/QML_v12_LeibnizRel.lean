import QML.QML_v12_LeibnizProof

/-!
# QML v12 — Leibniz: substitutions with provably equal entries

`SubE.EqE E T e e'`: the entries are equal, or componentwise so at a product type, or term
entries whose equality (either way round) is among the hypotheses `E`.  The relation passes to
the `□` and `◇_w` views with the hypotheses filtered to those under the modality (`boxConjs`,
`diaConjs`), whose boxed forms the outer hypotheses prove (`Proof.boxedConj`, `Proof.diaedConj`,
found by search).
-/

namespace V12

def VarType.isProd : VarType → Bool
  | .VTypeProd _ _ => true
  | _ => false

theorem VarType.isProd_of_step {U T : VarType} {s : Step} (hs : s.isProd = true)
    (hst : U.step s = some T) : U.isProd = true := by
  cases s <;> cases U <;> (try cases hs) <;> (try cases hst) <;> rfl

/-! ## Hypotheses under a modality -/

def WFF.boxConjs {σ : Signature} {Γ : Ctx} : WFF σ Γ 0 → List (WFF σ Γ.boxIn 0)
  | .box ψ => ψ.conjuncts
  | _ => []

def WFF.unboxx? {σ : Signature} {Γ : Ctx} (w : VarSymb) :
    WFF σ Γ 0 → Option (WFF σ (Γ.diaIn w) 0)
  | .imp (.dia y _ (.imp ψ .bot)) .bot => if h : y = w then some (h ▸ ψ) else none
  | _ => none

def WFF.diaConjs {σ : Signature} {Γ : Ctx} (w : VarSymb) (a : WFF σ Γ 0) :
    List (WFF σ (Γ.diaIn w) 0) :=
  match a.unboxx? w with
  | some ψ => ψ.conjuncts
  | none => []

theorem WFF.unboxx?_boxx {σ : Signature} {Γ : Ctx} (w : VarSymb)
    (hw : ∃ X, Γ.ref w = some (.VTypeDia X)) (ψ : WFF σ (Γ.diaIn w) 0) :
    (WFF.boxx w hw ψ).unboxx? w = some ψ :=
  dif_pos rfl

theorem WFF.diaConjs_boxx {σ : Signature} {Γ : Ctx} (w : VarSymb)
    (hw : ∃ X, Γ.ref w = some (.VTypeDia X)) (ψ : WFF σ (Γ.diaIn w) 0) :
    (WFF.boxx w hw ψ).diaConjs w = ψ.conjuncts := by
  simp only [WFF.diaConjs, WFF.unboxx?_boxx]

theorem WFF.unboxx?_eq {σ : Signature} {Γ : Ctx} {w : VarSymb}
    (hw : ∃ X, Γ.ref w = some (.VTypeDia X)) :
    ∀ {a : WFF σ Γ 0} {ψ : WFF σ (Γ.diaIn w) 0}, a.unboxx? w = some ψ → a = WFF.boxx w hw ψ := by
  intro a ψ h
  unfold WFF.unboxx? at h
  split at h
  · split at h
    · rename_i hyw
      subst hyw
      cases h
      rfl
    · cases h
  · cases h

namespace Proof

variable {σ : Signature} {Γ : Ctx}

def boxConj {c : WFF σ Γ.boxIn 0} : (a : WFF σ Γ 0) → c ∈ a.boxConjs → Proof σ Γ [a] (.box c)
  | .box ψ, h => Proof.box_mono (Proof.conjunct ψ h)
  | .atom _, h | .eq _ _, h | .top, h | .bot, h | .and _ _, h | .or _ _, h | .imp _ _, h
  | .all _ _, h | .ex _ _, h | .dia _ _ _, h => absurd h List.not_mem_nil

/-- ⭐The hypotheses prove the box of each conjunct under a box among them. -/
def boxedConj : (E : List (WFF σ Γ 0)) → {c : WFF σ Γ.boxIn 0} →
    c ∈ E.flatMap WFF.boxConjs → Proof σ Γ E (.box c)
  | [], _, h => absurd h List.not_mem_nil
  | a :: E, c, h =>
      if ha : c ∈ a.boxConjs then Proof.weakenTail E (Proof.boxConj a ha)
      else Proof.weak a (boxedConj E ((List.mem_append.mp h).resolve_left ha))

def diaConj (w : VarSymb) (hw : ∃ X, Γ.ref w = some (.VTypeDia X))
    {c : WFF σ (Γ.diaIn w) 0} (a : WFF σ Γ 0) (h : c ∈ a.diaConjs w) :
    Proof σ Γ [a] (WFF.boxx w hw c) := by
  unfold WFF.diaConjs at h
  split at h
  · rename_i ψ ho
    rw [WFF.unboxx?_eq hw ho]
    exact Proof.boxx_mono w hw (Proof.conjunct ψ h)
  · exact absurd h List.not_mem_nil

/-- ⭐The hypotheses prove the `□_w` of each conjunct under a `□_w` among them. -/
def diaedConj (w : VarSymb) (hw : ∃ X, Γ.ref w = some (.VTypeDia X)) :
    (E : List (WFF σ Γ 0)) → {c : WFF σ (Γ.diaIn w) 0} →
    c ∈ E.flatMap (WFF.diaConjs w) → Proof σ Γ E (WFF.boxx w hw c)
  | [], _, h => absurd h List.not_mem_nil
  | a :: E, c, h =>
      if ha : c ∈ a.diaConjs w then Proof.weakenTail E (Proof.diaConj w hw a ha)
      else Proof.weak a (diaedConj w hw E ((List.mem_append.mp h).resolve_left ha))

end Proof

/-! ## Provably equal entries -/

namespace SubE

variable {σ : Signature} {Δ : Ctx}

inductive EqE (E : List (WFF σ Δ 0)) : VarType → SubE σ Δ → SubE σ Δ → Prop
  | same {T : VarType} (e : SubE σ Δ) : EqE E T e e
  | prod {A B : VarType} {e e' : SubE σ Δ} :
      EqE E A (e.proj .fst) (e'.proj .fst) → EqE E B (e.proj .snd) (e'.proj .snd) →
      EqE E (.VTypeProd A B) e e'
  | mem {T : VarType} {a : Ann T} (t s : Term σ Δ T a) : T.isProd = false →
      eqRec T t s ∈ E → EqE E T (.tm t) (.tm s)
  | memSymm {T : VarType} {a : Ann T} (t s : Term σ Δ T a) : T.isProd = false →
      eqRec T s t ∈ E → EqE E T (.tm t) (.tm s)

namespace EqE

variable {E : List (WFF σ Δ 0)}

theorem symm {T : VarType} {e e' : SubE σ Δ} (h : EqE E T e e') : EqE E T e' e := by
  induction h with
  | same e => exact .same e
  | prod _ _ ih₁ ih₂ => exact .prod ih₁ ih₂
  | mem t s hT hm => exact .memSymm s t hT hm
  | memSymm t s hT hm => exact .mem s t hT hm

theorem proj_step {U T : VarType} {s : Step} {e e' : SubE σ Δ} (h : EqE E U e e')
    (hs : s.isProd = true) (hst : U.step s = some T) : EqE E T (e.proj s) (e'.proj s) := by
  cases h with
  | same => exact .same _
  | prod h₁ h₂ => cases s <;> (try cases hs) <;> cases hst <;> assumption
  | mem _ _ hT _ => exact nomatch (VarType.isProd_of_step hs hst).symm.trans hT
  | memSymm _ _ hT _ => exact nomatch (VarType.isProd_of_step hs hst).symm.trans hT

theorem sub {E' : List (WFF σ Δ 0)} (hE : ∀ φ ∈ E, φ ∈ E') {T : VarType} {e e' : SubE σ Δ}
    (h : EqE E T e e') : EqE E' T e e' := by
  induction h with
  | same e => exact .same e
  | prod _ _ ih₁ ih₂ => exact .prod ih₁ ih₂
  | mem t s hT hm => exact .mem t s hT (hE _ hm)
  | memSymm t s hT hm => exact .memSymm t s hT (hE _ hm)

theorem mono {Δ' : Ctx} (hle : Δ.Le Δ') {T : VarType} {e e' : SubE σ Δ} (h : EqE E T e e') :
    EqE (E.map (WFF.mono hle)) T (e.mono hle) (e'.mono hle) := by
  induction h with
  | same e => exact .same _
  | prod _ _ ih₁ ih₂ =>
      refine .prod ?_ ?_
      · rw [SubE.proj_mono, SubE.proj_mono]
        exact ih₁
      · rw [SubE.proj_mono, SubE.proj_mono]
        exact ih₂
  | mem t s hT hm => exact .mem _ _ hT (List.mem_map.mpr ⟨_, hm, eqRec_mono hle _ t s⟩)
  | memSymm t s hT hm => exact .memSymm _ _ hT (List.mem_map.mpr ⟨_, hm, eqRec_mono hle _ s t⟩)

end EqE

/-- Hypotheses containing all conjuncts of `t = s` relate `t` and `s`. -/
theorem eqE_of_conj {L : List (WFF σ Δ 0)} : (T : VarType) → {a : Ann T} →
    (t s : Term σ Δ T a) → (∀ c ∈ (eqRec T t s : WFF σ Δ 0).conjuncts, c ∈ L) →
    EqE L T (.tm t) (.tm s)
  | .Var, .var, t, s, h =>
      .mem t s rfl (h _ (by rw [eqRec_Var]; exact List.mem_singleton_self _))
  | .VTypeOne, .one, .unit, .unit, h => .mem _ _ rfl (h _ (List.mem_singleton_self _))
  | .VTypeProd A B, .prod _ _, .pair t₁ t₂, .pair s₁ s₂, h =>
      .prod (eqE_of_conj A t₁ s₁ fun c hc => h c (List.mem_append_left _ hc))
        (eqE_of_conj B t₂ s₂ fun c hc => h c (List.mem_append_right _ hc))
  | .VTypeBox _, .box _, .boxtm _, .boxtm _, h => .mem _ _ rfl (h _ (List.mem_singleton_self _))
  | .VTypeDia _, .dia _ _, .diatm _ _ _, .diatm _ _ _, h =>
      .mem _ _ rfl (h _ (List.mem_singleton_self _))

theorem eqE_of_conj' {L : List (WFF σ Δ 0)} (T : VarType) {a : Ann T} (t s : Term σ Δ T a)
    (h : ∀ c ∈ (eqRec T s t : WFF σ Δ 0).conjuncts, c ∈ L) : EqE L T (.tm t) (.tm s) :=
  (eqE_of_conj T s t h).symm

theorem EqE.unbox {E : List (WFF σ Δ 0)} {A : VarType} {e e' : SubE σ Δ}
    (h : EqE E (.VTypeBox A) e e') : EqE (E.flatMap WFF.boxConjs) A e.unbox e'.unbox := by
  cases h with
  | same => exact .same _
  | mem t s _ hm =>
      cases t with
      | boxtm t' =>
          cases s with
          | boxtm s' => exact eqE_of_conj A t' s' fun c hc => List.mem_flatMap.mpr ⟨_, hm, hc⟩
  | memSymm t s _ hm =>
      cases t with
      | boxtm t' =>
          cases s with
          | boxtm s' => exact eqE_of_conj' A t' s' fun c hc => List.mem_flatMap.mpr ⟨_, hm, hc⟩

theorem EqE.diaBody {E : List (WFF σ Δ 0)} {X : VarType} {w : VarSymb} {e e' : SubE σ Δ}
    (h : EqE E (.VTypeDia X) e e') (hw : e.idxAlong [] = w) :
    EqE (E.flatMap (WFF.diaConjs w)) X (e.diaBody w) (e'.diaBody w) := by
  cases h with
  | same => exact .same _
  | mem t s _ hm =>
      cases t with
      | diatm y hy t' =>
          cases s with
          | diatm _ hy' s' =>
              have hyw : y = w := hw
              subst hyw
              rw [SubE.diaBody_diatm, SubE.diaBody_diatm]
              exact eqE_of_conj X t' s' fun c hc => List.mem_flatMap.mpr ⟨_, hm, by
                change c ∈ (WFF.boxx y hy (eqRec X t' s')).diaConjs y
                rw [WFF.diaConjs_boxx]
                exact hc⟩
  | memSymm t s _ hm =>
      cases t with
      | diatm y hy t' =>
          cases s with
          | diatm _ hy' s' =>
              have hyw : y = w := hw
              subst hyw
              rw [SubE.diaBody_diatm, SubE.diaBody_diatm]
              exact eqE_of_conj' X t' s' fun c hc => List.mem_flatMap.mpr ⟨_, hm, by
                change c ∈ (WFF.boxx y hy' (eqRec X s' t')).diaConjs y
                rw [WFF.diaConjs_boxx]
                exact hc⟩

end SubE

/-- ⭐A base-typed equality between provably equal entries, found by search. -/
def Proof.eqE_var {σ : Signature} {Δ : Ctx} [Δ.NoSlots] {E : List (WFF σ Δ 0)}
    {e e' : SubE σ Δ} (h : SubE.EqE E .Var e e') (he : e.OkRef .Var) (he' : e'.OkRef .Var) :
    Proof σ Δ E (.eq (e.toVar he) (e'.toVar he')) :=
  if h₁ : e.toVar he = e'.toVar he' then
    Proof.conv (congrArg (WFF.eq (e.toVar he)) h₁) (Proof.eq_intro _)
  else if h₂ : WFF.eq (e.toVar he) (e'.toVar he') ∈ E then Proof.lookup h₂
  else if h₃ : WFF.eq (e'.toVar he') (e.toVar he) ∈ E then
    Proof.eq_symm_base (Proof.lookup h₃)
  else False.elim (by
    cases h with
    | same => exact h₁ rfl
    | @mem _ a t s _ hm =>
        cases a
        rw [eqRec_Var] at hm
        exact h₂ (by rw [SubE.toVar_tmSelf, SubE.toVar_tmSelf]; exact hm)
    | @memSymm _ a t s _ hm =>
        cases a
        rw [eqRec_Var] at hm
        exact h₃ (by rw [SubE.toVar_tmSelf, SubE.toVar_tmSelf]; exact hm))

/-! ## Provably equal substitutions -/

namespace Subst

variable {σ : Signature} {Δ : Ctx}

def EqRel (E : List (WFF σ Δ 0)) (Γ : Ctx) (θ θ' : Subst σ Δ) : Prop :=
  ∀ v T, Γ.ref v = some T → SubE.EqE E T (θ.at v) (θ'.at v)

theorem EqRel.symm {E : List (WFF σ Δ 0)} {Γ : Ctx} {θ θ' : Subst σ Δ} (h : EqRel E Γ θ θ') :
    EqRel E Γ θ' θ :=
  fun v T hv => (h v T hv).symm

theorem eqRel_of {E : List (WFF σ Δ 0)} {Γ : Ctx} {θ θ' : Subst σ Δ}
    (hvis : ∀ v T, v.lastProd = false → Γ v = some T → SubE.EqE E T (θ v) (θ' v)) :
    EqRel E Γ θ θ' := by
  intro v
  induction v with
  | root r => intro T hv; exact hvis _ _ rfl hv
  | step v s ih =>
      intro T hv
      simp only [Ctx.ref] at hv
      simp only [Subst.at]
      split_ifs at hv ⊢ with hs
      · cases hU : Γ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U =>
            rw [hU] at hv
            exact (ih U hU).proj_step hs hv
      · exact hvis _ _ (show (VarSymb.step v s).lastProd = false from Bool.eq_false_iff.mpr hs) hv

theorem eqRel_box {E : List (WFF σ Δ 0)} {Γ : Ctx} {θ θ' : Subst σ Δ} (h : EqRel E Γ θ θ') :
    EqRel (E.flatMap WFF.boxConjs) Γ.boxIn θ.box θ'.box := by
  refine eqRel_of ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      change (match Γ.ref u with | some (.VTypeBox A) => some A | _ => none) = some T at hv
      cases hu : Γ.ref u with
      | none => rw [hu] at hv; cases hv
      | some U =>
          rw [hu] at hv
          cases U <;> try cases hv
          exact (h u _ hu).unbox
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv

theorem eqRel_dia {E : List (WFF σ Δ 0)} {Γ : Ctx} {θ θ' : Subst σ Δ} (h : EqRel E Γ θ θ')
    {x w : VarSymb} (hw : (θ.at x).idxAlong [] = w) :
    EqRel (E.flatMap (WFF.diaConjs w) ++
        (E.flatMap WFF.boxConjs).map (WFF.mono (Ctx.le_boxIn_diaIn Δ w)))
      (Γ.diaIn x) (θ.dia x w) (θ'.dia x w) := by
  refine eqRel_of ?_
  intro v T _ hv
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with hux
      · subst hux
        cases hx : Γ.ref u with
        | none => rw [hx] at hv; cases hv
        | some U =>
            rw [hx] at hv
            cases U <;> try cases hv
            change SubE.EqE _ _ (if u = u then (θ.at u).diaBody w else SubE.hide)
              (if u = u then (θ'.at u).diaBody w else SubE.hide)
            rw [if_pos rfl, if_pos rfl]
            exact ((h u _ hx).diaBody hw).sub fun φ hφ => List.mem_append_left _ hφ
  | .step u .box =>
      change (match Γ.ref u with | some (.VTypeBox A) => some A | _ => none) = some T at hv
      cases hu : Γ.ref u with
      | none => rw [hu] at hv; cases hv
      | some U =>
          rw [hu] at hv
          cases U <;> try cases hv
          exact ((h u _ hu).unbox.mono _).sub fun φ hφ => List.mem_append_right _ hφ
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv

theorem eqRel_toFree {E : List (WFF σ Δ 0)} {Γ : Ctx} {θ θ' : Subst σ Δ} (h : EqRel E Γ θ θ')
    {d u : ℕ} (T : VarType) (hh : Δ (.root (.free u)) = none) :
    EqRel (E.map (WFF.mono (Ctx.le_insert hh T))) (Γ.insert (.bnd d) T) (θ.toFree d u T hh)
      (θ'.toFree d u T hh) := by
  refine eqRel_of ?_
  intro v U hlp hv
  by_cases hvr : v = .root (.bnd d)
  · rw [show θ.toFree d u T hh v = .ren (.root (.free u)) from if_pos hvr,
      show θ'.toFree d u T hh v = .ren (.root (.free u)) from if_pos hvr]
    exact .same _
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    rw [show θ.toFree d u T hh v = (θ v).mono (Ctx.le_insert hh T) from if_neg hvr,
      show θ'.toFree d u T hh v = (θ' v).mono (Ctx.le_insert hh T) from if_neg hvr]
    have h₁ := h v U ((Ctx.ref_nonprod Γ hlp).trans hv')
    rw [Subst.at_nonprod θ hlp, Subst.at_nonprod θ' hlp] at h₁
    exact h₁.mono _

end Subst

end V12
