import QML.QML_v12m_EqH
import QML.QML_v12m_LeibnizProof
import QML.QML_v12m_LeibnizSpine

/-!
# QML v12m — Leibniz along `≡`: substitutions with provably `≡` entries

The relation the Leibniz induction along `≡` (`QML_v12m_LeibnizH`) carries, with the box view of
possible objects on (`Opt`).  As the K-only one (`QML_v12_LeibnizRel`), with two differences:
* entries are compared by `≡`, which relates terms of different annotations, so the two
  substitutions may send a possible object to different witnesses;
* witnesses have entries too (`Subst.wit`), compared by `witEq`: what `≡` at a `◇` type says in
  the `□` view (`eqH_dia`).

The relation is **oriented**: `Proof.substEqH` proves both directions at once, so neither `≡` nor
the relation needs symmetry.  It passes to the views a formula can enter: `□` (the hypotheses
under a box, `boxConjs`), a fresh eigenvariable (`toFree`), and the views of a witness or a
possible object, with one witness (`eqRelH_optIn`, `eqRelH_dia`) or two opened together
(`eqRelH_optIn₂`, `eqRelH_dia₂`).
-/

namespace V12M

/- M1's construction is for K and D with `Opt` on: T off (`ModalSys.NoT`) until M2 step 6
   generalises it, so the class is in scope throughout. -/
set_option linter.unusedSectionVars false

variable [ModalSys] [ModalSys.NoT]

theorem ModalSys.T_false_of_opt (_hO : ModalSys.Opt = true) : ModalSys.T = false :=
  ModalSys.NoT.noT

theorem ModalSys.Four_false_of_opt (hO : ModalSys.Opt = true) : ModalSys.Four = false := by
  cases h : ModalSys.Four
  · rfl
  · exact absurd (ModalSys.noOpt_of_Four h) (by simp [hO])

/-- A product type. -/
def VarType.isProd : VarType → Bool
  | .VTypeProd _ _ => true
  | _ => false

theorem VarType.isProd_of_step (hT : ModalSys.T = false) {U T : VarType} {s : Step}
    (hs : s.isStruct = true) (hst : U.step s = some T) : U.isProd = true := by
  cases s <;> cases U <;> (try cases hs) <;> (try cases hst) <;> (try rfl)
  exact absurd (VarType.step_here hst).1 (by simp [hT])

/-! ## Hypotheses under a box -/

/-- The conjuncts under a box. -/
def WFF.boxConjs {σ : Signature} {Γ : Ctx} : WFF σ Γ 0 → List (WFF σ Γ.boxIn 0)
  | .box ψ => ψ.conjuncts
  | _ => []

namespace Proof

variable {σ : Signature} {Γ : Ctx}

def boxConj {c : WFF σ Γ.boxIn 0} : (a : WFF σ Γ 0) → c ∈ a.boxConjs → Proof σ Γ [a] (.box c)
  | .box ψ, h => Proof.box_mono (Proof.conjunct ψ h)
  | .atom _, h | .eq _ _, h | .top, h | .bot, h | .and _ _, h | .or _ _, h | .imp _ _, h
  | .all _ _, h | .ex _ _, h | .dia _ _ _, h | .here _ _ _ _, h | .back _ _ _ _, h
  | .retS _ _ _ _, h | .retxS _ _ _ _ _ _, h | .link _ _ _ _, h | .linkx _ _ _ _ _ _, h
  | .optx _ _ _ _ _, h => absurd h List.not_mem_nil

/-- ⭐The hypotheses prove the box of each conjunct under a box among them. -/
def boxedConj : (E : List (WFF σ Γ 0)) → {c : WFF σ Γ.boxIn 0} →
    c ∈ E.flatMap WFF.boxConjs → Proof σ Γ E (.box c)
  | [], _, h => absurd h List.not_mem_nil
  | a :: E, c, h =>
      if ha : c ∈ a.boxConjs then Proof.weakenTail E (Proof.boxConj a ha)
      else Proof.weak a (boxedConj E ((List.mem_append.mp h).resolve_left ha))

end Proof

/-! ## Two witnesses' equality, weakened -/

/-- Weakening commutes with `witEq`. -/
theorem witEq_mono {σ : Signature} {d : ℕ} (hO : ModalSys.Opt = true) {Δ Δ' : Ctx}
    (hle : Δ.Le Δ') (X : VarType) {z z' : VarSymb} (hz : ∃ Z, Δ.wit z = some Z)
    (hz' : ∃ Z, Δ.wit z' = some Z) {a b : Ann X} (c : Term σ (Δ.optIn z) X a)
    (c' : Term σ (Δ.optIn z') X b) :
    WFF.mono hle (witEq hO X hz hz' c c' : WFF σ Δ d) =
      witEq hO X (hz.imp fun _ h => hle.wit _ _ h) (hz'.imp fun _ h => hle.wit _ _ h)
        (Term.mono (hle.optIn z) c) (Term.mono (hle.optIn z') c') := by
  change WFF.imp (WFF.or _ _) (WFF.optx _ .arrow _ _ (WFF.optx _ .arrow _ _
    (WFF.mono ((hle.optIn z).optIn z') (eqH hO X _ _)))) = _
  rw [eqH_mono]
  change _ = WFF.imp (WFF.or _ _) (WFF.optx _ .arrow _ _ (WFF.optx _ .arrow _ _
    (eqH hO X (Term.mono _ (Term.mono (hle.optIn z) c))
      (Term.mono _ (Term.mono (hle.optIn z') c')))))
  simp only [Term.mono_mono]
  rfl

/-- A possible entry's witness entry, under `Opt`. -/
theorem SubE.toWit_diatm {σ : Signature} {Δ : Ctx} (hO : ModalSys.Opt = true) {x : VarSymb}
    (hx : ∃ X, Δ.ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (b : Term σ (Δ.diaIn x) A a) :
    SubE.toWit (.tm (.diatm x hx b)) = WitE.tm x (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx) b) :=
  dif_pos hO

/-! ## Provably `≡` entries -/

/-- Term entries that are equal, componentwise so at a product, or whose `≡` is a hypothesis. -/
inductive SubE.EqH {σ : Signature} {Δ : Ctx} (hO : ModalSys.Opt = true) (E : List (WFF σ Δ 0)) :
    VarType → SubE σ Δ → SubE σ Δ → Prop
  | same {T : VarType} (e : SubE σ Δ) : EqH hO E T e e
  | prod {A B : VarType} {e e' : SubE σ Δ} :
      EqH hO E A (e.proj .fst) (e'.proj .fst) → EqH hO E B (e.proj .snd) (e'.proj .snd) →
      EqH hO E (.VTypeProd A B) e e'
  | mem {T : VarType} {a b : Ann T} (t : Term σ Δ T a) (s : Term σ Δ T b) : T.isProd = false →
      eqH hO T t s ∈ E → EqH hO E T (.tm t) (.tm s)

/-- Witness entries that are equal, or whose `witEq` is a hypothesis. -/
inductive WitE.EqH {σ : Signature} {Δ : Ctx} (hO : ModalSys.Opt = true) (E : List (WFF σ Δ 0)) :
    VarType → WitE σ Δ → WitE σ Δ → Prop
  | same {X : VarType} (w : WitE σ Δ) : EqH hO E X w w
  | mem {X : VarType} {z z' : VarSymb} (hz : ∃ Z, Δ.wit z = some Z)
      (hz' : ∃ Z, Δ.wit z' = some Z) {a b : Ann X} (c : Term σ (Δ.optIn z) X a)
      (c' : Term σ (Δ.optIn z') X b) :
      witEq hO X hz hz' c c' ∈ E → EqH hO E X (.tm z c) (.tm z' c')

section Rel

variable {σ : Signature} {Δ : Ctx} {hO : ModalSys.Opt = true} {E : List (WFF σ Δ 0)}

theorem SubE.EqH.sub {E' : List (WFF σ Δ 0)} (hE : ∀ φ ∈ E, φ ∈ E') {T : VarType}
    {e e' : SubE σ Δ} (h : SubE.EqH hO E T e e') : SubE.EqH hO E' T e e' := by
  induction h with
  | same e => exact .same e
  | prod _ _ ih₁ ih₂ => exact .prod ih₁ ih₂
  | mem t s hT hm => exact .mem t s hT (hE _ hm)

theorem WitE.EqH.sub {E' : List (WFF σ Δ 0)} (hE : ∀ φ ∈ E, φ ∈ E') {X : VarType}
    {w w' : WitE σ Δ} (h : WitE.EqH hO E X w w') : WitE.EqH hO E' X w w' := by
  cases h with
  | same => exact .same _
  | mem hz hz' c c' hm => exact .mem hz hz' c c' (hE _ hm)

theorem SubE.EqH.proj_step {U T : VarType} {s : Step} {e e' : SubE σ Δ}
    (h : SubE.EqH hO E U e e') (hs : s.isStruct = true) (hst : U.step s = some T) :
    SubE.EqH hO E T (e.proj s) (e'.proj s) := by
  cases h with
  | same => exact .same _
  | prod h₁ h₂ => cases s <;> (try cases hs) <;> cases hst <;> assumption
  | mem _ _ hT _ =>
      exact nomatch (VarType.isProd_of_step (ModalSys.T_false_of_opt hO) hs hst).symm.trans hT

theorem SubE.EqH.mono {Δ' : Ctx} (hle : Δ.Le Δ') {T : VarType} {e e' : SubE σ Δ}
    (h : SubE.EqH hO E T e e') :
    SubE.EqH hO (E.map (WFF.mono hle)) T (e.mono hle) (e'.mono hle) := by
  induction h with
  | same e => exact .same _
  | prod _ _ ih₁ ih₂ =>
      refine .prod ?_ ?_
      · rw [SubE.proj_mono, SubE.proj_mono]
        exact ih₁
      · rw [SubE.proj_mono, SubE.proj_mono]
        exact ih₂
  | mem t s hT hm => exact .mem _ _ hT (List.mem_map.mpr ⟨_, hm, eqH_mono hO hle _ t s⟩)

theorem WitE.EqH.mono {Δ' : Ctx} (hle : Δ.Le Δ') {X : VarType} {w w' : WitE σ Δ}
    (h : WitE.EqH hO E X w w') :
    WitE.EqH hO (E.map (WFF.mono hle)) X (w.mono hle) (w'.mono hle) := by
  cases h with
  | same => exact .same _
  | mem hz hz' c c' hm =>
      exact .mem (hz.imp fun _ h => hle.wit _ _ h) (hz'.imp fun _ h => hle.wit _ _ h) _ _
        (List.mem_map.mpr ⟨_, hm, witEq_mono hO hle X hz hz' c c'⟩)

/-- Hypotheses containing all conjuncts of `t ≡ s` relate `t` and `s`. -/
theorem SubE.eqH_of_conj {L : List (WFF σ Δ 0)} : (T : VarType) → {a b : Ann T} →
    (t : Term σ Δ T a) → (s : Term σ Δ T b) →
    (∀ c ∈ (eqH hO T t s : WFF σ Δ 0).conjuncts, c ∈ L) → SubE.EqH hO L T (.tm t) (.tm s)
  | .Var, .var, .var, t, s, h =>
      .mem t s rfl (h _ (by rw [eqH_Var]; exact List.mem_singleton_self _))
  | .VTypeOne, _, _, t, s, h => .mem t s rfl (h _ (List.mem_singleton_self _))
  | .VTypeProd A B, .prod _ _, .prod _ _, .pair t₁ t₂, .pair s₁ s₂, h =>
      .prod (SubE.eqH_of_conj A t₁ s₁ fun c hc => h c (List.mem_append_left _ hc))
        (SubE.eqH_of_conj B t₂ s₂ fun c hc => h c (List.mem_append_right _ hc))
  | .VTypeBox _, .box _, .box _, .boxtm _, .boxtm _, h =>
      .mem _ _ rfl (h _ (List.mem_singleton_self _))
  | .VTypeDia _, .dia _ _, .dia _ _, .diatm _ _ _, .diatm _ _ _, h =>
      .mem _ _ rfl (h _ (List.mem_singleton_self _))

theorem SubE.EqH.unbox {A : VarType} {e e' : SubE σ Δ} (h : SubE.EqH hO E (.VTypeBox A) e e') :
    SubE.EqH hO (E.flatMap WFF.boxConjs) A e.unbox e'.unbox := by
  cases h with
  | same => exact .same _
  | mem t s _ hm =>
      cases t with
      | boxtm t' =>
          cases s with
          | boxtm s' => exact SubE.eqH_of_conj A t' s' fun c hc => List.mem_flatMap.mpr ⟨_, hm, hc⟩

theorem SubE.EqH.toWit {X : VarType} {e e' : SubE σ Δ} (h : SubE.EqH hO E (.VTypeDia X) e e') :
    WitE.EqH hO (E.flatMap WFF.boxConjs) X e.toWit e'.toWit := by
  cases h with
  | same => exact .same _
  | mem t s _ hm =>
      cases t with
      | diatm x hx t' =>
          cases s with
          | diatm x' hx' s' =>
              rw [SubE.toWit_diatm hO, SubE.toWit_diatm hO]
              exact .mem (Ctx.boxIn_wit_of hO hx) (Ctx.boxIn_wit_of hO hx') _ _
                (List.mem_flatMap.mpr ⟨_, hm, List.mem_singleton_self _⟩)

end Rel

/-- ⭐A base-typed `≡` between related entries, found by search. -/
def Proof.eqH_var {σ : Signature} {Δ : Ctx} [Δ.NoSlots] {hO : ModalSys.Opt = true}
    {E : List (WFF σ Δ 0)} {e e' : SubE σ Δ} (h : SubE.EqH hO E .Var e e') (he : e.OkRef .Var)
    (he' : e'.OkRef .Var) : Proof σ Δ E (.eq (e.toVar he) (e'.toVar he')) :=
  if h₁ : e.toVar he = e'.toVar he' then
    Proof.conv (congrArg (WFF.eq (e.toVar he)) h₁) (Proof.eq_intro _)
  else if h₂ : WFF.eq (e.toVar he) (e'.toVar he') ∈ E then Proof.lookup h₂
  else False.elim (by
    cases h with
    | same => exact h₁ rfl
    | @mem _ a b t s _ hm =>
        cases a
        cases b
        rw [eqH_Var] at hm
        exact h₂ (by rw [SubE.toVar_tmSelf, SubE.toVar_tmSelf]; exact hm))

/-! ## Related substitutions -/

/-- Two substitutions whose entries, and whose witnesses' entries, are provably `≡`. -/
structure Subst.EqRelH {σ : Signature} {Δ : Ctx} (hO : ModalSys.Opt = true)
    (E : List (WFF σ Δ 0)) (Γ : Ctx) (θ θ' : Subst σ Δ) : Prop where
  ty : ∀ v T, Γ.ref v = some T → SubE.EqH hO E T (θ.at v) (θ'.at v)
  wit : ∀ y X, Γ.wit y = some X → WitE.EqH hO E X (θ.wit y) (θ'.wit y)

namespace Subst

variable {σ : Signature} {Δ : Ctx} {hO : ModalSys.Opt = true} {E : List (WFF σ Δ 0)}

theorem eqRelH_of {Γ : Ctx} {θ θ' : Subst σ Δ}
    (hvis : ∀ v T, v.lastProj = false → Γ v = some T → SubE.EqH hO E T (θ v) (θ' v))
    (hwit : ∀ y X, Γ.wit y = some X → WitE.EqH hO E X (θ.wit y) (θ'.wit y)) :
    EqRelH hO E Γ θ θ' := by
  refine ⟨?_, hwit⟩
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
      · exact hvis _ _ (show (VarSymb.step v s).lastProj = false from Bool.eq_false_iff.mpr hs) hv

theorem eqRelH_box {Γ : Ctx} {θ θ' : Subst σ Δ} (h : EqRelH hO E Γ θ θ') :
    EqRelH hO (E.flatMap WFF.boxConjs) Γ.boxIn θ.box θ'.box := by
  refine eqRelH_of ?_ fun y X hy => ?_
  · intro v T _ hv
    match v with
    | .step u .box => exact (h.ty u _ (Ctx.boxIn_box hv).2).unbox
    | .step u .keep =>
        exact absurd (Ctx.boxIn_keep hv).1 (by simp [ModalSys.Four_false_of_opt hO])
    | .root _ => cases hv
    | .step _ .fst => cases hv
    | .step _ .snd => cases hv
    | .step _ .dia => cases hv
    | .step _ .here => cases hv
  · exact (h.ty y _ (Ctx.boxIn_wit.mp hy).2).toWit

theorem eqRelH_toFree {Γ : Ctx} {θ θ' : Subst σ Δ} (h : EqRelH hO E Γ θ θ') {d u : ℕ}
    (T : VarType) (hh : Δ (.root (.free u)) = none) :
    EqRelH hO (E.map (WFF.mono (Ctx.le_insert hh T))) (Γ.insert (.bnd d) T) (θ.toFree d u T hh)
      (θ'.toFree d u T hh) := by
  refine eqRelH_of ?_ fun y X hy => (h.wit y X hy).mono _
  intro v U hlp hv
  by_cases hvr : v = .root (.bnd d)
  · rw [show θ.toFree d u T hh v = .ren (.root (.free u)) from if_pos hvr,
      show θ'.toFree d u T hh v = .ren (.root (.free u)) from if_pos hvr]
    exact .same _
  · have hv' : Γ v = some U := Ctx.insert_ne_some hv hvr
    rw [show θ.toFree d u T hh v = (θ v).mono (Ctx.le_insert hh T) from if_neg hvr,
      show θ'.toFree d u T hh v = (θ' v).mono (Ctx.le_insert hh T) from if_neg hvr]
    have h₁ := h.ty v U ((Ctx.ref_nonproj Γ hlp).trans hv')
    rw [Subst.at_nonproj θ hlp, Subst.at_nonproj θ' hlp] at h₁
    exact h₁.mono _

/-- Into the view of a witness with one entry under both substitutions. -/
theorem eqRelH_optIn {Γ : Ctx} {θ θ' : Subst σ Δ} (h : EqRelH hO E Γ θ θ') {y z : VarSymb}
    (hsame : θ.wit y = θ'.wit y) :
    EqRelH hO (E.map (WFF.mono (Ctx.le_optIn Δ z))) (Γ.optIn y) (θ.optIn y z) (θ'.optIn y z) := by
  refine eqRelH_of ?_ fun y' X hy' => (h.wit y' X hy').mono _
  intro v T hlp hv
  by_cases hc : v = .step y .dia
  · subst hc
    rw [Subst.optIn_content, Subst.optIn_content, hsame]
    exact .same _
  · rw [Subst.optIn_ne _ _ hc, Subst.optIn_ne _ _ hc]
    rw [Ctx.optIn_ne hc] at hv
    have h₁ := h.ty v T ((Ctx.ref_nonproj Γ hlp).trans hv)
    rw [Subst.at_nonproj θ hlp, Subst.at_nonproj θ' hlp] at h₁
    exact h₁.mono _

/-- ⭐Into the view of a witness with two entries, both opened: the contents are related by
    their `≡`, which the caller supplies as hypotheses. -/
theorem eqRelH_optIn₂ {Γ : Ctx} {θ θ' : Subst σ Δ} (h : EqRelH hO E Γ θ θ') {y z₁ z₂ : VarSymb}
    {X : VarType} (hy : Γ.wit y = some X) {a₁ a₂ : Ann X} {c₁ : Term σ (Δ.optIn z₁) X a₁}
    {c₂ : Term σ (Δ.optIn z₂) X a₂} (hw₁ : θ.wit y = .tm z₁ c₁) (hw₂ : θ'.wit y = .tm z₂ c₂) :
    EqRelH hO ((eqH hO X (Term.mono (Ctx.le_optIn _ z₂) c₁)
          (Term.mono ((Ctx.le_optIn Δ z₁).optIn z₂) c₂) : WFF σ _ 0).conjuncts ++
        E.map (WFF.mono ((Ctx.le_optIn Δ z₁).trans (Ctx.le_optIn _ z₂))))
      (Γ.optIn y) ((θ.optIn y z₁).mono (Ctx.le_optIn _ z₂))
      ((θ'.optIn y z₂).mono ((Ctx.le_optIn Δ z₁).optIn z₂)) := by
  refine eqRelH_of ?_ fun y' X' hy' => ?_
  · intro v T hlp hv
    by_cases hc : v = .step y .dia
    · subst hc
      rw [Ctx.optIn_content hy] at hv
      cases hv
      change SubE.EqH _ _ _ ((θ.optIn y z₁ (.step y .dia)).mono _)
        ((θ'.optIn y z₂ (.step y .dia)).mono _)
      rw [Subst.optIn_content, Subst.optIn_content, hw₁, hw₂]
      change SubE.EqH _ _ _ (SubE.mono _ (dite (z₁ = z₁) _ _)) (SubE.mono _ (dite (z₂ = z₂) _ _))
      rw [dif_pos rfl, dif_pos rfl]
      change SubE.EqH _ _ _ (SubE.tm (Term.mono _ (Term.mono _ c₁)))
        (SubE.tm (Term.mono _ (Term.mono _ c₂)))
      rw [Term.mono_mono, Term.mono_mono]
      exact SubE.eqH_of_conj X _ _ fun c hc => List.mem_append_left _ hc
    · change SubE.EqH _ _ _ ((θ.optIn y z₁ v).mono _) ((θ'.optIn y z₂ v).mono _)
      rw [Subst.optIn_ne _ _ hc, Subst.optIn_ne _ _ hc, SubE.mono_mono, SubE.mono_mono]
      rw [Ctx.optIn_ne hc] at hv
      have h₁ := h.ty v T ((Ctx.ref_nonproj Γ hlp).trans hv)
      rw [Subst.at_nonproj θ hlp, Subst.at_nonproj θ' hlp] at h₁
      exact (h₁.mono _).sub fun φ hφ => List.mem_append_right _ hφ
  · change WitE.EqH _ _ _ (((θ.wit y').mono (Ctx.le_optIn Δ z₁)).mono (Ctx.le_optIn _ z₂))
      (((θ'.wit y').mono (Ctx.le_optIn Δ z₂)).mono ((Ctx.le_optIn Δ z₁).optIn z₂))
    rw [WitE.mono_mono, WitE.mono_mono]
    exact ((h.wit y' X' hy').mono _).sub fun φ hφ => List.mem_append_right _ hφ

/-- Into a `◇_x` view where both substitutions send `x` to one entry. -/
theorem eqRelH_dia {Γ : Ctx} {θ θ' : Subst σ Δ} (h : EqRelH hO E Γ θ θ') {x z : VarSymb}
    (hsame : θ.at x = θ'.at x) :
    EqRelH hO ((E.flatMap WFF.boxConjs).map (WFF.mono (Ctx.le_boxIn_diaIn Δ z))) (Γ.diaIn x)
      (θ.dia x z) (θ'.dia x z) := by
  refine eqRelH_of ?_ fun y X hy => (h.ty y _ (Ctx.boxIn_wit.mp hy).2).toWit.mono _
  intro v T _ hv
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with hux
      subst hux
      change SubE.EqH _ _ _ (if u = u then (θ.at u).diaBody z else SubE.hide)
        (if u = u then (θ'.at u).diaBody z else SubE.hide)
      rw [if_pos rfl, if_pos rfl, hsame]
      exact .same _
  | .step u .box => exact (h.ty u _ (Ctx.boxIn_box (Γ := Γ) hv).2).unbox.mono _
  | .step u .keep =>
      exact absurd (Ctx.boxIn_keep (Γ := Γ) hv).1 (by simp [ModalSys.Four_false_of_opt hO])
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

/-- ⭐Into a `◇_x` view where the two substitutions send `x` to possible objects over the
    witnesses `x₁` and `x₂`: both views weakened into the `□` view with `x₁` and `x₂` opened,
    the contents related by their `≡`, which the caller supplies as hypotheses. -/
theorem eqRelH_dia₂ {Γ : Ctx} {θ θ' : Subst σ Δ} (h : EqRelH hO E Γ θ θ') {x x₁ x₂ : VarSymb}
    {X : VarType} (hrx : Γ.ref x = some (.VTypeDia X))
    (hx₁ : ∃ Y, Δ.ref x₁ = some (.VTypeDia Y)) (hx₂ : ∃ Y, Δ.ref x₂ = some (.VTypeDia Y))
    {a₁ a₂ : Ann X} {b₁ : Term σ (Δ.diaIn x₁) X a₁} {b₂ : Term σ (Δ.diaIn x₂) X a₂}
    (he₁ : θ.at x = .tm (.diatm x₁ hx₁ b₁)) (he₂ : θ'.at x = .tm (.diatm x₂ hx₂ b₂)) :
    EqRelH hO ((eqH hO X (Term.mono (Ctx.le_diaIn_optIn₂ hO hx₁ x₂) b₁)
          (Term.mono (Ctx.le_diaIn_optIn₂' hO x₁ hx₂) b₂) : WFF σ _ 0).conjuncts ++
        (E.flatMap WFF.boxConjs).map
          (WFF.mono ((Ctx.le_optIn Δ.boxIn x₁).trans (Ctx.le_optIn _ x₂))))
      (Γ.diaIn x) ((θ.dia x x₁).mono (Ctx.le_diaIn_optIn₂ hO hx₁ x₂))
      ((θ'.dia x x₂).mono (Ctx.le_diaIn_optIn₂' hO x₁ hx₂)) := by
  refine eqRelH_of ?_ fun y Y hy => ?_
  · intro v T _ hv
    match v with
    | .step u .dia =>
        change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
          else none) = some T at hv
        split_ifs at hv with hux
        subst hux
        rw [hrx] at hv
        cases hv
        change SubE.EqH _ _ _ (SubE.mono _ (if u = u then (θ.at u).diaBody x₁ else SubE.hide))
          (SubE.mono _ (if u = u then (θ'.at u).diaBody x₂ else SubE.hide))
        rw [if_pos rfl, if_pos rfl, he₁, he₂]
        change SubE.EqH _ _ _ (SubE.mono _ (dite (x₁ = x₁) _ _))
          (SubE.mono _ (dite (x₂ = x₂) _ _))
        rw [dif_pos rfl, dif_pos rfl]
        change SubE.EqH _ _ _ (SubE.tm (Term.mono _ (Term.mono _ b₁)))
          (SubE.tm (Term.mono _ (Term.mono _ b₂)))
        rw [Term.mono_mono, Term.mono_mono]
        exact SubE.eqH_of_conj X _ _ fun c hc => List.mem_append_left _ hc
    | .step u .box =>
        change SubE.EqH _ _ _
          ((((θ.at u).unbox).mono (Ctx.le_boxIn_diaIn Δ x₁)).mono
            (Ctx.le_diaIn_optIn₂ hO hx₁ x₂))
          ((((θ'.at u).unbox).mono (Ctx.le_boxIn_diaIn Δ x₂)).mono
            (Ctx.le_diaIn_optIn₂' hO x₁ hx₂))
        rw [SubE.mono_mono, SubE.mono_mono]
        exact (((h.ty u _ (Ctx.boxIn_box (Γ := Γ) hv).2).unbox).mono _).sub
          fun φ hφ => List.mem_append_right _ hφ
    | .step u .keep =>
        exact absurd (Ctx.boxIn_keep (Γ := Γ) hv).1 (by simp [ModalSys.Four_false_of_opt hO])
    | .root _ => cases hv
    | .step _ .fst => cases hv
    | .step _ .snd => cases hv
    | .step _ .here => cases hv
  · change WitE.EqH _ _ _
      ((((θ.at y).toWit).mono (Ctx.le_boxIn_diaIn Δ x₁)).mono (Ctx.le_diaIn_optIn₂ hO hx₁ x₂))
      ((((θ'.at y).toWit).mono (Ctx.le_boxIn_diaIn Δ x₂)).mono (Ctx.le_diaIn_optIn₂' hO x₁ hx₂))
    rw [WitE.mono_mono, WitE.mono_mono]
    exact (((h.ty y _ (Ctx.boxIn_wit.mp hy).2).toWit).mono _).sub
      fun φ hφ => List.mem_append_right _ hφ

end Subst

end V12M
