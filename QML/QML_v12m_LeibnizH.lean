import QML.QML_v12m_LeibnizHRel

/-!
# QML v12m — ⭐Leibniz along `≡` (the box view of possible objects)

`Proof.substEqH`: two substitutions whose entries are provably `≡` (`Subst.EqRelH`) send a formula
to formulas that prove each other, both ways.  By induction on the formula, as the K-only
`Proof.substEq` (`QML_v12_LeibnizMain`), except where a possible object or a witness is sent to
two different witnesses.  There the two views are different contexts, and the case goes through
the `□` view with both witnesses opened (`Proof.optTwoFwd`, `Proof.optTwoBwd`):
* `◇⁰_y χ`: `◇⁰_{z₁} χ₁` and the witnesses' equality give `◇⁰_{z₁} ◇⁰_{z₂} (χ₁ ∧ c₁ ≡ c₂)`; the
  induction hypothesis in the doubly opened view, then `opt_out`;
* `◇_x χ`: the same in the `□` view, entered by the bridge (`dia_opt`, `opt_dia`).

`Proof.leibnizH`: from `t ≡ s` and `φ[t]`, `φ[s]`.
-/

namespace V12M

/- M1's construction is for K and D with `Opt` on: T off (`ModalSys.NoT`) until M2 step 6
   generalises it, so the class is in scope throughout. -/
set_option linter.unusedSectionVars false

variable [ModalSys] [ModalSys.NoT]

deriving instance DecidableEq for SubE
deriving instance DecidableEq for WitE

/-! ## Congruence at base type -/

mutual
  /-- Related substitutions give provably equal applications. -/
  def Proof.funcCongH {σ : Signature} {ι₁ ι₂ : VarSymb → VarSymb} {Γ Δ : Ctx} [Δ.NoSlots]
      {hO : ModalSys.Opt = true} (θ₁ θ₂ : Subst σ Δ) (hθ₁ : Subst.Ok Γ θ₁) (hθ₂ : Subst.Ok Γ θ₂)
      (hc₁ : Subst.Coh ι₁ Γ θ₁) (hc₂ : Subst.Coh ι₂ Γ θ₂) (E : List (WFF σ Δ 0))
      (hrel : Subst.EqRelH hO E Γ θ₁ θ₂) :
      {n : ℕ} → (g : Func σ Γ n) → (S : Spine σ Δ n) →
      Proof σ Δ E (WFF.eq (Term.func (S.fill (Func.subst ι₁ θ₁ hθ₁ hc₁ g)))
        (Term.func (S.fill (Func.subst ι₂ θ₂ hθ₂ hc₂ g))))
    | _, .F _, _ => Proof.eq_intro _
    | _, .eval g t, S =>
        have hab : Proof σ Δ E (.eq (Term.subst ι₁ θ₁ hθ₁ hc₁ t) (Term.subst ι₂ θ₂ hθ₂ hc₂ t)) :=
          Proof.conv (eqH_Var hO _ _) (Proof.termCongH θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel t rfl)
        have p₁ := Proof.funcCongH θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel g
          (.cons (Term.subst ι₁ θ₁ hθ₁ hc₁ t) S)
        have p₂ : Proof σ Δ E (WFF.eq
            (Term.func ((Spine.cons (Term.subst ι₁ θ₁ hθ₁ hc₁ t) S).fill
              (Func.subst ι₂ θ₂ hθ₂ hc₂ g)))
            (Term.func ((Spine.cons (Term.subst ι₂ θ₂ hθ₂ hc₂ t) S).fill
              (Func.subst ι₂ θ₂ hθ₂ hc₂ g)))) :=
          Proof.conv (instantiate_funcHole _ S _ _)
            (Proof.eq_elim _ _ hab (Proof.conv (instantiate_funcHole _ S _ _).symm
              (Proof.eq_intro _)))
        Proof.eq_trans_base p₁ p₂
    termination_by structural _ g => g

  /-- Related substitutions give provably equal base terms. -/
  def Proof.termCongH {σ : Signature} {ι₁ ι₂ : VarSymb → VarSymb} {Γ Δ : Ctx} [Δ.NoSlots]
      {hO : ModalSys.Opt = true} (θ₁ θ₂ : Subst σ Δ) (hθ₁ : Subst.Ok Γ θ₁) (hθ₂ : Subst.Ok Γ θ₂)
      (hc₁ : Subst.Coh ι₁ Γ θ₁) (hc₂ : Subst.Coh ι₂ Γ θ₂) (E : List (WFF σ Δ 0))
      (hrel : Subst.EqRelH hO E Γ θ₁ θ₂) :
      {T : VarType} → {a : Ann T} → (u : Term σ Γ T a) → T = .Var →
      Proof σ Δ E (eqH hO T (Term.subst ι₁ θ₁ hθ₁ hc₁ u) (Term.subst ι₂ θ₂ hθ₂ hc₂ u))
    | _, _, .var v hv, _ =>
        Proof.conv (eqH_Var hO _ _).symm (Proof.eqH_var (hrel.ty v _ hv) _ _)
    | _, _, .func f, _ =>
        Proof.conv (eqH_Var hO _ _).symm (Proof.funcCongH θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel f .nil)
    | _, _, .unit, h => nomatch h
    | _, _, .pair _ _, h => nomatch h
    | _, _, .boxtm _, h => nomatch h
    | _, _, .diatm _ _ _, h => nomatch h
    termination_by structural _ _ u => u
end

/-- Two substitutions with provably equal base terms give equivalent atoms. -/
def Proof.relCongG {σ : Signature} {ι₁ ι₂ : VarSymb → VarSymb} {Γ Δ : Ctx} [Δ.NoSlots]
    (θ₁ θ₂ : Subst σ Δ) (hθ₁ : Subst.Ok Γ θ₁) (hθ₂ : Subst.Ok Γ θ₂) (hc₁ : Subst.Coh ι₁ Γ θ₁)
    (hc₂ : Subst.Coh ι₂ Γ θ₂) (E : List (WFF σ Δ 0))
    (heq : ∀ u : Term σ Γ .Var .var,
      Proof σ Δ E (.eq (Term.subst ι₁ θ₁ hθ₁ hc₁ u) (Term.subst ι₂ θ₂ hθ₂ hc₂ u))) :
    {n : ℕ} → (ρ : Rel σ Γ n) → (S : Spine σ Δ n) →
    Proof σ Δ (WFF.atom (S.fillR (Rel.subst ι₁ θ₁ hθ₁ hc₁ ρ)) :: E)
      (WFF.atom (S.fillR (Rel.subst ι₂ θ₂ hθ₂ hc₂ ρ)))
  | _, .R _, _ => Proof.lookup List.mem_cons_self
  | _, .eval ρ t, S =>
      have p₁ := Proof.relCongG θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E heq ρ
        (.cons (Term.subst ι₁ θ₁ hθ₁ hc₁ t) S)
      have p₂ : Proof σ Δ
          (WFF.atom ((Spine.cons (Term.subst ι₁ θ₁ hθ₁ hc₁ t) S).fillR (Rel.subst ι₂ θ₂ hθ₂ hc₂ ρ))
            :: E)
          (WFF.atom ((Spine.cons (Term.subst ι₂ θ₂ hθ₂ hc₂ t) S).fillR
            (Rel.subst ι₂ θ₂ hθ₂ hc₂ ρ))) :=
        Proof.conv (instantiate_relHole S (Rel.subst ι₂ θ₂ hθ₂ hc₂ ρ) _)
          (Proof.eq_elim _ _ (Proof.weak _ (heq t))
            (Proof.conv (instantiate_relHole S (Rel.subst ι₂ θ₂ hθ₂ hc₂ ρ) _).symm
              (Proof.lookup List.mem_cons_self)))
      Proof.cut (Proof.ofSubset (List.sub_cons_cons _ _ _) p₂) p₁

/-! ## Two witnesses opened together -/

section OptTwo

variable {σ : Signature} (hO : ModalSys.Opt = true) {G : Ctx} [G.NoSlots] {z₁ z₂ : VarSymb}
  (hz₁ : ∃ Z, G.wit z₁ = some Z) (hz₂ : ∃ Z, G.wit z₂ = some Z) {X : VarType} {a b : Ann X}
  (c₁ : Term σ (G.optIn z₁) X a) (c₂ : Term σ (G.optIn z₂) X b) (H : List (WFF σ G 0))

/-- The hypotheses in the view with both witnesses opened: the contents' `≡`, and those of the
    outer world (`◇⁰` crosses no world). -/
abbrev optTwoHyps : List (WFF σ ((G.optIn z₁).optIn z₂) 0) :=
  (eqH hO X (Term.mono (Ctx.le_optIn _ z₂) c₁) (Term.mono ((Ctx.le_optIn G z₁).optIn z₂) c₂) :
      WFF σ _ 0).conjuncts ++
    H.map (WFF.mono ((Ctx.le_optIn G z₁).trans (Ctx.le_optIn _ z₂)))

/-- The view's hypotheses from the contents' `≡`, the outer hypotheses and a formula `φ`, in any
    order among others. -/
def optTwoProofs {M : List (WFF σ ((G.optIn z₁).optIn z₂) 0)}
    (heq : Proof σ _ M (eqH hO X (Term.mono (Ctx.le_optIn _ z₂) c₁)
      (Term.mono ((Ctx.le_optIn G z₁).optIn z₂) c₂)))
    (hH : ∀ h ∈ H, WFF.mono (Ctx.le_optIn _ z₂) (WFF.mono (Ctx.le_optIn G z₁) h) ∈ M) :
    Proofs σ _ M (optTwoHyps hO c₁ c₂ H) :=
  Proofs.append (Proofs.ofMem _ fun _ hc => Proof.cut (Proof.weakenTail M (Proof.conjunct _ hc))
      heq)
    (Proofs.ofMap _ H fun h hh => Proof.conv (WFF.mono_mono _ _ h) (Proof.lookup (hH h hh)))

/-- ⭐**From one witness to the other**: `◇⁰_{z₁} χ₁` and the witnesses' equality give
    `◇⁰_{z₂} χ₂`, if `χ₁` gives `χ₂` with both opened. -/
def Proof.optTwoFwd (hW : witEq hO X hz₁ hz₂ c₁ c₂ ∈ H) {χ₁ : WFF σ (G.optIn z₁) 0}
    {χ₂ : WFF σ (G.optIn z₂) 0}
    (inner : Proof σ ((G.optIn z₁).optIn z₂)
      (WFF.mono (Ctx.le_optIn _ z₂) χ₁ :: optTwoHyps hO c₁ c₂ H)
      (WFF.mono ((Ctx.le_optIn G z₁).optIn z₂) χ₂)) :
    Proof σ G (.optx hO .arrow z₁ hz₁ χ₁ :: H) (.optx hO .arrow z₂ hz₂ χ₂) :=
  -- In the doubly opened view: the contents' `≡`, `χ₁` and the outer hypotheses.
  have stepA := Proof.K_opt (Γ := G.optIn z₁) hO .arrow z₂ hz₂ (Δ₂ := [])
    (Δ₁ := χ₁ :: H.map (WFF.mono (Ctx.le_optIn G z₁)))
    (Proof.dischargeAll inner (.cons
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (optTwoProofs hO c₁ c₂ H (Proof.lookup List.mem_cons_self) fun h hh =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_map_of_mem (List.mem_map_of_mem hh))))))
  -- In the view of `z₁`: from the conjunction.
  have stepB : Proof σ (G.optIn z₁)
      ((χ₁.and (.optx hO .arrow z₂ hz₂ (eqH hO X (Term.mono (Ctx.le_optIn _ z₂) c₁)
        (Term.mono ((Ctx.le_optIn G z₁).optIn z₂) c₂)))) ::
        ([] ++ H.map (WFF.mono (Ctx.le_optIn G z₁))))
      (WFF.mono (Ctx.le_optIn G z₁) (.optx hO .arrow z₂ hz₂ χ₂)) :=
    .imp_elim (.imp_elim (Proof.ofSubset (fun _ h => List.mem_cons_of_mem _ h)
        (.imp_intro (.imp_intro stepA)))
      (.and_elim_l (Proof.lookup List.mem_cons_self)))
      (.and_elim_r (Proof.lookup List.mem_cons_self))
  have stepC := Proof.opt_out hO .arrow z₁ hz₁
    (Proof.K_opt hO .arrow z₁ hz₁ (Δ₂ := []) (Δ₁ := H) stepB)
  -- At `G`: the conjunction, from `χ₁` and the witnesses' equality.
  have hpres : Proof σ G (.optx hO .arrow z₁ hz₁ χ₁ :: H) (.optx hO .arrow z₁ hz₁ .top) :=
    Proof.ofSubset (fun _ h => by
        rw [List.mem_singleton.mp h]
        exact List.mem_cons_self)
      (Proof.K_opt hO .arrow z₁ hz₁ (Δ₂ := []) (Δ₁ := []) (φ := .top) (ψ := χ₁) .top_intro)
  have hQ := Proof.imp_elim (Proof.lookup (List.mem_cons_of_mem _ hW)) (.or_intro_l _ hpres)
  have hconj := Proof.dischargeAll (Proof.opt_fun hO .arrow z₁ hz₁ χ₁ _)
    (.cons (Proof.lookup List.mem_cons_self) (.cons hQ .nil))
  Proof.cut (Proof.ofSubset (List.sub_cons_cons _ _ _) stepC) hconj

/-- ⭐**Back from the other witness**: `◇⁰_{z₂} χ₂` and the witnesses' equality give
    `◇⁰_{z₁} χ₁`, if `χ₂` gives `χ₁` with both opened. -/
def Proof.optTwoBwd (hW : witEq hO X hz₁ hz₂ c₁ c₂ ∈ H) {χ₁ : WFF σ (G.optIn z₁) 0}
    {χ₂ : WFF σ (G.optIn z₂) 0}
    (inner : Proof σ ((G.optIn z₁).optIn z₂)
      (WFF.mono ((Ctx.le_optIn G z₁).optIn z₂) χ₂ :: optTwoHyps hO c₁ c₂ H)
      (WFF.mono (Ctx.le_optIn _ z₂) χ₁)) :
    Proof σ G (.optx hO .arrow z₂ hz₂ χ₂ :: H) (.optx hO .arrow z₁ hz₁ χ₁) :=
  let eqF : WFF σ ((G.optIn z₁).optIn z₂) 0 := eqH hO X (Term.mono (Ctx.le_optIn _ z₂) c₁)
    (Term.mono ((Ctx.le_optIn G z₁).optIn z₂) c₂)
  -- In the doubly opened view, from the conjunction of the contents' `≡` and `χ₂`.
  have stepA := Proof.K_opt (Γ := G.optIn z₁) hO .arrow z₂ hz₂ (Δ₂ := [])
    (Δ₁ := H.map (WFF.mono (Ctx.le_optIn G z₁)))
    (ψ := (eqH hO X (Term.mono (Ctx.le_optIn _ z₂) c₁)
      (Term.mono ((Ctx.le_optIn G z₁).optIn z₂) c₂)).and
        (WFF.mono ((Ctx.le_optIn G z₁).optIn z₂) χ₂))
    (Proof.dischargeAll inner (.cons (.and_elim_r (Proof.lookup List.mem_cons_self))
      (optTwoProofs hO c₁ c₂ H (.and_elim_l (Proof.lookup List.mem_cons_self)) fun h hh =>
        List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_map_of_mem hh)))))
  -- In the view of `z₁`: `χ₁`.
  have stepB : Proof σ (G.optIn z₁)
      (.optx hO .arrow z₂ hz₂ eqF :: ([] ++ (WFF.optx hO .arrow z₂ hz₂ χ₂ :: H).map
        (WFF.mono (Ctx.le_optIn G z₁)))) χ₁ :=
    Proof.opt_out (Γ := G.optIn z₁) hO .arrow z₂ hz₂ (Proof.cut (Proof.ofSubset (fun _ h => by
        rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
        stepA)
      (Proof.dischargeAll (Proof.opt_fun (Γ := G.optIn z₁) hO .arrow z₂ hz₂ eqF
          (WFF.mono ((Ctx.le_optIn G z₁).optIn z₂) χ₂))
        (.cons (Proof.lookup List.mem_cons_self)
          (.cons (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)) .nil))))
  have stepC :=
    Proof.K_opt hO .arrow z₁ hz₁ (Δ₂ := []) (Δ₁ := WFF.optx hO .arrow z₂ hz₂ χ₂ :: H) stepB
  -- At `G`: both present, from `χ₂` and the witnesses' equality.
  have hpres : Proof σ G (.optx hO .arrow z₂ hz₂ χ₂ :: H) (.optx hO .arrow z₂ hz₂ .top) :=
    Proof.ofSubset (fun _ h => by
        rw [List.mem_singleton.mp h]
        exact List.mem_cons_self)
      (Proof.K_opt hO .arrow z₂ hz₂ (Δ₂ := []) (Δ₁ := []) (φ := .top) (ψ := χ₂) .top_intro)
  have hQ := Proof.imp_elim (Proof.lookup (List.mem_cons_of_mem _ hW)) (.or_intro_r _ hpres)
  Proof.cut stepC hQ

end OptTwo

/-! ## The induction -/

/-- What the induction proves of a formula: both directions, for every pair of related
    substitutions into a presented context. -/
abbrev SubstEqHAt {σ : Signature} (hO : ModalSys.Opt = true) {Γ : Ctx} {d : ℕ}
    (ι₁ ι₂ : VarSymb → VarSymb) (hΓ : Γ.SlotsFrom d) (φ : WFF σ Γ d) : Type :=
  ∀ (Δ : Ctx) [Δ.Presented] (θ₁ θ₂ : Subst σ Δ) (hθ₁ : Subst.Ok Γ θ₁) (hθ₂ : Subst.Ok Γ θ₂)
    (hc₁ : Subst.Coh ι₁ Γ θ₁) (hc₂ : Subst.Coh ι₂ Γ θ₂) (E : List (WFF σ Δ 0)),
    Subst.EqRelH hO E Γ θ₁ θ₂ →
    Proof σ Δ (WFF.subst ι₁ θ₁ hθ₁ hc₁ hΓ Ctx.NoSlots.slots φ :: E)
        (WFF.subst ι₂ θ₂ hθ₂ hc₂ hΓ Ctx.NoSlots.slots φ) ×
      Proof σ Δ (WFF.subst ι₂ θ₂ hθ₂ hc₂ hΓ Ctx.NoSlots.slots φ :: E)
        (WFF.subst ι₁ θ₁ hθ₁ hc₁ hΓ Ctx.NoSlots.slots φ)

/-- Substituting into `◇_x` where the image of `x` is known to be `z`. -/
theorem WFF.subst_dia_eq {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d d' : ℕ}
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom d)
    (hΔ : Δ.SlotsFrom d') (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (φ : WFF σ (Γ.diaIn x) d) {z : VarSymb} (hz : ι x = z)
    (hz' : ∃ X, Δ.ref z = some (.VTypeDia X)) (hθz : Subst.Ok (Γ.diaIn x) (θ.dia x z))
    (hcz : Subst.Coh ι (Γ.diaIn x) (θ.dia x z)) :
    WFF.subst ι θ hθ hc hΓ hΔ (.dia x hx φ) =
      .dia z hz' (WFF.subst ι (θ.dia x z) hθz hcz (hΓ.diaIn x) (hΔ.diaIn z) φ) := by
  subst hz
  rfl

/-- ⭐**The `◇⁰_y` case**: one witness entry under both substitutions, by `K_opt`; two, through
    the view with both opened (`Proof.optTwoFwd`, `Proof.optTwoBwd`). -/
def Proof.optCaseH {σ : Signature} (hO : ModalSys.Opt = true) {Γ : Ctx} {d : ℕ}
    {ι₁ ι₂ : VarSymb → VarSymb} (hΓ : Γ.SlotsFrom d) (hO' : ModalSys.Opt = true) (y : VarSymb)
    (hy : ∃ X, Γ.wit y = some X) (ψ : WFF σ (Γ.optIn y) d)
    (ih : SubstEqHAt hO ι₁ ι₂ (hΓ.optIn y) ψ) :
    SubstEqHAt hO ι₁ ι₂ hΓ (.optx hO' .arrow y hy ψ) := by
  intro Δ _ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel
  have hw₁ : (θ₁.wit y).idxAlong [] = ι₁ y := hy.elim fun X hX => hc₁.wit hO y X hX []
  have hw₂ : (θ₂.wit y).idxAlong [] = ι₂ y := hy.elim fun X hX => hc₂.wit hO y X hX []
  have hok₁ : ∀ {z : VarSymb}, (θ₁.wit y).idxAlong [] = z → Subst.Ok (Γ.optIn y) (θ₁.optIn y z) :=
    fun hz => hy.elim fun _ hX => Subst.ok_optIn hθ₁ hO hX hz
  have hok₂ : ∀ {z : VarSymb}, (θ₂.wit y).idxAlong [] = z → Subst.Ok (Γ.optIn y) (θ₂.optIn y z) :=
    fun hz => hy.elim fun _ hX => Subst.ok_optIn hθ₂ hO hX hz
  have hcoh₁ : ∀ {z : VarSymb}, ι₁ y = z → Subst.Coh ι₁ (Γ.optIn y) (θ₁.optIn y z) :=
    fun hz => hy.elim fun _ hX => by
      have := Subst.coh_optIn hθ₁ hc₁ hO hX
      rwa [hz] at this
  have hcoh₂ : ∀ {z : VarSymb}, ι₂ y = z → Subst.Coh ι₂ (Γ.optIn y) (θ₂.optIn y z) :=
    fun hz => hy.elim fun _ hX => by
      have := Subst.coh_optIn hθ₂ hc₂ hO hX
      rwa [hz] at this
  have hwit₁ : ∀ {z : VarSymb}, (θ₁.wit y).idxAlong [] = z → ∃ X, Δ.wit z = some X :=
    fun hz => hy.elim fun X hX => WitE.wit_of (hθ₁.wit hO y X hX) hz
  have hwit₂ : ∀ {z : VarSymb}, (θ₂.wit y).idxAlong [] = z → ∃ X, Δ.wit z = some X :=
    fun hz => hy.elim fun X hX => WitE.wit_of (hθ₂.wit hO y X hX) hz
  refine if hsame : θ₁.wit y = θ₂.wit y then ?_ else ?_
  · -- One witness entry: `K_opt` in its view.
    have hw₂' : (θ₂.wit y).idxAlong [] = ι₁ y := hsame ▸ hw₁
    have hz : ι₂ y = ι₁ y := hw₂.symm.trans hw₂'
    have e₂ := WFF.subst_optx_eq θ₂ hθ₂ hc₂ hΓ Ctx.NoSlots.slots hO' y hy ψ hz (hwit₁ hw₁)
      (hok₂ hw₂') (hcoh₂ hz)
    have ih' := ih (Δ := Δ.optIn (ι₁ y)) (θ₁.optIn y (ι₁ y)) (θ₂.optIn y (ι₁ y)) (hok₁ hw₁)
      (hok₂ hw₂') (hcoh₁ rfl) (hcoh₂ hz) _ (Subst.eqRelH_optIn hrel hsame)
    exact (Proof.conv e₂.symm
        (Proof.K_opt hO' .arrow (ι₁ y) (hwit₁ hw₁) (Δ₂ := []) (Δ₁ := E) ih'.1),
      Proof.castHyps (congrArg (· :: E) e₂.symm)
        (Proof.K_opt hO' .arrow (ι₁ y) (hwit₁ hw₁) (Δ₂ := []) (Δ₁ := E) ih'.2))
  · -- Two witness entries, related by their equality: both opened.
    cases h₁ : θ₁.wit y with
    | hide => exact False.elim (hy.elim fun X hX => by
        have := hθ₁.wit hO y X hX
        rw [h₁] at this
        exact this)
    | ren w => exact False.elim (hy.elim fun X hX => by
        have h := hrel.wit y X hX
        rw [h₁] at h hsame
        generalize θ₂.wit y = w₂ at h hsame
        cases h with
        | same => exact hsame rfl)
    | @tm z₁ A₁ a₁ c₁ =>
      cases h₂ : θ₂.wit y with
      | hide => exact False.elim (hy.elim fun X hX => by
          have := hθ₂.wit hO y X hX
          rw [h₂] at this
          exact this)
      | ren w => exact False.elim (hy.elim fun X hX => by
          have h := hrel.wit y X hX
          rw [h₁, h₂] at h
          cases h)
      | @tm z₂ A₂ a₂ c₂ =>
        have hA : A₂ = A₁ := hy.elim fun X hX => by
          have o₁ := hθ₁.wit hO y X hX
          have o₂ := hθ₂.wit hO y X hX
          rw [h₁] at o₁
          rw [h₂] at o₂
          exact o₂.2.trans o₁.2.symm
        subst hA
        have hyA : Γ.wit y = some A₂ := hy.elim fun X hX => by
          have o₁ := hθ₁.wit hO y X hX
          rw [h₁] at o₁
          rw [hX, o₁.2]
        have hz₁ : (θ₁.wit y).idxAlong [] = z₁ := by rw [h₁]; rfl
        have hz₂ : (θ₂.wit y).idxAlong [] = z₂ := by rw [h₂]; rfl
        have hzw₁ := hwit₁ hz₁
        have hzw₂ := hwit₂ hz₂
        have hW : witEq hO A₂ hzw₁ hzw₂ c₁ c₂ ∈ E := by
          have h := hrel.wit y A₂ hyA
          rw [h₁, h₂] at h
          cases h with
          | same => exact absurd (h₁.trans h₂.symm) hsame
          | mem _ _ _ _ hm => exact hm
        have hzi₁ : ι₁ y = z₁ := hw₁.symm.trans hz₁
        have hzi₂ : ι₂ y = z₂ := hw₂.symm.trans hz₂
        have e₁ := WFF.subst_optx_eq θ₁ hθ₁ hc₁ hΓ Ctx.NoSlots.slots hO' y hy ψ hzi₁ hzw₁
          (hok₁ hz₁) (hcoh₁ hzi₁)
        have e₂ := WFF.subst_optx_eq θ₂ hθ₂ hc₂ hΓ Ctx.NoSlots.slots hO' y hy ψ hzi₂ hzw₂
          (hok₂ hz₂) (hcoh₂ hzi₂)
        have ih' := ih (Δ := (Δ.optIn z₁).optIn z₂)
          ((θ₁.optIn y z₁).mono (Ctx.le_optIn _ z₂))
          ((θ₂.optIn y z₂).mono ((Ctx.le_optIn Δ z₁).optIn z₂))
          (Subst.ok_mono (hok₁ hz₁) _) (Subst.ok_mono (hok₂ hz₂) _)
          (Subst.coh_mono (hcoh₁ hzi₁) _) (Subst.coh_mono (hcoh₂ hzi₂) _) _
          (Subst.eqRelH_optIn₂ hrel hyA h₁ h₂)
        have m₁ := (WFF.mono_subst (Ctx.le_optIn _ z₂) (θ₁.optIn y z₁) (hok₁ hz₁) (hcoh₁ hzi₁)
          (hΓ.optIn y) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ).symm
        have m₂ := (WFF.mono_subst ((Ctx.le_optIn Δ z₁).optIn z₂) (θ₂.optIn y z₂) (hok₂ hz₂)
          (hcoh₂ hzi₂) (hΓ.optIn y) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ).symm
        exact (Proof.castHyps (congrArg (· :: E) e₁.symm) (Proof.conv e₂.symm
            (Proof.optTwoFwd hO hzw₁ hzw₂ c₁ c₂ E hW
              (Proof.castHyps (congrArg (· :: _) m₁) (Proof.conv m₂ ih'.1)))),
          Proof.castHyps (congrArg (· :: E) e₂.symm) (Proof.conv e₁.symm
            (Proof.optTwoBwd hO hzw₁ hzw₂ c₁ c₂ E hW
              (Proof.castHyps (congrArg (· :: _) m₂) (Proof.conv m₁ ih'.2)))))

/-- `□` of the hypotheses' boxed conjuncts and one more boxed formula, from the hypotheses and
    that formula's box. -/
def Proof.boxedWith {σ : Signature} {Δ : Ctx} (E : List (WFF σ Δ 0)) (a : WFF σ Δ.boxIn 0)
    (M : List (WFF σ Δ 0)) (ha : WFF.box a ∈ M) (hE : ∀ φ ∈ E, φ ∈ M) :
    Proofs σ Δ M ((a :: E.flatMap WFF.boxConjs).map fun χ => WFF.box (Γ := Δ) χ) :=
  Proofs.ofMap (fun χ => WFF.box (Γ := Δ) χ) _ fun c hc =>
    if h : c = a then by
      subst h
      exact Proof.lookup ha
    else Proof.ofSubset hE (Proof.boxedConj E ((List.mem_cons.mp hc).resolve_left h))

/-- From `◇_{x₁} ψ₁` to `◇_{x₂} ψ₂` through the bridge, given the step between the witnesses'
    views in the `□` view. -/
def Proof.diaBridge {σ : Signature} (hO : ModalSys.Opt = true) {Δ : Ctx}
    (E : List (WFF σ Δ 0)) {x₁ x₂ : VarSymb} (hx₁ : ∃ X, Δ.ref x₁ = some (.VTypeDia X))
    (hx₂ : ∃ X, Δ.ref x₂ = some (.VTypeDia X)) {ψ₁ : WFF σ (Δ.diaIn x₁) 0}
    {ψ₂ : WFF σ (Δ.diaIn x₂) 0}
    (step : Proof σ Δ.boxIn
      (.optx hO .arrow x₁ (Ctx.boxIn_wit_of hO hx₁)
        (WFF.mono (Ctx.le_diaIn_boxIn_optIn' hO hx₁) ψ₁) ::
        E.flatMap WFF.boxConjs)
      (.optx hO .arrow x₂ (Ctx.boxIn_wit_of hO hx₂)
        (WFF.mono (Ctx.le_diaIn_boxIn_optIn' hO hx₂) ψ₂))) :
    Proof σ Δ (.dia x₁ hx₁ ψ₁ :: E) (.dia x₂ hx₂ ψ₂) :=
  have neg : Proof σ Δ.boxIn
      ((WFF.optx hO .arrow x₂ (Ctx.boxIn_wit_of hO hx₂)
        (WFF.mono (Ctx.le_diaIn_boxIn_optIn' hO hx₂) ψ₂)).neg :: E.flatMap WFF.boxConjs)
      (WFF.optx hO .arrow x₁ (Ctx.boxIn_wit_of hO hx₁)
        (WFF.mono (Ctx.le_diaIn_boxIn_optIn' hO hx₁) ψ₁)).neg :=
    .imp_intro (.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.ofSubset (List.sub_cons_cons _ _ _) step))
  .opt_dia hO x₂ hx₂ (.imp_intro (.imp_elim
    (Proof.weak _ (.dia_opt hO x₁ hx₁ (Proof.lookup List.mem_cons_self)))
    (Proof.dischargeAll (Proof.K_box neg)
      (Proof.boxedWith E _ _ List.mem_cons_self
        fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))))

/-- ⭐**The `◇_x` case**: one entry for `x` under both substitutions, by `K_dia`; two possible
    objects, through the bridge into the `□` view with both witnesses opened. -/
def Proof.diaCaseH {σ : Signature} (hO : ModalSys.Opt = true) {Γ : Ctx} {d : ℕ}
    {ι₁ ι₂ : VarSymb → VarSymb} (hΓ : Γ.SlotsFrom d) (x : VarSymb)
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (ψ : WFF σ (Γ.diaIn x) d)
    (ih : SubstEqHAt hO ι₁ ι₂ (hΓ.diaIn x) ψ) :
    SubstEqHAt hO ι₁ ι₂ hΓ (.dia x hx ψ) := by
  intro Δ _ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel
  have hw₁ : (θ₁.at x).idxAlong [] = ι₁ x := hx.elim fun _ hX => hc₁ x _ hX []
  have hw₂ : (θ₂.at x).idxAlong [] = ι₂ x := hx.elim fun _ hX => hc₂ x _ hX []
  have hok₁ : ∀ {z : VarSymb}, (θ₁.at x).idxAlong [] = z → Subst.Ok (Γ.diaIn x) (θ₁.dia x z) :=
    fun hz => Subst.ok_dia hθ₁ hx hz
  have hok₂ : ∀ {z : VarSymb}, (θ₂.at x).idxAlong [] = z → Subst.Ok (Γ.diaIn x) (θ₂.dia x z) :=
    fun hz => Subst.ok_dia hθ₂ hx hz
  have hcoh₁ : ∀ {z : VarSymb}, ι₁ x = z → Subst.Coh ι₁ (Γ.diaIn x) (θ₁.dia x z) := fun hz => by
    have := Subst.coh_dia hθ₁ hc₁ hx
    rwa [hz] at this
  have hcoh₂ : ∀ {z : VarSymb}, ι₂ x = z → Subst.Coh ι₂ (Γ.diaIn x) (θ₂.dia x z) := fun hz => by
    have := Subst.coh_dia hθ₂ hc₂ hx
    rwa [hz] at this
  have href₁ : ∀ {z : VarSymb}, (θ₁.at x).idxAlong [] = z →
      ∃ X, Δ.ref z = some (.VTypeDia X) :=
    fun hz => hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ₁ hX) hz
  have href₂ : ∀ {z : VarSymb}, (θ₂.at x).idxAlong [] = z →
      ∃ X, Δ.ref z = some (.VTypeDia X) :=
    fun hz => hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ₂ hX) hz
  refine if hsame : θ₁.at x = θ₂.at x then ?_ else ?_
  · -- One entry: `K_dia` in its view.
    have hw₂' : (θ₂.at x).idxAlong [] = ι₁ x := hsame ▸ hw₁
    have hz : ι₂ x = ι₁ x := hw₂.symm.trans hw₂'
    have e₂ := WFF.subst_dia_eq θ₂ hθ₂ hc₂ hΓ Ctx.NoSlots.slots x hx ψ hz (href₁ hw₁)
      (hok₂ hw₂') (hcoh₂ hz)
    have ih' := ih (Δ := Δ.diaIn (ι₁ x)) (θ₁.dia x (ι₁ x)) (θ₂.dia x (ι₁ x)) (hok₁ hw₁)
      (hok₂ hw₂') (hcoh₁ rfl) (hcoh₂ hz) _ (Subst.eqRelH_dia hrel hsame)
    exact (Proof.conv e₂.symm (Proof.dischargeAll
        (Proof.K_dia (ι₁ x) (href₁ hw₁) (Δ₁ := E.flatMap WFF.boxConjs) (Δ₂ := []) ih'.1)
        (.cons (Proof.lookup List.mem_cons_self)
          (Proofs.ofMap (fun χ => WFF.box (Γ := Δ) χ) _ fun _ hc =>
            Proof.weak _ (Proof.boxedConj E hc)))),
      Proof.castHyps (congrArg (· :: E) e₂.symm) (Proof.dischargeAll
        (Proof.K_dia (ι₁ x) (href₁ hw₁) (Δ₁ := E.flatMap WFF.boxConjs) (Δ₂ := []) ih'.2)
        (.cons (Proof.lookup List.mem_cons_self)
          (Proofs.ofMap (fun χ => WFF.box (Γ := Δ) χ) _ fun _ hc =>
            Proof.weak _ (Proof.boxedConj E hc)))))
  · -- Two possible objects, related by their `≡`: through the bridge.
    have hnot : ∀ (w : VarSymb), θ₁.at x = .ren w → False := fun w h₁ => hx.elim fun X hX => by
      have h := hrel.ty x _ hX
      rw [h₁] at h hsame
      generalize θ₂.at x = e₂ at h hsame
      cases h with
      | same => exact hsame rfl
    have hnot' : ∀ (w : VarSymb), θ₂.at x = .ren w → False := fun w h₂ => hx.elim fun X hX => by
      have h := hrel.ty x _ hX
      rw [h₂] at h hsame
      generalize θ₁.at x = e₁ at h hsame
      cases h with
      | same => exact hsame rfl
    have hbad₁ : ∀ {U : VarType}, (∀ X, U ≠ .VTypeDia X) → ∀ {a : Ann U} (t : Term σ Δ U a),
        θ₁.at x = .tm t → False := fun {_} hU {_} t h₁ => hx.elim fun X hX => by
      have o := Subst.okRef_at hθ₁ hX
      rw [h₁] at o
      exact hU X o
    have hbad₂ : ∀ {U : VarType}, (∀ X, U ≠ .VTypeDia X) → ∀ {a : Ann U} (t : Term σ Δ U a),
        θ₂.at x = .tm t → False := fun {_} hU {_} t h₂ => hx.elim fun X hX => by
      have o := Subst.okRef_at hθ₂ hX
      rw [h₂] at o
      exact hU X o
    cases h₁ : θ₁.at x with
    | hide => exact False.elim (hx.elim fun X hX => by
        have o := Subst.okRef_at hθ₁ hX
        rw [h₁] at o
        exact o)
    | ren w => exact False.elim (hnot w h₁)
    | tm t₁ =>
      cases t₁ with
      | var _ _ => exact False.elim (hbad₁ (fun _ h => by cases h) _ h₁)
      | func _ => exact False.elim (hbad₁ (fun _ h => by cases h) _ h₁)
      | unit => exact False.elim (hbad₁ (fun _ h => by cases h) _ h₁)
      | pair _ _ => exact False.elim (hbad₁ (fun _ h => by cases h) _ h₁)
      | boxtm _ => exact False.elim (hbad₁ (fun _ h => by cases h) _ h₁)
      | @diatm _ A₁ a₁ x₁ hx₁ b₁ =>
      cases h₂ : θ₂.at x with
      | hide => exact False.elim (hx.elim fun X hX => by
          have o := Subst.okRef_at hθ₂ hX
          rw [h₂] at o
          exact o)
      | ren w => exact False.elim (hnot' w h₂)
      | tm t₂ =>
        cases t₂ with
        | var _ _ => exact False.elim (hbad₂ (fun _ h => by cases h) _ h₂)
        | func _ => exact False.elim (hbad₂ (fun _ h => by cases h) _ h₂)
        | unit => exact False.elim (hbad₂ (fun _ h => by cases h) _ h₂)
        | pair _ _ => exact False.elim (hbad₂ (fun _ h => by cases h) _ h₂)
        | boxtm _ => exact False.elim (hbad₂ (fun _ h => by cases h) _ h₂)
        | @diatm _ A₂ a₂ x₂ hx₂ b₂ =>
        have hA : A₂ = A₁ := hx.elim fun X hX => by
          have o₁ := Subst.okRef_at hθ₁ hX
          have o₂ := Subst.okRef_at hθ₂ hX
          rw [h₁] at o₁
          rw [h₂] at o₂
          exact VarType.VTypeDia.inj (o₂.trans o₁.symm)
        subst hA
        have hrx : Γ.ref x = some (.VTypeDia A₂) := hx.elim fun X hX => by
          have o₁ := Subst.okRef_at hθ₁ hX
          rw [h₁] at o₁
          rw [hX, ← o₁]
        have hm : (eqH hO (.VTypeDia A₂) (Term.diatm x₁ hx₁ b₁) (Term.diatm x₂ hx₂ b₂) :
            WFF σ Δ 0) ∈ E := by
          have h := hrel.ty x _ hrx
          rw [h₁, h₂] at h
          cases h with
          | same => exact absurd (h₁.trans h₂.symm) hsame
          | mem _ _ _ hm => exact hm
        have hW : witEq hO A₂ (Ctx.boxIn_wit_of hO hx₁) (Ctx.boxIn_wit_of hO hx₂)
            (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx₁) b₁)
            (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx₂) b₂) ∈ E.flatMap WFF.boxConjs :=
          List.mem_flatMap.mpr ⟨_, hm, List.mem_singleton_self _⟩
        have hz₁ : (θ₁.at x).idxAlong [] = x₁ := by rw [h₁]; rfl
        have hz₂ : (θ₂.at x).idxAlong [] = x₂ := by rw [h₂]; rfl
        have hzi₁ : ι₁ x = x₁ := hw₁.symm.trans hz₁
        have hzi₂ : ι₂ x = x₂ := hw₂.symm.trans hz₂
        have e₁ := WFF.subst_dia_eq θ₁ hθ₁ hc₁ hΓ Ctx.NoSlots.slots x hx ψ hzi₁ hx₁ (hok₁ hz₁)
          (hcoh₁ hzi₁)
        have e₂ := WFF.subst_dia_eq θ₂ hθ₂ hc₂ hΓ Ctx.NoSlots.slots x hx ψ hzi₂ hx₂ (hok₂ hz₂)
          (hcoh₂ hzi₂)
        have ih' := ih (Δ := (Δ.boxIn.optIn x₁).optIn x₂)
          ((θ₁.dia x x₁).mono (Ctx.le_diaIn_optIn₂ hO hx₁ x₂))
          ((θ₂.dia x x₂).mono (Ctx.le_diaIn_optIn₂' hO x₁ hx₂))
          (Subst.ok_mono (hok₁ hz₁) _) (Subst.ok_mono (hok₂ hz₂) _)
          (Subst.coh_mono (hcoh₁ hzi₁) _) (Subst.coh_mono (hcoh₂ hzi₂) _) _
          (Subst.eqRelH_dia₂ hrel hrx hx₁ hx₂ h₁ h₂)
        have m₁ := WFF.mono_subst (Ctx.le_diaIn_optIn₂ hO hx₁ x₂) (θ₁.dia x x₁) (hok₁ hz₁)
          (hcoh₁ hzi₁) (hΓ.diaIn x) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ
        have m₂ := WFF.mono_subst (Ctx.le_diaIn_optIn₂' hO x₁ hx₂) (θ₂.dia x x₂) (hok₂ hz₂)
          (hcoh₂ hzi₂) (hΓ.diaIn x) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ
        have hyps : (eqH hO A₂ (Term.mono (Ctx.le_diaIn_optIn₂ hO hx₁ x₂) b₁)
              (Term.mono (Ctx.le_diaIn_optIn₂' hO x₁ hx₂) b₂) : WFF σ _ 0).conjuncts ++
            (E.flatMap WFF.boxConjs).map
              (WFF.mono ((Ctx.le_optIn Δ.boxIn x₁).trans (Ctx.le_optIn _ x₂))) =
            optTwoHyps hO (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx₁) b₁)
            (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx₂) b₂) (E.flatMap WFF.boxConjs) := by
          dsimp only [optTwoHyps]
          rw [Term.mono_mono, Term.mono_mono]
        exact (Proof.castHyps (congrArg (· :: E) e₁.symm) (Proof.conv e₂.symm
            (Proof.diaBridge hO E hx₁ hx₂ (Proof.optTwoFwd hO _ _ _ _ _ hW
              (Proof.castHyps (by rw [← m₁, WFF.mono_mono, ← hyps])
                (Proof.conv (by rw [← m₂, WFF.mono_mono]) ih'.1))))),
          Proof.castHyps (congrArg (· :: E) e₂.symm) (Proof.conv e₁.symm
            (Proof.diaBridge hO E hx₂ hx₁ (Proof.optTwoBwd hO _ _ _ _ _ hW
              (Proof.castHyps (by rw [← m₂, WFF.mono_mono, ← hyps])
                (Proof.conv (by rw [← m₁, WFF.mono_mono]) ih'.2))))))

theorem ModalSys.BStrong_false_of_opt (hO : ModalSys.Opt = true) : ModalSys.BStrong = false := by
  have := ModalSys.optStage hO
  simp only [Bool.or_eq_false_iff] at this
  exact this.1.2

theorem ModalSys.Five_false_of_opt (hO : ModalSys.Opt = true) : ModalSys.Five = false := by
  have := ModalSys.optStage hO
  simp only [Bool.or_eq_false_iff] at this
  exact this.2

/-- ⭐**Leibniz along `≡`, for substitutions**: two substitutions with provably `≡` entries send a
    formula to formulas that prove each other, both ways. -/
def Proof.substEqH {σ : Signature} (hO : ModalSys.Opt = true) : {Γ : Ctx} → {d : ℕ} →
    {ι₁ ι₂ : VarSymb → VarSymb} → (hΓ : Γ.SlotsFrom d) → (φ : WFF σ Γ d) →
    SubstEqHAt hO ι₁ ι₂ hΓ φ
  | Γ, _, ι₁, ι₂, _, .atom ρ => fun Δ _ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel =>
      have hv : ∀ u : Term σ Γ .Var .var,
          Proof σ Δ E (.eq (Term.subst ι₁ θ₁ hθ₁ hc₁ u) (Term.subst ι₂ θ₂ hθ₂ hc₂ u)) :=
        fun u => Proof.conv (eqH_Var hO _ _) (Proof.termCongH θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel u rfl)
      (Proof.relCongG θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hv ρ .nil,
        Proof.relCongG θ₂ θ₁ hθ₂ hθ₁ hc₂ hc₁ E (fun u => Proof.eq_symm_base (hv u)) ρ .nil)
  | Γ, _, ι₁, ι₂, _, .eq t s => fun Δ _ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel =>
      have hv : ∀ u : Term σ Γ .Var .var,
          Proof σ Δ E (.eq (Term.subst ι₁ θ₁ hθ₁ hc₁ u) (Term.subst ι₂ θ₂ hθ₂ hc₂ u)) :=
        fun u => Proof.conv (eqH_Var hO _ _) (Proof.termCongH θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel u rfl)
      (Proof.eq_trans_base (Proof.eq_symm_base (Proof.weak _ (hv t)))
          (Proof.eq_trans_base (Proof.lookup List.mem_cons_self) (Proof.weak _ (hv s))),
        Proof.eq_trans_base (Proof.weak _ (hv t))
          (Proof.eq_trans_base (Proof.lookup List.mem_cons_self)
            (Proof.eq_symm_base (Proof.weak _ (hv s)))))
  | _, _, _, _, _, .top => fun _ _ _ _ _ _ _ _ _ _ => (Proof.top_intro, Proof.top_intro)
  | _, _, _, _, _, .bot => fun _ _ _ _ _ _ _ _ _ _ =>
      (Proof.bot_elim _ (Proof.lookup List.mem_cons_self),
        Proof.bot_elim _ (Proof.lookup List.mem_cons_self))
  | _, _, _, _, hΓ, .and φ ψ => fun _ _ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel =>
      have ihφ := Proof.substEqH hO hΓ φ _ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel
      have ihψ := Proof.substEqH hO hΓ ψ _ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel
      (.and_intro
          (Proof.cut (Proof.ofSubset (List.sub_cons_cons _ _ _) ihφ.1)
            (.and_elim_l (Proof.lookup List.mem_cons_self)))
          (Proof.cut (Proof.ofSubset (List.sub_cons_cons _ _ _) ihψ.1)
            (.and_elim_r (Proof.lookup List.mem_cons_self))),
        .and_intro
          (Proof.cut (Proof.ofSubset (List.sub_cons_cons _ _ _) ihφ.2)
            (.and_elim_l (Proof.lookup List.mem_cons_self)))
          (Proof.cut (Proof.ofSubset (List.sub_cons_cons _ _ _) ihψ.2)
            (.and_elim_r (Proof.lookup List.mem_cons_self))))
  | _, _, _, _, hΓ, .or φ ψ => fun _ _ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel =>
      have ihφ := Proof.substEqH hO hΓ φ _ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel
      have ihψ := Proof.substEqH hO hΓ ψ _ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel
      (.or_elim (Proof.lookup List.mem_cons_self)
          (.or_intro_l _ (Proof.ofSubset (List.sub_cons_cons _ _ _) ihφ.1))
          (.or_intro_r _ (Proof.ofSubset (List.sub_cons_cons _ _ _) ihψ.1)),
        .or_elim (Proof.lookup List.mem_cons_self)
          (.or_intro_l _ (Proof.ofSubset (List.sub_cons_cons _ _ _) ihφ.2))
          (.or_intro_r _ (Proof.ofSubset (List.sub_cons_cons _ _ _) ihψ.2)))
  | _, _, _, _, hΓ, .imp φ ψ => fun _ _ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel =>
      have ihφ := Proof.substEqH hO hΓ φ _ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel
      have ihψ := Proof.substEqH hO hΓ ψ _ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel
      have sub3 : ∀ {a b c : WFF σ _ 0} {l : List (WFF σ _ 0)},
          ∀ z ∈ a :: l, z ∈ a :: b :: c :: l :=
        fun z hz => (List.mem_cons.mp hz).elim (fun h => by subst h; exact List.mem_cons_self)
          (fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
      (.imp_intro (Proof.cut (Proof.ofSubset sub3 ihψ.1)
          (.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
            (Proof.ofSubset (List.sub_cons_cons _ _ _) ihφ.2))),
        .imp_intro (Proof.cut (Proof.ofSubset sub3 ihψ.2)
          (.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
            (Proof.ofSubset (List.sub_cons_cons _ _ _) ihφ.1))))
  | _, d, _, _, hΓ, .all T ψ => fun Δ _ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel =>
      have hu : Δ.RootFresh (.free (Ctx.Presented.bound Δ)) :=
        Ctx.Presented.fresh_bound _ le_rfl
      have ih := Proof.substEqH hO (hΓ.insert T) ψ _ (θ₁.toFree d _ T hu.root)
        (θ₂.toFree d _ T hu.root) (Subst.ok_toFree hθ₁ T hu.root) (Subst.ok_toFree hθ₂ T hu.root)
        (Subst.coh_toFree hθ₁ hc₁ hΓ T hu.root) (Subst.coh_toFree hθ₂ hc₂ hΓ T hu.root)
        (E.map (WFF.weaken hu.root T)) (Subst.eqRelH_toFree hrel T hu.root)
      have elim₁ := Proof.conv
        (WFF.instantiate_toFree θ₁ hθ₁ hc₁ hΓ Ctx.NoSlots.slots _ hu T Ctx.NoSlots.slots ψ)
        (Proof.all_elim T (Term.eta (.root (.free _)) T (Ctx.ref_insert_root Δ _ T))
          (Proof.lookup List.mem_cons_self))
      have elim₂ := Proof.conv
        (WFF.instantiate_toFree θ₂ hθ₂ hc₂ hΓ Ctx.NoSlots.slots _ hu T Ctx.NoSlots.slots ψ)
        (Proof.all_elim T (Term.eta (.root (.free _)) T (Ctx.ref_insert_root Δ _ T))
          (Proof.lookup List.mem_cons_self))
      (Proof.conv (congrArg (WFF.all T)
          (WFF.bindFree_toFree θ₂ hθ₂ hc₂ hΓ Ctx.NoSlots.slots _ hu T ψ))
          (Proof.all_intro _ T hu (Proof.cut (Proof.ofSubset (List.sub_cons_cons _ _ _) ih.1)
            elim₁)),
        Proof.conv (congrArg (WFF.all T)
          (WFF.bindFree_toFree θ₁ hθ₁ hc₁ hΓ Ctx.NoSlots.slots _ hu T ψ))
          (Proof.all_intro _ T hu (Proof.cut (Proof.ofSubset (List.sub_cons_cons _ _ _) ih.2)
            elim₂)))
  | _, d, _, _, hΓ, .ex T ψ => fun Δ _ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel =>
      have hu : Δ.RootFresh (.free (Ctx.Presented.bound Δ)) :=
        Ctx.Presented.fresh_bound _ le_rfl
      have ih := Proof.substEqH hO (hΓ.insert T) ψ _ (θ₁.toFree d _ T hu.root)
        (θ₂.toFree d _ T hu.root) (Subst.ok_toFree hθ₁ T hu.root) (Subst.ok_toFree hθ₂ T hu.root)
        (Subst.coh_toFree hθ₁ hc₁ hΓ T hu.root) (Subst.coh_toFree hθ₂ hc₂ hΓ T hu.root)
        (E.map (WFF.weaken hu.root T)) (Subst.eqRelH_toFree hrel T hu.root)
      (Proof.ex_elim _ T hu
          (Proof.conv (congrArg (WFF.ex T)
            (WFF.bindFree_toFree θ₁ hθ₁ hc₁ hΓ Ctx.NoSlots.slots _ hu T ψ).symm)
            (Proof.lookup List.mem_cons_self))
          (Proof.ex_intro T (Term.eta (.root (.free _)) T (Ctx.ref_insert_root Δ _ T))
            (Proof.conv
              (WFF.instantiate_toFree θ₂ hθ₂ hc₂ hΓ Ctx.NoSlots.slots _ hu T Ctx.NoSlots.slots
                ψ).symm
              (Proof.ofSubset (List.sub_cons_cons _ _ _) ih.1))),
        Proof.ex_elim _ T hu
          (Proof.conv (congrArg (WFF.ex T)
            (WFF.bindFree_toFree θ₂ hθ₂ hc₂ hΓ Ctx.NoSlots.slots _ hu T ψ).symm)
            (Proof.lookup List.mem_cons_self))
          (Proof.ex_intro T (Term.eta (.root (.free _)) T (Ctx.ref_insert_root Δ _ T))
            (Proof.conv
              (WFF.instantiate_toFree θ₁ hθ₁ hc₁ hΓ Ctx.NoSlots.slots _ hu T Ctx.NoSlots.slots
                ψ).symm
              (Proof.ofSubset (List.sub_cons_cons _ _ _) ih.2))))
  | _, _, ι₁, ι₂, hΓ, .box ψ => fun Δ _ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel =>
      have ih := Proof.substEqH hO hΓ.boxIn ψ _ θ₁.box θ₂.box (Subst.ok_box hθ₁) (Subst.ok_box hθ₂)
        (Subst.coh_box hθ₁ hc₁) (Subst.coh_box hθ₂ hc₂) (E.flatMap WFF.boxConjs)
        (Subst.eqRelH_box hrel)
      (Proof.dischargeAll (Proof.K_box ih.1)
          (Proof.boxedWith E _ _ List.mem_cons_self fun _ h => List.mem_cons_of_mem _ h),
        Proof.dischargeAll (Proof.K_box ih.2)
          (Proof.boxedWith E _ _ List.mem_cons_self fun _ h => List.mem_cons_of_mem _ h))
  | _, _, _, _, hΓ, .dia x hx ψ =>
      Proof.diaCaseH hO hΓ x hx ψ (Proof.substEqH hO (hΓ.diaIn x) ψ)
  | _, _, _, _, hΓ, .optx hO' .arrow y hy ψ =>
      Proof.optCaseH hO hΓ hO' y hy ψ (Proof.substEqH hO (hΓ.optIn y) ψ)
  | _, _, _, _, _, .optx _ .ident _ hyI _ => fun _ _ _ _ _ _ _ _ _ _ =>
      absurd (hyI.elim fun _ h => (Ctx.witT_spec h).1 : ModalSys.T = true)
        (by simp [ModalSys.T_false_of_opt hO])
  | _, _, _, _, _, .here hT _ _ _ => fun _ _ _ _ _ _ _ _ _ _ =>
      absurd hT (by simp [ModalSys.T_false_of_opt hO])
  | _, _, _, _, _, .back hB _ _ _ => fun _ _ _ _ _ _ _ _ _ _ =>
      absurd hB (by simp [ModalSys.BStrong_false_of_opt hO])
  | _, _, _, _, _, .retS hB _ _ _ => fun _ _ _ _ _ _ _ _ _ _ =>
      absurd hB (by simp [ModalSys.BStrong_false_of_opt hO])
  | _, _, _, _, _, .retxS hB _ _ _ _ _ => fun _ _ _ _ _ _ _ _ _ _ =>
      absurd hB (by simp [ModalSys.BStrong_false_of_opt hO])
  | _, _, _, _, _, .link hV _ _ _ => fun _ _ _ _ _ _ _ _ _ _ =>
      absurd hV (by simp [ModalSys.Five_false_of_opt hO])
  | _, _, _, _, _, .linkx hV _ _ _ _ _ => fun _ _ _ _ _ _ _ _ _ _ =>
      absurd hV (by simp [ModalSys.Five_false_of_opt hO])

/-- ⭐**Leibniz along `≡`**: from `t ≡ s` and `φ[t]`, `φ[s]`, at every type, the two terms over
    possibly different witnesses. -/
def Proof.leibnizH {σ : Signature} (hO : ModalSys.Opt = true) {Γ : Ctx} [Γ.Presented]
    {Δ : List (WFF σ Γ 0)} (T : VarType) {a b : Ann T} {t : Term σ Γ T a} {s : Term σ Γ T b}
    {φ : WFF σ (Γ.insert (.bnd 0) T) 1} (hts : Proof σ Γ Δ (eqH hO T t s))
    (hφ : Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ)) :
    Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots s φ) :=
  have hr : Γ.RootFresh (.bnd 0) := Ctx.NoSlots.slots.rootFresh le_rfl
  have hrel : Subst.EqRelH hO (eqH hO T t s : WFF σ Γ 0).conjuncts (Γ.insert (.bnd 0) T)
      (Subst.single (.bnd 0) (.tm t)) (Subst.single (.bnd 0) (.tm s)) :=
    Subst.eqRelH_of (fun v U _ hv => by
        by_cases hvr : v = .root (.bnd 0)
        · subst hvr
          have hTU : T = U := by simpa [Ctx.insert] using hv
          subst hTU
          rw [Subst.single_root, Subst.single_root]
          exact SubE.eqH_of_conj T t s fun _ hc => hc
        · rw [Subst.single_ne _ hvr, Subst.single_ne _ hvr]
          exact .same _)
      fun _ _ _ => .same _
  have key := Proof.substEqH hO (Ctx.NoSlots.slots.insert T) φ _ (Subst.single (.bnd 0) (.tm t))
    (Subst.single (.bnd 0) (.tm s)) (Subst.ok_single (Ctx.Le.refl Γ) rfl)
    (Subst.ok_single (Ctx.Le.refl Γ) rfl) (Subst.coh_single hr (Ctx.Le.refl Γ) rfl)
    (Subst.coh_single hr (Ctx.Le.refl Γ) rfl) _ hrel
  Proof.dischargeAll key.1 (.cons hφ (Proofs.ofMem _ fun _ hc =>
    Proof.cut (Proof.weakenTail Δ (Proof.conjunct _ hc)) hts))

/-! ## Symmetry and transitivity -/

section EqHHoles

variable {σ : Signature} {Γ : Ctx} [Γ.NoSlots]

/-- Instantiating the slot leaves a weakened term of the outer context as it was. -/
theorem Term.subst_single_mono {T U : VarType} {a : Ann T} (u : Term σ Γ T a) {b : Ann U}
    (t : Term σ Γ U b) :
    (⟨_, Term.subst (Subst.singleIdx (.bnd 0) (.tm u)) (Subst.single (.bnd 0) (.tm u))
        (Subst.ok_single (Ctx.Le.refl Γ) rfl)
        (Subst.coh_single (Ctx.NoSlots.slots.rootFresh le_rfl) (Ctx.Le.refl Γ) rfl)
        (Term.mono (Ctx.le_insert Ctx.NoSlots.slots.root T) t)⟩ : Σ c, Term σ Γ U c) = ⟨b, t⟩ := by
  rw [Term.subst_mono, Term.subst_ren (Ctx.Le.refl Γ) _ _ _
    (fun v _ hv => Subst.single_at_ne (Ctx.NoSlots.ref_bnd0 hv)) t, Term.mono_refl]

/-- The hole on the left of `≡`. -/
abbrev eqHHoleL (hO : ModalSys.Opt = true) (T : VarType) {b : Ann T} (t : Term σ Γ T b) :
    WFF σ (Γ.insert (.bnd 0) T) 1 :=
  eqH hO T (Term.eta (.root (.bnd 0)) T (Ctx.ref_insert_root Γ _ T))
    (Term.mono (Ctx.le_insert Ctx.NoSlots.slots.root T) t)

/-- The hole on the right of `≡`. -/
abbrev eqHHoleR (hO : ModalSys.Opt = true) (T : VarType) {b : Ann T} (t : Term σ Γ T b) :
    WFF σ (Γ.insert (.bnd 0) T) 1 :=
  eqH hO T (Term.mono (Ctx.le_insert Ctx.NoSlots.slots.root T) t)
    (Term.eta (.root (.bnd 0)) T (Ctx.ref_insert_root Γ _ T))

theorem instantiate_eqHHoleL (hO : ModalSys.Opt = true) (T : VarType) {a b : Ann T}
    (u : Term σ Γ T a) (t : Term σ Γ T b) :
    WFF.instantiate Ctx.NoSlots.slots u (eqHHoleL hO T t) = (eqH hO T u t : WFF σ Γ 0) := by
  rw [WFF.instantiate, WFF.substRoot, WFF.subst_eqH]
  exact eqH_congr hO (Term.subst_eta_tm _ _ _ T _ _ u (Subst.single_root _ _))
    (Term.subst_single_mono u t)

theorem instantiate_eqHHoleR (hO : ModalSys.Opt = true) (T : VarType) {a b : Ann T}
    (u : Term σ Γ T a) (t : Term σ Γ T b) :
    WFF.instantiate Ctx.NoSlots.slots u (eqHHoleR hO T t) = (eqH hO T t u : WFF σ Γ 0) := by
  rw [WFF.instantiate, WFF.substRoot, WFF.subst_eqH]
  exact eqH_congr hO (Term.subst_single_mono u t)
    (Term.subst_eta_tm _ _ _ T _ _ u (Subst.single_root _ _))

end EqHHoles

/-- ⭐**Symmetry** of `≡`: Leibniz at `e ≡ t`, from `t ≡ t`. -/
def Proof.eqH_symm {σ : Signature} (hO : ModalSys.Opt = true) {Γ : Ctx} [Γ.Presented]
    {Δ : List (WFF σ Γ 0)} (T : VarType) {a b : Ann T} {t : Term σ Γ T a} {s : Term σ Γ T b}
    (h : Proof σ Γ Δ (eqH hO T t s)) : Proof σ Γ Δ (eqH hO T s t) :=
  Proof.conv (instantiate_eqHHoleL hO T s t)
    (Proof.leibnizH hO T h
      (Proof.conv (instantiate_eqHHoleL hO T t t).symm (Proof.eqH_refl hO T t)))

/-- ⭐**Transitivity** of `≡`: Leibniz at `t ≡ e`, from `t ≡ s` along `s ≡ r`. -/
def Proof.eqH_trans {σ : Signature} (hO : ModalSys.Opt = true) {Γ : Ctx} [Γ.Presented]
    {Δ : List (WFF σ Γ 0)} (T : VarType) {a b c : Ann T} {t : Term σ Γ T a}
    {s : Term σ Γ T b} {r : Term σ Γ T c} (h₁ : Proof σ Γ Δ (eqH hO T t s))
    (h₂ : Proof σ Γ Δ (eqH hO T s r)) : Proof σ Γ Δ (eqH hO T t r) :=
  Proof.conv (instantiate_eqHHoleR hO T r t)
    (Proof.leibnizH hO T h₂ (Proof.conv (instantiate_eqHHoleR hO T s t).symm h₁))

end V12M
