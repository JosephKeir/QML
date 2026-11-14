import QML.QML_v12m_ProofSubst
import QML.QML_v12m_EqHDef

/-!
# QML v12m — heterogeneous equality `≡` (the box view of possible objects)

`eqH hO T t s`, written `t ≡ s`: equality of two terms of one type whose **annotations may
differ** — at `◇` types, possible objects over different witnesses.  `eqRec` compares only within
one annotation, because without `Opt` nothing relates two witnesses' contents.  With `Opt` the `□`
view sees both witnesses at once (`◇⁰`), so two possible objects are equal when, along every arrow,
either is present only if both are, with equal contents:

    ⟨x; c⟩ ≡ ⟨x'; c'⟩  :=  □((◇⁰_x ⊤ ∨ ◇⁰_{x'} ⊤) → ◇⁰_x ◇⁰_{x'} (c ≡ c'))

(docs §12.2's clause with `In`, restated for the binder, §12.20).  At the other types `≡` has
`eqRec`'s clauses.

* `eqH`, `eqH_mono` (weakening commutes with it), `WFF.subst_eqH` (so does substitution);
* `Proof.eqH_refl`.
-/

namespace V12M

variable [ModalSys]

namespace Proof

/-- ⭐**Reflexivity** of `≡`.  At `◇` types: where the witness is present, its content is
    opened, and re-opened (`opt_reopen`) holds of itself. -/
def eqH_refl {σ : Signature} (hO : ModalSys.Opt = true) : {Γ : Ctx} → [Γ.NoSlots] →
    {Δ : List (WFF σ Γ 0)} → (T : VarType) → {a : Ann T} → (t : Term σ Γ T a) →
    Proof σ Γ Δ (eqH hO T t t)
  | _, _, _, .Var, .var, t => Proof.conv (eqH_Var hO t t).symm (.eq_intro t)
  | _, _, _, .VTypeOne, .one, .unit => .top_intro
  | _, _, _, .VTypeProd A B, .prod _ _, .pair t₁ t₂ =>
      .and_intro (eqH_refl hO A t₁) (eqH_refl hO B t₂)
  | _, _, _, .VTypeBox A, .box _, .boxtm t =>
      Proof.ofSubset (fun _ h => absurd h List.not_mem_nil)
        (Proof.K_box (Δ := []) (eqH_refl hO A t))
  | Γ, _, Δ, .VTypeDia A, .dia x _, .diatm _ hx t =>
      have hw := Ctx.boxIn_wit_of hO hx
      -- In the view of `x` (opened): `≡` of the content, re-opened.
      have hre : ∃ X, (Γ.boxIn.optIn x).wit x = some X ∧
          (Γ.boxIn.optIn x) (.step x .dia) = some X :=
        hw.imp fun _ h => ⟨h, Ctx.optIn_content h⟩
      have inner : Proof σ (Γ.boxIn.optIn x) [.top]
          (.optx hO .arrow x hw (eqH hO A
            (Term.mono (Ctx.le_optIn _ x) (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx) t))
            (Term.mono ((Ctx.le_optIn _ x).optIn x)
              (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx) t)))) :=
        Proof.weak _ (Proof.conv (by rw [eqH_mono])
          (Proof.opt_reopen hO .arrow x hre (eqH_refl hO A
            (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx) t))))
      have k := Proof.K_opt hO .arrow x hw (Δ₁ := []) (Δ₂ := []) inner
      have hor : Proof σ Γ.boxIn [.or (.optx hO .arrow x hw .top) (.optx hO .arrow x hw .top)] _ :=
        .or_elim (.ax _) (Proof.ofSubset (fun _ h => by
            rw [List.mem_singleton.mp h]
            exact List.mem_cons_self) k)
          (Proof.ofSubset (fun _ h => by
            rw [List.mem_singleton.mp h]
            exact List.mem_cons_self) k)
      Proof.ofSubset (fun _ h => absurd h List.not_mem_nil)
        (Proof.K_box (Δ := []) (.imp_intro hor))

/-- ⭐**The content of a present witness has a name**: `◇⁰_y ⊤ ⊢ ∃e. ◇⁰_y (y.dia ≡ e)`.  Derived
    (docs §12.18): inside the view, `y.dia ≡ y.dia`; re-opened (`opt_reopen`), `∃`-introduced at
    `y.dia`; carried out by `K_opt` and `opt_out`. -/
def opt_name {σ : Signature} (hO : ModalSys.Opt = true) {Γ : Ctx} [Γ.NoSlots] {y : VarSymb}
    {X : VarType} (hy : Γ.wit y = some X) :
    Proof σ Γ [.optx hO .arrow y ⟨X, hy⟩ .top] (.ex X (WFF.optName hO hy)) :=
  have h₀ : (Γ.optIn y).ref (.step y .dia) = some X := Ctx.ref_optIn_content hy
  have hre : ∃ X', (Γ.optIn y).wit y = some X' ∧ (Γ.optIn y) (.step y .dia) = some X' :=
    ⟨X, hy, Ctx.optIn_content hy⟩
  have reop := Proof.opt_reopen (Δ := []) hO .arrow y hre
    (Proof.eqH_refl hO X (Term.eta (σ := σ) (.step y .dia) X h₀))
  have hne : ¬ y.rt = .bnd 0 := fun h => by
    rw [(Ctx.NoSlots.slots (Γ := Γ)).wit y 0 h le_rfl] at hy
    cases hy
  have key : WFF.instantiate Ctx.NoSlots.slots (Term.eta (σ := σ) (.step y .dia) X h₀)
      (WFF.mono ((Ctx.le_optIn Γ y).insert (.bnd 0) X) (WFF.optName hO hy)) =
      .optx hO .arrow y (hre.imp fun _ h => h.1)
        (WFF.mono (Ctx.le_optIn _ y) (eqH hO X (Term.eta (.step y .dia) X h₀)
          (Term.eta (.step y .dia) X h₀))) := by
    rw [WFF.instantiate, WFF.substRoot,
      WFF.subst_mono (hΓ := (Ctx.NoSlots.slots (Γ := Γ)).insert X)]
    have hz : Subst.singleIdx (.bnd 0) (.tm (Term.eta (σ := σ) (.step y .dia) X h₀)) y = y :=
      if_neg hne
    have hθ := (Subst.ok_single (Ctx.Le.refl (Γ.optIn y)) (Γ := Γ.optIn y) (r := .bnd 0)
      (T := X) (e := .tm (Term.eta (σ := σ) (.step y .dia) X h₀)) rfl).restrict
        ((Ctx.le_optIn Γ y).insert (.bnd 0) X)
    have hc := (Subst.coh_single ((Ctx.NoSlots.slots (Γ := Γ.optIn y)).rootFresh le_rfl)
      (Ctx.Le.refl (Γ.optIn y)) (T := X)
      (e := .tm (Term.eta (σ := σ) (.step y .dia) X h₀)) rfl).restrict
        ((Ctx.le_optIn Γ y).insert (.bnd 0) X)
    have hθz := Subst.ok_optIn hθ hO (y := y) (z := y) (X := X) hy
      (rfl : (WitE.ren y : WitE σ (Γ.optIn y)).idxAlong [] = y)
    have hcz : Subst.Coh (Subst.singleIdx (.bnd 0) (.tm (Term.eta (σ := σ) (.step y .dia) X h₀)))
        ((Γ.insert (.bnd 0) X).optIn y)
        ((Subst.single (.bnd 0) (.tm (Term.eta (σ := σ) (.step y .dia) X h₀))).optIn y y) := by
      have := Subst.coh_optIn hθ hc hO (y := y) hy
      rwa [hz] at this
    have hat : ((Subst.single (.bnd 0) (.tm (Term.eta (σ := σ) (.step y .dia) X h₀))).optIn
        y y).at (.step y .dia) = .ren (.step y .dia) := by
      rw [Subst.at_nonproj _ rfl, Subst.optIn_content]
      rfl
    have hat₂ : ((Subst.single (.bnd 0) (.tm (Term.eta (σ := σ) (.step y .dia) X h₀))).optIn
        y y).at (.root (.bnd 0)) =
        .tm (Term.mono (Ctx.le_optIn _ y) (Term.eta (σ := σ) (.step y .dia) X h₀)) := by
      change ((Subst.single (.bnd 0) (.tm (Term.eta (σ := σ) (.step y .dia) X h₀))).optIn
        y y) (.root (.bnd 0)) = _
      rw [Subst.optIn_ne _ _ (fun h => by cases h), Subst.single_root]
      rfl
    rw [WFF.subst_optx_eq (Γ := Γ.insert (.bnd 0) X) (Δ := Γ.optIn y) _ _ _ _ _ hO y ⟨X, hy⟩ _
        hz ⟨X, hy⟩ hθz hcz, WFF.subst_eqH,
      eqH_congr hO (Term.subst_eta_renAt _ _ _ X _ _ _
          (Ctx.ref_optIn_content (Γ := Γ.optIn y) hy) hat)
        (Term.subst_eta_tm _ _ _ X _ _ _ hat₂),
      eqH_mono, Term.mono_eta]
  have p₁ : Proof σ (Γ.optIn y) [.top] (WFF.mono (Ctx.le_optIn Γ y) (.ex X (WFF.optName hO hy))) :=
    Proof.weak _ (Proof.ex_intro X (Term.eta (.step y .dia) X h₀) (Proof.conv key.symm reop))
  Proof.opt_out hO .arrow y ⟨X, hy⟩ (Proof.K_opt hO .arrow y ⟨X, hy⟩ (Δ₁ := []) (Δ₂ := []) p₁)

end Proof

end V12M
