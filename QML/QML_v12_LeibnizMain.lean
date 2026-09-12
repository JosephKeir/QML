import QML.QML_v12_LeibnizCong
import QML.QML_v12_LeibnizQuant

/-!
# QML v12 — ⭐the Leibniz principle

`Proof.substEq`: substitutions whose entries are equal or provably equal (from hypotheses `E`)
send a formula to formulas that prove each other.  By induction on the formula:

* atoms and base equalities: congruence (`relCong`, `termCong`);
* connectives: the induction hypothesis, both ways round for `→`;
* quantifiers: an eigenvariable (from the presentation, `Ctx.Presented`), `toFree`, and the
  quantifier-step identities;
* `□` and `◇_w`: K, with the hypotheses under the modality discharged by search.

`Proof.leibniz`: the instance substituting `t` and `s` for the slot.
-/

namespace V12

/-- ⭐Provably equal substitutions send a formula to formulas that prove each other. -/
def Proof.substEq {σ : Signature} : {Γ Δ : Ctx} → [Δ.Presented] → {d : ℕ} →
    {ι : VarSymb → VarSymb} → (θ₁ θ₂ : Subst σ Δ) → (hθ₁ : Subst.Ok Γ θ₁) →
    (hθ₂ : Subst.Ok Γ θ₂) → (hc₁ : Subst.Coh ι Γ θ₁) → (hc₂ : Subst.Coh ι Γ θ₂) →
    (hΓ : Γ.SlotsFrom d) → (E : List (WFF σ Δ 0)) → Subst.EqRel E Γ θ₁ θ₂ →
    (φ : WFF σ Γ d) →
    Proof σ Δ (WFF.subst ι θ₁ hθ₁ hc₁ hΓ Ctx.NoSlots.slots φ :: E)
      (WFF.subst ι θ₂ hθ₂ hc₂ hΓ Ctx.NoSlots.slots φ)
  | _, _, _, _, _, θ₁, θ₂, hθ₁, hθ₂, hc₁, hc₂, _, E, hrel, .atom ρ =>
      Proof.relCong θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel ρ .nil
  | _, Δ, _, _, ι, θ₁, θ₂, hθ₁, hθ₂, hc₁, hc₂, _, E, hrel, .eq t s =>
      have ht : Proof σ Δ E (.eq (Term.subst ι θ₁ hθ₁ hc₁ t) (Term.subst ι θ₂ hθ₂ hc₂ t)) :=
        Proof.conv (eqRec_Var _ _) (Proof.termCong θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel t rfl)
      have hs : Proof σ Δ E (.eq (Term.subst ι θ₁ hθ₁ hc₁ s) (Term.subst ι θ₂ hθ₂ hc₂ s)) :=
        Proof.conv (eqRec_Var _ _) (Proof.termCong θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ E hrel s rfl)
      Proof.eq_trans_base (Proof.eq_symm_base (Proof.weak _ ht))
        (Proof.eq_trans_base (Proof.lookup List.mem_cons_self) (Proof.weak _ hs))
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .top => Proof.top_intro
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .bot =>
      Proof.bot_elim _ (Proof.lookup List.mem_cons_self)
  | _, _, _, _, _, θ₁, θ₂, hθ₁, hθ₂, hc₁, hc₂, hΓ, E, hrel, .and φ ψ =>
      have ihφ := Proof.substEq θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ E hrel φ
      have ihψ := Proof.substEq θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ E hrel ψ
      .and_intro
        (Proof.cut (Proof.ofSubset (List.sub_cons_cons _ _ _) ihφ)
          (.and_elim_l (Proof.lookup List.mem_cons_self)))
        (Proof.cut (Proof.ofSubset (List.sub_cons_cons _ _ _) ihψ)
          (.and_elim_r (Proof.lookup List.mem_cons_self)))
  | _, _, _, _, _, θ₁, θ₂, hθ₁, hθ₂, hc₁, hc₂, hΓ, E, hrel, .or φ ψ =>
      have ihφ := Proof.substEq θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ E hrel φ
      have ihψ := Proof.substEq θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ E hrel ψ
      .or_elim (Proof.lookup List.mem_cons_self)
        (.or_intro_l _ (Proof.ofSubset (List.sub_cons_cons _ _ _) ihφ))
        (.or_intro_r _ (Proof.ofSubset (List.sub_cons_cons _ _ _) ihψ))
  | _, _, _, _, ι, θ₁, θ₂, hθ₁, hθ₂, hc₁, hc₂, hΓ, E, hrel, .imp φ ψ =>
      have ihφ := Proof.substEq θ₂ θ₁ hθ₂ hθ₁ hc₂ hc₁ hΓ E hrel.symm φ
      have ihψ := Proof.substEq θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ E hrel ψ
      .imp_intro
        (Proof.cut
          (Proof.ofSubset (fun x hx => (List.mem_cons.mp hx).elim
            (fun h => by subst h; exact List.mem_cons_self)
            (fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))))
            ihψ)
          (.imp_elim
            (Proof.lookup (x := WFF.imp (WFF.subst ι θ₁ hθ₁ hc₁ hΓ Ctx.NoSlots.slots φ)
              (WFF.subst ι θ₁ hθ₁ hc₁ hΓ Ctx.NoSlots.slots ψ))
              (List.mem_cons_of_mem _ List.mem_cons_self))
            (Proof.ofSubset (List.sub_cons_cons _ _ _) ihφ)))
  | _, Δ, _, d, _, θ₁, θ₂, hθ₁, hθ₂, hc₁, hc₂, hΓ, E, hrel, .all T ψ =>
      have hu : Δ.RootFresh (.free (Ctx.Presented.bound Δ)) := Ctx.Presented.fresh _ le_rfl
      have ih := Proof.substEq (θ₁.toFree d _ T hu.root) (θ₂.toFree d _ T hu.root)
        (Subst.ok_toFree hθ₁ T hu.root) (Subst.ok_toFree hθ₂ T hu.root)
        (Subst.coh_toFree hθ₁ hc₁ hΓ T hu.root) (Subst.coh_toFree hθ₂ hc₂ hΓ T hu.root)
        (hΓ.insert T) (E.map (WFF.weaken hu.root T)) (Subst.eqRel_toFree hrel T hu.root) ψ
      have elim := Proof.conv
        (WFF.instantiate_toFree θ₁ hθ₁ hc₁ hΓ Ctx.NoSlots.slots _ hu T Ctx.NoSlots.slots ψ)
        (Proof.all_elim T (Term.eta (.root (.free _)) T (Ctx.ref_insert_root Δ _ T))
          (Proof.lookup List.mem_cons_self))
      have step := Proof.cut (Proof.ofSubset (List.sub_cons_cons _ _ _) ih) elim
      Proof.conv
        (congrArg (WFF.all T)
          (WFF.bindFree_toFree θ₂ hθ₂ hc₂ hΓ Ctx.NoSlots.slots _ hu T ψ))
        (Proof.all_intro _ T hu step)
  | _, Δ, _, d, _, θ₁, θ₂, hθ₁, hθ₂, hc₁, hc₂, hΓ, E, hrel, .ex T ψ =>
      have hu : Δ.RootFresh (.free (Ctx.Presented.bound Δ)) := Ctx.Presented.fresh _ le_rfl
      have ih := Proof.substEq (θ₁.toFree d _ T hu.root) (θ₂.toFree d _ T hu.root)
        (Subst.ok_toFree hθ₁ T hu.root) (Subst.ok_toFree hθ₂ T hu.root)
        (Subst.coh_toFree hθ₁ hc₁ hΓ T hu.root) (Subst.coh_toFree hθ₂ hc₂ hΓ T hu.root)
        (hΓ.insert T) (E.map (WFF.weaken hu.root T)) (Subst.eqRel_toFree hrel T hu.root) ψ
      have p₁ := Proof.conv
        (congrArg (WFF.ex T)
          (WFF.bindFree_toFree θ₁ hθ₁ hc₁ hΓ Ctx.NoSlots.slots _ hu T ψ).symm)
        (Proof.lookup List.mem_cons_self)
      have p₂ := Proof.ex_intro T (Term.eta (.root (.free _)) T (Ctx.ref_insert_root Δ _ T))
        (Proof.conv
          (WFF.instantiate_toFree θ₂ hθ₂ hc₂ hΓ Ctx.NoSlots.slots _ hu T Ctx.NoSlots.slots ψ).symm
          (Proof.ofSubset (List.sub_cons_cons _ _ _) ih))
      Proof.ex_elim _ T hu p₁ p₂
  | _, Δ, _, _, ι, θ₁, θ₂, hθ₁, hθ₂, hc₁, hc₂, hΓ, E, hrel, .box ψ =>
      have ih := Proof.substEq θ₁.box θ₂.box (Subst.ok_box hθ₁) (Subst.ok_box hθ₂)
        (Subst.coh_box hθ₁ hc₁) (Subst.coh_box hθ₂ hc₂) hΓ.boxIn (E.flatMap WFF.boxConjs)
        (Subst.eqRel_box hrel) ψ
      Proof.dischargeAll (Proof.K_box ih)
        (Proofs.ofMap (fun χ => WFF.box (Γ := Δ) χ) _ fun c hc =>
          if h : c = WFF.subst ι θ₁.box (Subst.ok_box hθ₁) (Subst.coh_box hθ₁ hc₁) hΓ.boxIn
              Ctx.NoSlots.slots ψ then by
            subst h
            exact Proof.lookup List.mem_cons_self
          else Proof.weak _ (Proof.boxedConj E ((List.mem_cons.mp hc).resolve_left h)))
  | _, Δ, _, _, ι, θ₁, θ₂, hθ₁, hθ₂, hc₁, hc₂, hΓ, E, hrel, .dia x hx ψ =>
      have hw₁ : (θ₁.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc₁ x _ hX []
      have hw₂ : (θ₂.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc₂ x _ hX []
      have hwx : ∃ X, Δ.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ₁ hX) hw₁
      have ih := Proof.substEq (θ₁.dia x (ι x)) (θ₂.dia x (ι x)) (Subst.ok_dia hθ₁ hx hw₁)
        (Subst.ok_dia hθ₂ hx hw₂) (Subst.coh_dia hθ₁ hc₁ hx) (Subst.coh_dia hθ₂ hc₂ hx)
        (hΓ.diaIn x) _ (Subst.eqRel_dia hrel hw₁) ψ
      Proof.dischargeAll (Proof.K_dia (ι x) hwx ih)
        (.cons (Proof.lookup List.mem_cons_self)
          ((Proofs.ofMap (WFF.boxx (ι x) hwx) _ fun _ hc =>
              Proof.weak _ (Proof.diaedConj (ι x) hwx E hc)).append
            (Proofs.ofMap (fun χ => WFF.box (Γ := Δ) χ) _ fun _ hc =>
              Proof.weak _ (Proof.boxedConj E hc))))

/-- ⭐**Leibniz**: from `t = s` at any type and `φ[t]`, conclude `φ[s]`. -/
def Proof.leibniz {σ : Signature} {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)}
    (T : VarType) {a : Ann T} {t s : Term σ Γ T a} {φ : WFF σ (Γ.insert (.bnd 0) T) 1}
    (hts : Proof σ Γ Δ (eqRec T t s))
    (hφ : Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ)) :
    Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots s φ) :=
  have hr : Γ.RootFresh (.bnd 0) := Ctx.NoSlots.slots.rootFresh le_rfl
  have hrel : Subst.EqRel (eqRec T t s : WFF σ Γ 0).conjuncts (Γ.insert (.bnd 0) T)
      (Subst.single (.bnd 0) (.tm t)) (Subst.single (.bnd 0) (.tm s)) :=
    Subst.eqRel_of fun v U _ hv => by
      by_cases hvr : v = .root (.bnd 0)
      · subst hvr
        have hTU : T = U := by simpa [Ctx.insert] using hv
        subst hTU
        rw [show Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm t) (.root (.bnd 0)) = .tm t
            from if_pos rfl,
          show Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm s) (.root (.bnd 0)) = .tm s
            from if_pos rfl]
        exact SubE.eqE_of_conj T t s fun _ hc => hc
      · rw [show Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm t) v = .ren v from if_neg hvr,
          show Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm s) v = .ren v from if_neg hvr]
        exact .same _
  have key := Proof.substEq (Subst.single (.bnd 0) (.tm t)) (Subst.single (.bnd 0) (.tm s))
    (Subst.ok_single (Ctx.Le.refl Γ) rfl) (Subst.ok_single (Ctx.Le.refl Γ) rfl)
    (Subst.coh_single hr (Ctx.Le.refl Γ) rfl) (Subst.coh_single hr (Ctx.Le.refl Γ) rfl)
    (Ctx.NoSlots.slots.insert T) _ hrel φ
  Proof.dischargeAll key (.cons hφ (Proofs.ofMem _ fun _ hc =>
    Proof.cut (Proof.weakenTail Δ (Proof.conjunct _ hc)) hts))

end V12
