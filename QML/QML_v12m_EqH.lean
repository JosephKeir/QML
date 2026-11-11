import QML.QML_v12m_ProofSubst

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

/-- A `◇`-address is a witness of the `□` view, with `Opt` on. -/
theorem Ctx.boxIn_wit_of {Γ : Ctx} (hO : ModalSys.Opt = true) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) : ∃ X, Γ.boxIn.wit x = some X :=
  hx.imp fun _ h => Ctx.boxIn_wit.mpr ⟨hO, h⟩

/-- The `◇_x` view sits inside the `□` view with `x` and then `x'` opened. -/
theorem Ctx.le_diaIn_optIn₂ {Γ : Ctx} (hO : ModalSys.Opt = true) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (x' : VarSymb) :
    (Γ.diaIn x).Le ((Γ.boxIn.optIn x).optIn x') :=
  (hx.elim fun _ h => Ctx.le_diaIn_boxIn_optIn hO h).trans (Ctx.le_optIn _ x')

/-- The `◇_{x'}` view sits inside the `□` view with `x` and then `x'` opened. -/
theorem Ctx.le_diaIn_optIn₂' {Γ : Ctx} (hO : ModalSys.Opt = true) (x : VarSymb) {x' : VarSymb}
    (hx' : ∃ X, Γ.ref x' = some (.VTypeDia X)) :
    (Γ.diaIn x').Le ((Γ.boxIn.optIn x).optIn x') :=
  (hx'.elim fun _ h => Ctx.le_diaIn_boxIn_optIn hO h).trans ((Ctx.le_optIn Γ.boxIn x).optIn x')

/-- ⭐**Heterogeneous equality** `t ≡ s`: `=` at `Var`, `⊤` at `𝟙`, componentwise at `×`, `□ ≡`
    at `□A`, and at `◇A` the two witnesses present together with `≡` contents, along every
    arrow.  At one annotation it agrees with `eqRec` in what it says, but it is a different
    formula at `◇` types. -/
def eqH {σ : Signature} {d : ℕ} (hO : ModalSys.Opt = true) : {Γ : Ctx} → (T : VarType) →
    {a b : Ann T} → Term σ Γ T a → Term σ Γ T b → WFF σ Γ d
  | _, .Var, .var, .var, t, s => .eq t s
  | _, .VTypeOne, _, _, _, _ => .top
  | _, .VTypeProd A B, .prod _ _, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ =>
      .and (eqH hO A t₁ s₁) (eqH hO B t₂ s₂)
  | _, .VTypeBox A, .box _, .box _, .boxtm t, .boxtm s => .box (eqH hO A t s)
  | _, .VTypeDia A, .dia x _, .dia x' _, .diatm _ hx t, .diatm _ hx' s =>
      .box (.imp (.or (.optx hO x (Ctx.boxIn_wit_of hO hx) .top)
          (.optx hO x' (Ctx.boxIn_wit_of hO hx') .top))
        (.optx hO x (Ctx.boxIn_wit_of hO hx) (.optx hO x' (Ctx.boxIn_wit_of hO hx')
          (eqH hO A (Term.mono (Ctx.le_diaIn_optIn₂ hO hx x') t)
            (Term.mono (Ctx.le_diaIn_optIn₂' hO x hx') s)))))

/-- At base type `≡` is the primitive equality. -/
theorem eqH_Var {σ : Signature} {Γ : Ctx} {d : ℕ} (hO : ModalSys.Opt = true)
    (t s : Term σ Γ .Var .var) : (eqH hO .Var t s : WFF σ Γ d) = .eq t s := by
  cases t <;> cases s <;> rfl

/-- Weakening commutes with `≡`. -/
theorem eqH_mono {σ : Signature} {d : ℕ} (hO : ModalSys.Opt = true) : {Γ Γ' : Ctx} →
    (h : Γ.Le Γ') → (T : VarType) → {a b : Ann T} → (t : Term σ Γ T a) → (s : Term σ Γ T b) →
    WFF.mono h (eqH hO T t s : WFF σ Γ d) = eqH hO T (Term.mono h t) (Term.mono h s)
  | _, _, h, .Var, .var, .var, t, s =>
      (congrArg (WFF.mono h) (eqH_Var hO t s)).trans (eqH_Var hO _ _).symm
  | _, _, _, .VTypeOne, .one, .one, .unit, .unit => rfl
  | _, _, h, .VTypeProd A B, .prod _ _, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ => by
      change WFF.and (WFF.mono h (eqH hO A t₁ s₁)) (WFF.mono h (eqH hO B t₂ s₂)) = _
      rw [eqH_mono hO h A, eqH_mono hO h B]
      rfl
  | _, _, h, .VTypeBox A, .box _, .box _, .boxtm t, .boxtm s => by
      change WFF.box (WFF.mono h.boxIn (eqH hO A t s)) = _
      rw [eqH_mono hO h.boxIn A]
      rfl
  | Γ, _, h, .VTypeDia A, .dia x _, .dia x' _, .diatm _ hx t, .diatm _ hx' s => by
      have e := eqH_mono (d := d) hO ((h.boxIn.optIn x).optIn x') A
        (Term.mono (Ctx.le_diaIn_optIn₂ hO hx x') t)
        (Term.mono (Ctx.le_diaIn_optIn₂' hO x hx') s)
      simp only [Term.mono_mono] at e
      change WFF.box (WFF.imp (WFF.or _ _) (WFF.optx _ _ _ (WFF.optx _ _ _
        (WFF.mono ((h.boxIn.optIn x).optIn x') (eqH hO A _ _))))) = _
      rw [e]
      change _ = WFF.box (WFF.imp (WFF.or _ _) (WFF.optx _ _ _ (WFF.optx _ _ _
        (eqH hO A (Term.mono _ (Term.mono (h.diaIn x) t))
          (Term.mono _ (Term.mono (h.diaIn x') s))))))
      simp only [Term.mono_mono]
      rfl

/-! ## Substitution -/

/-- On the `◇_z` view, the `□` view of `θ` with `z` and then `z'` opened is `θ.dia`, weakened: the
    content's entry is the body either way (`SubE.toWit_optBody`), re-opened when `z' = z`
    (`WitE.optBody_mono`). -/
theorem Subst.simT_optIn₂_dia {σ : Signature} {Γ Δ : Ctx} {θ : Subst σ Δ} (hθ : Subst.Ok Γ θ)
    (hO : ModalSys.Opt = true) (ι : VarSymb → VarSymb) {z z' : VarSymb} {Z Y : VarType}
    (hZ : Γ.ref z = some (.VTypeDia Z)) (hY : Δ.ref (ι z) = some (.VTypeDia Y))
    (L : (Δ.diaIn (ι z)).Le ((Δ.boxIn.optIn (ι z)).optIn (ι z'))) :
    Subst.SimT (Γ.diaIn z) ((θ.box.optIn z (ι z)).optIn z' (ι z')) ((θ.dia z (ι z)).mono L) := by
  refine Subst.simT_of ?_
  intro v T _ hv
  match v with
  | .step u .dia =>
      change (if u = z then (match Γ.ref z with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with huz
      subst huz
      rw [hZ] at hv
      cases hv
      change SubE.Sim Z (((θ.box.optIn u (ι u)).optIn z' (ι z')) (.step u .dia))
        (SubE.mono L (if u = u then (θ.at u).diaBody (ι u) else SubE.hide))
      rw [if_pos rfl]
      by_cases hzz : u = z'
      · subst hzz
        rw [Subst.optIn_content]
        change SubE.Sim Z (((θ.box.wit u).mono (Ctx.le_optIn Δ.boxIn (ι u))).optBody (ι u)) _
        rw [← WitE.optBody_mono]
        change SubE.Sim Z (SubE.mono _ (((θ.at u).toWit).optBody (ι u))) _
        rw [SubE.toWit_optBody hO (ι u) (Subst.okRef_at hθ hZ) (Ctx.le_diaIn_boxIn_optIn hO hY),
          SubE.mono_mono]
        exact .refl _
      · rw [Subst.optIn_ne _ _ (fun h => hzz (by cases h; rfl)), Subst.optIn_content]
        change SubE.Sim Z (SubE.mono _ (((θ.at u).toWit).optBody (ι u))) _
        rw [SubE.toWit_optBody hO (ι u) (Subst.okRef_at hθ hZ) (Ctx.le_diaIn_boxIn_optIn hO hY),
          SubE.mono_mono]
        exact .refl _
  | .step u .box =>
      change SubE.Sim T (((θ.box.optIn z (ι z)).optIn z' (ι z')) (.step u .box))
        (SubE.mono L (((θ.at u).unbox).mono (Ctx.le_boxIn_diaIn Δ (ι z))))
      rw [Subst.optIn_ne _ _ (fun h => by cases h), Subst.optIn_ne _ _ (fun h => by cases h)]
      change SubE.Sim T (SubE.mono _ (SubE.mono _ ((θ.at u).unbox))) _
      simp only [SubE.mono_mono]
      exact .refl _
  | .step u .keep =>
      change SubE.Sim T (((θ.box.optIn z (ι z)).optIn z' (ι z')) (.step u .keep))
        (SubE.mono L (((θ.at u).keepE).mono (Ctx.le_boxIn_diaIn Δ (ι z))))
      rw [Subst.optIn_ne _ _ (fun h => by cases h), Subst.optIn_ne _ _ (fun h => by cases h)]
      change SubE.Sim T (SubE.mono _ (SubE.mono _ ((θ.at u).keepE))) _
      simp only [SubE.mono_mono]
      exact .refl _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

/-- On the `◇_{z'}` view, the same, with `z'` the witness opened last. -/
theorem Subst.simT_optIn₂_dia' {σ : Signature} {Γ Δ : Ctx} {θ : Subst σ Δ} (hθ : Subst.Ok Γ θ)
    (hO : ModalSys.Opt = true) (ι : VarSymb → VarSymb) (z : VarSymb) {z' : VarSymb}
    {Z' Y' : VarType} (hZ' : Γ.ref z' = some (.VTypeDia Z'))
    (hY' : Δ.ref (ι z') = some (.VTypeDia Y'))
    (L : (Δ.diaIn (ι z')).Le ((Δ.boxIn.optIn (ι z)).optIn (ι z'))) :
    Subst.SimT (Γ.diaIn z') ((θ.box.optIn z (ι z)).optIn z' (ι z')) ((θ.dia z' (ι z')).mono L) := by
  refine Subst.simT_of ?_
  intro v T _ hv
  match v with
  | .step u .dia =>
      change (if u = z' then (match Γ.ref z' with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with huz
      subst huz
      rw [hZ'] at hv
      cases hv
      change SubE.Sim Z' (((θ.box.optIn z (ι z)).optIn u (ι u)) (.step u .dia))
        (SubE.mono L (if u = u then (θ.at u).diaBody (ι u) else SubE.hide))
      rw [if_pos rfl, Subst.optIn_content]
      change SubE.Sim Z' (((θ.box.wit u).mono (Ctx.le_optIn Δ.boxIn (ι z))).optBody (ι u)) _
      rw [← WitE.optBody_mono]
      change SubE.Sim Z' (SubE.mono _ (((θ.at u).toWit).optBody (ι u))) _
      rw [SubE.toWit_optBody hO (ι u) (Subst.okRef_at hθ hZ') (Ctx.le_diaIn_boxIn_optIn hO hY'),
        SubE.mono_mono]
      exact .refl _
  | .step u .box =>
      change SubE.Sim T (((θ.box.optIn z (ι z)).optIn z' (ι z')) (.step u .box))
        (SubE.mono L (((θ.at u).unbox).mono (Ctx.le_boxIn_diaIn Δ (ι z'))))
      rw [Subst.optIn_ne _ _ (fun h => by cases h), Subst.optIn_ne _ _ (fun h => by cases h)]
      change SubE.Sim T (SubE.mono _ (SubE.mono _ ((θ.at u).unbox))) _
      simp only [SubE.mono_mono]
      exact .refl _
  | .step u .keep =>
      change SubE.Sim T (((θ.box.optIn z (ι z)).optIn z' (ι z')) (.step u .keep))
        (SubE.mono L (((θ.at u).keepE).mono (Ctx.le_boxIn_diaIn Δ (ι z'))))
      rw [Subst.optIn_ne _ _ (fun h => by cases h), Subst.optIn_ne _ _ (fun h => by cases h)]
      change SubE.Sim T (SubE.mono _ (SubE.mono _ ((θ.at u).keepE))) _
      simp only [SubE.mono_mono]
      exact .refl _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

/-- ⭐**Substitution commutes with `≡`**: at `◇` types the contents are substituted in the view
    with both witnesses opened, which is each content's own `◇` view weakened
    (`Subst.simT_optIn₂_dia`, `Subst.simT_optIn₂_dia'`). -/
theorem WFF.subst_eqH {σ : Signature} {ι : VarSymb → VarSymb} (hO : ModalSys.Opt = true) :
    {Γ Δ : Ctx} → {d d' : ℕ} → (θ : Subst σ Δ) → (hθ : Subst.Ok Γ θ) → (hc : Subst.Coh ι Γ θ) →
    (hΓ : Γ.SlotsFrom d) → (hΔ : Δ.SlotsFrom d') → (T : VarType) → {a b : Ann T} →
    (t : Term σ Γ T a) → (s : Term σ Γ T b) →
    WFF.subst ι θ hθ hc hΓ hΔ (eqH hO T t s : WFF σ Γ d) =
      eqH hO T (Term.subst ι θ hθ hc t) (Term.subst ι θ hθ hc s)
  | _, _, _, _, _, _, _, _, _, .Var, .var, .var, t, s => by
      rw [eqH_Var, eqH_Var]
      rfl
  | _, _, _, _, _, _, _, _, _, .VTypeOne, .one, .one, .unit, .unit => rfl
  | _, _, _, _, θ, hθ, hc, hΓ, hΔ, .VTypeProd A B, .prod _ _, .prod _ _, .pair t₁ t₂,
      .pair s₁ s₂ => by
      change WFF.and (WFF.subst ι θ hθ hc hΓ hΔ (eqH hO A t₁ s₁))
        (WFF.subst ι θ hθ hc hΓ hΔ (eqH hO B t₂ s₂)) = _
      rw [WFF.subst_eqH hO θ hθ hc hΓ hΔ A t₁ s₁, WFF.subst_eqH hO θ hθ hc hΓ hΔ B t₂ s₂]
      rfl
  | _, _, _, _, θ, hθ, hc, hΓ, hΔ, .VTypeBox A, .box _, .box _, .boxtm t, .boxtm s => by
      change WFF.box (WFF.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc)
        hΓ.boxIn hΔ.boxIn (eqH hO A t s)) = _
      rw [WFF.subst_eqH hO θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn hΔ.boxIn A t s]
      rfl
  | Γ, Δ, d, d', θ, hθ, hc, hΓ, hΔ, .VTypeDia A, .dia x _, .dia x' _, .diatm _ hx t,
      .diatm _ hx' s => by
      obtain ⟨X, hr⟩ := id hx
      obtain ⟨X', hr'⟩ := id hx'
      have hw : (θ.at x).idxAlong [] = ι x := hc x _ hr []
      have hw' : (θ.at x').idxAlong [] = ι x' := hc x' _ hr' []
      obtain ⟨Y, hY⟩ := SubE.ref_witness (Subst.okRef_at hθ hr) hw
      obtain ⟨Y', hY'⟩ := SubE.ref_witness (Subst.okRef_at hθ hr') hw'
      have hb : Γ.boxIn.wit x = some X := Ctx.boxIn_wit.mpr ⟨hO, hr⟩
      have hb' : (Γ.boxIn.optIn x).wit x' = some X' := Ctx.boxIn_wit.mpr ⟨hO, hr'⟩
      have hθ₁ := Subst.ok_optIn (Subst.ok_box hθ) hO hb ((Subst.coh_box hθ hc).wit hO x X hb [])
      have hc₁ := Subst.coh_optIn (Subst.ok_box hθ) (Subst.coh_box hθ hc) hO hb
      have hθ₂ := Subst.ok_optIn hθ₁ hO hb' (hc₁.wit hO x' X' hb' [])
      have hc₂ := Subst.coh_optIn hθ₁ hc₁ hO hb'
      have ih := WFF.subst_eqH (d := d) (d' := d') hO ((θ.box.optIn x (ι x)).optIn x' (ι x'))
        hθ₂ hc₂ ((hΓ.boxIn.optIn x).optIn x') ((hΔ.boxIn.optIn (ι x)).optIn (ι x')) A
        (Term.mono (Ctx.le_diaIn_optIn₂ hO hx x') t) (Term.mono (Ctx.le_diaIn_optIn₂' hO x hx') s)
      have L := Ctx.le_diaIn_optIn₂ hO ⟨Y, hY⟩ (ι x')
      have L' := Ctx.le_diaIn_optIn₂' hO (ι x) ⟨Y', hY'⟩
      rw [Term.subst_mono, Term.subst_mono,
        Term.subst_congr_eq _ _ _ (Subst.ok_mono (Subst.ok_dia hθ hx hw) L) _
          (Subst.coh_mono (Subst.coh_dia hθ hc hx) L) (Subst.simT_optIn₂_dia hθ hO ι hr hY L) t,
        Term.subst_congr_eq _ _ _ (Subst.ok_mono (Subst.ok_dia hθ hx' hw') L') _
          (Subst.coh_mono (Subst.coh_dia hθ hc hx') L')
          (Subst.simT_optIn₂_dia' hθ hO ι x hr' hY' L') s,
        ← Term.mono_subst L _ (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx),
        ← Term.mono_subst L' _ (Subst.ok_dia hθ hx' hw') (Subst.coh_dia hθ hc hx')] at ih
      exact congrArg (fun χ => WFF.box (WFF.imp
        (WFF.or (WFF.optx hO (ι x) (Ctx.boxIn_wit_of hO ⟨Y, hY⟩) .top)
          (WFF.optx hO (ι x') (Ctx.boxIn_wit_of hO ⟨Y', hY'⟩) .top))
        (WFF.optx hO (ι x) (Ctx.boxIn_wit_of hO ⟨Y, hY⟩)
          (WFF.optx hO (ι x') (Ctx.boxIn_wit_of hO ⟨Y', hY'⟩) χ)))) ih

/-- `≡` of terms equal with their annotations. -/
theorem eqH_congr {σ : Signature} {Γ : Ctx} {d : ℕ} (hO : ModalSys.Opt = true) {T : VarType}
    {a a' b b' : Ann T} {t : Term σ Γ T a} {t' : Term σ Γ T a'} {s : Term σ Γ T b}
    {s' : Term σ Γ T b'} (ht : (⟨a, t⟩ : Σ c, Term σ Γ T c) = ⟨a', t'⟩)
    (hs : (⟨b, s⟩ : Σ c, Term σ Γ T c) = ⟨b', s'⟩) :
    (eqH hO T t s : WFF σ Γ d) = eqH hO T t' s' := by
  cases ht
  cases hs
  rfl

/-- Substituting into `◇⁰_y` where the image of `y` is known to be `z`. -/
theorem WFF.subst_optx_eq {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d d' : ℕ}
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom d)
    (hΔ : Δ.SlotsFrom d') (hO : ModalSys.Opt = true) (y : VarSymb)
    (hy : ∃ X, Γ.wit y = some X) (φ : WFF σ (Γ.optIn y) d) {z : VarSymb} (hz : ι y = z)
    (hz' : ∃ X, Δ.wit z = some X) (hθz : Subst.Ok (Γ.optIn y) (θ.optIn y z))
    (hcz : Subst.Coh ι (Γ.optIn y) (θ.optIn y z)) :
    WFF.subst ι θ hθ hc hΓ hΔ (.optx hO y hy φ) =
      .optx hO z hz' (WFF.subst ι (θ.optIn y z) hθz hcz (hΓ.optIn y) (hΔ.optIn z) φ) := by
  subst hz
  rfl

/-- In the view of a witness its content is a visible address. -/
theorem Ctx.ref_optIn_content {Γ : Ctx} {y : VarSymb} {X : VarType} (hy : Γ.wit y = some X) :
    (Γ.optIn y).ref (.step y .dia) = some X :=
  (Ctx.ref_nonproj _ rfl).trans (Ctx.optIn_content hy)

/-- `◇⁰_y (y.dia ≡ e)`, `e` the slot: the witness `y` is present, with content `e`. -/
abbrev WFF.optName {σ : Signature} {Γ : Ctx} (hO : ModalSys.Opt = true) {y : VarSymb}
    {X : VarType} (hy : Γ.wit y = some X) : WFF σ (Γ.insert (.bnd 0) X) 1 :=
  WFF.optx hO y ⟨X, hy⟩ (eqH hO X
    (Term.eta (.step y .dia) X (Ctx.ref_optIn_content (Γ := Γ.insert (.bnd 0) X) hy))
    (Term.eta (.root (.bnd 0)) X
      ((Ctx.le_optIn _ y).ref (Ctx.ref_insert_root Γ (.bnd 0) X))))

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
          (.optx hO x hw (eqH hO A (Term.mono (Ctx.le_diaIn_optIn₂ hO hx x) t)
            (Term.mono (Ctx.le_diaIn_optIn₂' hO x hx) t))) :=
        Proof.weak _ (Proof.conv (by
            rw [eqH_mono]
            first | rfl | simp only [Term.mono_mono])
          (Proof.opt_reopen hO x hre (eqH_refl hO A
            (Term.mono (hx.elim fun _ h => Ctx.le_diaIn_boxIn_optIn hO h) t))))
      have k := Proof.K_opt hO x hw (Δ₁ := []) (Δ₂ := []) inner
      have hor : Proof σ Γ.boxIn [.or (.optx hO x hw .top) (.optx hO x hw .top)] _ :=
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
    Proof σ Γ [.optx hO y ⟨X, hy⟩ .top] (.ex X (WFF.optName hO hy)) :=
  have h₀ : (Γ.optIn y).ref (.step y .dia) = some X := Ctx.ref_optIn_content hy
  have hre : ∃ X', (Γ.optIn y).wit y = some X' ∧ (Γ.optIn y) (.step y .dia) = some X' :=
    ⟨X, hy, Ctx.optIn_content hy⟩
  have reop := Proof.opt_reopen (Δ := []) hO y hre
    (Proof.eqH_refl hO X (Term.eta (σ := σ) (.step y .dia) X h₀))
  have hne : ¬ y.rt = .bnd 0 := fun h => by
    rw [(Ctx.NoSlots.slots (Γ := Γ)).wit y 0 h le_rfl] at hy
    cases hy
  have key : WFF.instantiate Ctx.NoSlots.slots (Term.eta (σ := σ) (.step y .dia) X h₀)
      (WFF.mono ((Ctx.le_optIn Γ y).insert (.bnd 0) X) (WFF.optName hO hy)) =
      .optx hO y (hre.imp fun _ h => h.1)
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
  Proof.opt_out hO y ⟨X, hy⟩ (Proof.K_opt hO y ⟨X, hy⟩ (Δ₁ := []) (Δ₂ := []) p₁)

end Proof

end V12M
