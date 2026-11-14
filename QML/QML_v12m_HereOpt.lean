import QML.QML_v12m_LeibnizH
import QML.QML_v12m_LiftT

/-!
# QML v12m — `Here` with `Opt` on: the identity view (M2 step 4, part 2)

With `Opt` on, the primitive `WFF.here` is gated off (§12.32), and `Here` is defined: the
possible object `◇_x bd` is realised here by `t` when, at the identity arrow, its content is `≡`
to `t`,

    Here(◇_x bd, t)  :=  ◇⁰ᵀ_x (collapse₀ bd ≡ t)

(§12.25).  Its rules are derived from `◇⁰ᵀ`'s (`K_opt`, `opt_out`, `opt_fun`) and Leibniz along `≡`
(`Proof.leibnizH`), with no new rule:

* ⭐`WFF.hereO`: the definition;
* ⭐`Proof.hereO_fun`: one content — two realisations are `≡`;
* ⭐`Proof.hereO_subst`: so the two are interchangeable in every formula (`here_subst`);
* ⭐`Proof.hereO_eqH`: a realisation may be replaced by a `≡` one (`here_eq`).
* ⭐`WFF.collapse_viewReadTm`, `Proof.boxx_optBoxT`: `□_x` read in the identity view (the bridge,
  then `T_box`);
* ⭐`Proof.hereO_elim`, `Proof.hereO_intro`: `here_elim` and `here_intro`.
* ⭐`Proof.eqH_readCong`, `Term.collapse_viewReadTm`, `Proof.hereO_beta`: `≡` is a congruence under
  a hole term, and `here_beta`;
* ⭐`Proof.opt_nameT`: `◇⁰ᵀ_y ⊤ ⊢ ∃e. ◇⁰ᵀ_y (y.at ≡ e)`, `here_name` at the pinned subject.
-/

namespace V12M

variable [ModalSys]

/-- ⭐**`Here` with `Opt` on**: `◇⁰ᵀ_x (collapse₀ bd ≡ t)` — the identity arrow is in `x`'s
    extent, and the content there is `≡` to `t` (§12.25). -/
def WFF.hereO {σ : Signature} {d : ℕ} (hO : ModalSys.Opt = true) (hT : ModalSys.T = true)
    {Γ : Ctx} {A : VarType} {b : Ann (.VTypeDia A)} {a : Ann A} :
    Term σ Γ (.VTypeDia A) b → Term σ Γ A a → WFF σ Γ d
  | .diatm x hx bd, t =>
      .optx hO .ident x (hx.imp fun _ h => Ctx.witT_of hT hO h)
        (eqH hO A (Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) bd)
          (Term.mono (Ctx.le_optInT Γ x) t))

/-- ⭐**A view reading, read at the world itself**: collapsing `◇_x`'s view onto the identity
    view sends the hole formula `ψ` read at `bd` to `ψ`, collapsed onto the world, read at the
    collapsed body.  What `T_box` makes of `□_x (viewReadTm bd ψ)` through the bridge. -/
theorem WFF.collapse_viewReadTm {σ : Signature} (hO : ModalSys.Opt = true)
    (hT : ModalSys.T = true) {Γ : Ctx} [Γ.NoSlots] {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (bd : Term σ (Γ.diaIn x) A a) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    WFF.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) Ctx.NoSlots.slots
        (WFF.viewReadTm bd ψ) =
      WFF.instantiate Ctx.NoSlots.slots
        (Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) bd)
        (WFF.mono ((Ctx.le_optInT Γ x).insert (.bnd 0) A)
          (WFF.collapse ((Ctx.collapses_boxIn_self hT Γ).insert
              ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) A)
            ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A) ψ)) := by
  have D := Ctx.collapses_diaIn_optInT' (Γ := Γ) (x := x) (z := x) ⟨hT, hO, rfl⟩ hx
  refine (WFF.collapse_readAt D D (Ctx.Le.refl _) (Ctx.Le.refl _) Ctx.NoSlots.slots
    Ctx.NoSlots.slots bd _).trans ?_
  unfold WFF.readAt WFF.instantiate WFF.substRoot
  rw [WFF.collapse_mono ((Ctx.collapses_boxIn_self hT Γ).insert
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) A) _ _
    ((Ctx.le_optInT Γ x).insert (.bnd 0) A) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A)]

/-- The term form of `WFF.collapse_viewReadTm`: a hole term read at `bd` in `◇_x`'s view,
    collapsed onto the identity view, is the hole term (collapsed onto the world) read at the
    collapsed body. -/
theorem Term.collapse_viewReadTm {σ : Signature} (hO : ModalSys.Opt = true)
    (hT : ModalSys.T = true) {Γ : Ctx} [Γ.NoSlots] {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (bd : Term σ (Γ.diaIn x) A a) {B : VarType} {b : Ann B}
    (s : Term σ (Γ.boxIn.insert (.bnd 0) A) B b) :
    (⟨_, Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) (Term.viewReadTm bd s)⟩ :
        Σ c, Term σ (Γ.optInT x) B c) =
      ⟨_, Term.subst (Subst.singleIdx (.bnd 0)
            (.tm (Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) bd)))
          (Subst.single (.bnd 0)
            (.tm (Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) bd)))
          (Subst.ok_single (Ctx.Le.refl _) rfl)
          (Subst.coh_single (Ctx.NoSlots.slots.rootFresh le_rfl) (Ctx.Le.refl _) rfl)
          (Term.mono ((Ctx.le_optInT Γ x).insert (.bnd 0) A)
            (Term.collapse ((Ctx.collapses_boxIn_self hT Γ).insert
              ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) A) s))⟩ := by
  have D := Ctx.collapses_diaIn_optInT' (Γ := Γ) (x := x) (z := x) ⟨hT, hO, rfl⟩ hx
  have hr := (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).rootFresh (le_refl 0)
  have hcr : Subst.Corr ((Γ.diaIn x).insert (.bnd 0) A) D (Subst.single (.bnd 0) (.tm bd))
      (Subst.single (.bnd 0) (.tm (Term.collapse D bd))) := by
    refine Subst.corr_of (Subst.ok_single (Ctx.Le.refl _) rfl) ?_
    intro v U hlp hv
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      have hU : A = U := by simpa [Ctx.insert] using hv
      subst hU
      change SubE.Sim _ (Subst.at _ (.root (.bnd 0))) _
      rw [Subst.single_self, Subst.at_single_root]
      exact .refl _
    · have hv' : (Γ.diaIn x) v = some U := Ctx.insert_ne_some hv hvr
      have hne := Ctx.ref_rt_ne hr ((Ctx.ref_nonproj _ hlp).trans hv')
      change SubE.Sim U (Subst.at _ _) (SubE.collapse _ (if v = _ then _ else _))
      rw [if_neg hvr, Subst.single_at_ne (by rwa [VarSymb.collapse_rt])]
      exact .refl _
  have e := Term.collapse_subst (D.insert hr A) D (Subst.single (.bnd 0) (.tm bd))
    (Subst.ok_single (Ctx.Le.refl _) rfl)
    (Subst.coh_single hr (Ctx.Le.refl _) rfl) (Subst.single (.bnd 0) (.tm (Term.collapse D bd)))
    (Subst.ok_single (Ctx.Le.refl _) rfl)
    (Subst.coh_single (Ctx.NoSlots.slots.rootFresh le_rfl) (Ctx.Le.refl _) rfl) hcr
    (Term.mono ((Ctx.le_boxIn_diaIn Γ x).insert (.bnd 0) A) s)
  rw [Term.collapse_mono ((Ctx.collapses_boxIn_self hT Γ).insert
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) A) (D.insert hr A)
    ((Ctx.le_boxIn_diaIn Γ x).insert (.bnd 0) A) ((Ctx.le_optInT Γ x).insert (.bnd 0) A) s] at e
  exact e

/-- `◇⁰ᵀ_y (y.at ≡ e)`, `e` the slot: `y` is realised here, with content `e`.  This is
    `Here (η y) e` with `Opt` on. -/
abbrev WFF.optNameT {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hO : ModalSys.Opt = true)
    {y : VarSymb} {X : VarType} (hy : Γ.witT y = some X) : WFF σ (Γ.insert (.bnd 0) X) 1 :=
  WFF.optx hO .ident y ⟨X, (Ctx.le_insert Ctx.NoSlots.slots.root X).witT hy⟩ (eqH hO X
    (Term.eta (.step y .at) X
      (Ctx.ref_optInT_content ((Ctx.le_insert Ctx.NoSlots.slots.root X).witT hy)))
    (Term.eta (.root (.bnd 0)) X
      ((Ctx.le_optInT _ y).ref (Ctx.ref_insert_root Γ (.bnd 0) X))))

namespace Proof

variable {σ : Signature} (hO : ModalSys.Opt = true) (hT : ModalSys.T = true) {Γ : Ctx}
  [Γ.Presented] {Δ : List (WFF σ Γ 0)}

/-- ⭐**One content**: two realisations of one possible object are `≡`.  In the identity view,
    `c ≡ t` and `c ≡ t'` give `t ≡ t'` (`opt_fun`, then symmetry and transitivity), which is the
    outer `t ≡ t'` weakened (`opt_out`). -/
def hereO_fun {A : VarType} {b : Ann (.VTypeDia A)} (s : Term σ Γ (.VTypeDia A) b)
    {a a' : Ann A} (t : Term σ Γ A a) (t' : Term σ Γ A a')
    (ph : Proof σ Γ Δ (WFF.hereO hO hT s t)) (ph' : Proof σ Γ Δ (WFF.hereO hO hT s t')) :
    Proof σ Γ Δ (eqH hO A t t') := by
  match s, ph, ph' with
  | .diatm x hx bd, ph, ph' =>
    have hw : ∃ X, Γ.witK .ident x = some X := hx.imp fun _ h => Ctx.witT_of hT hO h
    have inner : Proof σ (Γ.optInK .ident x)
        ((eqH hO A (Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) bd)
            (Term.mono (Ctx.le_optInT Γ x) t)).and
          (eqH hO A (Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) bd)
            (Term.mono (Ctx.le_optInT Γ x) t')) :: ([] ++ ([] : List (WFF σ Γ 0)).map
              (WFF.mono (Ctx.le_optInK Γ .ident x))))
        (WFF.mono (Ctx.le_optInK Γ .ident x) (eqH hO A t t')) :=
      Proof.conv (eqH_mono hO (Ctx.le_optInT Γ x) A t t').symm
        (Proof.eqH_trans hO A (Proof.eqH_symm hO A (.and_elim_l (Proof.lookup List.mem_cons_self)))
          (.and_elim_r (Proof.lookup List.mem_cons_self)))
    exact Proof.opt_out hO .ident x hw
      (Proof.dischargeAll (Proof.K_opt hO .ident x hw (Δ₁ := []) (Δ₂ := []) inner)
        (.cons (Proof.dischargeAll (Proof.opt_fun hO .ident x hw _ _) (.cons ph (.cons ph' .nil)))
          .nil))

/-- ⭐**Functionality, substitutionally** (`here_subst` with `Opt` on): two realisations of one
    possible object are interchangeable in every formula — Leibniz along their `≡`. -/
def hereO_subst {A : VarType} {b : Ann (.VTypeDia A)} (s : Term σ Γ (.VTypeDia A) b)
    {a a' : Ann A} (t : Term σ Γ A a) (t' : Term σ Γ A a') (φ : WFF σ (Γ.insert (.bnd 0) A) 1)
    (ph : Proof σ Γ Δ (WFF.hereO hO hT s t)) (ph' : Proof σ Γ Δ (WFF.hereO hO hT s t'))
    (pf : Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ)) :
    Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t' φ) :=
  Proof.leibnizH hO A (hereO_fun hO hT s t t' ph ph') pf

/-- ⭐**Replacing the realisation** (`here_eq` with `Opt` on): a realisation may be replaced by a
    `≡` one — transitivity of `≡` in the identity view, the outer `t ≡ t'` carried in. -/
def hereO_eqH {A : VarType} {b : Ann (.VTypeDia A)} (s : Term σ Γ (.VTypeDia A) b)
    {a a' : Ann A} (t : Term σ Γ A a) (t' : Term σ Γ A a')
    (ph : Proof σ Γ Δ (WFF.hereO hO hT s t)) (pe : Proof σ Γ Δ (eqH hO A t t')) :
    Proof σ Γ Δ (WFF.hereO hO hT s t') := by
  match s, ph with
  | .diatm x hx bd, ph =>
    have hw : ∃ X, Γ.witK .ident x = some X := hx.imp fun _ h => Ctx.witT_of hT hO h
    have inner : Proof σ (Γ.optInK .ident x)
        (eqH hO A (Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) bd)
            (Term.mono (Ctx.le_optInT Γ x) t) ::
          ([] ++ [eqH hO A t t'].map (WFF.mono (Ctx.le_optInK Γ .ident x))))
        (eqH hO A (Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) bd)
          (Term.mono (Ctx.le_optInT Γ x) t')) :=
      Proof.eqH_trans hO A (Proof.lookup List.mem_cons_self)
        (Proof.conv (eqH_mono hO (Ctx.le_optInT Γ x) A t t')
          (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))
    exact Proof.dischargeAll (Proof.K_opt hO .ident x hw (Δ₁ := [eqH hO A t t']) (Δ₂ := []) inner)
      (.cons ph (.cons pe .nil))

/-- ⭐**`□_x` read at the identity witness** (`Opt`, T): what is necessary over `x`'s extent
    holds in `x`'s identity view, collapsed.  The bridge takes `□_x χ` to `□ □⁰_x χ`, and `T_box`
    reads that at the world itself, where the arrow witness is the identity witness. -/
def boxx_optBoxT (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (χ : WFF σ (Γ.diaIn x) 0) (pb : Proof σ Γ Δ (WFF.boxx x hx χ)) :
    Proof σ Γ Δ (WFF.optBox hO .ident x (hx.imp fun _ h => Ctx.witT_of hT hO h)
      (WFF.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) Ctx.NoSlots.slots χ)) := by
  have pbox : Proof σ Γ Δ (.box (WFF.optx hO .arrow x (Ctx.boxIn_wit_of hO hx)
      (WFF.mono (Ctx.le_diaIn_boxIn_optIn' hO hx) χ.neg)).neg) :=
    .or_elim (.lem _) (Proof.lookup List.mem_cons_self)
      (.bot_elim _ (.imp_elim (Proof.weak _ pb)
        (.opt_dia hO x hx (Proof.lookup List.mem_cons_self))))
  refine Proof.conv ?_ (Proof.T_box hT pbox)
  obtain ⟨Z, hZ⟩ := Ctx.boxIn_wit_of hO hx
  change WFF.imp (WFF.optx hO .ident x _ (WFF.collapse
    ((Ctx.collapses_boxIn_self hT Γ).optIn_zero hO hZ) _
    (WFF.mono (Ctx.le_diaIn_boxIn_optIn' hO hx) χ.neg))) .bot = _
  rw [WFF.collapse_mono (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) _ _ (Ctx.Le.refl _)
    Ctx.NoSlots.slots, WFF.mono_refl]
  rfl

/-- ⭐**Elimination** (`here_elim` with `Opt` on): if `◇_x bd` is realised here by `t`, what is
    necessary over `x`'s extent holds of `t`.  `□_x` is read in the identity view
    (`boxx_optBoxT`, `WFF.collapse_viewReadTm`), Leibniz along the realisation's `≡` moves the
    hole from the collapsed body to `t`, and `opt_out` leaves the view. -/
def hereO_elim (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType}
    {a : Ann A} (t : Term σ Γ A a) {a' : Ann A} (bd : Term σ (Γ.diaIn x) A a')
    (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1)
    (ph : Proof σ Γ Δ (WFF.hereO hO hT (Term.diatm x hx bd) t))
    (pb : Proof σ Γ Δ (WFF.boxx x hx (WFF.viewReadTm bd ψ))) :
    Proof σ Γ Δ (WFF.hereRead hT t ψ) := by
  have hw : ∃ X, Γ.witK .ident x = some X := hx.imp fun _ h => Ctx.witT_of hT hO h
  have pT := Proof.conv (congrArg (WFF.optBox hO .ident x hw)
      (WFF.collapse_viewReadTm hO hT hx bd ψ))
    (boxx_optBoxT hO hT x hx _ pb)
  have inner : Proof σ (Γ.optInK .ident x)
      (eqH hO A (Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) bd)
          (Term.mono (Ctx.le_optInT Γ x) t) ::
        ([(WFF.instantiate Ctx.NoSlots.slots
            (Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) bd)
            (WFF.mono ((Ctx.le_optInT Γ x).insert (.bnd 0) A)
              (WFF.collapse ((Ctx.collapses_boxIn_self hT Γ).insert
                  ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) A)
                ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A) ψ)) :
              WFF σ (Γ.optInK .ident x) 0)] ++
          ([] : List (WFF σ Γ 0)).map (WFF.mono (Ctx.le_optInK Γ .ident x))))
      (WFF.mono (Ctx.le_optInK Γ .ident x) (WFF.hereRead hT t ψ)) :=
    Proof.conv (WFF.mono_instantiate (Ctx.le_optInT Γ x) Ctx.NoSlots.slots Ctx.NoSlots.slots t
        _).symm
      (Proof.leibnizH (Γ := Γ.optInT x) hO A (Proof.lookup List.mem_cons_self)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))
  exact Proof.opt_out hO .ident x hw
    (Proof.dischargeAll (Proof.K_opt hO .ident x hw (Δ₁ := []) (Δ₂ := [_]) inner)
      (.cons ph (.cons pT .nil)))

/-- ⭐**Introduction** (`here_intro` with `Opt` on): what holds of the realisation here is
    possible for the witness.  By contradiction: `¬◇_x χ` gives `□_x ¬χ`, which `hereO_elim` reads
    at `t` (both readings commute with `¬`). -/
def hereO_intro (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType}
    {a : Ann A} (t : Term σ Γ A a) {a' : Ann A} (bd : Term σ (Γ.diaIn x) A a')
    (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1)
    (ph : Proof σ Γ Δ (WFF.hereO hO hT (Term.diatm x hx bd) t))
    (pr : Proof σ Γ Δ (WFF.hereRead hT t ψ)) :
    Proof σ Γ Δ (WFF.dia x hx (WFF.viewReadTm bd ψ)) := by
  have dn : Proof σ (Γ.diaIn x)
      ((WFF.viewReadTm bd ψ).neg.neg ::
        (([] : List (WFF σ (Γ.diaIn x) 0)) ++
          ([] : List (WFF σ Γ.boxIn 0)).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x))))
      (WFF.viewReadTm bd ψ) :=
    .or_elim (.lem _) (Proof.lookup List.mem_cons_self)
      (.bot_elim _ (.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
        (Proof.lookup List.mem_cons_self)))
  have pbx : Proof σ Γ ((WFF.dia x hx (WFF.viewReadTm bd ψ)).neg :: Δ)
      (WFF.boxx x hx (WFF.viewReadTm bd ψ.neg)) :=
    .imp_intro (.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.ofSubset (fun _ h => by
          rw [List.mem_singleton.mp h]
          exact List.mem_cons_self)
        (Proof.K_dia x hx (Δ₁ := []) (Δ₂ := []) dn)))
  exact .or_elim (.lem (WFF.dia x hx (WFF.viewReadTm bd ψ))) (Proof.lookup List.mem_cons_self)
    (.bot_elim _ (.imp_elim (hereO_elim hO hT x hx t bd ψ.neg (Proof.weak _ ph) pbx)
      (Proof.weak _ pr)))

/-- ⭐**`≡` is a congruence under a hole term**: from `u ≡ v`, `s[u] ≡ s[v]`.  Leibniz at the
    hole formula `s[u] ≡ s[·]`, from reflexivity. -/
def eqH_readCong {A B : VarType} {a a' : Ann A} {b : Ann B} (u : Term σ Γ A a)
    (v : Term σ Γ A a') (s : Term σ (Γ.insert (.bnd 0) A) B b)
    (h : Proof σ Γ Δ (eqH hO A u v)) :
    Proof σ Γ Δ (eqH hO B
      (Term.subst (Subst.singleIdx (.bnd 0) (.tm u)) (Subst.single (.bnd 0) (.tm u))
        (Subst.ok_single (Ctx.Le.refl Γ) rfl)
        (Subst.coh_single (Ctx.NoSlots.slots.rootFresh le_rfl) (Ctx.Le.refl Γ) rfl) s)
      (Term.subst (Subst.singleIdx (.bnd 0) (.tm v)) (Subst.single (.bnd 0) (.tm v))
        (Subst.ok_single (Ctx.Le.refl Γ) rfl)
        (Subst.coh_single (Ctx.NoSlots.slots.rootFresh le_rfl) (Ctx.Le.refl Γ) rfl) s)) := by
  have inst : ∀ {c : Ann A} (w : Term σ Γ A c),
      WFF.instantiate Ctx.NoSlots.slots w
          (eqH hO B (Term.mono (Ctx.le_insert Ctx.NoSlots.slots.root A)
            (Term.subst (Subst.singleIdx (.bnd 0) (.tm u)) (Subst.single (.bnd 0) (.tm u))
              (Subst.ok_single (Ctx.Le.refl Γ) rfl)
              (Subst.coh_single (Ctx.NoSlots.slots.rootFresh le_rfl) (Ctx.Le.refl Γ) rfl) s))
            s) =
        (eqH hO B
          (Term.subst (Subst.singleIdx (.bnd 0) (.tm u)) (Subst.single (.bnd 0) (.tm u))
            (Subst.ok_single (Ctx.Le.refl Γ) rfl)
            (Subst.coh_single (Ctx.NoSlots.slots.rootFresh le_rfl) (Ctx.Le.refl Γ) rfl) s)
          (Term.subst (Subst.singleIdx (.bnd 0) (.tm w)) (Subst.single (.bnd 0) (.tm w))
            (Subst.ok_single (Ctx.Le.refl Γ) rfl)
            (Subst.coh_single (Ctx.NoSlots.slots.rootFresh le_rfl) (Ctx.Le.refl Γ) rfl) s) :
          WFF σ Γ 0) := by
    intro c w
    rw [WFF.instantiate, WFF.substRoot, WFF.subst_eqH]
    exact eqH_congr hO (Term.subst_single_mono_slot w _) rfl
  exact Proof.conv (inst v)
    (Proof.leibnizH hO A h (Proof.conv (inst u).symm (Proof.eqH_refl hO B _)))

/-- ⭐**β** (`here_beta` with `Opt` on): the realisation of a body read through a hole term is
    the realisation read through the same hole — `≡`'s congruence in the identity view. -/
def hereO_beta (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType}
    {a : Ann A} (t : Term σ Γ A a) {a' : Ann A} (bd : Term σ (Γ.diaIn x) A a')
    {B : VarType} {b : Ann B} (s : Term σ (Γ.boxIn.insert (.bnd 0) A) B b)
    (ph : Proof σ Γ Δ (WFF.hereO hO hT (Term.diatm x hx bd) t)) :
    Proof σ Γ Δ (WFF.hereO hO hT (Term.diatm x hx (Term.viewReadTm bd s))
      (Term.hereRead hT t s)) := by
  have hw : ∃ X, Γ.witK .ident x = some X := hx.imp fun _ h => Ctx.witT_of hT hO h
  have ea : Term.mono (Ctx.le_optInT Γ x) (Term.hereRead hT t s) =
      Term.subst (Subst.singleIdx (.bnd 0) (.tm (Term.mono (Ctx.le_optInT Γ x) t)))
        (Subst.single (.bnd 0) (.tm (Term.mono (Ctx.le_optInT Γ x) t)))
        (Subst.ok_single (Ctx.Le.refl _) rfl)
        (Subst.coh_single (Ctx.NoSlots.slots.rootFresh le_rfl) (Ctx.Le.refl _) rfl)
        (Term.mono ((Ctx.le_optInT Γ x).insert (.bnd 0) A)
          (Term.collapse ((Ctx.collapses_boxIn_self hT Γ).insert
            ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) A) s)) := by
    rw [Term.mono_hereRead hT (Ctx.le_optInT Γ x) t s]
    unfold Term.hereRead
    rw [Term.collapse_mono ((Ctx.collapses_boxIn_self hT Γ).insert
        ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) A) _ _
      ((Ctx.le_optInT Γ x).insert (.bnd 0) A) s]
  have inner : Proof σ (Γ.optInK .ident x)
      (eqH hO A (Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) bd)
          (Term.mono (Ctx.le_optInT Γ x) t) ::
        (([] : List (WFF σ (Γ.optInK .ident x) 0)) ++
          ([] : List (WFF σ Γ 0)).map (WFF.mono (Ctx.le_optInK Γ .ident x))))
      (eqH hO B (Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx)
          (Term.viewReadTm bd s))
        (Term.mono (Ctx.le_optInT Γ x) (Term.hereRead hT t s))) :=
    Proof.conv (eqH_congr hO (Term.collapse_viewReadTm hO hT hx bd s).symm
        (congrArg (Sigma.mk _) ea.symm))
      (eqH_readCong (Γ := Γ.optInT x) hO _ _ _ (Proof.lookup List.mem_cons_self))
  exact Proof.dischargeAll (Proof.K_opt hO .ident x hw (Δ₁ := []) (Δ₂ := []) inner)
    (.cons ph .nil)

omit [Γ.Presented] in
/-- ⭐**A realised possible object's content has a name** (`here_name` with `Opt` on, at the
    pinned subject): `◇⁰ᵀ_y ⊤ ⊢ ∃e. ◇⁰ᵀ_y (y.at ≡ e)`.  As `Proof.opt_name`, at the identity
    kind: inside the view `y.at ≡ y.at`, re-opened, `∃`-introduced at `y.at`, carried out by
    `K_opt` and `opt_out`.  What the KT tree names identity contents by. -/
def opt_nameT [Γ.NoSlots] {y : VarSymb} {X : VarType} (hy : Γ.witT y = some X) :
    Proof σ Γ [.optx hO .ident y ⟨X, hy⟩ .top] (.ex X (WFF.optNameT hO hy)) := by
  have h₀ : (Γ.optInT y).ref (.step y .at) = some X := Ctx.ref_optInT_content hy
  have hyT : (Γ.optInT y).witT y = some X := (Ctx.le_optInT Γ y).witT hy
  have hre : ∃ X', (Γ.optInT y).witK .ident y = some X' ∧
      (Γ.optInT y) (.step y WitKind.ident.step) = some X' :=
    ⟨X, hyT, Ctx.optInT_content hy⟩
  have reop := Proof.opt_reopen (Δ := []) hO .ident y hre
    (Proof.eqH_refl hO X (Term.eta (σ := σ) (.step y .at) X h₀))
  have hne : y.rt ≠ .bnd 0 := Ctx.NoSlots.ref_bnd0 (Ctx.witT_spec hy).2.2
  have key : WFF.instantiate Ctx.NoSlots.slots (Term.eta (σ := σ) (.step y .at) X h₀)
      (WFF.mono ((Ctx.le_optInT Γ y).insert (.bnd 0) X) (WFF.optNameT hO hy)) =
      .optx hO .ident y (hre.imp fun _ h => h.1)
        (WFF.mono (Ctx.le_optInK _ .ident y) (eqH hO X (Term.eta (.step y .at) X h₀)
          (Term.eta (.step y .at) X h₀))) := by
    rw [WFF.instantiate, WFF.substRoot,
      WFF.subst_mono (hΓ := (Ctx.NoSlots.slots (Γ := Γ)).insert X)]
    have hz : Subst.singleIdx (.bnd 0) (.tm (Term.eta (σ := σ) (.step y .at) X h₀)) y = y :=
      if_neg hne
    have hθ := (Subst.ok_single (Ctx.Le.refl (Γ.optInT y)) (Γ := Γ.optInT y) (r := .bnd 0)
      (T := X) (e := .tm (Term.eta (σ := σ) (.step y .at) X h₀)) rfl).restrict
        ((Ctx.le_optInT Γ y).insert (.bnd 0) X)
    have hc := (Subst.coh_single ((Ctx.NoSlots.slots (Γ := Γ.optInT y)).rootFresh le_rfl)
      (Ctx.Le.refl (Γ.optInT y)) (T := X)
      (e := .tm (Term.eta (σ := σ) (.step y .at) X h₀)) rfl).restrict
        ((Ctx.le_optInT Γ y).insert (.bnd 0) X)
    have hyI : (Γ.insert (.bnd 0) X).witT y = some X :=
      (Ctx.le_insert Ctx.NoSlots.slots.root X).witT hy
    have hat₀ : (Subst.single (.bnd 0) (.tm (Term.eta (σ := σ) (.step y .at) X h₀))).at y =
        .ren y := Subst.single_at_ne hne
    have hθz := Subst.ok_optInT hθ (y := y) (z := y) hyI (by rw [hat₀]; rfl)
    have hcz : Subst.Coh (Subst.singleIdx (.bnd 0) (.tm (Term.eta (σ := σ) (.step y .at) X h₀)))
        ((Γ.insert (.bnd 0) X).optInT y)
        ((Subst.single (.bnd 0) (.tm (Term.eta (σ := σ) (.step y .at) X h₀))).optInT y y) := by
      have := Subst.coh_optInT hθ hc (y := y) hyI
      rwa [hz] at this
    have hat : ((Subst.single (.bnd 0) (.tm (Term.eta (σ := σ) (.step y .at) X h₀))).optInT
        y y).at (.step y .at) = .ren (.step y .at) := by
      rw [Subst.at_nonproj _ rfl, Subst.optInT_content, hat₀]
      rfl
    have hat₂ : ((Subst.single (.bnd 0) (.tm (Term.eta (σ := σ) (.step y .at) X h₀))).optInT
        y y).at (.root (.bnd 0)) =
        .tm (Term.mono (Ctx.le_optInT _ y) (Term.eta (σ := σ) (.step y .at) X h₀)) := by
      change ((Subst.single (.bnd 0) (.tm (Term.eta (σ := σ) (.step y .at) X h₀))).optInT
        y y) (.root (.bnd 0)) = _
      rw [Subst.optInT_ne _ _ (fun h => by cases h), Subst.single_root]
      rfl
    rw [WFF.subst_optxT_eq (Γ := Γ.insert (.bnd 0) X) (Δ := Γ.optInT y) _ _ _ _ _ hO y ⟨X, hyI⟩
        _ hz ⟨X, hyT⟩ hθz hcz, WFF.subst_eqH,
      eqH_congr hO (Term.subst_eta_renAt _ _ _ X _ _ _
          (Ctx.ref_optInT_content (Γ := Γ.optInT y) hyT) hat)
        (Term.subst_eta_tm _ _ _ X _ _ _ hat₂)]
    change _ = WFF.optx hO .ident y _ (WFF.mono (Ctx.le_optInT _ y) _)
    rw [eqH_mono, Term.mono_eta]
  have p₁ : Proof σ (Γ.optInK .ident y)
      (.top :: (([] : List (WFF σ (Γ.optInK .ident y) 0)) ++
        ([] : List (WFF σ Γ 0)).map (WFF.mono (Ctx.le_optInK Γ .ident y))))
      (WFF.mono (Ctx.le_optInK Γ .ident y) (.ex X (WFF.optNameT hO hy))) :=
    Proof.weak _ (Proof.ex_intro X (Term.eta (.step y .at) X h₀) (Proof.conv key.symm reop))
  exact Proof.opt_out hO .ident y ⟨X, hy⟩
    (Proof.K_opt hO .ident y ⟨X, hy⟩ (Δ₁ := []) (Δ₂ := []) p₁)

end Proof

end V12M
