import QML.QML_v12m_GKShift

/-!
# QML v12m — collapsing GK derivations (weak T with `Opt`, docs §12.35)

T's principal cut reductions (`□R` against `TL`, `diaT` against `◇_xL`) re-derive a premise at a
lower level: the premise collapsed onto the current world.  With `Opt` on the collapse is not a
substitution (it turns `◇⁰_y` into `◇⁰ᵀ_y`, a change of kind), so it is proved by induction on the
height (`GK.collapseD`), with the eigenvariable rules renamed to a root fresh for the target first.

* `Subst.CorrW.single`, `WFF.collapse_single`: a single-root substitution commutes with a collapse
  at any level; `WFF.collapse_instantiate`, `WFF.collapse_bindFree` are instances.
* `WFF.collapse_collapse`: collapses at two levels commute (for `TL` and `diaT` inside a collapsed
  derivation), the formula form of `Term.collapse_collapse`.
* ⭐`GK.collapseD`.
-/

namespace V12M

variable [ModalSys] {σ : Signature}

/-! ## A single-root substitution and a collapse -/

/-- A single-root substitution's witnesses go to themselves, so at every level they correspond. -/
theorem Subst.CorrW.single {k : ℕ} {Λ Ω Ω' : Ctx} {r : Root} {T : VarType}
    {D : Ctx.Collapses k Ω Ω'} (hr : Λ.RootFresh r) (hle : Λ.Le Ω) {e : SubE σ Ω}
    {e' : SubE σ Ω'} : Subst.CorrW (Λ.insert r T) D (Subst.single r e) (Subst.single r e') := by
  cases k with
  | zero => exact Subst.CorrW.single_zero hr hle
  | succ k =>
      intro y X hy z hzi
      have hz : y = z := hzi
      subst hz
      refine ⟨rfl, X, hle.wit y X hy, ?_⟩
      change SubE.Sim X (SubE.ren (.step (y.collapse k) .dia))
        (SubE.ren ((VarSymb.step y .dia).collapse (k + 1)))
      rw [VarSymb.collapse_level_succ rfl]
      exact .refl _

/-- ⭐**Collapsing a single-root substitution** is substituting the collapsed entry into the
    collapsed formula, at any level. -/
theorem WFF.collapse_single {k : ℕ} {Λ Λ' Ω Ω' : Ctx} {d d' : ℕ} (C : Ctx.Collapses k Λ Λ')
    (D : Ctx.Collapses k Ω Ω') {r : Root} (hr : Λ.RootFresh r) (hr' : Λ'.RootFresh r)
    {T : VarType} (hle : Λ.Le Ω) (hle' : Λ'.Le Ω') {e : SubE σ Ω} (he : e.OkRef T)
    (hs : (Λ.insert r T).SlotsFrom d) (hs' : (Λ'.insert r T).SlotsFrom d)
    (ht : Ω.SlotsFrom d') (ht' : Ω'.SlotsFrom d') (φ : WFF σ (Λ.insert r T) d) :
    WFF.collapse D ht (WFF.subst (Subst.singleIdx r e) (Subst.single r e)
        (Subst.ok_single hle he) (Subst.coh_single hr hle he) hs ht φ) =
      WFF.subst (Subst.singleIdx r (e.collapse D)) (Subst.single r (e.collapse D))
        (Subst.ok_single hle' (SubE.okRef_collapse D he))
        (Subst.coh_single hr' hle' (SubE.okRef_collapse D he)) hs' ht'
        (WFF.collapse (C.insert hr T) hs φ) := by
  refine WFF.collapse_subst (C.insert hr T) D _ _ _ _ _ _ hs hs' ht ht' ?_ φ
    (fun _ => Subst.CorrW.single hr hle)
  refine Subst.corr_of (Subst.ok_single hle he) ?_
  intro v U hlp hv
  by_cases hvr : v = .root r
  · subst hvr
    have hU : T = U := by simpa [Ctx.insert] using hv
    subst hU
    change SubE.Sim _ (Subst.at _ (.root r)) _
    rw [Subst.single_self, Subst.at_single_root]
    exact .refl _
  · have hv' : Λ v = some U := Ctx.insert_ne_some hv hvr
    have hne := Ctx.ref_rt_ne hr ((Ctx.ref_nonproj _ hlp).trans hv')
    change SubE.Sim U (Subst.at _ _) (SubE.collapse _ (if v = _ then _ else _))
    rw [if_neg hvr, Subst.single_at_ne (by rwa [VarSymb.collapse_rt])]
    exact .refl _

/-- Collapsing an instance is instantiating the collapse with the collapsed term. -/
theorem WFF.collapse_instantiate {k : ℕ} {Γ₁ Γ₂ : Ctx} [Γ₁.NoSlots] [Γ₂.NoSlots]
    (C : Ctx.Collapses k Γ₁ Γ₂) {T : VarType} {a : Ann T} (t : Term σ Γ₁ T a)
    (φ : WFF σ (Γ₁.insert (.bnd 0) T) 1) :
    WFF.collapse C Ctx.NoSlots.slots (WFF.instantiate Ctx.NoSlots.slots t φ) =
      WFF.instantiate Ctx.NoSlots.slots (Term.collapse C t)
        (WFF.collapse (C.insert ((Ctx.NoSlots.slots (Γ := Γ₁)).rootFresh le_rfl) T)
          ((Ctx.NoSlots.slots (Γ := Γ₁)).insert T) φ) :=
  WFF.collapse_single C C ((Ctx.NoSlots.slots (Γ := Γ₁)).rootFresh le_rfl)
    ((Ctx.NoSlots.slots (Γ := Γ₂)).rootFresh le_rfl) (Ctx.Le.refl _) (Ctx.Le.refl _)
    (e := .tm t) rfl _ _ _ _ φ

/-- Collapsing a bound eigenvariable is binding it in the collapse, the root fresh on both
    sides. -/
theorem WFF.collapse_bindFree {k : ℕ} {Γ₁ Γ₂ : Ctx} [Γ₁.NoSlots] [Γ₂.NoSlots]
    (C : Ctx.Collapses k Γ₁ Γ₂) {u : ℕ} (hu : Γ₁.RootFresh (.free u))
    (hu' : Γ₂.RootFresh (.free u)) (T : VarType) (φ : WFF σ (Γ₁.insert (.free u) T) 0) :
    WFF.collapse (C.insert ((Ctx.NoSlots.slots (Γ := Γ₁)).rootFresh le_rfl) T)
        ((Ctx.NoSlots.slots (Γ := Γ₁)).insert T) (WFF.bindFree u hu Ctx.NoSlots.slots T φ) =
      WFF.bindFree u hu' Ctx.NoSlots.slots T
        (WFF.collapse (C.insert hu T) ((Ctx.NoSlots.slots (Γ := Γ₁)).insertFree u T) φ) :=
  WFF.collapse_single C (C.insert ((Ctx.NoSlots.slots (Γ := Γ₁)).rootFresh le_rfl) T) hu hu'
    (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ₁)).root T)
    (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ₂)).root T)
    (e := .ren (.root (.bnd 0))) (Ctx.ref_insert_root Γ₁ (.bnd 0) T) _ _ _ _ φ

/-! ## Collapses at two levels commute -/

theorem Rel.collapse_collapse {k m : ℕ} {Γ₁ Γ₂ Γ₃ Γ₄ : Ctx}
    (h₁₂ : Ctx.Collapses (k + 1 + m) Γ₁ Γ₂) (h₂₃ : Ctx.Collapses m Γ₂ Γ₃)
    (h₁₄ : Ctx.Collapses m Γ₁ Γ₄) (h₄₃ : Ctx.Collapses (k + m) Γ₄ Γ₃) :
    ∀ {n : ℕ} (ρ : Rel σ Γ₁ n),
      Rel.collapse h₂₃ (Rel.collapse h₁₂ ρ) = Rel.collapse h₄₃ (Rel.collapse h₁₄ ρ)
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.collapse h₂₃ (Rel.collapse h₁₂ ρ))
          (Term.collapse h₂₃ (Term.collapse h₁₂ t)) =
        Rel.eval (Rel.collapse h₄₃ (Rel.collapse h₁₄ ρ)) (Term.collapse h₄₃ (Term.collapse h₁₄ t))
      rw [Rel.collapse_collapse h₁₂ h₂₃ h₁₄ h₄₃ ρ,
        eq_of_heq (Sigma.mk.inj (Term.collapse_collapse h₁₂ h₂₃ h₁₄ h₄₃ t)).2]

/-- ⭐**Collapsing at level `k + 1 + m` then `m` is collapsing at `m` then `k + m`**, for formulas,
    with `Opt` on (the relation primitives are off there, `ModalSys.optStage`). -/
theorem WFF.collapse_collapse (hO : ModalSys.Opt = true) : ∀ {k m : ℕ} {Γ₁ Γ₂ Γ₃ Γ₄ : Ctx}
    {d : ℕ} (h₁₂ : Ctx.Collapses (k + 1 + m) Γ₁ Γ₂) (h₂₃ : Ctx.Collapses m Γ₂ Γ₃)
    (h₁₄ : Ctx.Collapses m Γ₁ Γ₄) (h₄₃ : Ctx.Collapses (k + m) Γ₄ Γ₃)
    (hs₁ : Γ₁.SlotsFrom d) (hs₂ : Γ₂.SlotsFrom d) (hs₄ : Γ₄.SlotsFrom d) (φ : WFF σ Γ₁ d),
    WFF.collapse h₂₃ hs₂ (WFF.collapse h₁₂ hs₁ φ) = WFF.collapse h₄₃ hs₄ (WFF.collapse h₁₄ hs₁ φ)
  | _, _, _, _, _, _, _, h₁₂, h₂₃, h₁₄, h₄₃, _, _, _, .atom ρ =>
      congrArg WFF.atom (Rel.collapse_collapse h₁₂ h₂₃ h₁₄ h₄₃ ρ)
  | _, _, _, _, _, _, _, h₁₂, h₂₃, h₁₄, h₄₃, _, _, _, .eq t s =>
      congrArg₂ WFF.eq (eq_of_heq (Sigma.mk.inj (Term.collapse_collapse h₁₂ h₂₃ h₁₄ h₄₃ t)).2)
        (eq_of_heq (Sigma.mk.inj (Term.collapse_collapse h₁₂ h₂₃ h₁₄ h₄₃ s)).2)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, _, _, _, h₁₂, h₂₃, h₁₄, h₄₃, hs₁, hs₂, hs₄, .and φ ψ =>
      congrArg₂ WFF.and (WFF.collapse_collapse hO h₁₂ h₂₃ h₁₄ h₄₃ hs₁ hs₂ hs₄ φ)
        (WFF.collapse_collapse hO h₁₂ h₂₃ h₁₄ h₄₃ hs₁ hs₂ hs₄ ψ)
  | _, _, _, _, _, _, _, h₁₂, h₂₃, h₁₄, h₄₃, hs₁, hs₂, hs₄, .or φ ψ =>
      congrArg₂ WFF.or (WFF.collapse_collapse hO h₁₂ h₂₃ h₁₄ h₄₃ hs₁ hs₂ hs₄ φ)
        (WFF.collapse_collapse hO h₁₂ h₂₃ h₁₄ h₄₃ hs₁ hs₂ hs₄ ψ)
  | _, _, _, _, _, _, _, h₁₂, h₂₃, h₁₄, h₄₃, hs₁, hs₂, hs₄, .imp φ ψ =>
      congrArg₂ WFF.imp (WFF.collapse_collapse hO h₁₂ h₂₃ h₁₄ h₄₃ hs₁ hs₂ hs₄ φ)
        (WFF.collapse_collapse hO h₁₂ h₂₃ h₁₄ h₄₃ hs₁ hs₂ hs₄ ψ)
  | _, _, _, _, _, _, _, h₁₂, h₂₃, h₁₄, h₄₃, hs₁, hs₂, hs₄, .all T φ =>
      congrArg (WFF.all T) (WFF.collapse_collapse hO (h₁₂.insert (hs₁.rootFresh le_rfl) T)
        (h₂₃.insert (hs₂.rootFresh le_rfl) T) (h₁₄.insert (hs₁.rootFresh le_rfl) T)
        (h₄₃.insert (hs₄.rootFresh le_rfl) T) (hs₁.insert T) (hs₂.insert T) (hs₄.insert T) φ)
  | _, _, _, _, _, _, _, h₁₂, h₂₃, h₁₄, h₄₃, hs₁, hs₂, hs₄, .ex T φ =>
      congrArg (WFF.ex T) (WFF.collapse_collapse hO (h₁₂.insert (hs₁.rootFresh le_rfl) T)
        (h₂₃.insert (hs₂.rootFresh le_rfl) T) (h₁₄.insert (hs₁.rootFresh le_rfl) T)
        (h₄₃.insert (hs₄.rootFresh le_rfl) T) (hs₁.insert T) (hs₂.insert T) (hs₄.insert T) φ)
  | _, m, _, _, _, _, _, h₁₂, h₂₃, h₁₄, h₄₃, hs₁, hs₂, hs₄, .box φ =>
      congrArg WFF.box (WFF.collapse_collapse hO (m := m + 1) h₁₂.boxIn h₂₃.boxIn h₁₄.boxIn
        h₄₃.boxIn hs₁.boxIn hs₂.boxIn hs₄.boxIn φ)
  | k, m, _, _, Γ₃, Γ₄, d, h₁₂, h₂₃, h₁₄, h₄₃, hs₁, hs₂, hs₄, .dia x hx φ => by
      have key : ∀ (y : VarSymb) (_hy : y = (x.collapse (k + 1 + m)).collapse m)
          (P : ∃ X, Γ₃.ref y = some (.VTypeDia X))
          (h' : Ctx.Collapses (k + m + 1) (Γ₄.diaIn (x.collapse m)) (Γ₃.diaIn y))
          (hs' : (Γ₄.diaIn (x.collapse m)).SlotsFrom d),
          WFF.collapse h₂₃ hs₂ (WFF.collapse h₁₂ hs₁ (WFF.dia x hx φ)) =
            WFF.dia y P (WFF.collapse h' hs' (WFF.collapse (h₁₄.diaIn x) (hs₁.diaIn x) φ)) := by
        intro y hy P h' hs'
        subst hy
        exact congrArg (WFF.dia _ _) (WFF.collapse_collapse hO (m := m + 1) (h₁₂.diaIn x)
          (h₂₃.diaIn _) (h₁₄.diaIn x) h' (hs₁.diaIn x) (hs₂.diaIn _) hs' φ)
      exact key _ (VarSymb.collapse_collapse x k m).symm _ _ (hs₄.diaIn _)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .here _ _ _ hO' =>
      absurd hO (by rw [hO']; decide)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .back hB _ _ _ =>
      absurd hO (by rw [ModalSys.noOpt_of_BStrong hB]; decide)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .retS hB _ _ _ =>
      absurd hO (by rw [ModalSys.noOpt_of_BStrong hB]; decide)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .retxS hB _ _ _ _ _ =>
      absurd hO (by rw [ModalSys.noOpt_of_BStrong hB]; decide)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .link hV _ _ _ =>
      absurd hO (by rw [ModalSys.noOpt_of_Five hV]; decide)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .linkx hV _ _ _ _ _ =>
      absurd hO (by rw [ModalSys.noOpt_of_Five hV]; decide)
  | k, 0, _, _, _, _, _, h₁₂, h₂₃, h₁₄, h₄₃, hs₁, hs₂, hs₄, .optx hO' .arrow y hy φ => by
      obtain ⟨X, hX⟩ := id hy
      exact congrArg (WFF.optx hO' .ident _ _) (WFF.collapse_collapse hO (m := 0)
        (h₁₂.optIn_succ hX) (h₂₃.optIn_zero hO ((h₁₂.wit y X hX).2 k rfl))
        (h₁₄.optIn_zero hO hX) (h₄₃.optInT ((h₁₄.wit y X hX).1 rfl)) (hs₁.optIn y)
        (hs₂.optIn _) (hs₄.optInT y) φ)
  | k, m + 1, _, _, Γ₃, Γ₄, d, h₁₂, h₂₃, h₁₄, h₄₃, hs₁, hs₂, hs₄, .optx hO' .arrow y hy φ => by
      obtain ⟨X, hX⟩ := id hy
      have hX₂ := (h₁₂.wit y X hX).2 (k + 1 + m) rfl
      have hX₄ := (h₁₄.wit y X hX).2 m rfl
      have key : ∀ (z : VarSymb) (_hz : z = (y.collapse (k + 1 + m)).collapse m)
          (P : ∃ X, Γ₃.wit z = some X)
          (h' : Ctx.Collapses (k + m + 1) (Γ₄.optIn (y.collapse m)) (Γ₃.optIn z))
          (hs' : (Γ₄.optIn (y.collapse m)).SlotsFrom d),
          WFF.collapse h₂₃ hs₂ (WFF.collapse h₁₂ hs₁ (WFF.optx hO' .arrow y hy φ)) =
            WFF.optx hO' .arrow z P
              (WFF.collapse h' hs' (WFF.collapse (h₁₄.optIn_succ hX) (hs₁.optIn y) φ)) := by
        intro z hz P h' hs'
        subst hz
        exact congrArg (WFF.optx hO' .arrow _ _) (WFF.collapse_collapse hO (m := m + 1)
          (h₁₂.optIn_succ hX) (h₂₃.optIn_succ hX₂) (h₁₄.optIn_succ hX) h' (hs₁.optIn y)
          (hs₂.optIn _) hs' φ)
      exact key _ (VarSymb.collapse_collapse y k m).symm _ (h₄₃.optIn_succ hX₄) (hs₄.optIn _)
  | k, m, _, _, Γ₃, Γ₄, d, h₁₂, h₂₃, h₁₄, h₄₃, hs₁, hs₂, hs₄, .optx hO' .ident y hy φ => by
      obtain ⟨X, hX⟩ := id hy
      have key : ∀ (z : VarSymb) (_hz : z = (y.collapse (k + 1 + m)).collapse m)
          (P : ∃ X, Γ₃.witT z = some X)
          (h' : Ctx.Collapses (k + m) (Γ₄.optInT (y.collapse m)) (Γ₃.optInT z))
          (hs' : (Γ₄.optInT (y.collapse m)).SlotsFrom d),
          WFF.collapse h₂₃ hs₂ (WFF.collapse h₁₂ hs₁ (WFF.optx hO' .ident y hy φ)) =
            WFF.optx hO' .ident z P
              (WFF.collapse h' hs' (WFF.collapse (h₁₄.optInT hX) (hs₁.optInT y) φ)) := by
        intro z hz P h' hs'
        subst hz
        exact congrArg (WFF.optx hO' .ident _ _) (WFF.collapse_collapse hO (h₁₂.optInT hX)
          (h₂₃.optInT (h₁₂.witT hX)) (h₁₄.optInT hX) h' (hs₁.optInT y) (hs₂.optInT _) hs' φ)
      exact key _ (VarSymb.collapse_collapse y k m).symm _ (h₄₃.optInT (h₁₄.witT hX))
        (hs₄.optInT _)

/-- Collapsing keeps the weight. -/
theorem WFF.weight_collapse : ∀ {k : ℕ} {Γ₁ Γ₂ : Ctx} {d : ℕ} (h : Ctx.Collapses k Γ₁ Γ₂)
    (hs : Γ₁.SlotsFrom d) (φ : WFF σ Γ₁ d), (WFF.collapse h hs φ).weight = φ.weight
  | _, _, _, _, _, _, .atom _ => rfl
  | _, _, _, _, _, _, .eq _ _ => rfl
  | _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, h, hs, .and φ ψ => by
      simp only [WFF.collapse, WFF.weight]
      rw [WFF.weight_collapse h hs φ, WFF.weight_collapse h hs ψ]
  | _, _, _, _, h, hs, .or φ ψ => by
      simp only [WFF.collapse, WFF.weight]
      rw [WFF.weight_collapse h hs φ, WFF.weight_collapse h hs ψ]
  | _, _, _, _, h, hs, .imp φ ψ => by
      simp only [WFF.collapse, WFF.weight]
      rw [WFF.weight_collapse h hs φ, WFF.weight_collapse h hs ψ]
  | _, _, _, _, _, _, .all _ φ => by
      simp only [WFF.collapse, WFF.weight]; rw [WFF.weight_collapse _ _ φ]
  | _, _, _, _, _, _, .ex _ φ => by
      simp only [WFF.collapse, WFF.weight]; rw [WFF.weight_collapse _ _ φ]
  | _, _, _, _, _, _, .box φ => by
      simp only [WFF.collapse, WFF.weight]; rw [WFF.weight_collapse _ _ φ]
  | _, _, _, _, _, _, .dia _ _ φ => by
      simp only [WFF.collapse, WFF.weight]; rw [WFF.weight_collapse _ _ φ]
  | _, _, _, _, _, _, .here _ _ _ _ => rfl
  | _, _, _, _, _, _, .back _ _ _ _ => rfl
  | _, _, _, _, _, _, .retS _ _ _ Φ => by
      simp only [WFF.collapse, WFF.weight]; rw [WFF.weight_collapse _ _ Φ]
  | _, _, _, _, _, _, .retxS _ _ _ _ _ Φ => by
      simp only [WFF.collapse, WFF.weight]; rw [WFF.weight_collapse _ _ Φ]
  | _, _, _, _, _, _, .link _ _ _ Φ => by
      simp only [WFF.collapse, WFF.weight]; rw [WFF.weight_collapse _ _ Φ]
  | _, _, _, _, _, _, .linkx _ _ _ _ _ Φ => by
      simp only [WFF.collapse, WFF.weight]; rw [WFF.weight_collapse _ _ Φ]
  | 0, _, _, _, _, _, .optx _ .arrow _ _ φ => by
      simp only [WFF.collapse, WFF.weight]; rw [WFF.weight_collapse _ _ φ]
  | _ + 1, _, _, _, _, _, .optx _ .arrow _ _ φ => by
      simp only [WFF.collapse, WFF.weight]; rw [WFF.weight_collapse _ _ φ]
  | _, _, _, _, _, _, .optx _ .ident _ _ φ => by
      simp only [WFF.collapse, WFF.weight]; rw [WFF.weight_collapse _ _ φ]

/-- Collapsing keeps atoms atoms. -/
theorem WFF.IsAtom.collapse {k : ℕ} {Γ₁ Γ₂ : Ctx} {d : ℕ} {h : Ctx.Collapses k Γ₁ Γ₂}
    {hs : Γ₁.SlotsFrom d} : ∀ {φ : WFF σ Γ₁ d}, φ.IsAtom → (WFF.collapse h hs φ).IsAtom
  | .atom _, _ => trivial
  | .eq _ _, _ => trivial

/-! ## Lists, copies and eigenvariables -/

theorem map_collapse_mono {k : ℕ} {Γ₁ Γ₂ Γ₁' Γ₂' : Ctx} [Γ₁.NoSlots] [Γ₁'.NoSlots]
    (h : Ctx.Collapses k Γ₁ Γ₂) (h' : Ctx.Collapses k Γ₁' Γ₂') (l₁ : Γ₁.Le Γ₁') (l₂ : Γ₂.Le Γ₂')
    (L : List (WFF σ Γ₁ 0)) :
    (L.map (WFF.mono l₁)).map (WFF.collapse h' Ctx.NoSlots.slots) =
      (L.map (WFF.collapse h Ctx.NoSlots.slots)).map (WFF.mono l₂) := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun δ _ => WFF.collapse_mono h h' l₁ l₂ _ _ δ

theorem map_collapse_weaken {k : ℕ} {Γ₁ Γ₂ : Ctx} [Γ₁.NoSlots] (C : Ctx.Collapses k Γ₁ Γ₂)
    {r : Root} (hr₁ : Γ₁.RootFresh r) (hr₂ : Γ₂.RootFresh r) (T : VarType)
    (hs : (Γ₁.insert r T).SlotsFrom 0) (L : List (WFF σ Γ₁ 0)) :
    (L.map (WFF.weaken hr₁.root T)).map (WFF.collapse (C.insert hr₁ T) hs) =
      (L.map (WFF.collapse C Ctx.NoSlots.slots)).map (WFF.weaken hr₂.root T) := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun δ _ =>
    WFF.collapse_mono C (C.insert hr₁ T) (Ctx.le_insert hr₁.root T) (Ctx.le_insert hr₂.root T)
      _ _ δ

/-- Collapsing the folds of the conclusions, one view in, is folding the collapsed conclusions
    (4 off: there are no other copies). -/
theorem collapse_kp4 (hF : ModalSys.Four = false) {k : ℕ} {Γ₁ Γ₂ : Ctx} [Γ₁.NoSlots]
    [Γ₂.NoSlots] (C : Ctx.Collapses k Γ₁ Γ₂) (L : List (WFF σ Γ₁ 0)) :
    (kp4 L).map (WFF.collapse C.boxIn Ctx.NoSlots.slots) =
      kp4 (L.map (WFF.collapse C Ctx.NoSlots.slots)) := by
  by_cases hO : ModalSys.Opt = true
  · rw [kp4_of_opt hO, kp4_of_opt hO, List.map_flatMap, List.flatMap_map]
    refine List.flatMap_congr fun A _ => ?_
    cases A with
    | dia y hy θ =>
        obtain ⟨X, hX⟩ := id hy
        exact congrArg (fun χ => [WFF.optx hO .arrow (y.collapse k) _ χ])
          (WFF.collapse_mono (C.diaIn y) (C.boxIn.optIn_succ (Ctx.boxIn_wit.mpr ⟨hO, hX⟩)) _ _
            _ _ θ)
    | optx hO' κ y hy φ => cases κ <;> cases k <;> rfl
    | _ => rfl
  · rw [kp4_of_not hF (Bool.eq_false_iff.mpr hO), kp4_of_not hF (Bool.eq_false_iff.mpr hO)]
    rfl

namespace GK

/-- An eigenvariable renamed to another root fresh for the context: the premise's sequent moves
    along `R`, weakened formulas stay, and the bound formula does not change. -/
theorem eigenRename {Γ : Ctx} [Γ.Presented] {u u' : ℕ} {T : VarType}
    (hu : Γ.RootFresh (.free u)) (hu' : Γ.RootFresh (.free u')) :
    ∃ R : WFF σ (Γ.insert (.free u) T) 0 → WFF σ (Γ.insert (.free u') T) 0,
      (∀ δ : WFF σ Γ 0, R (WFF.weaken hu.root T δ) = WFF.weaken hu'.root T δ) ∧
      (∀ φ, WFF.bindFree u' hu' Ctx.NoSlots.slots T (R φ) =
        WFF.bindFree u hu Ctx.NoSlots.slots T φ) ∧
      ∀ {n : ℕ} {Δ' Θ' : List (WFF σ (Γ.insert (.free u) T) 0)},
        GK σ n (Γ.insert (.free u) T) Δ' Θ' →
        GK σ n (Γ.insert (.free u') T) (Δ'.map R) (Θ'.map R) := by
  haveI := Ctx.Presented.insertFree inferInstance u' hu' T
  have hΓ : Γ.SlotsFrom 0 := Ctx.NoSlots.slots
  have key : ∀ ψ : WFF σ Γ 0, WFF.subst id (Subst.idRen Γ) Subst.ok_idRen Subst.coh_idRen hΓ
      Ctx.NoSlots.slots ψ = ψ := fun ψ =>
    (WFF.subst_ren (Ctx.Le.refl Γ) _ _ _ hΓ _ (fun v _ _ => Subst.at_idRen v) ψ
      (fun _ _ _ _ => rfl)).trans (WFF.mono_refl _ ψ)
  refine ⟨WFF.subst _ ((Subst.idRen Γ).rename u u' T hu'.root)
      (Subst.ok_rename Subst.ok_idRen T hu'.root)
      (Subst.coh_rename Subst.ok_idRen Subst.coh_idRen hu T hu'.root) (hΓ.insertFree u T)
      Ctx.NoSlots.slots, fun δ => ?_, fun φ => ?_,
    fun p => p.subst ((Subst.idRen Γ).rename u u' T hu'.root)
      (Subst.ok_rename Subst.ok_idRen T hu'.root)
      (Subst.coh_rename Subst.ok_idRen Subst.coh_idRen hu T hu'.root) (hΓ.insertFree u T)⟩
  · exact (WFF.subst_weaken_rename (Subst.idRen Γ) Subst.ok_idRen Subst.coh_idRen hΓ hΓ hu hu'
      T δ).trans (congrArg _ (key δ))
  · have e := (congrArg (WFF.all T) (WFF.subst_bindFree (Subst.idRen Γ) Subst.ok_idRen
      Subst.coh_idRen hΓ hΓ hu hu' T φ)).symm.trans (key (WFF.all T (WFF.bindFree u hu hΓ T φ)))
    exact eq_of_heq (WFF.all.inj e).2

/-- ⭐**Collapsing a derivation**, height kept: with `Opt` on (so T's identity views, and 4 off),
    a derivation over `Γ₁` collapsed at any level `k` onto `Γ₂` (docs §12.35). -/
theorem collapseD (hO : ModalSys.Opt = true) : ∀ (n : ℕ) {k : ℕ} {Γ₁ Γ₂ : Ctx} [Γ₁.Presented]
    [Γ₂.Presented] (C : Ctx.Collapses k Γ₁ Γ₂) {Δ Θ : List (WFF σ Γ₁ 0)}, GK σ n Γ₁ Δ Θ →
    GK σ n Γ₂ (Δ.map (WFF.collapse C Ctx.NoSlots.slots))
      (Θ.map (WFF.collapse C Ctx.NoSlots.slots)) := by
  have hF : ModalSys.Four = false := by
    cases h4 : ModalSys.Four
    · rfl
    · rw [ModalSys.noOpt_of_Four h4] at hO; cases hO
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k Γ₁ Γ₂ _ _ C Δ Θ p
  cases p with
  | ax P hP h₁ h₂ => exact .ax _ hP.collapse (List.mem_map_of_mem h₁) (List.mem_map_of_mem h₂)
  | botL h => exact .botL (List.mem_map_of_mem h)
  | topR h => exact .topR (List.mem_map_of_mem h)
  | andL h p => exact .andL (List.mem_map_of_mem h) (ih _ (Nat.lt_succ_self _) C p)
  | andR h p q =>
      exact .andR (List.mem_map_of_mem h) (ih _ (Nat.lt_succ_self _) C p)
        (ih _ (Nat.lt_succ_self _) C q)
  | orL h p q =>
      exact .orL (List.mem_map_of_mem h) (ih _ (Nat.lt_succ_self _) C p)
        (ih _ (Nat.lt_succ_self _) C q)
  | orR h p => exact .orR (List.mem_map_of_mem h) (ih _ (Nat.lt_succ_self _) C p)
  | impL h p q =>
      exact .impL (List.mem_map_of_mem h) (ih _ (Nat.lt_succ_self _) C p)
        (ih _ (Nat.lt_succ_self _) C q)
  | impR h p => exact .impR (List.mem_map_of_mem h) (ih _ (Nat.lt_succ_self _) C p)
  | @allL _ _ _ _ _ T φ _ t h p =>
      have q := ih _ (Nat.lt_succ_self _) C p
      rw [List.map_cons, WFF.collapse_instantiate C t φ] at q
      exact .allL T _ (List.mem_map_of_mem h) q
  | @exR _ _ _ _ _ T φ _ t h p =>
      have q := ih _ (Nat.lt_succ_self _) C p
      rw [List.map_cons, WFF.collapse_instantiate C t φ] at q
      exact .exR T _ (List.mem_map_of_mem h) q
  | @allR _ _ _ _ _ u T hu φ h p =>
      obtain ⟨b, hb₁, hb₂⟩ : ∃ b, Γ₁.RootFresh (.free b) ∧ Γ₂.RootFresh (.free b) :=
        ⟨_, Ctx.Presented.fresh_bound _ (le_max_left _ _),
          Ctx.Presented.fresh_bound _ (le_max_right _ _)⟩
      obtain ⟨R, hRw, hRb, hRd⟩ := eigenRename (σ := σ) (T := T) hu hb₁
      haveI := Ctx.Presented.insertFree inferInstance b hb₁ T
      haveI := Ctx.Presented.insertFree inferInstance b hb₂ T
      have p' := hRd p
      rw [List.map_cons, List.map_map, List.map_map,
        show R ∘ WFF.weaken hu.root T = WFF.weaken hb₁.root T from funext hRw] at p'
      have q := ih _ (Nat.lt_succ_self _) (C.insert hb₁ T) p'
      rw [List.map_cons, map_collapse_weaken C hb₁ hb₂ T, map_collapse_weaken C hb₁ hb₂ T] at q
      refine .allR b T hb₂ ?_ q
      have hm := List.mem_map_of_mem (f := WFF.collapse C Ctx.NoSlots.slots) h
      rw [← hRb φ] at hm
      exact (congrArg (fun A => A ∈ Θ.map (WFF.collapse C Ctx.NoSlots.slots))
        (congrArg (WFF.all T) (WFF.collapse_bindFree C hb₁ hb₂ T (R φ)))).mp hm
  | @exL _ _ _ _ _ u T hu φ h p =>
      obtain ⟨b, hb₁, hb₂⟩ : ∃ b, Γ₁.RootFresh (.free b) ∧ Γ₂.RootFresh (.free b) :=
        ⟨_, Ctx.Presented.fresh_bound _ (le_max_left _ _),
          Ctx.Presented.fresh_bound _ (le_max_right _ _)⟩
      obtain ⟨R, hRw, hRb, hRd⟩ := eigenRename (σ := σ) (T := T) hu hb₁
      haveI := Ctx.Presented.insertFree inferInstance b hb₁ T
      haveI := Ctx.Presented.insertFree inferInstance b hb₂ T
      have p' := hRd p
      rw [List.map_cons, List.map_map, List.map_map,
        show R ∘ WFF.weaken hu.root T = WFF.weaken hb₁.root T from funext hRw] at p'
      have q := ih _ (Nat.lt_succ_self _) (C.insert hb₁ T) p'
      rw [List.map_cons, map_collapse_weaken C hb₁ hb₂ T, map_collapse_weaken C hb₁ hb₂ T] at q
      refine .exL b T hb₂ ?_ q
      have hm := List.mem_map_of_mem (f := WFF.collapse C Ctx.NoSlots.slots) h
      rw [← hRb φ] at hm
      exact (congrArg (fun A => A ∈ Δ.map (WFF.collapse C Ctx.NoSlots.slots))
        (congrArg (WFF.ex T) (WFF.collapse_bindFree C hb₁ hb₂ T (R φ)))).mp hm
  | ref t p => exact .ref (Term.collapse C t) (ih _ (Nat.lt_succ_self _) C p)
  | @repl _ _ _ _ _ P hP t s h₁ h₂ p =>
      have q := ih _ (Nat.lt_succ_self _) C p
      rw [List.map_cons, WFF.collapse_instantiate C s P] at q
      refine .repl hP.collapse (Term.collapse C t) (Term.collapse C s) (List.mem_map_of_mem h₁)
        ?_ q
      rw [← WFF.collapse_instantiate C t P]
      exact List.mem_map_of_mem h₂
  | @boxR _ _ _ _ _ Δ₁ φ L h₁ h₂ h₃ p =>
      have q := ih _ (Nat.lt_succ_self _) C.boxIn p
      rw [cp4_of_not hF, List.append_nil, List.map_cons, collapse_kp4 hF C L] at q
      refine .boxR (Δ₁ := Δ₁.map (WFF.collapse C.boxIn Ctx.NoSlots.slots))
        (L := L.map (WFF.collapse C Ctx.NoSlots.slots)) (List.mem_map_of_mem h₁) ?_
        (List.map_subset _ h₃) ?_
      · intro χ hχ
        obtain ⟨χ₀, hχ₀, rfl⟩ := List.mem_map.mp hχ
        exact List.mem_map_of_mem (h₂ χ₀ hχ₀)
      · rw [cp4_of_not hF, List.append_nil]; exact q
  | @serial _ _ _ _ _ hD Δ₁ L h₂ h₃ p =>
      have q := ih _ (Nat.lt_succ_self _) C.boxIn p
      rw [cp4_of_not hF, List.append_nil, collapse_kp4 hF C L] at q
      refine .serial hD (Δ₁ := Δ₁.map (WFF.collapse C.boxIn Ctx.NoSlots.slots))
        (L := L.map (WFF.collapse C Ctx.NoSlots.slots)) ?_ (List.map_subset _ h₃) ?_
      · intro χ hχ
        obtain ⟨χ₀, hχ₀, rfl⟩ := List.mem_map.mp hχ
        exact List.mem_map_of_mem (h₂ χ₀ hχ₀)
      · rw [cp4_of_not hF, List.append_nil]; exact q
  | @diaL _ _ _ _ _ x hx ψ Δ₁ Θ₁ L h₁ h₂ h₃ h₄ p =>
      have q := ih _ (Nat.lt_succ_self _) (C.diaIn x) p
      rw [cp4_of_not hF, List.append_nil, List.map_cons, List.map_append,
        map_collapse_mono C.boxIn (C.diaIn x) (Ctx.le_boxIn_diaIn Γ₁ x)
          (Ctx.le_boxIn_diaIn Γ₂ (x.collapse k)),
        map_collapse_mono C.boxIn (C.diaIn x) (Ctx.le_boxIn_diaIn Γ₁ x)
          (Ctx.le_boxIn_diaIn Γ₂ (x.collapse k)), collapse_kp4 hF C L] at q
      refine .diaL (x.collapse k) (hx.imp fun _ h => C x _ h)
        (Δ₁ := Δ₁.map (WFF.collapse C.boxIn Ctx.NoSlots.slots))
        (Θ₁ := Θ₁.map (WFF.collapse (C.diaIn x) Ctx.NoSlots.slots))
        (L := L.map (WFF.collapse C Ctx.NoSlots.slots)) (List.mem_map_of_mem h₁) ?_ ?_
        (List.map_subset _ h₄) ?_
      · intro χ hχ
        obtain ⟨χ₀, hχ₀, rfl⟩ := List.mem_map.mp hχ
        exact List.mem_map_of_mem (h₂ χ₀ hχ₀)
      · intro χ hχ
        obtain ⟨χ₀, hχ₀, rfl⟩ := List.mem_map.mp hχ
        exact List.mem_map_of_mem (h₃ χ₀ hχ₀)
      · rw [cp4_of_not hF, List.append_nil]; exact q
  | @optL _ _ _ _ hO' κ y hy ψ h p =>
      obtain ⟨X, hX⟩ := id hy
      cases κ with
      | ident =>
          have q := ih _ (Nat.lt_succ_self _) (C.optInT hX) p
          rw [List.map_cons, map_collapse_mono C (C.optInT hX) (Ctx.le_optInT Γ₁ y)
            (Ctx.le_optInT Γ₂ _), map_collapse_mono C (C.optInT hX) (Ctx.le_optInT Γ₁ y)
            (Ctx.le_optInT Γ₂ _)] at q
          exact .optL hO' .ident (y.collapse k) ⟨X, C.witT hX⟩ (List.mem_map_of_mem h) q
      | arrow =>
          cases k with
          | zero =>
              have q := ih _ (Nat.lt_succ_self _) (C.optIn_zero hO hX) p
              rw [List.map_cons, map_collapse_mono C (C.optIn_zero hO hX) (Ctx.le_optIn Γ₁ y)
                (Ctx.le_optInT Γ₂ y), map_collapse_mono C (C.optIn_zero hO hX)
                (Ctx.le_optIn Γ₁ y) (Ctx.le_optInT Γ₂ y)] at q
              exact .optL hO' .ident y ⟨X, (C.wit y X hX).1 rfl⟩ (List.mem_map_of_mem h) q
          | succ k =>
              have q := ih _ (Nat.lt_succ_self _) (C.optIn_succ hX) p
              rw [List.map_cons, map_collapse_mono C (C.optIn_succ hX) (Ctx.le_optIn Γ₁ y)
                (Ctx.le_optIn Γ₂ (y.collapse k)), map_collapse_mono C (C.optIn_succ hX)
                (Ctx.le_optIn Γ₁ y) (Ctx.le_optIn Γ₂ (y.collapse k))] at q
              exact .optL hO' .arrow (y.collapse k) ⟨X, (C.wit y X hX).2 k rfl⟩
                (List.mem_map_of_mem h) q
  | @reopenR _ _ _ _ hO' κ y hy χ h p =>
      have q := ih _ (Nat.lt_succ_self _) C p
      obtain ⟨X, hX, hXd⟩ := id hy
      cases κ with
      | ident =>
          have hop : ∃ X, Γ₂.witK .ident (y.collapse k) = some X ∧
              Γ₂ (.step (y.collapse k) WitKind.ident.step) = some X := ⟨X, C.witT hX, by
            have := C (.step y .at) X ((Ctx.ref_nonproj _ rfl).trans hXd)
            rwa [VarSymb.collapse_at, Ctx.ref_nonproj _ rfl] at this⟩
          have e : WFF.collapse C Ctx.NoSlots.slots (.optx hO' .ident y (hy.imp fun _ h => h.1)
              (WFF.mono (Ctx.le_optInK Γ₁ .ident y) χ)) =
              .optx hO' .ident (y.collapse k) (hop.imp fun _ h => h.1)
                (WFF.mono (Ctx.le_optInK Γ₂ .ident (y.collapse k))
                  (WFF.collapse C Ctx.NoSlots.slots χ)) :=
            congrArg (WFF.optx hO' .ident _ _) (WFF.collapse_mono C (C.optInT hX) _ _ _ _ χ)
          exact .reopenR hO' .ident (y.collapse k) hop (e ▸ List.mem_map_of_mem h) q
      | arrow =>
          cases k with
          | zero =>
              have hop : ∃ X, Γ₂.witK .ident y = some X ∧
                  Γ₂ (.step y WitKind.ident.step) = some X := ⟨X, (C.wit y X hX).1 rfl, by
                have := C (.step y .dia) X ((Ctx.ref_nonproj _ rfl).trans hXd)
                rwa [VarSymb.collapse_dia_zero_opt hO, Ctx.ref_nonproj _ rfl] at this⟩
              have e : WFF.collapse C Ctx.NoSlots.slots (.optx hO' .arrow y
                  (hy.imp fun _ h => h.1) (WFF.mono (Ctx.le_optInK Γ₁ .arrow y) χ)) =
                  .optx hO' .ident y (hop.imp fun _ h => h.1)
                    (WFF.mono (Ctx.le_optInK Γ₂ .ident y) (WFF.collapse C Ctx.NoSlots.slots χ)) :=
                congrArg (WFF.optx hO' .ident _ _)
                  (WFF.collapse_mono C (C.optIn_zero hO hX) _ _ _ _ χ)
              exact .reopenR hO' .ident y hop (e ▸ List.mem_map_of_mem h) q
          | succ k =>
              have hop : ∃ X, Γ₂.witK .arrow (y.collapse k) = some X ∧
                  Γ₂ (.step (y.collapse k) WitKind.arrow.step) = some X :=
                ⟨X, (C.wit y X hX).2 k rfl, by
                  have := C (.step y .dia) X ((Ctx.ref_nonproj _ rfl).trans hXd)
                  rwa [VarSymb.collapse_level_succ rfl, Ctx.ref_nonproj _ rfl] at this⟩
              have e : WFF.collapse C Ctx.NoSlots.slots (.optx hO' .arrow y
                  (hy.imp fun _ h => h.1) (WFF.mono (Ctx.le_optInK Γ₁ .arrow y) χ)) =
                  .optx hO' .arrow (y.collapse k) (hop.imp fun _ h => h.1)
                    (WFF.mono (Ctx.le_optInK Γ₂ .arrow (y.collapse k))
                      (WFF.collapse C Ctx.NoSlots.slots χ)) :=
                congrArg (WFF.optx hO' .arrow _ _)
                  (WFF.collapse_mono C (C.optIn_succ hX) _ _ _ _ χ)
              exact .reopenR hO' .arrow (y.collapse k) hop (e ▸ List.mem_map_of_mem h) q
  | @TL _ _ _ _ _ hT φ h p =>
      have q := ih _ (Nat.lt_succ_self _) C p
      rw [List.map_cons, ← WFF.collapse_collapse hO (k := k) (m := 0) C.boxIn
        (Ctx.collapses_boxIn_self hT Γ₂) (Ctx.collapses_boxIn_self hT Γ₁) C Ctx.NoSlots.slots
        Ctx.NoSlots.slots Ctx.NoSlots.slots φ] at q
      exact .TL hT (List.mem_map_of_mem h) q
  | @diaT _ _ _ _ _ hT hO'' x hx φ h p =>
      have q := ih _ (Nat.lt_succ_self _) C p
      obtain ⟨X, hX⟩ := id hx
      have hY : Γ₂.ref (x.collapse k) = some (.VTypeDia X) := C x _ hX
      have e : WFF.collapse C Ctx.NoSlots.slots (WFF.diaId hT hO'' x hx φ) =
          WFF.diaId hT hO'' (x.collapse k) ⟨X, hY⟩
            (WFF.collapse (C.diaIn x) Ctx.NoSlots.slots φ) :=
        congrArg (WFF.optx hO'' .ident _ _) (WFF.collapse_collapse hO (k := k) (m := 0)
          (C.diaIn x) (Ctx.collapses_diaIn_optInT hT hO'' Γ₂ hY)
          (Ctx.collapses_diaIn_optInT hT hO'' Γ₁ hX) (C.optInT (Ctx.witT_of hT hO'' hX))
          Ctx.NoSlots.slots Ctx.NoSlots.slots Ctx.NoSlots.slots φ).symm
      rw [List.map_cons, e] at q
      exact .diaT hT hO'' (x.collapse k) ⟨X, hY⟩ (List.mem_map_of_mem h) q

end GK

end V12M
