import QML.QML_v12m_GKSubform
import QML.QML_v12m_RetMono

/-!
# QML v12m — the sharp subformula property for GK

⭐`GK.subformula_sharp_of_provable`: every ND-provable sequent of K, KD, K4 and KD4 has a cut-free
derivation in which **every formula is a single substitution instance of a subformula of the end
sequent up to copies** (`WFF.SubC`, `SharpSub.inst`), or an atom introduced by `ref` (`t = t`) or
`repl` (from two members `t = s` and `P(t)`).  "Up to copies" is K4's: a syntactic subformula
(`WFF.SubF`), its subformulas, and under 4 the copies one view in, `□(shift χ)` of `□χ` and
`◇_{y.keep}(shift χ)` of `◇_y χ`.  Without 4 the copies do not arise and these are the syntactic
subformulas.

The step from `GSub` (`GSub.sharp`) shows each of its closure steps keeps a single instance:
* connectives and views: substitution commutes with each former;
* a quantifier's body at a term `t`: instantiating after `θ.under` is substituting along
  `θ.set (bnd d) t` (`WFF.instantiate_subst_under`);
* at an eigenvariable: `bindFree_toFree` and `openFree_bindFree` give `θ.toFree`;
* weakening, and a `□` view formula moved into a `◇_x` view: `WFF.mono_subst`, and for the atoms
  `WFF.mono_instantiate` (`SharpSub.mono`).
* a copy: shifting commutes with substitution (`WFF.shift_subst` with `Subst.shiftCorr_box_box`,
  `Subst.shiftCorr_dia_keep`), so the copy of an instance of `□χ` is an instance of the copy of
  `□χ` (`SharpSub.box_keep`, `SharpSub.dia_keep`).
-/

namespace V12M

variable [ModalSys] {σ : Signature}

/-! ## Syntactic subformulas -/

/-- ⭐`χ` **occurs in** `φ`: the syntactic subformula relation, through binders (bodies at the next
    depth) and views. -/
inductive WFF.SubF {Γ' : Ctx} {d' : ℕ} (χ : WFF σ Γ' d') :
    {Γ : Ctx} → {d : ℕ} → WFF σ Γ d → Prop where
  | refl : WFF.SubF χ χ
  | and_l {Γ : Ctx} {d : ℕ} {φ ψ : WFF σ Γ d} : WFF.SubF χ φ → WFF.SubF χ (φ.and ψ)
  | and_r {Γ : Ctx} {d : ℕ} {φ ψ : WFF σ Γ d} : WFF.SubF χ ψ → WFF.SubF χ (φ.and ψ)
  | or_l {Γ : Ctx} {d : ℕ} {φ ψ : WFF σ Γ d} : WFF.SubF χ φ → WFF.SubF χ (φ.or ψ)
  | or_r {Γ : Ctx} {d : ℕ} {φ ψ : WFF σ Γ d} : WFF.SubF χ ψ → WFF.SubF χ (φ.or ψ)
  | imp_l {Γ : Ctx} {d : ℕ} {φ ψ : WFF σ Γ d} : WFF.SubF χ φ → WFF.SubF χ (φ.imp ψ)
  | imp_r {Γ : Ctx} {d : ℕ} {φ ψ : WFF σ Γ d} : WFF.SubF χ ψ → WFF.SubF χ (φ.imp ψ)
  | all {Γ : Ctx} {d : ℕ} {T : VarType} {φ : WFF σ (Γ.insert (.bnd d) T) (d + 1)} :
      WFF.SubF χ φ → WFF.SubF χ (.all T φ)
  | ex {Γ : Ctx} {d : ℕ} {T : VarType} {φ : WFF σ (Γ.insert (.bnd d) T) (d + 1)} :
      WFF.SubF χ φ → WFF.SubF χ (.ex T φ)
  | box {Γ : Ctx} {d : ℕ} {φ : WFF σ Γ.boxIn d} : WFF.SubF χ φ → WFF.SubF χ (WFF.box (Γ := Γ) φ)
  | dia {Γ : Ctx} {d : ℕ} {x : VarSymb} {hx : ∃ X, Γ.ref x = some (.VTypeDia X)}
      {φ : WFF σ (Γ.diaIn x) d} : WFF.SubF χ φ → WFF.SubF χ (.dia x hx φ)

theorem WFF.SubF.trans {Γa Γb Γc : Ctx} {da db dc : ℕ} {a : WFF σ Γa da} {b : WFF σ Γb db}
    {c : WFF σ Γc dc} (h₁ : WFF.SubF a b) (h₂ : WFF.SubF b c) : WFF.SubF a c := by
  induction h₂ with
  | refl => exact h₁
  | and_l _ ih => exact .and_l ih
  | and_r _ ih => exact .and_r ih
  | or_l _ ih => exact .or_l ih
  | or_r _ ih => exact .or_r ih
  | imp_l _ ih => exact .imp_l ih
  | imp_r _ ih => exact .imp_r ih
  | all _ ih => exact .all ih
  | ex _ ih => exact .ex ih
  | box _ ih => exact .box ih
  | dia _ ih => exact .dia ih

/-- ⭐**Subformulas up to copies** of `ψ`: its syntactic subformulas, closed under taking
    subformulas and, under 4, the copies one view in (`□(shift χ)` of `□χ`,
    `◇_{y.keep}(shift χ)` of `◇_y χ`). -/
inductive WFF.SubC {Γ₀ : Ctx} (ψ : WFF σ Γ₀ 0) : {Γ : Ctx} → {d : ℕ} → WFF σ Γ d → Prop where
  | self : WFF.SubC ψ ψ
  | sub {Γ Γ' : Ctx} {d d' : ℕ} {χ : WFF σ Γ d} {φ : WFF σ Γ' d'} :
      WFF.SubF χ φ → WFF.SubC ψ φ → WFF.SubC ψ χ
  | box_keep {Γ : Ctx} {d : ℕ} (hF : ModalSys.Four = true) (hs : Γ.boxIn.SlotsFrom d)
      {φ : WFF σ Γ.boxIn d} : WFF.SubC ψ (WFF.box (Γ := Γ) φ) →
      WFF.SubC ψ (WFF.box (Γ := Γ.boxIn) (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) hs φ))
  | dia_keep {Γ : Ctx} {d : ℕ} (hF : ModalSys.Four = true) {y : VarSymb}
      {hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)} (hs : (Γ.diaIn y).SlotsFrom d)
      {φ : WFF σ (Γ.diaIn y) d} : WFF.SubC ψ (WFF.dia y hy φ) →
      WFF.SubC ψ (WFF.dia (.step y .keep) (Ctx.exists_keep_dia hF hy)
        (WFF.shift (Ctx.shifts_diaIn_keep hF Γ y) hs φ))

/-- Without 4, the subformulas up to copies are the syntactic ones. -/
theorem WFF.SubC.subF {Γ₀ : Ctx} {ψ : WFF σ Γ₀ 0} (hF : ModalSys.Four = false) {Γ : Ctx} {d : ℕ}
    {χ : WFF σ Γ d} (h : WFF.SubC ψ χ) : WFF.SubF χ ψ := by
  induction h with
  | self => exact .refl
  | sub h₁ _ ih => exact h₁.trans ih
  | box_keep hF' => exact absurd hF' (by rw [hF]; decide)
  | dia_keep hF' => exact absurd hF' (by rw [hF]; decide)

/-! ## Instantiating after a substitution -/

/-- ⭐Instantiating a body substituted under its binder at `t` is substituting along `θ` with the
    binder's slot sent to `t`. -/
theorem WFF.instantiate_subst_under [ModalSys.NoOpt] {ι : VarSymb → VarSymb} {Γ₁ Γ : Ctx} {d : ℕ}
    (θ : Subst σ Γ) (hθ : Subst.Ok Γ₁ θ) (hc : Subst.Coh ι Γ₁ θ) (hΓ₁ : Γ₁.SlotsFrom d)
    (hΓ : Γ.SlotsFrom 0) {T : VarType} {a : Ann T} (t : Term σ Γ T a)
    (χ : WFF σ (Γ₁.insert (.bnd d) T) (d + 1)) :
    WFF.instantiate hΓ t (WFF.subst (VarSymb.shiftSlot ι d 0) (θ.under d 0 T hΓ.root)
        (Subst.ok_under hθ T hΓ.root) (Subst.coh_under hθ hc hΓ₁ T hΓ.root) (hΓ₁.insert T)
        (hΓ.insert T) χ) =
      WFF.subst (Subst.setIdx ι (.bnd d) (.tm t)) (θ.set (.bnd d) (.tm t))
        (Subst.ok_set hθ rfl) (Subst.coh_set hθ hc (hΓ₁.rootFresh le_rfl) rfl) (hΓ₁.insert T) hΓ
        χ := by
  have hrΓ : Γ.RootFresh (.bnd 0) := hΓ.rootFresh le_rfl
  unfold WFF.instantiate WFF.substRoot
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ χ
  refine Subst.sim_of (hwit := fun _ _ _ _ => by wit_refl) ?_
  intro v U hlp hv
  rw [Subst.comp_apply]
  by_cases hvr : v = .root (.bnd d)
  · subst hvr
    rw [Subst.set_root, show θ.under d 0 T hΓ.root (.root (.bnd d)) = .ren (.root (.bnd 0))
      from by slot_rfl, SubE.comp_ren, Subst.at_single_root]
    exact .refl _
  · have hv' : Γ₁ v = some U := Ctx.insert_ne_some hv hvr
    rw [Subst.set_ne _ _ hvr,
      show θ.under d 0 T hΓ.root v = (θ v).mono (Ctx.le_insert hΓ.root T) from if_neg hvr,
      SubE.comp_mono (Subst.idRen Γ) Subst.ok_idRen Subst.coh_idRen (Ctx.le_insert hΓ.root T)
        (Ctx.Le.refl Γ) _ _ _
        (fun w _ hw' => by
          rw [Subst.single_at_ne (Ctx.ref_rt_ne hrΓ hw'), Subst.at_idRen]
          rfl)
        (hθ v U hlp hv'),
      SubE.comp_idRen, SubE.mono_refl]
    exact .refl _

theorem WFF.IsAtom.mono {Γ Γ' : Ctx} {d : ℕ} {h : Γ.Le Γ'} {P : WFF σ Γ d} (hP : P.IsAtom) :
    (WFF.mono h P).IsAtom := by
  cases P <;> first | exact trivial | exact hP.elim

/-! ## The sharp family -/

/-- ⭐**Single instances of subformulas** of `E`, and the atoms `ref` and `repl` introduce. -/
inductive SharpSub {Γ₀ : Ctx} (E : List (WFF σ Γ₀ 0)) : (Γ : Ctx) → WFF σ Γ 0 → Prop where
  | inst {Γ : Ctx} {φ : WFF σ Γ 0} {ψ : WFF σ Γ₀ 0} (hψ : ψ ∈ E) {Γ₁ : Ctx} {d₁ : ℕ}
      {χ : WFF σ Γ₁ d₁} (hχ : WFF.SubC ψ χ) {ι : VarSymb → VarSymb} (θ : Subst σ Γ)
      (hθ : Subst.Ok Γ₁ θ) (hc : Subst.Coh ι Γ₁ θ) (hΓ₁ : Γ₁.SlotsFrom d₁) (hΓ : Γ.SlotsFrom 0) :
      φ = WFF.subst ι θ hθ hc hΓ₁ hΓ χ → SharpSub E Γ φ
  | refl_eq {Γ : Ctx} {φ : WFF σ Γ 0} (t : Term σ Γ .Var .var) : φ = .eq t t → SharpSub E Γ φ
  | repl {Γ : Ctx} [Γ.NoSlots] {φ : WFF σ Γ 0} {Q : WFF σ (Γ.insert (.bnd 0) .Var) 1}
      (hQ : Q.IsAtom) (t s : Term σ Γ .Var .var) : SharpSub E Γ (.eq t s) →
      SharpSub E Γ (WFF.instantiate Ctx.NoSlots.slots t Q) →
      φ = WFF.instantiate Ctx.NoSlots.slots s Q → SharpSub E Γ φ

namespace SharpSub

variable {Γ₀ : Ctx} {E : List (WFF σ Γ₀ 0)} {Γ : Ctx}

/-- A non-atomic member is an instance of a subformula. -/
theorem inst_of {φ : WFF σ Γ 0} (h : SharpSub E Γ φ) (hn : ¬ φ.IsAtom) :
    ∃ ψ ∈ E, ∃ (Γ₁ : Ctx) (d₁ : ℕ) (χ : WFF σ Γ₁ d₁), WFF.SubC ψ χ ∧
      ∃ (ι : VarSymb → VarSymb) (θ : Subst σ Γ) (hθ : Subst.Ok Γ₁ θ) (hc : Subst.Coh ι Γ₁ θ)
        (hΓ₁ : Γ₁.SlotsFrom d₁) (hΓ : Γ.SlotsFrom 0), φ = WFF.subst ι θ hθ hc hΓ₁ hΓ χ := by
  cases h with
  | inst hψ hχ θ hθ hc hΓ₁ hΓ he => exact ⟨_, hψ, _, _, _, hχ, _, θ, hθ, hc, hΓ₁, hΓ, he⟩
  | refl_eq t he => exact absurd (he ▸ trivial) hn
  | repl hQ t s _ _ he => exact absurd (he ▸ hQ.instantiate) hn

theorem mem [Γ₀.NoSlots] {ψ : WFF σ Γ₀ 0} (hψ : ψ ∈ E) : SharpSub E Γ₀ ψ :=
  .inst hψ .self (Subst.idRen Γ₀) Subst.ok_idRen Subst.coh_idRen Ctx.NoSlots.slots
    Ctx.NoSlots.slots
    ((WFF.subst_ren (Ctx.Le.refl _) _ _ _ _ _ (fun v _ _ => Subst.at_idRen v) ψ
      (fun _ _ _ _ => rfl)).trans
      (WFF.mono_refl _ ψ)).symm

theorem and_l {φ ψ : WFF σ Γ 0} (h : SharpSub E Γ (φ.and ψ)) : SharpSub E Γ φ := by
  obtain ⟨ψ₀, hψ₀, Γ₁, d₁, χ, hχ, ι, θ, hθ, hc, hΓ₁, hΓ, he⟩ :=
    h.inst_of (by simp [WFF.IsAtom])
  cases χ
  case and χ₁ χ₂ =>
    simp only [WFF.subst] at he
    obtain ⟨rfl, -⟩ := WFF.and.inj he
    exact .inst hψ₀ (WFF.SubC.sub (.and_l .refl) hχ) θ hθ hc hΓ₁ hΓ rfl
  case optx k _ hy _ =>
    cases k
    · simp only [WFF.subst] at he; cases he
    · simp only [WFF.subst] at he; cases he
  all_goals (simp only [WFF.subst] at he; cases he)

theorem and_r {φ ψ : WFF σ Γ 0} (h : SharpSub E Γ (φ.and ψ)) : SharpSub E Γ ψ := by
  obtain ⟨ψ₀, hψ₀, Γ₁, d₁, χ, hχ, ι, θ, hθ, hc, hΓ₁, hΓ, he⟩ :=
    h.inst_of (by simp [WFF.IsAtom])
  cases χ
  case and χ₁ χ₂ =>
    simp only [WFF.subst] at he
    obtain ⟨-, rfl⟩ := WFF.and.inj he
    exact .inst hψ₀ (WFF.SubC.sub (.and_r .refl) hχ) θ hθ hc hΓ₁ hΓ rfl
  case optx k _ hy _ =>
    cases k
    · simp only [WFF.subst] at he; cases he
    · simp only [WFF.subst] at he; cases he
  all_goals (simp only [WFF.subst] at he; cases he)

theorem or_l {φ ψ : WFF σ Γ 0} (h : SharpSub E Γ (φ.or ψ)) : SharpSub E Γ φ := by
  obtain ⟨ψ₀, hψ₀, Γ₁, d₁, χ, hχ, ι, θ, hθ, hc, hΓ₁, hΓ, he⟩ :=
    h.inst_of (by simp [WFF.IsAtom])
  cases χ
  case or χ₁ χ₂ =>
    simp only [WFF.subst] at he
    obtain ⟨rfl, -⟩ := WFF.or.inj he
    exact .inst hψ₀ (WFF.SubC.sub (.or_l .refl) hχ) θ hθ hc hΓ₁ hΓ rfl
  case optx k _ hy _ =>
    cases k
    · simp only [WFF.subst] at he; cases he
    · simp only [WFF.subst] at he; cases he
  all_goals (simp only [WFF.subst] at he; cases he)

theorem or_r {φ ψ : WFF σ Γ 0} (h : SharpSub E Γ (φ.or ψ)) : SharpSub E Γ ψ := by
  obtain ⟨ψ₀, hψ₀, Γ₁, d₁, χ, hχ, ι, θ, hθ, hc, hΓ₁, hΓ, he⟩ :=
    h.inst_of (by simp [WFF.IsAtom])
  cases χ
  case or χ₁ χ₂ =>
    simp only [WFF.subst] at he
    obtain ⟨-, rfl⟩ := WFF.or.inj he
    exact .inst hψ₀ (WFF.SubC.sub (.or_r .refl) hχ) θ hθ hc hΓ₁ hΓ rfl
  case optx k _ hy _ =>
    cases k
    · simp only [WFF.subst] at he; cases he
    · simp only [WFF.subst] at he; cases he
  all_goals (simp only [WFF.subst] at he; cases he)

theorem imp_l {φ ψ : WFF σ Γ 0} (h : SharpSub E Γ (φ.imp ψ)) : SharpSub E Γ φ := by
  obtain ⟨ψ₀, hψ₀, Γ₁, d₁, χ, hχ, ι, θ, hθ, hc, hΓ₁, hΓ, he⟩ :=
    h.inst_of (by simp [WFF.IsAtom])
  cases χ
  case imp χ₁ χ₂ =>
    simp only [WFF.subst] at he
    obtain ⟨rfl, -⟩ := WFF.imp.inj he
    exact .inst hψ₀ (WFF.SubC.sub (.imp_l .refl) hχ) θ hθ hc hΓ₁ hΓ rfl
  case optx k _ hy _ =>
    cases k
    · simp only [WFF.subst] at he; cases he
    · simp only [WFF.subst] at he; cases he
  all_goals (simp only [WFF.subst] at he; cases he)

theorem imp_r {φ ψ : WFF σ Γ 0} (h : SharpSub E Γ (φ.imp ψ)) : SharpSub E Γ ψ := by
  obtain ⟨ψ₀, hψ₀, Γ₁, d₁, χ, hχ, ι, θ, hθ, hc, hΓ₁, hΓ, he⟩ :=
    h.inst_of (by simp [WFF.IsAtom])
  cases χ
  case imp χ₁ χ₂ =>
    simp only [WFF.subst] at he
    obtain ⟨-, rfl⟩ := WFF.imp.inj he
    exact .inst hψ₀ (WFF.SubC.sub (.imp_r .refl) hχ) θ hθ hc hΓ₁ hΓ rfl
  case optx k _ hy _ =>
    cases k
    · simp only [WFF.subst] at he; cases he
    · simp only [WFF.subst] at he; cases he
  all_goals (simp only [WFF.subst] at he; cases he)

theorem all_inst [ModalSys.NoOpt]
    [Γ.NoSlots] {T : VarType} {φ : WFF σ (Γ.insert (.bnd 0) T) 1} {a : Ann T}
    (t : Term σ Γ T a) (h : SharpSub E Γ (.all T φ)) :
    SharpSub E Γ (WFF.instantiate Ctx.NoSlots.slots t φ) := by
  obtain ⟨ψ₀, hψ₀, Γ₁, d₁, χ, hχ, ι, θ, hθ, hc, hΓ₁, hΓ, he⟩ :=
    h.inst_of (by simp [WFF.IsAtom])
  cases χ
  case all T' χ' =>
    simp only [WFF.subst] at he
    obtain ⟨rfl, he⟩ := WFF.all.inj he
    obtain rfl := eq_of_heq he
    exact .inst hψ₀ (WFF.SubC.sub (.all .refl) hχ) _ _ _ _ _
      (WFF.instantiate_subst_under θ hθ hc hΓ₁ hΓ t χ')
  case optx k _ hy _ =>
    cases k
    · simp only [WFF.subst] at he; cases he
    · simp only [WFF.subst] at he; cases he
  all_goals (simp only [WFF.subst] at he; cases he)

theorem ex_inst [ModalSys.NoOpt]
    [Γ.NoSlots] {T : VarType} {φ : WFF σ (Γ.insert (.bnd 0) T) 1} {a : Ann T}
    (t : Term σ Γ T a) (h : SharpSub E Γ (.ex T φ)) :
    SharpSub E Γ (WFF.instantiate Ctx.NoSlots.slots t φ) := by
  obtain ⟨ψ₀, hψ₀, Γ₁, d₁, χ, hχ, ι, θ, hθ, hc, hΓ₁, hΓ, he⟩ :=
    h.inst_of (by simp [WFF.IsAtom])
  cases χ
  case ex T' χ' =>
    simp only [WFF.subst] at he
    obtain ⟨rfl, he⟩ := WFF.ex.inj he
    obtain rfl := eq_of_heq he
    exact .inst hψ₀ (WFF.SubC.sub (.ex .refl) hχ) _ _ _ _ _
      (WFF.instantiate_subst_under θ hθ hc hΓ₁ hΓ t χ')
  case optx k _ hy _ =>
    cases k
    · simp only [WFF.subst] at he; cases he
    · simp only [WFF.subst] at he; cases he
  all_goals (simp only [WFF.subst] at he; cases he)

theorem all_eigen [Γ.NoSlots] {u : ℕ} {T : VarType} (hu : Γ.RootFresh (.free u))
    {φ : WFF σ (Γ.insert (.free u) T) 0}
    (h : SharpSub E Γ (.all T (WFF.bindFree u hu Ctx.NoSlots.slots T φ))) :
    SharpSub E (Γ.insert (.free u) T) φ := by
  obtain ⟨ψ₀, hψ₀, Γ₁, d₁, χ, hχ, ι, θ, hθ, hc, hΓ₁, hΓ, he⟩ :=
    h.inst_of (by simp [WFF.IsAtom])
  cases χ
  case all T' χ' =>
    simp only [WFF.subst] at he
    obtain ⟨rfl, he⟩ := WFF.all.inj he
    have he' := eq_of_heq he
    rw [← WFF.bindFree_toFree θ hθ hc hΓ₁ hΓ u hu T χ'] at he'
    have e := congrArg (WFF.openFree u hu Ctx.NoSlots.slots) he'
    rw [WFF.openFree_bindFree, WFF.openFree_bindFree] at e
    exact .inst hψ₀ (WFF.SubC.sub (.all .refl) hχ) _ _ _ _ _ e
  case optx k _ hy _ =>
    cases k
    · simp only [WFF.subst] at he; cases he
    · simp only [WFF.subst] at he; cases he
  all_goals (simp only [WFF.subst] at he; cases he)

theorem ex_eigen [Γ.NoSlots] {u : ℕ} {T : VarType} (hu : Γ.RootFresh (.free u))
    {φ : WFF σ (Γ.insert (.free u) T) 0}
    (h : SharpSub E Γ (.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T φ))) :
    SharpSub E (Γ.insert (.free u) T) φ := by
  obtain ⟨ψ₀, hψ₀, Γ₁, d₁, χ, hχ, ι, θ, hθ, hc, hΓ₁, hΓ, he⟩ :=
    h.inst_of (by simp [WFF.IsAtom])
  cases χ
  case ex T' χ' =>
    simp only [WFF.subst] at he
    obtain ⟨rfl, he⟩ := WFF.ex.inj he
    have he' := eq_of_heq he
    rw [← WFF.bindFree_toFree θ hθ hc hΓ₁ hΓ u hu T χ'] at he'
    have e := congrArg (WFF.openFree u hu Ctx.NoSlots.slots) he'
    rw [WFF.openFree_bindFree, WFF.openFree_bindFree] at e
    exact .inst hψ₀ (WFF.SubC.sub (.ex .refl) hχ) _ _ _ _ _ e
  case optx k _ hy _ =>
    cases k
    · simp only [WFF.subst] at he; cases he
    · simp only [WFF.subst] at he; cases he
  all_goals (simp only [WFF.subst] at he; cases he)

theorem weaken {δ : WFF σ Γ 0} (h : SharpSub E Γ δ) :
    ∀ {u : ℕ} {T : VarType} (hu : Γ.RootFresh (.free u)),
      SharpSub E (Γ.insert (.free u) T) (WFF.weaken hu.root T δ) := by
  induction h with
  | inst hψ hχ θ hθ hc hΓ₁ hΓ he =>
      intro u T hu
      subst he
      exact .inst hψ hχ (θ.mono (Ctx.le_insert hu.root T)) _ _ hΓ₁ (hΓ.insertFree u T)
        (WFF.mono_subst _ θ hθ hc hΓ₁ hΓ _ _)
  | refl_eq t he =>
      intro u T hu
      subst he
      exact .refl_eq (Term.mono (Ctx.le_insert hu.root T) t) rfl
  | @repl _ φ Q hQ t s _ _ he ih₁ ih₂ =>
      intro u T hu
      subst he
      have e := fun (r : Term σ _ .Var .var) =>
        WFF.mono_instantiate (Ctx.le_insert hu.root T) Ctx.NoSlots.slots Ctx.NoSlots.slots r Q
      refine .repl hQ.mono (Term.mono (Ctx.le_insert hu.root T) t)
        (Term.mono (Ctx.le_insert hu.root T) s) (ih₁ hu) ?_ (e s)
      rw [← e t]
      exact ih₂ hu

/-- Weakening along any context inclusion. -/
theorem mono {φ : WFF σ Γ 0} (h : SharpSub E Γ φ) :
    ∀ {Γ' : Ctx} [Γ'.NoSlots] (hle : Γ.Le Γ'), SharpSub E Γ' (WFF.mono hle φ) := by
  induction h with
  | inst hψ hχ θ hθ hc hΓ₁ hΓ he =>
      intro Γ' _ hle
      subst he
      exact .inst hψ hχ (θ.mono hle) _ _ hΓ₁ Ctx.NoSlots.slots
        (WFF.mono_subst _ θ hθ hc hΓ₁ hΓ _ _)
  | refl_eq t he =>
      intro Γ' _ hle
      subst he
      exact .refl_eq (Term.mono hle t) rfl
  | @repl _ φ Q hQ t s _ _ he ih₁ ih₂ =>
      intro Γ' _ hle
      subst he
      have e := fun (r : Term σ _ .Var .var) =>
        WFF.mono_instantiate hle Ctx.NoSlots.slots Ctx.NoSlots.slots r Q
      refine .repl hQ.mono (Term.mono hle t) (Term.mono hle s) (ih₁ hle) ?_ (e s)
      rw [← e t]
      exact ih₂ hle

theorem box {φ : WFF σ Γ.boxIn 0} (h : SharpSub E Γ (WFF.box (Γ := Γ) φ)) :
    SharpSub E Γ.boxIn φ := by
  obtain ⟨ψ₀, hψ₀, Γ₁, d₁, χ, hχ, ι, θ, hθ, hc, hΓ₁, hΓ, he⟩ :=
    h.inst_of (by simp [WFF.IsAtom])
  cases χ
  case box χ' =>
    simp only [WFF.subst] at he
    obtain rfl := WFF.box.inj he
    exact .inst hψ₀ (WFF.SubC.sub (.box .refl) hχ) _ _ _ hΓ₁.boxIn hΓ.boxIn rfl
  case optx k _ hy _ =>
    cases k
    · simp only [WFF.subst] at he; cases he
    · simp only [WFF.subst] at he; cases he
  all_goals (simp only [WFF.subst] at he; cases he)

theorem box_dia {φ : WFF σ Γ.boxIn 0} (x : VarSymb) (h : SharpSub E Γ (WFF.box (Γ := Γ) φ)) :
    SharpSub E (Γ.diaIn x) (WFF.mono (Ctx.le_boxIn_diaIn Γ x) φ) := by
  obtain ⟨ψ₀, hψ₀, Γ₁, d₁, χ, hχ, ι, θ, hθ, hc, hΓ₁, hΓ, he⟩ :=
    h.inst_of (by simp [WFF.IsAtom])
  cases χ
  case box χ' =>
    simp only [WFF.subst] at he
    obtain rfl := WFF.box.inj he
    exact .inst hψ₀ (WFF.SubC.sub (.box .refl) hχ) _ _ _ hΓ₁.boxIn (hΓ.diaIn x)
      (WFF.mono_subst _ _ _ _ _ _ _ _)
  case optx k _ hy _ =>
    cases k
    · simp only [WFF.subst] at he; cases he
    · simp only [WFF.subst] at he; cases he
  all_goals (simp only [WFF.subst] at he; cases he)

theorem dia {x : VarSymb} {hx : ∃ X, Γ.ref x = some (.VTypeDia X)} {φ : WFF σ (Γ.diaIn x) 0}
    (h : SharpSub E Γ (.dia x hx φ)) : SharpSub E (Γ.diaIn x) φ := by
  obtain ⟨ψ₀, hψ₀, Γ₁, d₁, χ, hχ, ι, θ, hθ, hc, hΓ₁, hΓ, he⟩ :=
    h.inst_of (by simp [WFF.IsAtom])
  cases χ
  case dia y hy χ' =>
    have hw : (θ.at y).idxAlong [] = ι y := hy.elim fun _ hY => hc y _ hY []
    change WFF.dia x hx φ = WFF.dia (ι y) _ (WFF.subst ι (θ.dia y (ι y)) (Subst.ok_dia hθ hy hw)
      (Subst.coh_dia hθ hc hy) (hΓ₁.diaIn y) (hΓ.diaIn (ι y)) χ') at he
    obtain ⟨rfl, he⟩ := WFF.dia.inj he
    exact .inst hψ₀ (WFF.SubC.sub (.dia .refl) hχ) _ _ _ _ _ (eq_of_heq he)
  case optx k _ hy _ =>
    cases k
    · simp only [WFF.subst] at he; cases he
    · simp only [WFF.subst] at he; cases he
  all_goals (simp only [WFF.subst] at he; cases he)

theorem box_keep [Γ.NoSlots] (hF : ModalSys.Four = true) {φ : WFF σ Γ.boxIn 0}
    (h : SharpSub E Γ (WFF.box (Γ := Γ) φ)) :
    SharpSub E Γ.boxIn
      (WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots φ)) := by
  obtain ⟨ψ₀, hψ₀, Γ₁, d₁, χ, hχ, ι, θ, hθ, hc, hΓ₁, hΓ, he⟩ :=
    h.inst_of (by simp [WFF.IsAtom])
  cases χ
  case box χ' =>
    simp only [WFF.subst] at he
    obtain rfl := WFF.box.inj he
    exact .inst hψ₀ (hχ.box_keep hF hΓ₁.boxIn) θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc)
      hΓ₁.boxIn Ctx.NoSlots.slots (congrArg WFF.box (WFF.shift_subst (Ctx.shifts_boxIn_boxIn hF Γ₁)
        (Ctx.shifts_boxIn_boxIn hF Γ) θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) θ.box.box
        (Subst.ok_box (Subst.ok_box hθ)) (Subst.coh_box (Subst.ok_box hθ) (Subst.coh_box hθ hc))
        hΓ₁.boxIn hΓ₁.boxIn.boxIn _ _ (Subst.shiftCorr_box_box hF hθ) χ'))
  case optx k _ hy _ =>
    cases k
    · simp only [WFF.subst] at he; cases he
    · simp only [WFF.subst] at he; cases he
  all_goals (simp only [WFF.subst] at he; cases he)

theorem dia_keep [Γ.NoSlots] (hF : ModalSys.Four = true) {y : VarSymb}
    {hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)} {φ : WFF σ (Γ.diaIn y) 0}
    (h : SharpSub E Γ (.dia y hy φ)) :
    SharpSub E Γ.boxIn (WFF.dia (.step y .keep) (Ctx.exists_keep_dia hF hy)
      (WFF.shift (Ctx.shifts_diaIn_keep hF Γ y) Ctx.NoSlots.slots φ)) := by
  obtain ⟨ψ₀, hψ₀, Γ₁, d₁, χ, hχ, ι, θ, hθ, hc, hΓ₁, hΓ, he⟩ :=
    h.inst_of (by simp [WFF.IsAtom])
  cases χ
  case dia z hz χ' =>
    have hw : (θ.at z).idxAlong [] = ι z := hz.elim fun _ hZ => hc z _ hZ []
    change WFF.dia y hy φ = WFF.dia (ι z) _ (WFF.subst ι (θ.dia z (ι z)) (Subst.ok_dia hθ hz hw)
      (Subst.coh_dia hθ hc hz) (hΓ₁.diaIn z) (hΓ.diaIn (ι z)) χ') at he
    obtain ⟨rfl, he⟩ := WFF.dia.inj he
    obtain rfl := eq_of_heq he
    have hz' : ∃ X, Γ.ref (ι z) = some (.VTypeDia X) :=
      hz.elim fun _ hZ => SubE.ref_witness (Subst.okRef_at hθ hZ) hw
    have hk₂ : ι (.step z .keep) = .step (ι z) .keep :=
      hz.elim fun _ hZ => Subst.coh_keep_dia hθ hc hZ
    have hwk : (θ.box.at (.step z .keep)).idxAlong [] = .step (ι z) .keep :=
      hz.elim fun _ hZ => Subst.idx_box_keep_dia hF hθ hc hZ
    refine .inst hψ₀ (hχ.dia_keep hF (hΓ₁.diaIn z)) θ.box (Subst.ok_box hθ)
      (Subst.coh_box hθ hc) hΓ₁.boxIn Ctx.NoSlots.slots ?_
    rw [WFF.subst_dia θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ₁.boxIn
      Ctx.NoSlots.slots (Ctx.exists_keep_dia hF hz) _ hk₂ (Ctx.exists_keep_dia hF hz')
      (Subst.ok_dia (Subst.ok_box hθ) (Ctx.exists_keep_dia hF hz) hwk)
      (hk₂ ▸ Subst.coh_dia (Subst.ok_box hθ) (Subst.coh_box hθ hc)
        (Ctx.exists_keep_dia hF hz))
      Ctx.NoSlots.slots]
    exact congrArg (WFF.dia _ _) (WFF.shift_subst (Ctx.shifts_diaIn_keep hF Γ₁ z)
      (Ctx.shifts_diaIn_keep hF Γ (ι z)) (θ.dia z (ι z)) (Subst.ok_dia hθ hz hw)
      (Subst.coh_dia hθ hc hz) _ _ _ (hΓ₁.diaIn z) _ _ _
      (Subst.shiftCorr_dia_keep hF hθ hz hw) χ')
  case optx k _ hy _ =>
    cases k
    · simp only [WFF.subst] at he; cases he
    · simp only [WFF.subst] at he; cases he
  all_goals (simp only [WFF.subst] at he; cases he)

end SharpSub

/-- ⭐**Gentzen's subformulas are single instances**: every member of `GSub E` is an instance of a
    syntactic subformula of `E`, or an atom `ref` or `repl` introduces. -/
theorem GSub.sharp [ModalSys.NoOpt]
    {Γ₀ : Ctx} [Γ₀.NoSlots] {E : List (WFF σ Γ₀ 0)} {Γ : Ctx} {φ : WFF σ Γ 0}
    (h : GSub E Γ φ) : SharpSub E Γ φ := by
  induction h with
  | mem h => exact .mem h
  | refl_eq t => exact .refl_eq t rfl
  | repl hQ t s _ _ ih₁ ih₂ => exact .repl hQ t s ih₁ ih₂ rfl
  | and_l _ ih => exact ih.and_l
  | and_r _ ih => exact ih.and_r
  | or_l _ ih => exact ih.or_l
  | or_r _ ih => exact ih.or_r
  | imp_l _ ih => exact ih.imp_l
  | imp_r _ ih => exact ih.imp_r
  | all_inst t _ ih => exact ih.all_inst t
  | ex_inst t _ ih => exact ih.ex_inst t
  | all_eigen hu _ ih => exact ih.all_eigen hu
  | ex_eigen hu _ ih => exact ih.ex_eigen hu
  | weaken hu _ ih => exact ih.weaken hu
  | box _ ih => exact ih.box
  | box_dia x _ ih => exact ih.box_dia x
  | dia _ ih => exact ih.dia
  | view_dia x _ ih => exact ih.mono _
  | box_keep hF _ ih => exact ih.box_keep hF
  | dia_keep hF _ ih => exact ih.dia_keep hF

/-- A derivation in one family is one in any larger family. -/
theorem GKS.mono {P Q : (Γ : Ctx) → WFF σ Γ 0 → Prop} (hPQ : ∀ Γ φ, P Γ φ → Q Γ φ)
    {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} (d : GKS σ P n Γ Δ Θ) : GKS σ Q n Γ Δ Θ := by
  have hS : ∀ {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)}, SeqIn P Γ Δ Θ → SeqIn Q Γ Δ Θ :=
    fun h => ⟨fun φ hφ => hPQ _ _ (h.1 φ hφ), fun φ hφ => hPQ _ _ (h.2 φ hφ)⟩
  induction d with
  | ax h A hA h₁ h₂ => exact .ax (hS h) A hA h₁ h₂
  | botL h h' => exact .botL (hS h) h'
  | topR h h' => exact .topR (hS h) h'
  | andL h h' _ ih => exact .andL (hS h) h' ih
  | andR h h' _ _ ih₁ ih₂ => exact .andR (hS h) h' ih₁ ih₂
  | orL h h' _ _ ih₁ ih₂ => exact .orL (hS h) h' ih₁ ih₂
  | orR h h' _ ih => exact .orR (hS h) h' ih
  | impL h h' _ _ ih₁ ih₂ => exact .impL (hS h) h' ih₁ ih₂
  | impR h h' _ ih => exact .impR (hS h) h' ih
  | allL h T t h' _ ih => exact .allL (hS h) T t h' ih
  | allR h u T hu h' _ ih => exact .allR (hS h) u T hu h' ih
  | exL h u T hu h' _ ih => exact .exL (hS h) u T hu h' ih
  | exR h T t h' _ ih => exact .exR (hS h) T t h' ih
  | ref h t _ ih => exact .ref (hS h) t ih
  | repl h hQ t s h₁ h₂ _ ih => exact .repl (hS h) hQ t s h₁ h₂ ih
  | boxR h h₁ h₂ h₃ _ ih => exact .boxR (hS h) h₁ h₂ h₃ ih
  | diaL h x hx h₁ h₂ h₃ h₄ _ ih => exact .diaL (hS h) x hx h₁ h₂ h₃ h₄ ih
  | serial h hD h₂ h₃ _ ih => exact .serial (hS h) hD h₂ h₃ ih

/-- ⭐**The sharp subformula property**: every ND-provable sequent of K, KD, K4 and KD4 has a
    cut-free derivation in which every formula is a single substitution instance of a subformula
    of the end sequent up to copies (a syntactic one without 4, `WFF.SubC.subF`), or an atom
    introduced by `ref` or `repl`. -/
theorem GK.subformula_sharp_of_provable [ModalSys.GKSys] {Γ : Ctx} [Γ.Presented]
    {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (p : Provable Δ φ) :
    ∃ n, GKS σ (SharpSub (Δ ++ [φ])) n Γ Δ [φ] :=
  let ⟨n, d⟩ := GK.subformula_of_provable p
  ⟨n, d.mono fun _ _ h => h.sharp⟩

end V12M
