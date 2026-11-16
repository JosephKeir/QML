import QML.QML_v12m_TCanonKT
import QML.QML_v12m_Compactness

/-!
# QML v12m — contexts with identity views opened at the top (route 2)

Completeness so far is for contexts declaring no address that ends in an identity reading
(`Ctx.NoTopAt`).  Here the rest (docs §12.36, route 2):

* **The steps of a presentation commute** with an identity opening: a free declaration and an arrow
  opening only add entries at other addresses (`Ctx.insert_optInT_comm`, `Ctx.optIn_optInT_comm`).
  So ⭐`CtxExpr.normT`: every presented context **is** `Γ'.optInTs L` with `Γ'` presented and
  `NoTopAt`, the identity openings that took effect moved to the end (one that did nothing where it
  stood is dropped).
* Then one reduction, iterated: a sequent over `C.optInT y` says what `◇⁰ᵀ_y ⊤` and `◇⁰ᵀ_y` of its
  formulas say over `C`.
-/

namespace V12M

set_option linter.unusedSectionVars false

variable [ModalSys]

open OCanon

/-! ## Contexts: extensionality and commutation -/

/-- Contexts with the same declarations and witnesses are equal. -/
theorem Ctx.ext' {Γ Δ : Ctx} (h₁ : Γ.ty = Δ.ty) (h₂ : Γ.wit = Δ.wit) : Γ = Δ := by
  cases Γ
  cases Δ
  cases h₁
  cases h₂
  rfl

/-- Opening the identity view of an address that is not a possibility here changes nothing. -/
theorem Ctx.optInT_of_witT_none {Γ : Ctx} {y : VarSymb} (h : Γ.witT y = none) :
    Γ.optInT y = Γ := by
  refine Ctx.ext' (funext fun v => ?_) rfl
  change Γ.optInTTy y v = Γ v
  unfold Ctx.optInTTy
  by_cases hv : v = .step y .at
  · rw [if_pos hv, h]
  · rw [if_neg hv]

/-- ⭐A fresh declaration commutes with an identity opening that takes effect. -/
theorem Ctx.insert_optInT_comm {Γ : Ctx} {u : ℕ} (hu : Γ.RootFresh (.free u)) {y : VarSymb}
    {X : VarType} (hy : Γ.witT y = some X) (T : VarType) :
    (Γ.optInT y).insert (.free u) T = (Γ.insert (.free u) T).optInT y := by
  have hyI : (Γ.insert (.free u) T).witT y = some X := (Ctx.le_insert (hu _ rfl) T).witT hy
  have hrt : y.rt ≠ .free u := fun he => by
    have h₁ := Ctx.ref_none_of_rootFresh hu y he
    rw [(Ctx.witT_spec hy).2.2] at h₁
    cases h₁
  refine Ctx.ext' (funext fun v => ?_) rfl
  change (if v = .root (.free u) then some T
      else if v.atBelow (.free u) then none else Γ.optInTTy y v) =
    (Γ.insert (.free u) T).optInTTy y v
  unfold Ctx.optInTTy
  by_cases hv : v = .step y .at
  · subst hv
    have hab : (VarSymb.step y .at).atBelow (.free u) = false := by
      simp [VarSymb.atBelow, VarSymb.rt, hrt]
    rw [if_neg (fun h => by cases h), if_pos rfl, if_pos rfl, hyI, hy, hab]
    rfl
  · rw [if_neg hv, if_neg hv]
    rfl

/-- ⭐An arrow opening commutes with an identity opening that takes effect. -/
theorem Ctx.optIn_optInT_comm {Γ : Ctx} {y : VarSymb} {X : VarType} (hy : Γ.witT y = some X)
    (z : VarSymb) : (Γ.optInT y).optIn z = (Γ.optIn z).optInT y := by
  have hyI : (Γ.optIn z).witT y = some X := (Ctx.le_optIn Γ z).witT hy
  refine Ctx.ext' (funext fun v => ?_) rfl
  change (if v = .step z .dia then (match Γ.wit z with
      | some X' => some X' | none => Γ.optInTTy y v) else Γ.optInTTy y v) =
    (Γ.optIn z).optInTTy y v
  unfold Ctx.optInTTy
  by_cases hv : v = .step y .at
  · subst hv
    rw [if_neg (fun h => by cases h), if_pos rfl, if_pos rfl, hy, hyI]
  · rw [if_neg hv, if_neg hv]
    rfl

/-! ## Several identity openings -/

/-- The identity views of the list's addresses opened, the head last. -/
def Ctx.optInTs (Γ : Ctx) : List VarSymb → Ctx
  | [] => Γ
  | y :: L => (Γ.optInTs L).optInT y

/-- Every opening of the list takes effect: each address is a possibility where it is opened. -/
def Ctx.OptTEff (Γ : Ctx) : List VarSymb → Prop
  | [] => True
  | y :: L => Γ.OptTEff L ∧ ∃ X, (Γ.optInTs L).witT y = some X

theorem Ctx.optInTs_wit (Γ : Ctx) : ∀ L : List VarSymb, (Γ.optInTs L).wit = Γ.wit
  | [] => rfl
  | _ :: L => Ctx.optInTs_wit Γ L

theorem Ctx.le_optInTs (Γ : Ctx) : ∀ L : List VarSymb, Γ.Le (Γ.optInTs L)
  | [] => Ctx.Le.refl Γ
  | y :: L => (Ctx.le_optInTs Γ L).trans (Ctx.le_optInT _ y)

theorem Ctx.Le.optInTs {Γ Γ' : Ctx} (h : Γ.Le Γ') : ∀ L : List VarSymb,
    (Γ.optInTs L).Le (Γ'.optInTs L)
  | [] => h
  | y :: L => (Ctx.Le.optInTs h L).optInT y

theorem Ctx.OptTEff.mono {Γ Γ' : Ctx} (h : Γ.Le Γ') : ∀ {L : List VarSymb}, Γ.OptTEff L →
    Γ'.OptTEff L
  | [], _ => trivial
  | _ :: L, ⟨he, X, hX⟩ => ⟨Ctx.OptTEff.mono h he, X, (Ctx.Le.optInTs h L).witT hX⟩

/-- The identity openings keep every declaration. -/
theorem Ctx.optInTs_ty_le (Γ : Ctx) : ∀ (L : List VarSymb) {v : VarSymb} {U : VarType},
    Γ v = some U → Γ.optInTs L v = some U
  | [], _, _, h => h
  | y :: L, _, _, h => Ctx.optInT_ty_le _ y _ (Ctx.optInTs_ty_le Γ L h)

theorem Ctx.RootFresh.optInTs {Γ : Ctx} {r : Root} (h : Γ.RootFresh r) :
    ∀ L : List VarSymb, (Γ.optInTs L).RootFresh r
  | [] => h
  | y :: L => (Ctx.RootFresh.optInTs h L).optInK .ident y

theorem Ctx.insert_optInTs_comm {Γ : Ctx} {u : ℕ} (hu : Γ.RootFresh (.free u)) (T : VarType) :
    ∀ {L : List VarSymb}, Γ.OptTEff L →
      (Γ.optInTs L).insert (.free u) T = (Γ.insert (.free u) T).optInTs L
  | [], _ => rfl
  | y :: L, ⟨he, _, hX⟩ => by
      change ((Γ.optInTs L).optInT y).insert (.free u) T =
        ((Γ.insert (.free u) T).optInTs L).optInT y
      rw [Ctx.insert_optInT_comm (Ctx.RootFresh.optInTs hu L) hX T,
        Ctx.insert_optInTs_comm hu T he]

theorem Ctx.optIn_optInTs_comm {Γ : Ctx} (z : VarSymb) :
    ∀ {L : List VarSymb}, Γ.OptTEff L → (Γ.optInTs L).optIn z = (Γ.optIn z).optInTs L
  | [], _ => rfl
  | y :: L, ⟨he, _, hX⟩ => by
      change ((Γ.optInTs L).optInT y).optIn z = ((Γ.optIn z).optInTs L).optInT y
      rw [Ctx.optIn_optInT_comm hX z, Ctx.optIn_optInTs_comm z he]

/-! ## The normal form of a presentation -/

theorem Ctx.noTopAt_empty : Ctx.empty.NoTopAt := fun _ _ h => by cases h

theorem Ctx.noTopAt_diaIn (Γ : Ctx) (x : VarSymb) : (Γ.diaIn x).NoTopAt :=
  fun _ T hv => by cases (show (none : Option VarType) = some T from hv)

/-- ⭐**Identity openings move to the end of a presentation**: every presented context is a context
    with no identity reading at its top, presented, with the openings that took effect applied
    last. -/
theorem CtxExpr.normT : ∀ e : CtxExpr, e.Fresh → ∃ (e' : CtxExpr) (L : List VarSymb),
    e'.Fresh ∧ e'.denote.NoTopAt ∧ e'.denote.OptTEff L ∧ e.denote = e'.denote.optInTs L
  | .empty, _ => ⟨.empty, [], trivial, Ctx.noTopAt_empty, trivial, rfl⟩
  | .insertFree e u T, ⟨hf, hu⟩ => by
      obtain ⟨e', L, hf', hna, heff, heq⟩ := CtxExpr.normT e hf
      have hu' : e'.denote.RootFresh (.free u) := by
        refine ⟨fun v hv => ?_, fun y hy => ?_⟩
        · cases hd : e'.denote v with
          | none => rfl
          | some U =>
              have h₁ := Ctx.optInTs_ty_le e'.denote L hd
              rw [← heq, hu v hv] at h₁
              cases h₁
        · have h₁ := hu.wit y hy
          rwa [heq, Ctx.optInTs_wit] at h₁
      refine ⟨.insertFree e' u T, L, ⟨hf', hu'⟩, Ctx.NoTopAt.insert' hna _ _,
        heff.mono (Ctx.le_insert (hu' _ rfl) T), ?_⟩
      change e.denote.insert (.free u) T = (e'.denote.insert (.free u) T).optInTs L
      rw [heq, Ctx.insert_optInTs_comm hu' T heff]
  | .boxIn e, hf => ⟨.boxIn e, [], hf, Ctx.noTopAt_boxIn _, trivial, rfl⟩
  | .diaIn e x, hf => ⟨.diaIn e x, [], hf, Ctx.noTopAt_diaIn _ x, trivial, rfl⟩
  | .optIn e .arrow z, hf => by
      obtain ⟨e', L, hf', hna, heff, heq⟩ := CtxExpr.normT e hf
      refine ⟨.optIn e' .arrow z, L, hf', Ctx.NoTopAt.optIn' hna z,
        heff.mono (Ctx.le_optIn _ z), ?_⟩
      change e.denote.optIn z = (e'.denote.optIn z).optInTs L
      rw [heq, Ctx.optIn_optInTs_comm z heff]
  | .optIn e .ident y, hf => by
      obtain ⟨e', L, hf', hna, heff, heq⟩ := CtxExpr.normT e hf
      change ∃ (e'' : CtxExpr) (L' : List VarSymb), e''.Fresh ∧ e''.denote.NoTopAt ∧
        e''.denote.OptTEff L' ∧ e.denote.optInT y = e''.denote.optInTs L'
      cases hw : e.denote.witT y with
      | none =>
          rw [Ctx.optInT_of_witT_none hw]
          exact ⟨e', L, hf', hna, heff, heq⟩
      | some X =>
          refine ⟨e', y :: L, hf', hna, ⟨heff, X, heq ▸ hw⟩, ?_⟩
          rw [heq]
          rfl

/-! ## Presentations of the opened contexts -/

/-- A presentation with identity views opened at the end. -/
def CtxExpr.optInTs (e : CtxExpr) : List VarSymb → CtxExpr
  | [] => e
  | y :: L => .optIn (e.optInTs L) .ident y

theorem CtxExpr.denote_optInTs (e : CtxExpr) : ∀ L : List VarSymb,
    (e.optInTs L).denote = e.denote.optInTs L
  | [] => rfl
  | y :: L => by
      change (e.optInTs L).denote.optInT y = (e.denote.optInTs L).optInT y
      rw [CtxExpr.denote_optInTs e L]

theorem CtxExpr.Fresh.optInTs {e : CtxExpr} (h : e.Fresh) : ∀ L : List VarSymb,
    (e.optInTs L).Fresh
  | [] => h
  | _ :: L => CtxExpr.Fresh.optInTs h L

/-- The opened contexts of a presented context are presented. -/
def Ctx.presentedOptInTs (e : CtxExpr) (h : e.Fresh) (L : List VarSymb) :
    (e.denote.optInTs L).Presented :=
  ⟨e.optInTs L, h.optInTs L, CtxExpr.denote_optInTs e L⟩

/-! ## Validity, and the reduction -/

variable {σ : Signature}

/-- A sequent **holds in every model**, in every environment respecting its identity contents
    (what soundness asks; vacuous where no identity reading is declared at the top). -/
def ValidO {Γ : Ctx} (Δ : List (WFF σ Γ 0)) (φ : WFF σ Γ 0) : Prop :=
  ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W} (env : M.Env Γ w),
    Γ.NoProjLast → env.OpenedT → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ

/-- ⭐**Route 2's reduction**: a valid sequent over `C.optInT y` is provable when every valid
    sequent over `C` is.  Over `C`, `◇⁰ᵀ_y ⊤` and `◇⁰ᵀ_y` of its formulas give `◇⁰ᵀ_y` of its
    conclusion (an environment over the view is one over `C` pushed into it, `optPushT`); back
    in the view, where `y.at` is declared, the hypotheses reopen (`opt_reopen`) and the
    conclusion comes out (`opt_out`). -/
theorem complete_optInT {C : Ctx} {y : VarSymb} {X : VarType} (hy : C.witT y = some X)
    [(C.optInT y).Presented]
    (ih : ∀ {Δ : List (WFF σ C 0)} {φ : WFF σ C 0}, ValidO Δ φ → Provable Δ φ)
    {Δ : List (WFF σ (C.optInT y) 0)} {φ : WFF σ (C.optInT y) 0} (hval : ValidO Δ φ) :
    Provable Δ φ := by
  obtain ⟨-, hO, -⟩ := Ctx.witT_spec hy
  have hyK : ∃ X, C.witK .ident y = some X := ⟨X, hy⟩
  let W : WFF σ (C.optInT y) 0 → WFF σ C 0 := fun ψ => .optx hO .ident y hyK ψ
  have hv' : ValidO (W .top :: Δ.map W) (W φ) := by
    intro M hM w env _ hop hΔ
    obtain ⟨X', h', hd, -⟩ := hΔ _ List.mem_cons_self
    obtain rfl : X' = X := Option.some.inj (h'.symm.trans hy)
    refine ⟨X', h', hd, hval M hM (env.optPushT y h' hd) (Ctx.Presented.noProjLast _)
      (hop.optPushT h' hd) fun ψ hψ => ?_⟩
    obtain ⟨X'', h'', hd'', hs⟩ := hΔ (W ψ) (List.mem_cons_of_mem _ (List.mem_map_of_mem hψ))
    obtain rfl : X'' = X' := Option.some.inj (h''.symm.trans h')
    exact hs
  have hp := Provable.monoCtx (Ctx.le_optInT C y) (ih hv')
  have hdecl : ∃ X', (C.optInT y).witK .ident y = some X' ∧
      (C.optInT y) (.step y .at) = some X' :=
    ⟨X, (Ctx.le_optInT C y).witT hy, Ctx.optInT_content hy⟩
  have hall : ∀ x ∈ (W .top :: Δ.map W).map (WFF.mono (Ctx.le_optInT C y)), Provable Δ x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨Proof.opt_reopen hO .ident y hdecl .top_intro⟩
    · obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp ha
      exact ⟨Proof.opt_reopen hO .ident y hdecl (Proof.lookup hψ)⟩
  exact (Provable.of_all hall hp).map
    (Proof.opt_out hO .ident y ⟨X, (Ctx.le_optInT C y).witT hy⟩)

variable [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.WeakTO]

/-- Completeness over the opened contexts of a presented context with no identity reading at its
    top, by the reduction, one opening at a time. -/
theorem complete_optInTs (hO : ModalSys.Opt = true) (e : CtxExpr) (hf : e.Fresh)
    (hna : e.denote.NoTopAt) : ∀ (L : List VarSymb), e.denote.OptTEff L →
      ∀ {Δ : List (WFF σ (e.denote.optInTs L) 0)} {φ : WFF σ (e.denote.optInTs L) 0},
        ValidO Δ φ → Provable Δ φ
  | [], _, Δ, φ, hval => by
      haveI : e.denote.Presented := ⟨e, hf, rfl⟩
      exact OCanon.completenessT hO hna fun M hM w env hnp hΔ =>
        hval M hM env hnp (fun _ _ _ hv => (hna _ _ hv).elim) hΔ
  | y :: L, ⟨heff, _, hX⟩, _, _, hval => by
      haveI : ((e.denote.optInTs L).optInT y).Presented :=
        Ctx.presentedOptInTs e hf (y :: L)
      exact complete_optInT hX (complete_optInTs hO e hf hna L heff) hval

/-- ⭐**Completeness with `Opt` on, T included, for every presented context**: a sequent that holds
    in every model, in every environment respecting its identity contents, is provable. -/
theorem completenessO (hO : ModalSys.Opt = true) {Γ : Ctx} [hp : Γ.Presented]
    {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (hval : ValidO Δ φ) : Provable Δ φ := by
  obtain ⟨e', L, hf', hna, heff, heq⟩ := CtxExpr.normT hp.expr hp.fresh
  have hΓ : Γ = e'.denote.optInTs L := hp.denote_eq.symm.trans heq
  subst hΓ
  exact complete_optInTs hO e' hf' hna L heff hval

/-- ⭐**Soundness and completeness with `Opt` on, T included** (strong T off), for every presented
    context over a countable signature. -/
theorem provable_iff_validO (hO : ModalSys.Opt = true) {Γ : Ctx} [Γ.Presented]
    {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} : Provable Δ φ ↔ ValidO Δ φ :=
  ⟨fun ⟨p⟩ M hM _ env hnp hop => Model.soundness p M hM env (Ctx.Presented.tame Γ) hnp hop,
    completenessO hO⟩

end V12M
