import QML.QML_v12m_TCanonDom
import QML.QML_v12m_ReadRen

/-!
# QML v12m — the KT tree with `Opt` on: `≡` in the theory is identity of denotations

Strong T's canonical law (`posRet_exists`) asks, at **every** world, for a possible object whose
content at the self arrow is a given object.  The candidate is a Henkin root `c` with
`◇⁰ᵀ_c (c.at ≡ t)`; its content there is `c`'s identity name `d`, and the theory has `d ≡ t`.
What is missing is that `≡` in the theory means equal denotations (docs §12.36, strong T):

* ⭐`faithO`: `t ≡ s` in a world's theory gives `rdenO t = rdenO s`, by induction on the type:
  `=` by the classes, products componentwise, `□` at the children (`AccO.box`) and at the self
  arrow (`T_box`, `WFF.collapse_eqH`), `◇` by presence and contents along each arrow.

Syntactic: no truth lemma is used, so it holds at every world (the truth lemma needs `DecidesO`).
-/

namespace V12M

set_option linter.unusedSectionVars false

variable [ModalSys]

namespace OCanon

open Canon

variable {σ : Signature} {N₀ : ℕ}

variable (hO : ModalSys.Opt = true) [Countable σ.FuncSyms] [Countable σ.RelSyms]

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- Weakening the name sentence. -/
theorem nameSent_mono {Γ Γ' : Ctx} (h : Γ.Le Γ') (hT : ModalSys.T = true) {x : VarSymb}
    {A : VarType} (hx : Γ.ref x = some (.VTypeDia A)) {a : Ann A} (t : Term σ Γ A a) :
    WFF.mono h (TCanon.nameSent hT hO hx t) = TCanon.nameSent hT hO (h.ref hx) (Term.mono h t) := by
  change WFF.optx hO .ident x _ (WFF.mono (h.optInK .ident x) (eqH hO A _ _)) =
    WFF.optx hO .ident x _ (eqH hO A (Term.eta (.step x .at) A _)
      (Term.mono (Ctx.le_optInT Γ' x) (Term.mono h t)))
  rw [eqH_mono, Term.mono_eta, Term.mono_mono, Term.mono_mono]

/-! ## Presence and contents of two witnesses -/

/-- Two possible objects with one extent and equal contents along it are equal. -/
theorem sigma_set_ext {α : Type} {β : α → Type} :
    ∀ {o o' : Σ E : Set α, (a : E) → β a.1}, o.1 = o'.1 →
      (∀ a (h : a ∈ o.1) (h' : a ∈ o'.1), o.2 ⟨a, h⟩ = o'.2 ⟨a, h'⟩) → o = o'
  | ⟨E, f⟩, ⟨E', f'⟩, hE, hf => by
      change E = E' at hE
      subst hE
      congr 1
      funext ⟨a, h⟩
      exact hf a h h

/-- ⭐**Presence passes along `≡`**: from the witnesses' equality and the first's presence, the
    second's. -/
def Proof.witEqK_pres {Γ : Ctx} (κ : WitKind) {z z' : VarSymb} (hz : ∃ Z, Γ.witK κ z = some Z)
    (hz' : ∃ Z, Γ.witK κ z' = some Z) (hz'' : ∃ Z, (Γ.optInK κ z).witK κ z' = some Z)
    (φ : WFF σ ((Γ.optInK κ z).optInK κ z') 0) :
    Proof σ Γ [.imp (.or (.optx hO κ z hz .top) (.optx hO κ z' hz' .top))
        (.optx hO κ z hz (.optx hO κ z' hz'' φ)), .optx hO κ z hz .top]
      (.optx hO κ z' hz' .top) :=
  Proof.opt_out hO κ z hz (.imp_elim (Proof.ofSubset (fun _ h => by simp at h) (.imp_intro
      (Proof.K_opt hO κ z hz (Δ₁ := []) (Δ₂ := [])
        (Proof.K_opt hO κ z' hz'' (Δ₁ := []) (Δ₂ := []) (φ := .top) (ψ := φ) .top_intro))))
    (.imp_elim (Proof.lookup List.mem_cons_self)
      (.or_intro_l _ (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))))

/-- The same from the second's presence. -/
def Proof.witEqK_pres' {Γ : Ctx} (κ : WitKind) {z z' : VarSymb} (hz : ∃ Z, Γ.witK κ z = some Z)
    (hz' : ∃ Z, Γ.witK κ z' = some Z) (hz'' : ∃ Z, (Γ.optInK κ z).witK κ z' = some Z)
    (φ : WFF σ ((Γ.optInK κ z).optInK κ z') 0) :
    Proof σ Γ [.imp (.or (.optx hO κ z hz .top) (.optx hO κ z' hz' .top))
        (.optx hO κ z hz (.optx hO κ z' hz'' φ)), .optx hO κ z' hz' .top]
      (.optx hO κ z hz .top) :=
  .imp_elim (Proof.ofSubset (fun _ h => by simp at h) (.imp_intro
      (Proof.K_opt hO κ z hz (Δ₁ := []) (Δ₂ := []) (φ := .top) (ψ := .optx hO κ z' hz'' φ)
        .top_intro)))
    (.imp_elim (Proof.lookup List.mem_cons_self)
      (.or_intro_r _ (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))))

/-- ⭐**A child opened a witness exactly when it has `◇⁰_x ⊤`** at the child stage. -/
theorem AccO.opened_iff {w w' : World σ N₀} (ha : AccO hO w w') {i : ℕ × ℕ} {x : VarSymb}
    {X : VarType} (hX : (w.L.ctx i).boxIn.wit x = some X) :
    Opened w w' x ↔ (⟨childStage i, .optx hO .arrow x ⟨X, (ha.boxIn_le i).wit x X hX⟩ .top⟩ :
      w'.L.sys.Sentence σ) ∈ w'.T := by
  set M := max i.1 i.2
  have hM : (w.L.ctx i).boxIn.Le (bview w M) := (le_diag_max w i).boxIn
  have hw' : (w'.L.ctx (childStage i)).wit x = some X := (ha.boxIn_le i).wit x X hX
  constructor
  · intro ho
    have hd : w'.L.ctx (childStage i) (.step x .dia) = some X := ha.opened_at ho (hM.wit x X hX)
    exact World.mem_of_provable (Δ := []) (fun _ h => by simp at h)
      ⟨Proof.opt_reopen hO .arrow x ⟨X, hw', hd⟩ (ψ := .top) .top_intro⟩
  · intro hp
    rcases ha.decides M x X ((ha.wit M x).trans (hM.wit x X hX)) with hd | hneg
    · exact ⟨M, X, hM.wit x X hX, hd⟩
    · exact (w'.mcs.bot_not_mem (i := childStage i) (World.mem_of_provable (Δ := [_, _])
        (fun ψ hψ => by
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact hneg
          · rw [List.mem_singleton.mp hψ]
            exact hp)
        ⟨.imp_elim (Proof.lookup List.mem_cons_self)
          (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩)).elim

/-- ⭐**Out of two opened views**: at a stage declaring both contents, `◇⁰_x ◇⁰_x' ψ` gives `ψ`
    there. -/
theorem mem_out₂ (w : World σ N₀) (j : ℕ × ℕ) {x x' : VarSymb} {X X' : VarType}
    (hX : (w.L.ctx j).wit x = some X) (hX' : (w.L.ctx j).wit x' = some X')
    (hz' : ∃ Z, ((w.L.ctx j).optIn x).wit x' = some Z)
    (hle : (((w.L.ctx j).optIn x).optIn x').Le (w.L.ctx j))
    (ψ : WFF σ (((w.L.ctx j).optIn x).optIn x') 0)
    (hm : (⟨j, .optx hO .arrow x ⟨X, hX⟩ (.optx hO .arrow x' hz' ψ)⟩ : w.L.sys.Sentence σ) ∈
      w.T) :
    (⟨j, WFF.mono hle ψ⟩ : w.L.sys.Sentence σ) ∈ w.T := by
  have e : ψ = WFF.mono ((Ctx.le_optIn (w.L.ctx j) x).optIn x')
      (WFF.mono (Ctx.le_optIn (w.L.ctx j) x') (WFF.mono hle ψ)) := by
    rw [WFF.mono_mono, WFF.mono_mono, WFF.mono_refl]
  rw [e] at hm
  exact World.mem_of_provable (Δ := [_]) (fun φ hφ => by rw [List.mem_singleton.mp hφ]; exact hm)
    ⟨Proof.opt_out hO .arrow x' ⟨X', hX'⟩
      (Proof.opt_out hO .arrow x ⟨X, hX⟩ (Proof.lookup List.mem_cons_self))⟩

theorem mem_imp_or_l (w : World σ N₀) (j : ℕ × ℕ) {φ ψ χ : WFF σ (w.L.ctx j) 0}
    (h : (⟨j, .imp (.or φ ψ) χ⟩ : w.L.sys.Sentence σ) ∈ w.T)
    (hφ : (⟨j, φ⟩ : w.L.sys.Sentence σ) ∈ w.T) : (⟨j, χ⟩ : w.L.sys.Sentence σ) ∈ w.T :=
  World.mem_of_provable (Δ := [_, _])
    (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact h
      · rw [List.mem_singleton.mp hψ]
        exact hφ)
    ⟨.imp_elim (Proof.lookup List.mem_cons_self)
      (.or_intro_l _ (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))⟩

theorem mem_imp_or_r (w : World σ N₀) (j : ℕ × ℕ) {φ ψ χ : WFF σ (w.L.ctx j) 0}
    (h : (⟨j, .imp (.or φ ψ) χ⟩ : w.L.sys.Sentence σ) ∈ w.T)
    (hψ' : (⟨j, ψ⟩ : w.L.sys.Sentence σ) ∈ w.T) : (⟨j, χ⟩ : w.L.sys.Sentence σ) ∈ w.T :=
  World.mem_of_provable (Δ := [_, _])
    (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact h
      · rw [List.mem_singleton.mp hψ]
        exact hψ')
    ⟨.imp_elim (Proof.lookup List.mem_cons_self)
      (.or_intro_r _ (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))⟩

/-- Presence passes along `≡`, as membership, both ways. -/
theorem mem_pres (w : World σ N₀) (j : ℕ × ℕ) (κ : WitKind) {z z' : VarSymb}
    {hz : ∃ Z, (w.L.ctx j).witK κ z = some Z} {hz' : ∃ Z, (w.L.ctx j).witK κ z' = some Z}
    {hz'' : ∃ Z, ((w.L.ctx j).optInK κ z).witK κ z' = some Z}
    {φ : WFF σ (((w.L.ctx j).optInK κ z).optInK κ z') 0}
    (h : (⟨j, .imp (.or (.optx hO κ z hz .top) (.optx hO κ z' hz' .top))
        (.optx hO κ z hz (.optx hO κ z' hz'' φ))⟩ : w.L.sys.Sentence σ) ∈ w.T) :
    (⟨j, .optx hO κ z hz .top⟩ : w.L.sys.Sentence σ) ∈ w.T ↔
      (⟨j, .optx hO κ z' hz' .top⟩ : w.L.sys.Sentence σ) ∈ w.T := by
  have hmem : ∀ θ : WFF σ (w.L.ctx j) 0, (⟨j, θ⟩ : w.L.sys.Sentence σ) ∈ w.T →
      ∀ ψ ∈ [.imp (.or (.optx hO κ z hz .top) (.optx hO κ z' hz' .top))
        (.optx hO κ z hz (.optx hO κ z' hz'' φ)), θ], (⟨j, ψ⟩ : w.L.sys.Sentence σ) ∈ w.T :=
    fun θ hθ ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact h
      · rw [List.mem_singleton.mp hψ]
        exact hθ
  exact ⟨fun hp => World.mem_of_provable (hmem _ hp) ⟨Proof.witEqK_pres hO κ hz hz' hz'' φ⟩,
    fun hp => World.mem_of_provable (hmem _ hp) ⟨Proof.witEqK_pres' hO κ hz hz' hz'' φ⟩⟩

theorem mem_extentO_acc_iff {w : World σ N₀} {x : VarSymb} (w' : SuccO hO w)
    (hd : w'.1.depth - w.depth ≠ 0) : w' ∈ extentO w x ↔ Opened w w'.1 x :=
  ⟨fun h => (extentO_child h hd).2, fun ho => Or.inl ⟨SuccO.acc w' hd, ho⟩⟩

theorem mem_extentO_self_iff {w : World σ N₀} {x : VarSymb} (w' : SuccO hO w)
    (hd : w'.1.depth - w.depth = 0) : w' ∈ extentO w x ↔ SelfIn hO w x :=
  ⟨fun h => (extentO_self h hd).2, fun hs => Or.inr ⟨(SuccO.self w' hd).2, hs⟩⟩

/-- ⭐**The `◇` case of faithfulness**, given it at the content type. -/
theorem faithO_dia {A : VarType}
    (ih : ∀ {a b : Ann A} (w : World σ N₀) (i : ℕ × ℕ) (t : Term σ (w.L.ctx i) A a)
      (s : Term σ (w.L.ctx i) A b), (⟨i, eqH hO A t s⟩ : w.L.sys.Sentence σ) ∈ w.T →
        rdenO hO w i (Ctx.Le.refl _) t = rdenO hO w i (Ctx.Le.refl _) s)
    {a b : Ann A} (w : World σ N₀) (i : ℕ × ℕ) {x x' : VarSymb}
    (hx : ∃ X, (w.L.ctx i).ref x = some (.VTypeDia X))
    (hx' : ∃ X, (w.L.ctx i).ref x' = some (.VTypeDia X))
    (t : Term σ ((w.L.ctx i).diaIn x) A a) (s : Term σ ((w.L.ctx i).diaIn x') A b)
    (hm : (⟨i, eqH hO (.VTypeDia A) (Term.diatm x hx t) (Term.diatm x' hx' s)⟩ :
      w.L.sys.Sentence σ) ∈ w.T) :
    rdenO hO w i (Ctx.Le.refl _) (Term.diatm x hx t) =
      rdenO hO w i (Ctx.Le.refl _) (Term.diatm x' hx' s) := by
  obtain ⟨X, hX⟩ := Ctx.boxIn_wit_of hO hx
  obtain ⟨X', hX'⟩ := Ctx.boxIn_wit_of hO hx'
  -- along a proper arrow: the child's copy of the witnesses' equality
  have hchild : ∀ w' : SuccO hO w, w'.1.depth - w.depth ≠ 0 →
      (Opened w w'.1 x ↔ Opened w w'.1 x') := by
    intro w' hd
    have ha := SuccO.acc w' hd
    have hc := ha.box i _ (childStage i) (ha.boxIn_le i) hm
    rw [ha.opened_iff hO hX, ha.opened_iff hO hX']
    exact mem_pres hO w'.1 (childStage i) .arrow hc
  -- at the self arrow: the identity witnesses' equality
  have hselfc : ∀ hT : ModalSys.T = true,
      (⟨i, WFF.collapse (Ctx.collapses_boxIn_self hT _) Ctx.NoSlots.slots
        (witEq hO A ⟨X, hX⟩ ⟨X', hX'⟩ (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx) t)
          (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx') s))⟩ :
        w.L.sys.Sentence σ) ∈ w.T := fun hT =>
    World.mem_of_provable (w := w) (Δ := [_])
      (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hm)
      ⟨Proof.T_box hT (Proof.lookup List.mem_cons_self)⟩
  have hrx := (Ctx.boxIn_wit.mp hX).2
  have hrx' := (Ctx.boxIn_wit.mp hX').2
  have hself : SelfIn hO w x ↔ SelfIn hO w x' := by
    constructor
    · rintro ⟨hT, ⟨j, Y, hyj, hp⟩, hna⟩
      have hc := hselfc hT
      rw [WFF.collapse_witEq hO _ _ A hX hX'] at hc
      have hcK := (World.mem_lift (w := w) (le_sup_left : i ≤ i ⊔ j)).mp hc
      have hpK := (World.mem_lift (w := w) (le_sup_right : j ≤ i ⊔ j)).mp hp
      exact ⟨hT, ⟨i ⊔ j, X', (w.L.ctx_le le_sup_left).ref hrx',
        (mem_pres hO w (i ⊔ j) .ident hcK).mp hpK⟩, hna⟩
    · rintro ⟨hT, ⟨j, Y, hyj, hp⟩, hna⟩
      have hc := hselfc hT
      rw [WFF.collapse_witEq hO _ _ A hX hX'] at hc
      have hcK := (World.mem_lift (w := w) (le_sup_left : i ≤ i ⊔ j)).mp hc
      have hpK := (World.mem_lift (w := w) (le_sup_right : j ≤ i ⊔ j)).mp hp
      exact ⟨hT, ⟨i ⊔ j, X, (w.L.ctx_le le_sup_left).ref hrx,
        (mem_pres hO w (i ⊔ j) .ident hcK).mpr hpK⟩, hna⟩
  -- the contents at the self arrow, read at the names
  have hcont : ∀ (hs : SelfIn hO w x) (hs' : SelfIn hO w x'),
      rdenO hO w (i ⊔ hs.name.i₀) (Ctx.Le.refl _) (selfTerm hs (Ctx.Le.refl _) t).2 =
        rdenO hO w (i ⊔ hs'.name.i₀) (Ctx.Le.refl _) (selfTerm hs' (Ctx.Le.refl _) s).2 := by
    intro hs hs'
    have hT := hs.1
    have hk₁ : i ⊔ hs.name.i₀ ≤ (i ⊔ hs.name.i₀) ⊔ (i ⊔ hs'.name.i₀) := le_sup_left
    have hk₂ : i ⊔ hs'.name.i₀ ≤ (i ⊔ hs.name.i₀) ⊔ (i ⊔ hs'.name.i₀) := le_sup_right
    set K := (i ⊔ hs.name.i₀) ⊔ (i ⊔ hs'.name.i₀)
    have hiK : i ≤ K := le_sup_left.trans hk₁
    have hj₁ : hs.name.i₀ ≤ K := le_sup_right.trans hk₁
    have hj₂ : hs'.name.i₀ ≤ K := le_sup_right.trans hk₂
    refine (rdenO_mono' (w.L.ctx_le hk₁) _ w K _ (Ctx.Le.refl _) (Ctx.Le.refl _)).symm.trans
      (Eq.trans ?_ (rdenO_mono' (w.L.ctx_le hk₂) _ w K _ (Ctx.Le.refl _) (Ctx.Le.refl _)))
    rw [selfTerm_mono hs _ hk₁, selfTerm_mono hs' _ hk₂]
    have hfree := hs.2.2 K
    have hxK := hs.decl hj₁
    have hxK' := hs'.decl hj₂
    have hc := w.fresh_deeper (Nat.lt_succ_self w.depth) 0 K
    set P := Term.collapse (Ctx.collapses_diaIn_optInT hT hO _ hxK)
      (Term.mono (((Ctx.Le.refl _).trans (w.L.ctx_le hiK)).diaIn x) t) with hP
    set P' := Term.collapse (Ctx.collapses_diaIn_optInT hT hO _ hxK')
      (Term.mono (((Ctx.Le.refl _).trans (w.L.ctx_le hiK)).diaIn x') s) with hP'
    -- each content is `≡` to its reading, in its identity view
    have hn₁ := (World.mem_lift (w := w) hj₁).mp hs.name.nameSent_mem
    rw [nameSent_mono, Term.mono_eta] at hn₁
    have hn₂ := (World.mem_lift (w := w) hj₂).mp hs'.name.nameSent_mem
    rw [nameSent_mono, Term.mono_eta] at hn₂
    have hS₁ := World.mem_of_provable (w := w) (Δ := [_])
      (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hn₁)
      ⟨TCanon.selfEq hT hO hfree hxK hc (hs.declName hj₁) P⟩
    have hS₂ := World.mem_of_provable (w := w) (Δ := [_])
      (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hn₂)
      ⟨TCanon.selfEq hT hO hfree hxK' hc (hs'.declName hj₂) P'⟩
    -- the two contents are `≡` in the two views
    have hc₀ := hselfc hT
    rw [WFF.collapse_witEq hO _ _ A hX hX'] at hc₀
    have hcK := (World.mem_lift (w := w) hiK).mp hc₀
    have hpK : (⟨K, .optx hO .ident x ⟨_, Ctx.witT_of hT hO hxK⟩ .top⟩ :
        w.L.sys.Sentence σ) ∈ w.T :=
      World.mem_of_provable (w := w) (Δ := [_])
        (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hS₁)
        ⟨Proof.K_opt hO .ident x _ (Δ₁ := []) (Δ₂ := []) (φ := .top) .top_intro⟩
    have h₂ := mem_imp_or_l w K hcK hpK
    have hrxi : (w.L.ctx i).ref x = some (.VTypeDia X) := hrx
    have e₁ : Term.collapse ((Ctx.collapses_boxIn_self hT _).optIn_zero hO hX)
        (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx) t) =
        Term.mono (Ctx.Le.refl _) (Term.collapse (Ctx.collapses_diaIn_optInT hT hO _ hrxi) t) :=
      Term.collapse_mono _ _ _ _ t
    have e₂ : P = Term.mono ((w.L.ctx_le hiK).optInT x)
        (Term.collapse (Ctx.collapses_diaIn_optInT hT hO _ hrxi) t) :=
      Term.collapse_mono _ _ _ _ t
    have hrxi' : (w.L.ctx i).ref x' = some (.VTypeDia X') := hrx'
    have e₁' : Term.collapse ((Ctx.collapses_boxIn_self hT _).optIn_zero hO hX')
        (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx') s) =
        Term.mono (Ctx.Le.refl _) (Term.collapse (Ctx.collapses_diaIn_optInT hT hO _ hrxi') s) :=
      Term.collapse_mono _ _ _ _ s
    have e₂' : P' = Term.mono ((w.L.ctx_le hiK).optInT x')
        (Term.collapse (Ctx.collapses_diaIn_optInT hT hO _ hrxi') s) :=
      Term.collapse_mono _ _ _ _ s
    rw [e₁, e₁'] at h₂
    have hy'' : ∃ Z, ((w.L.ctx K).optInK .ident x).witK .ident x' = some Z :=
      ⟨_, (Ctx.le_optInT _ x).witT (Ctx.witT_of hT hO hxK')⟩
    have hH : (⟨K, .optx hO .ident x ⟨_, Ctx.witT_of hT hO hxK⟩ (.optx hO .ident x' hy''
        (eqH hO A (Term.mono (Ctx.le_optInT _ x') P)
          (Term.mono ((Ctx.le_optInT _ x).optInT x') P')))⟩ :
        w.L.sys.Sentence σ) ∈ w.T := by
      rw [e₂, e₂', Term.mono_mono, Term.mono_mono]
      refine (congrArg (fun φ => (⟨K, φ⟩ : w.L.sys.Sentence σ) ∈ w.T) ?_).mp h₂
      change WFF.optx hO .ident x _ (WFF.optx hO .ident x' _ (WFF.mono _ (eqH hO A _ _))) = _
      rw [eqH_mono, Term.mono_mono, Term.mono_mono, Term.mono_mono, Term.mono_mono]
    exact ih w K _ _ (World.mem_of_provable (w := w) (Δ := [_, _, _])
      (fun ψ hψ => by
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact hH
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact hS₁
        · rw [List.mem_singleton.mp hψ]
          exact hS₂)
      ⟨TCanon.selfCombine hO _ _ hy'' P P' _ _⟩)
  refine sigma_set_ext (α := SuccO hO w) (β := fun w' : SuccO hO w => RDomO hO A w'.1)
    (o := rdenO hO w i (Ctx.Le.refl _) (Term.diatm x hx t))
    (o' := rdenO hO w i (Ctx.Le.refl _) (Term.diatm x' hx' s)) ?_ ?_
  · change extentO (hO := hO) w x = extentO w x'
    ext w'
    by_cases hd : w'.1.depth - w.depth = 0
    · exact (mem_extentO_self_iff hO w' hd).trans
        (hself.trans (mem_extentO_self_iff hO w' hd).symm)
    · exact (mem_extentO_acc_iff hO w' hd).trans
        ((hchild w' hd).trans (mem_extentO_acc_iff hO w' hd).symm)
  · intro w' h h'
    by_cases hd : w'.1.depth - w.depth = 0
    · obtain ⟨w₁, h₁⟩ := w'
      have he := (extentO_self h hd).1
      change w₁ = w at he
      subst he
      rw [rdenO_diatm_self _ hx t ⟨_, h⟩ hd, rdenO_diatm_self _ hx' s ⟨_, h'⟩ hd]
      exact hcont _ _
    · rw [rdenO_diatm_acc _ hx t ⟨w', h⟩ hd, rdenO_diatm_acc _ hx' s ⟨w', h'⟩ hd]
      have ha := SuccO.acc w' hd
      have ho := (extentO_child h hd).2
      have ho' := (extentO_child h' hd).2
      set M := max i.1 i.2
      have hM : (w.L.ctx i).boxIn.Le (bview w M) := (le_diag_max w i).boxIn
      have hb := ha.boxIn_le i
      have hdx : w'.1.L.ctx (childStage i) (.step x .dia) = some X :=
        ha.opened_at ho (hM.wit x X hX)
      have hdx' : w'.1.L.ctx (childStage i) (.step x' .dia) = some X' :=
        ha.opened_at ho' (hM.wit x' X' hX')
      have hc := ha.box i _ (childStage i) hb hm
      have hp := (ha.opened_iff hO hX).mp ho
      have h₂ := mem_imp_or_l w'.1 (childStage i) hc hp
      have hle : (((w'.1.L.ctx (childStage i)).optIn x).optIn x').Le
          (w'.1.L.ctx (childStage i)) :=
        Ctx.optIns_le_of (Ctx.Le.refl _) (L := [x', x]) fun y hy Y hY => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · obtain rfl : Y = X' := Option.some.inj (hY.symm.trans (hb.wit _ X' hX'))
            exact hdx'
          · obtain rfl : Y = X := Option.some.inj (hY.symm.trans (hb.wit _ X hX))
            exact hdx
      have h₃ := mem_out₂ hO w'.1 (childStage i) (hb.wit x X hX) (hb.wit x' X' hX') _ hle _ h₂
      simp only [eqH_mono, Term.mono_mono] at h₃
      have := ih w'.1 (childStage i) _ _ h₃
      rw [rdenO_mono, rdenO_mono] at this
      exact this

/-- ⭐**`≡` in the theory is identity of denotations**, at every world and type. -/
theorem faithO : ∀ (A : VarType) {a b : Ann A} (w : World σ N₀) (i : ℕ × ℕ)
    (t : Term σ (w.L.ctx i) A a) (s : Term σ (w.L.ctx i) A b),
    (⟨i, eqH hO A t s⟩ : w.L.sys.Sentence σ) ∈ w.T →
      rdenO hO w i (Ctx.Le.refl _) t = rdenO hO w i (Ctx.Le.refl _) s
  | .Var, .var, .var, w, i, t, s, hm => by
      rw [eqH_Var] at hm
      rw [rdenO_var_cls, rdenO_var_cls]
      refine (World.cls_eq_iff le_rfl le_rfl).mpr ?_
      simpa only [World.liftT, Term.mono_refl] using hm
  | .VTypeOne, .one, .one, _, _, .unit, .unit, _ => rfl
  | .VTypeProd A B, .prod _ _, .prod _ _, w, i, .pair t₁ t₂, .pair s₁ s₂, hm => by
      have h := w.mcs.and_mem_iff.mp hm
      exact Prod.ext (faithO A w i t₁ s₁ h.1) (faithO B w i t₂ s₂ h.2)
  | .VTypeBox A, .box _, .box _, w, i, .boxtm t, .boxtm s, hm => by
      funext w'
      by_cases hd : w'.1.depth - w.depth = 0
      · rw [rdenO_boxtm_self _ t w' hd, rdenO_boxtm_self _ s w' hd]
        obtain ⟨w₁, h₁⟩ := w'
        obtain ⟨hT, hw⟩ := SuccO.self (hO := hO) ⟨w₁, h₁⟩ hd
        change w₁ = w at hw
        subst hw
        have hc := World.mem_of_provable (w := w₁) (Δ := [_])
          (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hm)
          ⟨Proof.T_box hT (Proof.lookup List.mem_cons_self)⟩
        rw [WFF.collapse_eqH] at hc
        exact faithO A w₁ i _ _ hc
      · rw [rdenO_boxtm_acc _ t w' hd, rdenO_boxtm_acc _ s w' hd]
        have ha := SuccO.acc (hO := hO) w' hd
        have hc := ha.box i (eqH hO A t s) (childStage i) (ha.boxIn_le i) hm
        rw [eqH_mono] at hc
        have := faithO A w'.1 (childStage i) _ _ hc
        rwa [rdenO_mono, rdenO_mono] at this
  | .VTypeDia A, .dia x _, .dia x' _, w, i, .diatm _ hx t, .diatm _ hx' s, hm =>
      faithO_dia hO (fun w i t s h => faithO A w i t s h) w i hx hx' t s hm

end OCanon

end V12M
