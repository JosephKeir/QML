import QML.QML_v12m_TCanonFaith

/-!
# QML v12m — the KT tree with `Opt` on: strong T's witnesses

Strong T's canonical law (`posRet_exists`, docs §12.36): every object of a world is the content,
at the self arrow, of some possible object.  For the object of a term `t`:

* ⭐`exists_realHyp`: `T_dia` derives `∃c:◇A. ◇⁰ᵀ_c (c.at ≡ t)`, and the world's `∃`-witness
  property gives a Henkin root `c` for it (`WFF.subst_realHyp_single`: the instance at a root is
  strong T's hypothesis about that root);
* ⭐`posRet_rden`: `c` is realised at the world itself, its content there is its identity name `d`,
  the theory has `d ≡ t` (`Proof.optT_eq`), and `≡` in the theory is identity (`faithO`).
-/

namespace V12M

set_option linter.unusedSectionVars false

variable [ModalSys]

variable {σ : Signature}

/-- ⭐**Strong T's hypothesis, instantiated at a declared root**: the fresh root sent to the
    η-expansion of `c` makes `◇⁰ᵀ_{c₀} (c₀.at ≡ t)` into `◇⁰ᵀ_c (c.at ≡ t)`. -/
theorem WFF.subst_realHyp_single (hT : ModalSys.T = true) (hO : ModalSys.Opt = true)
    {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ') {c₀ c : ℕ}
    (hc₀ : Γ.RootFresh (.free c₀)) {A : VarType}
    (hc : Γ'.ref (.root (.free c)) = some (.VTypeDia A)) {a : Ann A} (t : Term σ Γ A a) :
    WFF.subst (Subst.singleIdx (.free c₀) (.tm (Term.eta (.root (.free c)) (.VTypeDia A) hc)))
        (Subst.single (.free c₀) (.tm (Term.eta (.root (.free c)) (.VTypeDia A) hc)))
        (Subst.ok_single h rfl) (Subst.coh_single hc₀ h rfl)
        ((Ctx.NoSlots.slots (Γ := Γ)).insertFree c₀ (.VTypeDia A)) Ctx.NoSlots.slots
        (WFF.realHyp hT (.root (.free c₀)) (Ctx.ref_insert_root Γ (.free c₀) (.VTypeDia A))
          (Term.weaken hc₀.root (.VTypeDia A) t)) =
      WFF.realHyp hT (.root (.free c)) hc (Term.mono h t) := by
  rw [WFF.realHyp_opt hT hO, WFF.realHyp_opt hT hO]
  set e : SubE σ Γ' := .tm (Term.eta (.root (.free c)) (.VTypeDia A) hc)
  have hθ : Subst.Ok (Γ.insert (.free c₀) (.VTypeDia A)) (Subst.single (.free c₀) e) :=
    Subst.ok_single h rfl
  have hcθ : Subst.Coh (Subst.singleIdx (.free c₀) e) (Γ.insert (.free c₀) (.VTypeDia A))
      (Subst.single (.free c₀) e) := Subst.coh_single hc₀ h rfl
  have hwΓ := Ctx.witT_of hT hO (Ctx.ref_insert_root Γ (.free c₀) (.VTypeDia A))
  have hwΔ := Ctx.witT_of hT hO hc
  have hat : (Subst.single (.free c₀) e).at (.root (.free c₀)) = e := Subst.at_single_root _ _
  have hidx : ((Subst.single (.free c₀) e).at (.root (.free c₀))).idxAlong [] =
      .root (.free c) := by
    rw [hat]
    rfl
  have hz : Subst.singleIdx (.free c₀) e (.root (.free c₀)) = .root (.free c) :=
    (hcθ _ _ (Ctx.ref_insert_root Γ (.free c₀) (.VTypeDia A)) []).symm.trans hidx
  have hcz : Subst.Coh (Subst.singleIdx (.free c₀) e)
      ((Γ.insert (.free c₀) (.VTypeDia A)).optInT (.root (.free c₀)))
      ((Subst.single (.free c₀) e).optInT (.root (.free c₀)) (.root (.free c))) := by
    have := Subst.coh_optInT hθ hcθ hwΓ
    rwa [hz] at this
  refine (WFF.subst_optxT_eq (Subst.single (.free c₀) e) hθ hcθ
    ((Ctx.NoSlots.slots (Γ := Γ)).insertFree c₀ (.VTypeDia A)) Ctx.NoSlots.slots hO
    (.root (.free c₀)) ⟨A, hwΓ⟩ _ hz ⟨A, hwΔ⟩ (Subst.ok_optInT hθ hwΓ hidx) hcz).trans ?_
  rw [WFF.subst_eqH]
  have tmOf : ∀ {Ω : Ctx} {b b' : Ann A} {s : Term σ Ω A b} {s' : Term σ Ω A b'},
      (⟨b, s⟩ : Σ c, Term σ Ω A c) = ⟨b', s'⟩ → SubE.tm s = SubE.tm s' := by
    intro Ω b b' s s' e
    cases e
    rfl
  have hcol : (VarSymb.step (.root (.free c)) .dia).collapse 0 =
      .step (.root (.free c)) .at := by
    simp [VarSymb.collapse, Step.diaZero, Step.isProj, hO]
  have hat₁ : ((Subst.single (.free c₀) e).optInT (.root (.free c₀))
      (.root (.free c))).at (.step (.root (.free c₀)) .at) =
      .tm (Term.eta (.step (.root (.free c)) .at) A (Ctx.ref_optInT_content hwΔ)) := by
    rw [Subst.at_nonproj _ rfl, Subst.optInT_content, hat]
    change (if h : ModalSys.T = true ∧ ModalSys.Opt = true ∧
        VarSymb.root (.free c) = .root (.free c) then _ else _) = _
    rw [dif_pos ⟨hT, hO, rfl⟩]
    exact tmOf ((Term.collapse_eta _ _ A _).trans (Term.eta_congr hcol A _ _))
  refine congrArg (WFF.optx hO .ident _ _) (eqH_congr hO
    (Term.subst_eta_tm _ _ _ A _ _ _ hat₁) ?_)
  rw [Term.subst_mono, Term.weaken, Term.subst_mono]
  refine (Term.subst_ren (h.trans (Ctx.le_optInT _ (.root (.free c)))) _ _ _
    (fun v T hv => ?_) t).trans ?_
  · rw [Subst.at_optInT_of hcθ hwΓ hidx v T ((Ctx.le_insert hc₀.root _).ref hv),
      Subst.single_at_ne (Ctx.ref_rt_ne hc₀ hv)]
    rfl
  · rw [Term.mono_mono]


/-- Two contents of one identity view, `≡` to one term there, are `≡`. -/
def Proof.optT_eq (hO : ModalSys.Opt = true) {Γ : Ctx} [Γ.Presented] {x : VarSymb}
    (hy : ∃ X, Γ.witK .ident x = some X) {B : VarType} {a b b' : Ann B}
    (e : Term σ (Γ.optInT x) B a) (u : Term σ Γ B b) (u' : Term σ Γ B b') :
    Proof σ Γ [.optx hO .ident x hy (eqH hO B e (Term.mono (Ctx.le_optInT Γ x) u)),
        .optx hO .ident x hy (eqH hO B e (Term.mono (Ctx.le_optInT Γ x) u'))]
      (eqH hO B u u') := by
  have inner : Proof σ (Γ.optInT x)
      [WFF.and (eqH hO B e (Term.mono (Ctx.le_optInT Γ x) u))
        (eqH hO B e (Term.mono (Ctx.le_optInT Γ x) u'))]
      (WFF.mono (Ctx.le_optInK Γ .ident x) (eqH hO B u u')) :=
    Proof.conv (eqH_mono hO _ B u u').symm (Proof.eqH_trans hO B
      (Proof.eqH_symm hO B (Proof.and_elim_l (Proof.lookup List.mem_cons_self)))
      (Proof.and_elim_r (Proof.lookup List.mem_cons_self)))
  have k := Proof.K_opt hO .ident x hy (Δ₁ := []) (Δ₂ := []) inner
  exact Proof.opt_out hO .ident x hy (.imp_elim
    (Proof.ofSubset (fun _ h => by simp at h) (.imp_intro k))
    (Proof.opt_fun hO .ident x hy _ _))

namespace OCanon

open Canon

variable {N₀ : ℕ} (hO : ModalSys.Opt = true)

include hO in
/-- ⭐**Strong T's witness in a world**: for every term, a Henkin root realised here by it, by the
    theory's own word (`T_dia`, then the `∃`-witness). -/
theorem exists_realHyp (hT : ModalSys.T = true) (hTS : ModalSys.TStrongW = true)
    (w : World σ N₀) (i : ℕ × ℕ) {A : VarType} {a : Ann A} (t : Term σ (w.L.ctx i) A a) :
    ∃ (i' : ℕ × ℕ) (hi : i ≤ i') (c : ℕ)
      (hc : (w.L.ctx i').ref (.root (.free c)) = some (.VTypeDia A)),
      (⟨i', WFF.realHyp hT (.root (.free c)) hc (Term.mono (w.L.ctx_le hi) t)⟩ :
        w.L.sys.Sentence σ) ∈ w.T := by
  have hc₀ := w.fresh_deeper (Nat.lt_succ_self w.depth) 0 i
  set c₀ := names N₀ (w.depth + 1) 0
  set R := WFF.realHyp hT (.root (.free c₀))
    (Ctx.ref_insert_root (w.L.ctx i) (.free c₀) (.VTypeDia A))
    (Term.weaken hc₀.root (.VTypeDia A) t)
  have hE : (⟨i, .ex (.VTypeDia A) (WFF.bindFree c₀ hc₀ Ctx.NoSlots.slots (.VTypeDia A) R)⟩ :
      w.L.sys.Sentence σ) ∈ w.T :=
    World.mem_of_provable (Δ := []) (fun _ h => by simp at h)
      ⟨Proof.T_dia hT hTS A t c₀ hc₀ (Δ := [])
        (.ex_intro _ (Term.eta (.root (.free c₀)) (.VTypeDia A)
            (Ctx.ref_insert_root _ _ _))
          (Proof.conv ((WFF.instantiate_eta_openFree c₀ hc₀ Ctx.NoSlots.slots Ctx.NoSlots.slots
              _).trans (WFF.openFree_bindFree c₀ hc₀ Ctx.NoSlots.slots R)).symm
            (Proof.lookup List.mem_cons_self)))⟩
  obtain ⟨i', hi, c, hc, hmem⟩ := w.exW hE
  rw [WFF.instantiate_bindFree (w.L.ctx_le hi) c₀ hc₀ _ R,
    WFF.subst_realHyp_single hT hO (w.L.ctx_le hi) hc₀ hc t] at hmem
  exact ⟨i', hi, c, hc, hmem⟩

theorem sig_readNames' {ν : VarSymb → Option VarSymb} {k : ℕ} {Γ₁ Γ₂ : Ctx}
    (h : Ctx.ReadsNames ν k Γ₁ Γ₂) {T : VarType} {p q : Σ b : Ann T, Term σ Γ₁ T b}
    (e : p = q) :
    (⟨_, Term.readNames h p.2⟩ : Σ b, Term σ Γ₂ T b) = ⟨_, Term.readNames h q.2⟩ := by
  subst e
  rfl

/-- A root's content at the world itself is its identity name. -/
theorem selfTerm_eta {w : World σ N₀} {c : ℕ} (hs : SelfIn hO w (.root (.free c)))
    {i : ℕ × ℕ} {A : VarType} (hc : (w.L.ctx i).ref (.root (.free c)) = some (.VTypeDia A))
    (hA : A = hs.name.A) :
    (⟨_, (selfTerm hs (Ctx.Le.refl _) (Term.eta (.step (.root (.free c)) .dia) A
        (Ctx.ref_diaIn_of hc))).2⟩ : Σ b, Term σ (w.L.ctx (i ⊔ hs.name.i₀)) A b) =
      ⟨_, Term.eta (.root (.free hs.name.c)) A (hA ▸ hs.declName le_sup_right)⟩ := by
  subst hA
  have hcol : (VarSymb.step (.root (.free c)) .dia).collapse 0 =
      .step (.root (.free c)) .at := by
    simp [VarSymb.collapse, Step.diaZero, Step.isProj, hO]
  change (⟨_, Term.readNames _ (Term.collapse _ (Term.mono _ (Term.eta _ _ _)))⟩ :
    Σ b, Term σ (w.L.ctx (i ⊔ hs.name.i₀)) _ b) = _
  rw [Term.mono_eta]
  have hxT := Ctx.witT_of hs.1 hO (hs.decl (le_sup_right : hs.name.i₀ ≤ i ⊔ hs.name.i₀))
  have e₁ := (Term.collapse_eta (σ := σ)
    (Ctx.collapses_diaIn_optInT hs.1 hO _ (hs.decl (le_sup_right : hs.name.i₀ ≤ i ⊔ hs.name.i₀)))
    _ _ ((Ctx.Le.refl _).ref (Ctx.ref_diaIn_of ((w.L.ctx_le le_sup_left).ref hc)))).trans
    (Term.eta_congr hcol hs.name.A _ (Ctx.ref_optInT_content hxT))
  refine (sig_readNames' _ e₁).trans ((Term.readNames_eta _ _ _ _).trans
    (Term.eta_congr ?_ _ _ _))
  exact VarSymb.readNames_at_named (TCanon.nameAt_self _ _)

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- ⭐**Strong T's law in raw form**: every object of a world is the content, at the self arrow,
    of a definable possible object. -/
theorem posRet_rden (hT : ModalSys.T = true) (hTS : ModalSys.TStrongW = true) (w : World σ N₀)
    {A : VarType} (o : RDomO hO A w) (ho : DefinableO hO A w o) :
    ∃ (p : RDomO hO (.VTypeDia A) w) (_ : DefinableO hO (.VTypeDia A) w p)
      (hm : SuccO.selfArr hT w ∈ p.1), p.2 ⟨_, hm⟩ = o := by
  obtain ⟨i, a, t, rfl⟩ := ho
  obtain ⟨i', hi, c, hc, hmem⟩ := exists_realHyp hO hT hTS w i t
  rw [WFF.realHyp_opt hT hO] at hmem
  have hpres : (⟨i', TCanon.idPresent hT hO hc⟩ : w.L.sys.Sentence σ) ∈ w.T :=
    World.mem_of_provable (Δ := [_]) (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hmem)
      ⟨Proof.K_opt hO .ident _ _ (Δ₁ := []) (Δ₂ := []) (φ := .top) .top_intro⟩
  have hs : SelfIn hO w (.root (.free c)) :=
    ⟨hT, ⟨i', A, hc, hpres⟩, World.stagesNoAt hT hO w⟩
  have hm : SuccO.selfArr hT w ∈ extentO (hO := hO) w (.root (.free c)) := Or.inr ⟨rfl, hs⟩
  -- the content at the self arrow, read at the name, is the term's object
  have key : ∀ hs' : SelfIn hO w (.root (.free c)),
      rdenO hO w (i' ⊔ hs'.name.i₀) (Ctx.Le.refl _)
          (selfTerm hs' (Ctx.Le.refl _) (Term.eta (.step (.root (.free c)) .dia) A
            (Ctx.ref_diaIn_of hc))).2 =
        rdenO hO w i (Ctx.Le.refl _) t := by
    intro hs'
    set K := i' ⊔ hs'.name.i₀
    have hK : i' ≤ K := le_sup_left
    have hA : A = hs'.name.A := by
      have h₁ := hs'.decl (le_sup_right : hs'.name.i₀ ≤ K)
      rw [(w.L.ctx_le hK).ref hc] at h₁
      cases h₁
      rfl
    rw [rdenO_sig (selfTerm_eta hO hs' hc hA)]
    have hn := (World.mem_lift (w := w) (le_sup_right : hs'.name.i₀ ≤ K)).mp
      hs'.name.nameSent_mem
    rw [nameSent_mono, Term.mono_eta] at hn
    have hr := (World.mem_lift (w := w) hK).mp hmem
    have hr' : (⟨K, TCanon.nameSent hT hO ((w.L.ctx_le hK).ref hc)
        (Term.mono (w.L.ctx_le (hi.trans hK)) t)⟩ : w.L.sys.Sentence σ) ∈ w.T := by
      have e := nameSent_mono hO (w.L.ctx_le hK) hT hc (Term.mono (w.L.ctx_le hi) t)
      rw [Term.mono_mono] at e
      rw [← e]
      exact hr
    have heq : ∀ {Y : VarType} (hxY : (w.L.ctx K).ref (.root (.free c)) = some (.VTypeDia Y))
        (hdY : (w.L.ctx K).ref (.root (.free hs'.name.c)) = some Y),
        (⟨K, TCanon.nameSent hT hO hxY (Term.eta (.root (.free hs'.name.c)) Y hdY)⟩ :
          w.L.sys.Sentence σ) ∈ w.T →
        (hYA : Y = A) →
        (⟨K, eqH hO A (Term.eta (.root (.free hs'.name.c)) A (hYA ▸ hdY))
          (Term.mono (w.L.ctx_le (hi.trans hK)) t)⟩ : w.L.sys.Sentence σ) ∈ w.T := by
      intro Y hxY hdY hnY hYA
      subst hYA
      exact World.mem_of_provable (Δ := [_, _])
        (fun ψ hψ => by
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact hnY
          · rw [List.mem_singleton.mp hψ]
            exact hr')
        ⟨Proof.optT_eq hO _ _ _ _⟩
    have h₂ := heq _ _ hn hA.symm
    have := faithO hO A w K _ _ h₂
    rw [rdenO_mono' (w.L.ctx_le (hi.trans hK)) t w K i] at this
    exact this
  exact ⟨_, definableO_rden (Ctx.Le.refl _) (Term.eta (.root (.free c)) (.VTypeDia A) hc), hm,
    (rdenO_diatm_self _ _ _ ⟨_, hm⟩ (Nat.sub_self _)).trans (key _)⟩

end OCanon


/-! ## NecT: necessary objects with a given value here -/

/-- ⭐**NecT's hypothesis, instantiated at a declared root**: `c₀.here ≡ t` becomes `c.here ≡ t`. -/
theorem WFF.subst_necHyp_single (hT : ModalSys.T = true) (hO : ModalSys.Opt = true)
    {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ') {c₀ c : ℕ}
    (hc₀ : Γ.RootFresh (.free c₀)) {A : VarType}
    (hc : Γ'.ref (.root (.free c)) = some (.VTypeBox A)) {a : Ann A} (t : Term σ Γ A a) :
    WFF.subst (Subst.singleIdx (.free c₀) (.tm (Term.eta (.root (.free c)) (.VTypeBox A) hc)))
        (Subst.single (.free c₀) (.tm (Term.eta (.root (.free c)) (.VTypeBox A) hc)))
        (Subst.ok_single h rfl) (Subst.coh_single hc₀ h rfl)
        ((Ctx.NoSlots.slots (Γ := Γ)).insertFree c₀ (.VTypeBox A)) Ctx.NoSlots.slots
        (WFF.necHyp hT hO (.root (.free c₀)) (Ctx.ref_insert_root Γ (.free c₀) (.VTypeBox A))
          (Term.weaken hc₀.root (.VTypeBox A) t)) =
      WFF.necHyp hT hO (.root (.free c)) hc (Term.mono h t) := by
  set e : SubE σ Γ' := .tm (Term.eta (.root (.free c)) (.VTypeBox A) hc)
  have hθ : Subst.Ok (Γ.insert (.free c₀) (.VTypeBox A)) (Subst.single (.free c₀) e) :=
    Subst.ok_single h rfl
  have hcθ : Subst.Coh (Subst.singleIdx (.free c₀) e) (Γ.insert (.free c₀) (.VTypeBox A))
      (Subst.single (.free c₀) e) := Subst.coh_single hc₀ h rfl
  have hat : (Subst.single (.free c₀) e).at (.root (.free c₀)) = e := Subst.at_single_root _ _
  have hcol : (VarSymb.root (.free c)).inner.collapse 0 = .step (.root (.free c)) .here := by
    rw [VarSymb.inner_box (Subst.keepOnly_false hO)]
    simp [VarSymb.collapse, Step.isProj]
  have hat₁ : (Subst.single (.free c₀) e).at (.step (.root (.free c₀)) .here) =
      .tm (Term.collapse (Ctx.collapses_boxIn_self hT Γ')
        (Term.eta (VarSymb.root (.free c)).inner A (Ctx.ref_inner hc))) := by
    change (if Step.here.isStruct then
      ((Subst.single (.free c₀) e).at (.root (.free c₀))).proj .here else _) = _
    rw [if_pos (show Step.here.isStruct = true from rfl), hat]
    change (if hT : ModalSys.T = true then _ else _) = _
    rw [dif_pos hT]
  rw [WFF.necHyp, WFF.necHyp, WFF.subst_eqH]
  refine eqH_congr hO ((Term.subst_eta_tm _ _ _ A _ _ _ hat₁).trans
    ((Term.collapse_eta _ _ A _).trans (Term.eta_congr hcol A _ _))) ?_
  rw [Term.weaken, Term.subst_mono]
  exact (Term.subst_ren h _ _ _ (fun v T hv => Subst.single_at_ne (Ctx.ref_rt_ne hc₀ hv)) t)

namespace OCanon

open Canon

variable {N₀ : ℕ} (hO : ModalSys.Opt = true)

include hO in
/-- ⭐**NecT's witness in a world**: for every term, a Henkin root `c : □A` with `c.here ≡ t`. -/
theorem exists_necHyp (hT : ModalSys.T = true) (hTS : ModalSys.TStrong = true)
    (w : World σ N₀) (i : ℕ × ℕ) {A : VarType} {a : Ann A} (t : Term σ (w.L.ctx i) A a) :
    ∃ (i' : ℕ × ℕ) (hi : i ≤ i') (c : ℕ)
      (hc : (w.L.ctx i').ref (.root (.free c)) = some (.VTypeBox A)),
      (⟨i', WFF.necHyp hT hO (.root (.free c)) hc (Term.mono (w.L.ctx_le hi) t)⟩ :
        w.L.sys.Sentence σ) ∈ w.T := by
  have hc₀ := w.fresh_deeper (Nat.lt_succ_self w.depth) 0 i
  set c₀ := names N₀ (w.depth + 1) 0
  set R := WFF.necHyp hT hO (.root (.free c₀))
    (Ctx.ref_insert_root (w.L.ctx i) (.free c₀) (.VTypeBox A))
    (Term.weaken hc₀.root (.VTypeBox A) t)
  have hE : (⟨i, .ex (.VTypeBox A) (WFF.bindFree c₀ hc₀ Ctx.NoSlots.slots (.VTypeBox A) R)⟩ :
      w.L.sys.Sentence σ) ∈ w.T :=
    World.mem_of_provable (Δ := []) (fun _ h => by simp at h)
      ⟨Proof.T_nec hT hTS hO A t c₀ hc₀ (Δ := [])
        (.ex_intro _ (Term.eta (.root (.free c₀)) (.VTypeBox A)
            (Ctx.ref_insert_root _ _ _))
          (Proof.conv ((WFF.instantiate_eta_openFree c₀ hc₀ Ctx.NoSlots.slots Ctx.NoSlots.slots
              _).trans (WFF.openFree_bindFree c₀ hc₀ Ctx.NoSlots.slots R)).symm
            (Proof.lookup List.mem_cons_self)))⟩
  obtain ⟨i', hi, c, hc, hmem⟩ := w.exW hE
  rw [WFF.instantiate_bindFree (w.L.ctx_le hi) c₀ hc₀ _ R,
    WFF.subst_necHyp_single hT hO (w.L.ctx_le hi) hc₀ hc t] at hmem
  exact ⟨i', hi, c, hc, hmem⟩

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- ⭐**NecT's law in raw form**: every object of a world is the value at the self arrow of a
    definable necessary object. -/
theorem necRet_rden (hT : ModalSys.T = true) (hTS : ModalSys.TStrong = true) (w : World σ N₀)
    {A : VarType} (o : RDomO hO A w) (ho : DefinableO hO A w o) :
    ∃ (n : RDomO hO (.VTypeBox A) w) (_ : DefinableO hO (.VTypeBox A) w n),
      n (SuccO.selfArr hT w) = o := by
  obtain ⟨i, a, t, rfl⟩ := ho
  obtain ⟨i', hi, c, hc, hmem⟩ := exists_necHyp hO hT hTS w i t
  have hcol : (VarSymb.root (.free c)).inner.collapse 0 = .step (.root (.free c)) .here := by
    rw [VarSymb.inner_box (Subst.keepOnly_false hO)]
    simp [VarSymb.collapse, Step.isProj]
  refine ⟨_, definableO_rden (Ctx.Le.refl _) (Term.eta (.root (.free c)) (.VTypeBox A) hc), ?_⟩
  refine (rdenO_boxtm_self (Ctx.Le.refl _) _ (SuccO.selfArr hT w) (Nat.sub_self _)).trans ?_
  rw [rdenO_sig ((Term.collapse_eta _ _ A _).trans (Term.eta_congr hcol A _
    (Ctx.ref_here_of hT hc)))]
  have := faithO hO A w i' _ _ hmem
  rw [rdenO_mono' (w.L.ctx_le hi) t w i' i] at this
  exact this

end OCanon

end V12M
