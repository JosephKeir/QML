import QML.QML_v12m_CanonLeaf
import QML.QML_v12m_CanonTerm

/-!
# QML v12m — the canonical model: what `Here` says

The facts about `Here` atoms the truth lemma's `here` case needs, at the level of the theory.

* `Term.viewReadTm_eta_diaAbsA`: the term round trip — abstracting a view term and reading it back
  with the content address in the hole gives the term.
* ⭐`mem_here_realised`: a realised witness's possible object `⟨x; b⟩` has as its content here the
  realisation of `b` — the term the canonical model reads its content off (`interp_dia_self`).
* `realised_of_here` (in `CanonModel`, where strong T's frame condition uses it): a `Here` atom
  about `⟨x; b⟩` makes `x` realised.
-/

namespace V12M

variable [ModalSys]

/-- ⭐**The round trip, for terms**: a term of the `◇_x` view is its abstraction read back with the
    content address's η-expansion in the hole. -/
theorem Term.viewReadTm_eta_diaAbsA {σ : Signature} {Γ : Ctx} [hp : Γ.Presented] (x : VarSymb)
    {A : VarType} (hxA : Γ.ref x = some (.VTypeDia A)) {T : VarType} {b : Ann T}
    (t : Term σ (Γ.diaIn x) T b) :
    (⟨_, Term.viewReadTm (Term.eta (.step x .dia) A (Ctx.ref_diaIn_of hxA))
        (Term.diaAbsA x hxA t)⟩ : Σ c, Term σ (Γ.diaIn x) T c) = ⟨b, t⟩ := by
  unfold Term.viewReadTm
  rw [Term.subst_mono]
  unfold Term.diaAbsA
  refine (Term.subst_comp_sig _ _ (Subst.idS σ (Γ.diaIn x)) _ _ _ _ Subst.ok_idS Subst.coh_idS
    ?_ t).trans ?_
  · refine Subst.sim_of ?_
    intro v T' hlp hv
    rcases Subst.diaIn_casesA (σ := σ) hxA (hp.not_below hxA rfl) hv with
      ⟨rfl, rfl⟩ | ⟨_, _, hen, hroot⟩
    · change SubE.Sim _ (.ren (.step x .dia))
        ((if x = x then SubE.ren (.root (.bnd 0)) else .hide).comp _ _ _)
      rw [if_pos rfl]
      change SubE.Sim _ (.ren (.step x .dia))
        (if (VarSymb.root (Root.bnd 0)) = .root (.bnd 0) then
          SubE.tm (Term.eta (.step x .dia) T' (Ctx.ref_diaIn_of hxA))
        else .ren (.root (.bnd 0)))
      rw [if_pos rfl]
      exact .ren_eta _ _
    · change SubE.Sim _ (.ren v) ((Subst.diaAbsA σ _ x v).comp _ _ _)
      rw [hen _]
      change SubE.Sim _ (.ren v)
        ((Subst.single (σ := σ) (Δ := Γ.diaIn x) (.bnd 0)
          (.tm (Term.eta (.step x .dia) A (Ctx.ref_diaIn_of hxA)))).at v)
      rw [Subst.at_nonproj _ hlp]
      change SubE.Sim _ (.ren v) (if v = .root (.bnd 0) then _ else .ren v)
      rw [if_neg (hroot (.bnd 0))]
      exact .refl _
  · exact (Term.subst_idS_mono (Ctx.Le.refl _) _ _ t).trans
      (congrArg (Sigma.mk _) (Term.mono_refl _ t))

namespace Canon

variable {σ : Signature} {N₀ : ℕ}

/-- ⭐**A realised witness's possible object has its realisation as content here**: from the
    datum's atom `Here (η x) t₀`, `here_beta` with the body abstracted, and the round trip. -/
theorem mem_here_realised {w : World σ N₀} {x : VarSymb} (hr : w.Realised x) {i : ℕ × ℕ}
    {X : VarType} (hx : (w.L.ctx i).ref x = some (.VTypeDia X)) {B : VarType} {β : Ann B}
    (bd : Term σ ((w.L.ctx i).diaIn x) B β) :
    (⟨i ⊔ hr.data.i₀, WFF.here hr.T
        (Term.mono (w.L.ctx_le le_sup_left) (Term.diatm x ⟨X, hx⟩ bd))
        (realisedTerm w hr (Ctx.Le.refl _) ⟨X, hx⟩ bd).2⟩ : w.L.sys.Sentence σ) ∈ w.T := by
  have hdecl : (w.L.ctx (i ⊔ hr.data.i₀)).ref x = some (.VTypeDia hr.data.A) :=
    realisedDecl hr (Ctx.Le.refl _) ⟨X, hx⟩
  have hat := hr.data.hhereAt w.mcs (i ⊔ hr.data.i₀) le_sup_right hdecl
  have hmem := World.mem_of_provable (w := w) (Δ := [_]) (fun ψ hψ => by
      rw [List.mem_singleton.mp hψ]; exact hat)
    ⟨Proof.here_beta hr.T x ⟨_, hdecl⟩ (Term.mono (w.L.ctx_le le_sup_right) hr.data.t₀)
      (Term.eta (.step x .dia) hr.data.A (Ctx.ref_diaIn_of hdecl))
      (Term.diaAbsA x hdecl (Term.mono (realisedLe w hr (Ctx.Le.refl _)) bd))
      (Proof.lookup List.mem_cons_self)⟩
  rwa [WFF.here_congr hr.T (sig_diatm (Term.viewReadTm_eta_diaAbsA x hdecl _)) rfl] at hmem

/-! ## The `here` case of the truth lemma -/

section HereCase

variable (w₀ : World σ N₀) [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoB]

/-- The truth lemma at the equations of one type: what the `here` case receives from the
    induction, `eqRec` being smaller than `Here` (`WFF.size_eqRec`). -/
abbrev EqTruth (w : World σ N₀) (A : VarType) : Prop :=
  ∀ (K : ℕ × ℕ) {b : Ann A} (u u' : Term σ (w.L.ctx K) A b),
    (model w₀).sat (canonEnv w₀ w K) (eqRec A u u' : WFF σ (w.L.ctx K) 0) ↔
      (⟨K, eqRec A u u'⟩ : w.L.sys.Sentence σ) ∈ w.T

/-- ⭐**Equal denotations carry `Here` facts** — (F) of docs §10.38.  Tags determine annotations
    (`ann_eq_of_rden`), so the two contents can be equated (`eqRec`, by the truth lemma at a smaller
    formula), and `Proof.here_eq` moves the atom. -/
theorem here_transfer (hT : ModalSys.T = true) {w : World σ N₀} {A : VarType}
    (IH : EqTruth w₀ w A) {K : ℕ × ℕ} {c : Ann (.VTypeDia A)}
    (S : Term σ (w.L.ctx K) (.VTypeDia A) c) {b b' : Ann A}
    (r : Term σ (w.L.ctx K) A b) (r' : Term σ (w.L.ctx K) A b')
    (he : rden w K (Ctx.Le.refl _) r = rden w K (Ctx.Le.refl _) r')
    (hmem : (⟨K, WFF.here hT S r⟩ : w.L.sys.Sentence σ) ∈ w.T) :
    (⟨K, WFF.here hT S r'⟩ : w.L.sys.Sentence σ) ∈ w.T := by
  obtain rfl := ann_eq_of_rden hT (Ctx.Presented.declOK hT _) (Ctx.Le.refl _) r r' he
  have heq : (⟨K, eqRec A r r'⟩ : w.L.sys.Sentence σ) ∈ w.T := by
    refine (IH K r r').mp ((Model.sat_eqRec _ A r r').mpr ?_)
    rw [interp_canon w₀ r (fun _ _ _ => rfl), interp_canon w₀ r' (fun _ _ _ => rfl)]
    exact toDom_congr w₀ he _ _
  refine World.mem_of_provable (Δ := [WFF.here hT S r, eqRec A r r']) (fun ψ hψ => ?_)
    ⟨Proof.here_eq hT S r r' (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact hmem
  · rw [List.mem_singleton.mp hψ]
    exact heq

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoB] in
/-- A term and its lift to a later stage denote alike. -/
theorem rden_lift {w : World σ N₀} {i K : ℕ × ℕ} (h : i ≤ K) {A : VarType} {a : Ann A}
    (t : Term σ (w.L.ctx i) A a) :
    rden w K (Ctx.Le.refl _) (Term.mono (w.L.ctx_le h) t) = rden w i (Ctx.Le.refl _) t := by
  rw [rden_mono]
  exact rden_congr _ _ _ _ _ _

/-- ⭐⭐**The truth lemma's `here` case.**  Satisfaction says the witness is realised and the
    content there is indistinguishable from `t`'s value; membership says the theory co-names them.
    *Membership ⇒ truth*: the atom makes the witness realised (`realised_of_here`), the realised
    body is co-named with `t` (`mem_here_realised`), so their representatives are related
    (`DTerm.rel_of_coname`).  *Truth ⇒ membership*: the related representatives carry the atom from
    the realised body to `t`, one equal denotation at a time (`here_transfer`) and across the
    relation once. -/
theorem here_truth (hT : ModalSys.T = true) {w : World σ N₀} {i : ℕ × ℕ} {x : VarSymb}
    (hx : ∃ X, (w.L.ctx i).ref x = some (.VTypeDia X)) {A : VarType} {β : Ann A}
    (bd : Term σ ((w.L.ctx i).diaIn x) A β) {a : Ann A} (t : Term σ (w.L.ctx i) A a)
    (IH : EqTruth w₀ w A) :
    (model w₀).sat (canonEnv w₀ w i) (WFF.here hT (Term.diatm x hx bd) t : WFF σ _ 0) ↔
      (⟨i, WFF.here hT (Term.diatm x hx bd) t⟩ : w.L.sys.Sentence σ) ∈ w.T := by
  obtain ⟨X, h⟩ := id hx
  rw [Model.sat_here_diatm hT (canonEnv w₀ w i) hx h t bd]
  have hD : Model.interp (canonEnv w₀ w i) t =
      toDom w₀ A w (rden w i (Ctx.Le.refl _) t) (definable_rden _ _) :=
    interp_canon w₀ t (fun _ _ _ => rfl)
  have hC : ∀ (hr : w.Realised x)
      (hm : (model w₀).frame.reflAcc hT w ∈
        ((model w₀).posEval ((canonEnv w₀ w i).ref x h)).1),
      Model.interp ((canonEnv w₀ w i).diaPush x h ⟨(model w₀).frame.reflAcc hT w, hm⟩) bd =
        toDom w₀ A w (rden w (i ⊔ hr.data.i₀) (Ctx.Le.refl _)
          (realisedTerm w hr (Ctx.Le.refl _) hx bd).2) (definable_rden _ _) :=
    fun hr hm => interp_dia_self w₀ hr.data (hr.data.declType i hx)
      (fun {_Γ'} {_b} s {_k} {_e'} {_env'} hag' => interp_canon w₀ s hag') (fun _ _ _ => rfl) h
      (World.real_of_realised hr) (realisedDecl hr (Ctx.Le.refl _) hx)
      (realisedLe w hr (Ctx.Le.refl _)) hT hm bd
  constructor
  · rintro ⟨hm, u, u', hu, hu', hrel⟩
    have hm' : (⟨w, ⟨R.refl hT w⟩⟩ : Succ w) ∈ extent w x := canonEnv_extent w₀ w i h ▸ hm
    have hr : w.Realised x := (extent_self hm' (Nat.sub_self _)).2
    rw [hC hr hm, fromDom_toDom] at hu
    rw [hD, fromDom_toDom] at hu'
    -- one stage for everything
    set k := i ⊔ hr.data.i₀
    set K := k ⊔ (u.i ⊔ u'.i)
    have hkK : k ≤ K := le_sup_left
    have hiK : i ≤ K := le_sup_left.trans hkK
    have huK : u.i ≤ K := le_sup_left.trans le_sup_right
    have hu'K : u'.i ≤ K := le_sup_right.trans le_sup_right
    let S : Term σ (w.L.ctx K) (.VTypeDia A) _ := Term.mono (w.L.ctx_le hiK) (Term.diatm x hx bd)
    -- the realised body is co-named with the subject, here at `K`
    have h₁ : (⟨K, WFF.here hT S (Term.mono (w.L.ctx_le hkK)
        (realisedTerm w hr (Ctx.Le.refl _) hx bd).2)⟩ : w.L.sys.Sentence σ) ∈ w.T := by
      have := (World.mem_lift hkK).mp (mem_here_realised hr h bd)
      change (⟨K, WFF.here hT (Term.mono _ (Term.mono _ (Term.diatm x hx bd))) _⟩ :
        w.L.sys.Sentence σ) ∈ w.T at this
      rwa [Term.mono_mono] at this
    -- carried to the representative `u`, then across the relation to `u'`
    have h₂ := here_transfer w₀ hT IH S _ (u.lift K huK)
      ((rden_lift hkK _).trans (hu.symm.trans (rden_lift huK u.t).symm)) h₁
    have h₃ : (⟨K, WFF.here hT S (u'.lift K hu'K)⟩ : w.L.sys.Sentence σ) ∈ w.T := by
      have key := hrel K huK hu'K (WFF.here hT
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := w.L.ctx K)).root A) S)
        (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root _ (.bnd 0) A)))
      rw [WFF.instantiate_here_slot, WFF.instantiate_here_slot] at key
      exact key.mp h₂
    -- and to `t`
    have h₄ := here_transfer w₀ hT IH S _ (Term.mono (w.L.ctx_le hiK) t)
      ((rden_lift hu'K u'.t).trans (hu'.trans (rden_lift hiK t).symm)) h₃
    exact (World.mem_lift hiK).mpr h₄
  · intro hmem
    have hr : w.Realised x := realised_of_here hT h bd t hmem
    have hm : (model w₀).frame.reflAcc hT w ∈
        ((model w₀).posEval ((canonEnv w₀ w i).ref x h)).1 := by
      rw [canonEnv_extent]
      exact self_mem_extent hr
    refine ⟨hm, ⟨i ⊔ hr.data.i₀, _, (realisedTerm w hr (Ctx.Le.refl _) hx bd).2⟩, ⟨i, a, t⟩,
      ?_, ?_, ?_⟩
    · rw [hC hr hm, fromDom_toDom]
    · rw [hD, fromDom_toDom]
    · have hk : i ≤ i ⊔ hr.data.i₀ := le_sup_left
      have ht : (⟨i ⊔ hr.data.i₀, WFF.here hT (Term.mono (w.L.ctx_le hk) (Term.diatm x hx bd))
          (Term.mono (w.L.ctx_le hk) t)⟩ : w.L.sys.Sentence σ) ∈ w.T :=
        (World.mem_lift hk).mp hmem
      exact (DTerm.rel_of_coname hT _ (mem_here_realised hr h bd) ht).trans
        (DTerm.rel_lift ⟨i, a, t⟩ hk).symm

end HereCase

end Canon

end V12M
