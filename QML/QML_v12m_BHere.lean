import QML.QML_v12m_BLeaf

/-!
# QML v12m — B's canonical model: what `Here` says

The truth lemma's `here` case on the network, as in the tree (`QML_v12m_CanonHere`): the
theory-level facts are shared (`Canon.mem_here_datum`, `Canon.DTerm.rel_of_coname`), and a `Here`
atom is read along a world's own arrow.

* ⭐`here_transfer`: equal denotations carry `Here` facts — tags determine annotations
  (`ann_eq_of_rden_ctx`), so the two contents can be equated.
* ⭐⭐`here_truth`: the `here` case of the truth lemma.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

namespace BData

variable [ModalSys.NoFour] {B : BData σ}

variable (B) in
/-- The truth lemma at the equations of one type: what the `here` case receives from the
    induction, `eqRec` being smaller than `Here` (`WFF.size_eqRec`). -/
abbrev EqTruth (s : B.W) (A : VarType) : Prop :=
  ∀ (K : ℕ) {b : Ann A} (u u' : Term σ ((B.w s).ctx K) A b),
    B.model.sat (B.canonEnv s K) (eqRec A u u' : WFF σ ((B.w s).ctx K) 0) ↔
      eqRec A u u' ∈ (B.w s).M K

/-- ⭐**Equal denotations carry `Here` facts** (docs §10.38 (F)).  Tags determine annotations
    (`ann_eq_of_rden_ctx`), so the two contents can be equated (`eqRec`, by the truth lemma at a
    smaller formula), and `Proof.here_eq` moves the atom. -/
theorem here_transfer (hT : ModalSys.T = true) {s : B.W} {A : VarType}
    (IH : B.EqTruth s A) {K : ℕ} {c : Ann (.VTypeDia A)}
    (S : Term σ ((B.w s).ctx K) (.VTypeDia A) c) {b b' : Ann A}
    (r : Term σ ((B.w s).ctx K) A b) (r' : Term σ ((B.w s).ctx K) A b')
    (he : B.rden s K (Ctx.Le.refl _) r = B.rden s K (Ctx.Le.refl _) r')
    (hmem : WFF.here hT S r ∈ (B.w s).M K) :
    WFF.here hT S r' ∈ (B.w s).M K := by
  obtain rfl := B.ann_eq_of_rden_ctx hT r r' he
  have heq : eqRec A r r' ∈ (B.w s).M K := by
    refine (IH K r r').mp ((Model.sat_eqRec _ A r r').mpr ?_)
    rw [interp_canon r (fun _ _ _ => rfl), interp_canon r' (fun _ _ _ => rfl)]
    exact toDom_congr he _ _
  refine BWorld.mem_of_provable (Δ := [WFF.here hT S r, eqRec A r r']) (fun ψ hψ => ?_)
    ⟨Proof.here_eq hT S r r' (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact hmem
  · rw [List.mem_singleton.mp hψ]
    exact heq

/-- ⭐⭐**The truth lemma's `here` case**, as in the tree (`Canon.here_truth`).  Satisfaction says
    the witness is realised and the content along the world's own arrow is indistinguishable from
    `t`'s value; membership says the theory co-names them.
    *Membership ⇒ truth*: the atom makes the witness realised (`BWorld.datum_of_here`) and relates
    its realisation and `t` (`rel_here`).  *Truth ⇒ membership*: related representatives carry
    the atom from the realised body to `t`, one equal denotation at a time (`here_transfer`) and
    across the relation once. -/
theorem here_truth (hT : ModalSys.T = true) {s : B.W} {i : ℕ} {x : VarSymb}
    (hx : ∃ X, ((B.w s).ctx i).ref x = some (.VTypeDia X)) {A : VarType} {β : Ann A}
    (bd : Term σ (((B.w s).ctx i).diaIn x) A β) {a : Ann A} (t : Term σ ((B.w s).ctx i) A a)
    (IH : B.EqTruth s A) :
    B.model.sat (B.canonEnv s i) (WFF.here hT (Term.diatm x hx bd) t : WFF σ _ 0) ↔
      WFF.here hT (Term.diatm x hx bd) t ∈ (B.w s).M i := by
  obtain ⟨X, h⟩ := id hx
  rw [Model.sat_here_diatm hT (B.canonEnv s i) hx h t bd]
  have hD : Model.interp (B.canonEnv s i) t =
      B.toDom A s (B.rden s i (Ctx.Le.refl _) t) (definable_rden _ _) :=
    interp_canon t (fun _ _ _ => rfl)
  have hC : ∀ (hr : (B.w s).Realised x)
      (hm : B.model.frame.reflAcc hT s ∈ (B.model.posEval ((B.canonEnv s i).ref x h)).1),
      Model.interp ((B.canonEnv s i).diaPush x h ⟨B.model.frame.reflAcc hT s, hm⟩) bd =
        B.toDom A s (B.rden s (max i hr.data.i₀) (Ctx.Le.refl _)
          (B.realTerm hr (Ctx.Le.refl _) hx bd).2) (definable_rden _ _) :=
    fun hr hm => interp_dia_self hr
      (fun {_Γ'} {_b} u {_k} {_e'} {_env'} hag' => interp_canon u hag')
      (fun _ _ _ => rfl) h hT hm bd
  constructor
  · rintro ⟨hm, u, u', hu, hu', hrel⟩
    have hm' : B.model.frame.reflAcc hT s ∈ B.extent s x := canonEnv_extent s i h ▸ hm
    have hr : (B.w s).Realised x :=
      (mem_extent_self hm' fun ⟨_, hk⟩ => B.irrefl s (B.lbR hk)).2
    rw [hC hr hm, fromDom_toDom] at hu
    rw [hD, fromDom_toDom] at hu'
    -- one stage for everything
    set k := max i hr.data.i₀
    set K := max k (max u.i u'.i)
    have hkK : k ≤ K := le_max_left _ _
    have hiK : i ≤ K := (le_max_left _ _).trans hkK
    have huK : u.i ≤ K := (le_max_left _ _).trans (le_max_right _ _)
    have hu'K : u'.i ≤ K := (le_max_right _ _).trans (le_max_right _ _)
    let S : Term σ ((B.w s).ctx K) (.VTypeDia A) _ :=
      Term.mono ((B.w s).le hiK) (Term.diatm x hx bd)
    -- the realised body is co-named with the subject, here at `K`
    have h₁ : WFF.here hT S (Term.mono ((B.w s).le hkK)
        (B.realTerm hr (Ctx.Le.refl _) hx bd).2) ∈ (B.w s).M K := by
      have := (BWorld.mem_lift hkK).mp (mem_here_real hr h bd)
      change WFF.here hT (Term.mono _ (Term.mono _ (Term.diatm x hx bd))) _ ∈ (B.w s).M K
        at this
      rwa [Term.mono_mono] at this
    -- carried to the representative `u`, then across the relation to `u'`
    have h₂ := here_transfer hT IH S _ (u.lift K huK)
      ((rden_lift hkK _).trans (hu.symm.trans (rden_lift huK u.t).symm)) h₁
    have h₃ : WFF.here hT S (u'.lift K hu'K) ∈ (B.w s).M K := by
      have key := hrel K huK hu'K (WFF.here hT
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (B.w s).ctx K)).root A) S)
        (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root _ (.bnd 0) A)))
      rw [WFF.instantiate_here_slot, WFF.instantiate_here_slot] at key
      exact key.mp h₂
    -- and to `t`
    have h₄ := here_transfer hT IH S _ (Term.mono ((B.w s).le hiK) t)
      ((rden_lift hu'K u'.t).trans (hu'.trans (rden_lift hiK t).symm)) h₃
    exact (BWorld.mem_lift hiK).mpr h₄
  · intro hmem
    have hr : (B.w s).Realised x := (B.w s).datum_of_here hT h bd t hmem
    have hm : B.model.frame.reflAcc hT s ∈ (B.model.posEval ((B.canonEnv s i).ref x h)).1 := by
      rw [canonEnv_extent]
      exact Or.inr ⟨B.irrefl s, hr⟩
    refine ⟨hm, _, ⟨i, a, t⟩, ?_, ?_, rel_here hT hx bd t hr hmem⟩
    · rw [hC hr hm, fromDom_toDom]
    · rw [hD, fromDom_toDom]

end BData

end BArrow

end V12M
