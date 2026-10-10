import QML.QML_v12m_BTruth

/-!
# QML v12m — B's canonical model: `Back`, truth ⇒ membership (strong B, T off)

The truth lemma's `back` case in the direction the canonical `Ret` does not give for free
(docs §11.20, "Step 5 begun").

* ⭐`BData.mem_back_of_sat_diaFree`: at a `◇`-free content a true `Back` atom is in the theory.
  Suppose not.  `back_ret` turns the failure into a failing universal — some value `c` of the
  carrier's object along the leg (`◇[e ↦ c] □(e.box = bd)`) is not `t` — and Henkin witnessing
  names it.  The induction hypothesis makes the instance false in the model: some arrow of the
  leg brings the carrier's object home as `c`.  But a true `Back` makes the round trip
  (`Ret_fwd`), so the same arrow brings it home as something `Ind` to `t`; at a `◇`-free type
  `Ind` is equality (`ind_eq_of_diaFree`, by interchange at an `eqRec` slot), and `c = t`.
* `WFF.openFree_bindFree`: opening a bound body at its own eigenvariable gives it back, which is
  how a universal of the theory reaches `back_ret`'s subproof (`Proof.back_of_all`).
-/

namespace V12M

variable [ModalSys]

section Open

variable {σ : Signature} {Γ : Ctx} {T : VarType}

/-- ⭐Opening a bound body at its own eigenvariable gives the body back (`bindFree_openFree`'s
    converse): renaming the variable to the slot and the slot back to the variable composes to the
    identity renaming. -/
theorem WFF.openFree_bindFree (u : ℕ) (hu : Γ.RootFresh (.free u)) (hs : Γ.SlotsFrom 0)
    (φ : WFF σ (Γ.insert (.free u) T) 0) :
    WFF.openFree u hu hs (WFF.bindFree u hu hs T φ) = φ := by
  unfold WFF.openFree WFF.bindFree WFF.renameRoot
  rw [WFF.subst_comp _ _ (Subst.idRen _) _ _ _ _ Subst.ok_idRen Subst.coh_idRen _ _ _ ?_ φ]
  · exact (WFF.subst_ren (Ctx.Le.refl _) _ _ _ _ _ (fun v _ _ => Subst.at_idRen v) φ).trans
      (WFF.mono_refl _ φ)
  refine Subst.sim_of ?_
  intro v U hlp hv
  by_cases hvr : v = .root (.free u)
  · subst hvr
    change SubE.Sim U (.ren _) ((Subst.single (σ := σ) (.free u) (.ren (.root (.bnd 0)))
      (.root (.free u))).comp _ _ _)
    rw [show Subst.single (σ := σ) (Δ := Γ.insert (.bnd 0) T) (.free u) (.ren (.root (.bnd 0)))
      (.root (.free u)) = .ren (.root (.bnd 0)) from if_pos rfl]
    change SubE.Sim U _ (((Subst.idRen Γ).toFree 0 u T hu.root) (.root (.bnd 0)))
    rw [show ((Subst.idRen (σ := σ) Γ).toFree 0 u T hu.root) (.root (.bnd 0)) =
      .ren (.root (.free u)) from if_pos rfl]
    exact .refl _
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    have hvb : v ≠ .root (.bnd 0) := fun h => by
      rw [h, hs.root] at hv'
      cases hv'
    change SubE.Sim U (.ren _) ((Subst.single (σ := σ) (.free u) (.ren (.root (.bnd 0))) v).comp
      _ _ _)
    rw [show Subst.single (σ := σ) (Δ := Γ.insert (.bnd 0) T) (.free u) (.ren (.root (.bnd 0)))
      v = .ren v from if_neg hvr]
    change SubE.Sim U _ (((Subst.idRen Γ).toFree 0 u T hu.root).at v)
    rw [Subst.at_nonproj _ hlp,
      show (Subst.idRen (σ := σ) Γ).toFree 0 u T hu.root v =
        ((Subst.idRen Γ) v).mono (Ctx.le_insert hu.root T) from if_neg hvb]
    exact .refl _

end Open

/-! ## `back_ret` from a universal -/

section BackRet

variable {σ : Signature} {Γ : Ctx} [Γ.NoSlots]

/-- `back_ret`'s premise and conclusion over its fresh value `c`, as one implication: if the
    carrier's object comes back along the leg as `c`, then `c` is `t`. -/
def WFF.backRetImp (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) (c : ℕ) (hc : Γ.RootFresh (.free c)) : WFF σ (Γ.insert (.free c) A) 0 :=
  .imp ((O.mono (Ctx.le_insert hc.root A)).ret hS
      (Term.eta (.root (.free c)) A (Ctx.ref_insert_root Γ (.free c) A))
      (WFF.mono ((O.le_view_mono (Ctx.le_insert hc.root A)).insert (.bnd 0) _)
        (WFF.backRetBody (OutLeg.slotsFrom Ctx.NoSlots.slots O) hA bd)))
    (eqRec A (Term.eta (.root (.free c)) A (Ctx.ref_insert_root Γ (.free c) A))
      (Term.castAnn hA (Term.weaken hc.root A t)))

/-- `back_ret`'s premise as a universal: every value the carrier's object comes back as along
    the leg is `t`. -/
def WFF.backRetAll (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) (c : ℕ) (hc : Γ.RootFresh (.free c)) : WFF σ Γ 0 :=
  .all A (WFF.bindFree c hc Ctx.NoSlots.slots A (WFF.backRetImp hS O hA bd t c hc))

/-- ⭐`∀c (◇[e ↦ c] □(e.box = bd) → c = t), ◇⊤ ⊢ Back bd t`: `back_ret`, its subproof
    instantiating the universal at the fresh value (`WFF.openFree_bindFree`). -/
def Proof.back_of_all (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true) (O : OutLeg Γ)
    {A : VarType} (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀)
    {a : Ann A} (t : Term σ Γ A a) (c : ℕ) (hc : Γ.RootFresh (.free c)) :
    Proof σ Γ [WFF.backRetAll hS O hA bd t c hc, O.dia .top] (O.back hS bd t) := by
  refine Proof.back_ret hS hB O hA bd t c hc
    (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)) ?_
  refine Proof.imp_elim (Proof.conv ?_ (Proof.all_elim A
    (Term.eta (.root (.free c)) A (Ctx.ref_insert_root Γ (.free c) A))
    (φ := WFF.mono ((Ctx.le_insert hc.root A).insert (.bnd 0) A)
      (WFF.bindFree c hc Ctx.NoSlots.slots A (WFF.backRetImp hS O hA bd t c hc)))
    (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))))
    (Proof.lookup List.mem_cons_self)
  rw [WFF.instantiate_eta_openFree c hc Ctx.NoSlots.slots, WFF.openFree_bindFree]
  rfl

end BackRet

/-! ## Unpacking a weakened returning possibility -/

section Agree

variable {σ : Signature} {M : Model σ} {Γ Γ' : Ctx}

/-- A returning possibility along a leg, weakened to a larger context, read back in the smaller
    one: an arrow of the old leg, the body there, and the way home (`sat_ret_agree`'s converse). -/
theorem OutLeg.ret_of_sat_agree {h : Γ.Le Γ'} {w : M.frame.W} {env : M.Env Γ w}
    {env' : M.Env Γ' w} (hag : Model.Env.Agree h env env') (hS : ModalSys.BStrong = true)
    (O : OutLeg Γ) {A : VarType} {a : Ann A} (t' : Term σ Γ' A a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1)
    (hs : M.sat env' ((O.mono h).ret hS t' (WFF.mono ((O.le_view_mono h).insert (.bnd 0) _) Φ))) :
    ∃ (i : O.Arr env) (e : M.frame.Dom (.VTypeBox A) (O.acc env i).1),
      M.sat ((O.push env i).extend (.bnd 0) e) Φ ∧
        ∃ r : M.frame.R (O.acc env i).1 w,
          M.Ind (M.necEval (e : M.frame.Nec A (O.acc env i).1) ⟨w, ⟨r⟩⟩)
            (Model.interp env' t') := by
  cases O with
  | nec =>
      obtain ⟨i, e, hΦ, r, hr⟩ := hs
      exact ⟨i, e, (Model.sat_mono (Model.Env.extend_agree (Model.Env.boxPush_agree hag i)
        (.bnd 0) e) Φ).mp hΦ, r, hr⟩
  | pos y hy =>
      obtain ⟨Y, hY, a, e, hΦ, r, hr⟩ := hs
      have hYc : Y = hy.choose := by
        have e' := hY.symm.trans (h.ref hy.choose_spec)
        simp only [Option.some.injEq, VarType.VTypeDia.injEq] at e'
        exact e'
      subst hYc
      have href := Model.Env.ref_agree hag y hy.choose_spec
      let w₁ : (M.posEval (env.ref y hy.choose_spec)).1 := ⟨a.1, by rw [href]; exact a.2⟩
      exact ⟨w₁, e, (Model.sat_mono (Model.Env.extend_agree
        (Model.Env.diaPush_agree hag hy.choose_spec w₁ a.2) (.bnd 0) e) Φ).mp hΦ, r, hr⟩

end Agree

namespace BArrow

variable {σ : Signature}

namespace BData

variable [ModalSys.NoFour] {B : BData σ}

/-- ⭐**At a `◇`-free type canonical `Ind` is equality**: related representatives are
    interchangeable at the slot formula `z = u'`, whose `u'`-instance is provable; so the
    `u`-instance is in the theory, and true by the induction hypothesis at `eqRec`. -/
theorem ind_eq_of_diaFree {s : B.W} {A : VarType} (hA : A.diaFree = true)
    {o o' : B.model.frame.Dom A s}
    (IH : ∀ (K : ℕ) (u u' : Term σ ((B.w s).ctx K) A (Ann.eta (.root (.bnd 0)) A)),
      (eqRec A u u' : WFF σ _ 0) ∈ (B.w s).M K →
        B.model.sat (B.canonEnv s K) (eqRec A u u' : WFF σ _ 0))
    (h : B.Ind o o') : o = o' := by
  obtain ⟨⟨i, a, u⟩, ⟨i', a', u'⟩, hu, hu', hrel⟩ := h
  obtain rfl := Ann.eq_of_diaFree hA a (Ann.eta (.root (.bnd 0)) A)
  obtain rfl := Ann.eq_of_diaFree hA a' (Ann.eta (.root (.bnd 0)) A)
  have hK : i ≤ max i i' := le_max_left _ _
  have hK' : i' ≤ max i i' := le_max_right _ _
  have key := hrel _ hK hK' (eqRec A
    (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root _ (.bnd 0) A))
    (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (B.w s).ctx (max i i'))).root A)
      (Term.mono ((B.w s).le hK') u')))
  rw [WFF.instantiate_eqRec_slot hA, WFF.instantiate_eqRec_slot hA] at key
  have h0 : (eqRec A (Term.mono ((B.w s).le hK') u') (Term.mono ((B.w s).le hK') u') :
      WFF σ _ 0) ∈ (B.w s).M (max i i') :=
    BWorld.mem_of_provable (Δ := []) (fun _ h => by simp at h) ⟨Proof.eqRec_refl A _⟩
  have hsat := IH _ _ _ (BWorld.mem_T.mp (key.mpr (BWorld.mem_T.mpr h0)))
  rw [Model.sat_eqRec, interp_canon _ (Model.Env.Agree.refl' _),
    interp_canon _ (Model.Env.Agree.refl' _)] at hsat
  have he := toDom_inj hsat
  change B.rden s _ _ (Term.mono ((B.w s).le hK) u) =
    B.rden s _ _ (Term.mono ((B.w s).le hK') u') at he
  rw [rden_lift hK u, rden_lift hK' u', hu, hu'] at he
  rw [← B.toDom_fromDom A s o, ← B.toDom_fromDom A s o']
  exact toDom_congr he _ _

omit [ModalSys.NoFour] in
/-- `Back`'s size dominates everything its `◇`-free case looks at. -/
theorem size_back_ge {Γ : Ctx} (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A} (t : Term σ Γ A a) :
    3 * A.eqRecSize + 5 ≤ (O.back hS bd t : WFF σ Γ 0).size := by
  cases O <;> simp only [OutLeg.back, WFF.size, BLeg.carrier, VarType.eqRecSize] <;> omega

omit [ModalSys.NoFour] in
theorem size_backRetImp {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) (O : OutLeg Γ)
    {A : VarType} (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀)
    {a : Ann A} (t : Term σ Γ A a) (c : ℕ) (hc : Γ.RootFresh (.free c)) :
    (WFF.backRetImp hS O hA bd t c hc).size = 3 * A.eqRecSize + 3 := by
  cases O <;>
  simp only [WFF.backRetImp, OutLeg.ret, OutLeg.retS, OutLeg.mono, WFF.size, WFF.size_mono,
    WFF.backRetBody, WFF.size_eqRec, RShape.flat, NShape.flat, VarType.eqRecSize] <;> omega

omit [ModalSys.NoFour] in
theorem size_dia_top {Γ : Ctx} (O : OutLeg Γ) : (O.dia (.top : WFF σ O.view 0)).size ≤ 3 := by
  cases O <;> simp [OutLeg.dia, WFF.neg, WFF.size]

/-- ⭐⭐**`Back`, truth ⇒ membership, at a `◇`-free content** (strong B; docs §11.20).  Were the
    atom not in the theory, `back_ret` (`Proof.back_of_all`) would make its universal fail, and
    Henkin witnessing gives a value `g` with `◇[e ↦ g] □(e.box = bd)` and `g ≠ t` at a later stage.
    By the induction hypothesis that is true: an arrow of the leg brings the carrier's object home
    as `g`.  The atom is true, so it makes the round trip (`sat_back_rt`): the same arrow brings it
    home as something `Ind` to `t`.  At a `◇`-free type `Ind` is equality
    (`ind_eq_of_diaFree`), so `g = t`.  The induction hypothesis is used below `Back`'s size only
    (`size_back_ge`). -/
theorem mem_back_of_sat_diaFree (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    {s : B.W} {i : ℕ} (O : OutLeg ((B.w s).ctx i)) {A : VarType} (hA : A.diaFree = true)
    {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A} (t : Term σ ((B.w s).ctx i) A a)
    (IH : ∀ (K : ℕ) (φ : WFF σ ((B.w s).ctx K) 0),
      φ.size < (O.back hS bd t : WFF σ _ 0).size →
        (B.model.sat (B.canonEnv s K) φ ↔ φ ∈ (B.w s).M K))
    (h : B.model.sat (B.canonEnv s i) (O.back hS bd t : WFF σ _ 0)) :
    (O.back hS bd t : WFF σ _ 0) ∈ (B.w s).M i := by
  have hsz := size_back_ge hS O bd t
  have hrt := OutLeg.sat_back_rt hS (B.canonEnv s i) O bd t h
  obtain ⟨⟨i₀⟩, hrt⟩ := hrt
  have hdia : O.dia (.top : WFF σ O.view 0) ∈ (B.w s).M i :=
    (IH i _ (by have := size_dia_top (σ := σ) O; omega)).mp
      ((OutLeg.sat_dia (B.canonEnv s i) O _).mpr ⟨i₀, trivial⟩)
  have hind : ∀ {x y : B.model.frame.Dom A s}, B.Ind x y → x = y := fun hxy =>
    ind_eq_of_diaFree hA (fun K u u' hm => (IH K _ (by rw [WFF.size_eqRec]; omega)).mpr hm) hxy
  by_contra hnot
  have hc : ((B.w s).ctx i).RootFresh (.free ((B.w s).l i).length) := ctxOf_fresh le_rfl
  have hall : WFF.backRetAll hS O hA bd t _ hc ∉ (B.w s).M i := fun hm =>
    hnot (BWorld.mem_of_provable (Δ := [_, _]) (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hm
      · rw [List.mem_singleton.mp hψ]; exact hdia)
      ⟨Proof.back_of_all hS hB O hA bd t _ hc⟩)
  obtain ⟨j, hij, ag, g, hneg⟩ := (B.w s).allW (((B.w s).mcs i).neg_mem_iff.mpr hall)
  have hns := fun hs => ((B.w s).mcs j).neg_mem_iff.mp hneg ((IH j _ (by
    rw [WFF.size_instantiate, WFF.size_mono, WFF.bindFree, WFF.renameRoot, WFF.size_subst,
      size_backRetImp]
    omega)).mp hs)
  rw [Model.sat_instantiate _ (noProjLast s j) _ g,
    Model.sat_mono (Model.Env.extend_agree (canonEnv_le s hij) (.bnd 0) _),
    Model.sat_bindFree _ (noProjLast s i) _ hc] at hns
  refine hns fun hR => ?_
  set og := Model.interp (B.canonEnv s j) g
  obtain ⟨i₁, e, hΦ, r, hr⟩ := OutLeg.ret_of_sat_agree
    (Model.Env.agree_extend (B.canonEnv s i) hc.root og) hS O _ _ hR
  have hslot : ((B.canonEnv s i).extend (.free _) og).ref (.root (.free _))
      (Ctx.ref_insert_root _ (.free ((B.w s).l i).length) A) = og :=
    Model.Env.extend_root _ (.free _) og (Ctx.ref_insert_root _ _ A)
  -- the body: the object out there is the carrier's
  unfold WFF.backRetBody at hΦ
  have hslot0 : ((O.push (B.canonEnv s i) i₁).extend (.bnd 0) e).ref (.root (.bnd 0))
      (Ctx.ref_insert_root O.view (.bnd 0) (.VTypeBox A)) = e :=
    Model.Env.extend_root _ (.bnd 0) e (Ctx.ref_insert_root O.view (.bnd 0) (.VTypeBox A))
  rw [Model.sat_eqRec, Model.interp_castAnn,
    Model.interp_mono (Model.Env.agree_extend _ (OutLeg.slotsFrom Ctx.NoSlots.slots O).root _),
    Model.interp_eta, hslot0] at hΦ
  rw [hΦ, Model.box_beta] at hr
  obtain ⟨r', hr'⟩ := hrt i₁
  change B.Ind _ _ at hr hr'
  rw [Model.interp_eta, hslot] at hr
  have h₁ := hind hr
  have h₂ := hind hr'
  rw [Model.sat_eqRec, Model.interp_castAnn, Term.weaken,
    Model.interp_mono (Model.Env.agree_extend _ hc.root _), Model.interp_eta, hslot]
  exact h₁.symm.trans h₂

end BData

end BArrow

end V12M
