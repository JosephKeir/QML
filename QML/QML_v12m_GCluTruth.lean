import QML.QML_v12m_GCluRet
import QML.QML_v12m_BBackTruth

/-!
# QML v12m — 5 on the growing tree: the cluster model's truth lemma

* `mem_back_of_sat_diaFreeC`, ⭐`mem_back_of_sat_necC`, ⭐`mem_back_of_sat_posC`: `Back`, truth ⇒
  membership.
* ⭐`ctruth`: the truth lemma, `□` and `◇` through `box_pathO_iff` and `dia_pathO_iff`.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

variable (hM₀ : Theory.IsMCS M₀)

variable {hM₀}

/-! ## `Back`, truth ⇒ membership -/

/-- ⭐At a `◇`-free type `cInd` is equality (`BData.ind_eq_of_diaFree`). -/
theorem cind_eq_of_diaFree (hX : CluFlags) {s : GW hF M₀} {A : VarType} (hA : A.diaFree = true)
    {o o' : (cframe hF hM₀ hX).Dom A s}
    (IH : ∀ (K : ℕ) (u u' : Term σ (ctxOf (glat s K)) A (Ann.eta (.root (.bnd 0)) A)),
      (eqRec A u u' : WFF σ _ 0) ∈ (gw hM₀ s).M K →
        (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s K) (eqRec A u u' : WFF σ _ 0))
    (h : cInd hM₀ hX o o') : o = o' := by
  obtain ⟨⟨i, a, u⟩, ⟨i', a', u'⟩, hu, hu', hrel⟩ := h
  obtain rfl := Ann.eq_of_diaFree hA a (Ann.eta (.root (.bnd 0)) A)
  obtain rfl := Ann.eq_of_diaFree hA a' (Ann.eta (.root (.bnd 0)) A)
  have hK : i ≤ max i i' := le_max_left _ _
  have hK' : i' ≤ max i i' := le_max_right _ _
  have key := hrel _ hK hK' (eqRec A
    (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root _ (.bnd 0) A))
    (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (gw hM₀ s).ctx (max i i'))).root A)
      (Term.mono ((gw hM₀ s).le hK') u')))
  rw [WFF.instantiate_eqRec_slot hA, WFF.instantiate_eqRec_slot hA] at key
  have h0 : (eqRec A (Term.mono ((gw hM₀ s).le hK') u') (Term.mono ((gw hM₀ s).le hK') u') :
      WFF σ _ 0) ∈ (gw hM₀ s).M (max i i') :=
    BWorld.mem_of_provable (Δ := []) (fun _ h => by simp at h) ⟨Proof.eqRec_refl A _⟩
  have hsat := IH _ _ _ (BWorld.mem_T.mp (key.mpr (BWorld.mem_T.mpr h0)))
  rw [Model.sat_eqRec, interp_ccanon hX _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _),
    interp_ccanon hX _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)] at hsat
  have he := ctoDom_inj hX hsat
  change cden hM₀ hX s _ _ (Term.mono ((gw hM₀ s).le hK) u) =
    cden hM₀ hX s _ _ (Term.mono ((gw hM₀ s).le hK') u') at he
  rw [cden_lift hX hK u, cden_lift hX hK' u', hu, hu'] at he
  rw [← ctoDom_fromDom hM₀ hX A s o, ← ctoDom_fromDom hM₀ hX A s o']
  exact ctoDom_congr hX he _ _

/-- ⭐⭐**`Back`, truth ⇒ membership, at a `◇`-free content** (`BData.mem_back_of_sat_diaFree`):
    were the atom not in the theory, `back_ret` would give a value `g ≠ t` that the leg brings
    home; the atom's round trip brings it home as `t`; `Ind` is equality. -/
theorem mem_back_of_sat_diaFreeC (hX : CluFlags) (hS : ModalSys.BStrong = true) {s : GW hF M₀}
    {i : ℕ} (O : OutLeg (ctxOf (glat s i))) {A : VarType} (hA : A.diaFree = true) {a₀ : Ann A}
    (bd : Term σ O.view.boxIn A a₀) {a : Ann A} (t : Term σ (ctxOf (glat s i)) A a)
    (IH : ∀ (K : ℕ) (φ : WFF σ (ctxOf (glat s K)) 0),
      φ.size < (O.back hS bd t : WFF σ _ 0).size →
        ((cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s K) φ ↔ φ ∈ (gw hM₀ s).M K))
    (h : (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s i) (O.back hS bd t : WFF σ _ 0)) :
    (O.back hS bd t : WFF σ _ 0) ∈ (gw hM₀ s).M i := by
  have hB := hX.bS hS
  have hT := hX.bT hB
  have hsz := BData.size_back_ge hS O bd t
  have hrt := OutLeg.sat_back_rt hS (ccanonEnv hM₀ hX s i) O bd t h
  obtain ⟨⟨i₀⟩, hrt⟩ := hrt
  have hdia : O.dia (.top : WFF σ O.view 0) ∈ (gw hM₀ s).M i :=
    (IH i _ (by have := BData.size_dia_top (σ := σ) O; omega)).mp
      ((OutLeg.sat_dia (ccanonEnv hM₀ hX s i) O _).mpr ⟨i₀, trivial⟩)
  have hind : ∀ {x y : (cframe hF hM₀ hX).Dom A s}, cIndM hM₀ hX x y → x = y := fun hxy =>
    cind_eq_of_diaFree hX hA (fun K u u' hm => (IH K _ (by rw [WFF.size_eqRec]; omega)).mpr hm)
      (hxy.1 hT)
  by_contra hnot
  have hc : (ctxOf (glat s i)).RootFresh (.free (glat s i).length) := ctxOf_fresh le_rfl
  have hall : WFF.backRetAll hS O hA bd t _ hc ∉ (gw hM₀ s).M i := fun hm =>
    hnot (BWorld.mem_of_provable (Δ := [_, _]) (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hm
      · rw [List.mem_singleton.mp hψ]; exact hdia)
      ⟨Proof.back_of_all hS hB O hA bd t _ hc⟩)
  obtain ⟨j, hij, ag, g, hneg⟩ := (gw hM₀ s).allW (((gw hM₀ s).mcs i).neg_mem_iff.mpr hall)
  have hns := fun hs => ((gw hM₀ s).mcs j).neg_mem_iff.mp hneg ((IH j _ (by
    rw [WFF.size_instantiate, WFF.size_mono, WFF.bindFree, WFF.renameRoot, WFF.size_subst,
      BData.size_backRetImp]
    omega)).mp hs)
  rw [Model.sat_instantiate _ (Ctx.Presented.noProjLast _) _ g,
    Model.sat_mono (Model.Env.extend_agree (ccanonEnv_le hX s hij) (.bnd 0) _),
    Model.sat_bindFree _ (Ctx.Presented.noProjLast _) _ hc] at hns
  refine hns fun hR => ?_
  set og := Model.interp (ccanonEnv hM₀ hX s j) g
  obtain ⟨i₁, e, hΦ, r, hr⟩ := OutLeg.ret_of_sat_agree
    (Model.Env.agree_extend (ccanonEnv hM₀ hX s i) hc.root og) hS O _ _ hR
  have hslot : ((ccanonEnv hM₀ hX s i).extend (.free _) og).ref (.root (.free _))
      (Ctx.ref_insert_root _ (.free (glat s i).length) A) = og :=
    Model.Env.extend_root _ (.free _) og (Ctx.ref_insert_root _ _ A)
  unfold WFF.backRetBody at hΦ
  have hslot0 : ((O.push (ccanonEnv hM₀ hX s i) i₁).extend (.bnd 0) e).ref (.root (.bnd 0))
      (Ctx.ref_insert_root O.view (.bnd 0) (.VTypeBox A)) = e :=
    Model.Env.extend_root _ (.bnd 0) e (Ctx.ref_insert_root O.view (.bnd 0) (.VTypeBox A))
  rw [Model.sat_eqRec, Model.interp_castAnn,
    Model.interp_mono (Model.Env.agree_extend _ (OutLeg.slotsFrom Ctx.NoSlots.slots O).root _),
    Model.interp_eta, hslot0] at hΦ
  rw [hΦ, Model.box_beta] at hr
  obtain ⟨r', hr'⟩ := hrt i₁
  change cIndM hM₀ hX _ _ at hr hr'
  rw [Model.interp_eta, hslot] at hr
  have h₁ := hind hr
  have h₂ := hind hr'
  rw [Model.sat_eqRec, Model.interp_castAnn, Term.weaken,
    Model.interp_mono (Model.Env.agree_extend _ hc.root _), Model.interp_eta, hslot]
  exact h₁.symm.trans h₂

/-- ⭐⭐**`Back`, truth ⇒ membership, row 1** (`BData.mem_back_of_sat_nec`).  At a `◇`-free content,
    `mem_back_of_sat_diaFreeC`.  Otherwise `cRet` is an atom of the theory with these data and this
    witness.  A plain leg has no witness, and a possible carrier has one, so the atom is row 1
    (here, unlike on the arrow network, a witness's extent can be every arrow).  `nec_inj` twice
    makes the carriers' denotations equal, `ann_eq_of_toDomC` the annotations, the induction
    hypothesis puts `eqRec` of carriers and of values in the theory, and `back_eqC`, `back_eq` move
    the atom to ours. -/
theorem mem_back_of_sat_necC (hX : CluFlags) (hS : ModalSys.BStrong = true) {s : GW hF M₀}
    {i : ℕ} {A : VarType} {a₀ : Ann A} (bd : Term σ (ctxOf (glat s i)).boxIn.boxIn A a₀)
    {a : Ann A} (t : Term σ (ctxOf (glat s i)) A a)
    (IH : ∀ (K : ℕ) (φ : WFF σ (ctxOf (glat s K)) 0),
      φ.size < ((OutLeg.nec : OutLeg (ctxOf (glat s i))).back hS bd t : WFF σ _ 0).size →
        ((cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s K) φ ↔ φ ∈ (gw hM₀ s).M K))
    (h : (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s i)
      ((OutLeg.nec : OutLeg (ctxOf (glat s i))).back hS bd t : WFF σ _ 0)) :
    ((OutLeg.nec : OutLeg (ctxOf (glat s i))).back hS bd t : WFF σ _ 0) ∈ (gw hM₀ s).M i := by
  have hT := hX.bT (hX.bS hS)
  have hSh : ModalSys.shaped = true := ModalSys.shaped_of_T hT
  by_cases hA : A.diaFree = true
  · exact mem_back_of_sat_diaFreeC hX hS .nec hA bd t IH h
  have hsz := BData.size_back_ge hS .nec bd t
  change cRet hM₀ hX _ _ _ _ at h
  rcases h with ⟨-, -, hA' | ⟨hS', i', L, c, ct, a', t', hmem, hdata, htag, hval⟩⟩
  · exact absurd hA' hA
  revert c ct hmem hdata htag
  cases L with
  | pos =>
      intro c ct _ _ htag
      have htag' : (cTag hM₀ hX .pos (ctoDom hM₀ hX _ s
          (cden hM₀ hX s i' (Ctx.Le.refl _) ct) (cdefinable_den hX _ _))).isSome = false := by
        rw [htag]
        rfl
      simp [cTag, hSh] at htag'
  | nec =>
      intro c ct
      cases ct with
      | boxtm u =>
          cases u with
          | boxtm bd' =>
              intro hmem hdata _
              obtain ⟨-, hval'⟩ := Sigma.mk.inj_iff.mp hdata
              have hfun := eq_of_heq hval'
              have hc : ctoDom hM₀ hX _ s (cden hM₀ hX s i' (Ctx.Le.refl _)
                    (Term.boxtm (Term.boxtm bd'))) (cdefinable_den hX _ _) =
                  ctoDom hM₀ hX _ s (cden hM₀ hX s i (Ctx.Le.refl _)
                    (Term.boxtm (Term.boxtm bd))) (cdefinable_den hX _ _) := by
                rw [← interp_ccanon hX (Term.boxtm (Term.boxtm bd)) (Model.Env.Agree.refl' _)
                  (Ctx.Presented.noProjLast _)]
                exact (cmodel hF hM₀ hX).nec_inj (funext fun a₁ =>
                  (cmodel hF hM₀ hX).nec_inj (funext fun b =>
                    congrFun (congrFun hfun ⟨a₁, Set.mem_univ _⟩) b))
              have hv : ctoDom hM₀ hX A s (cden hM₀ hX s i' (Ctx.Le.refl _) t')
                    (cdefinable_den hX _ _) =
                  ctoDom hM₀ hX A s (cden hM₀ hX s i (Ctx.Le.refl _) t)
                    (cdefinable_den hX _ _) := by
                rw [hval, interp_ccanon hX t (Model.Env.Agree.refl' _)
                  (Ctx.Presented.noProjLast _)]
              obtain ⟨⟨⟩⟩ := ann_eq_of_toDomC hX hT _ _ hc
              obtain rfl := ann_eq_of_toDomC hX hT _ _ hv
              have hK : i ≤ max i i' := le_max_left _ _
              have hK' : i' ≤ max i i' := le_max_right _ _
              have hmc := (IH _ _ (by
                rw [WFF.size_eqRec]; simp only [VarType.eqRecSize] at hsz ⊢; omega)).mp
                (sat_eqRec_liftC hX hK' hK _ _ hc)
              have hmv := (IH _ _ (by rw [WFF.size_eqRec]; omega)).mp
                (sat_eqRec_liftC hX hK' hK _ _ hv)
              refine (BWorld.mem_lift hK).mpr (BWorld.mem_of_provable (Δ := [_, _, _])
                (fun ψ hψ => by
                  rcases List.mem_cons.mp hψ with rfl | hψ
                  · exact (BWorld.mem_lift hK').mp hmem
                  rcases List.mem_cons.mp hψ with rfl | hψ
                  · exact hmc
                  · rw [List.mem_singleton.mp hψ]; exact hmv)
                ⟨Proof.back_eq hS .nec _ _ _ (Proof.back_eqC hS .nec _ _ _
                  (Proof.lookup List.mem_cons_self)
                  (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))
                  (Proof.lookup (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ List.mem_cons_self)))⟩)

/-- One shape at two stages means one annotation (`ann_eq_of_crawShape`). -/
theorem ann_eq_of_crawShapeL (hX : CluFlags) (hT : ModalSys.T = true) {s : GW hF M₀} {A : VarType}
    {i i' : ℕ} {a a' : Ann A} (t : Term σ (ctxOf (glat s i)) A a)
    (t' : Term σ (ctxOf (glat s i')) A a')
    (h : crawShape hT (cden hM₀ hX s i (Ctx.Le.refl _) t) =
      crawShape hT (cden hM₀ hX s i' (Ctx.Le.refl _) t')) : a = a' := by
  have hK : i ≤ max i i' := le_max_left _ _
  have hK' : i' ≤ max i i' := le_max_right _ _
  refine ann_eq_of_crawShape (hM₀ := hM₀) hX hT (Term.mono ((gw hM₀ s).le hK) t)
    (Term.mono ((gw hM₀ s).le hK') t') ?_
  rw [cden_lift hX hK t, cden_lift hX hK' t']
  exact h

/-- ⭐⭐**`Back`, truth ⇒ membership, row 2** (`BData.mem_back_of_sat_pos`), with no fresh arrow:
    the tag is the carrier's whole shape.  At a `◇`-free content, `mem_back_of_sat_diaFreeC`.
    Otherwise `cRet` is an atom with these data and this shape.  A possible carrier has a tag, so
    the atom is row 2.  One shape is one annotation (`ann_eq_of_crawShapeL`), so one witness; the
    data then give the contents, which with the annotation make the carriers' denotations equal.
    `eqRec` of carriers and of values is true, so in the theory, and `back_eqC`, `back_eq` move
    the atom to ours. -/
theorem mem_back_of_sat_posC (hX : CluFlags) (hS : ModalSys.BStrong = true) {s : GW hF M₀}
    {i : ℕ} {y : VarSymb} (hy : ∃ Y, (ctxOf (glat s i)).ref y = some (.VTypeDia Y)) {A : VarType}
    {a₀ : Ann A} (bd : Term σ ((ctxOf (glat s i)).diaIn y).boxIn A a₀) {a : Ann A}
    (t : Term σ (ctxOf (glat s i)) A a)
    (IH : ∀ (K : ℕ) (φ : WFF σ (ctxOf (glat s K)) 0),
      φ.size < ((OutLeg.pos y hy : OutLeg (ctxOf (glat s i))).back hS bd t : WFF σ _ 0).size →
        ((cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s K) φ ↔ φ ∈ (gw hM₀ s).M K))
    (h : (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s i)
      ((OutLeg.pos y hy : OutLeg (ctxOf (glat s i))).back hS bd t : WFF σ _ 0)) :
    ((OutLeg.pos y hy : OutLeg (ctxOf (glat s i))).back hS bd t : WFF σ _ 0) ∈ (gw hM₀ s).M i := by
  have hT := hX.bT (hX.bS hS)
  have hSh : ModalSys.shaped = true := ModalSys.shaped_of_T hT
  by_cases hA : A.diaFree = true
  · exact mem_back_of_sat_diaFreeC hX hS (.pos y hy) hA bd t IH h
  have hsz := BData.size_back_ge hS (.pos y hy) bd t
  change (cmodel hF hM₀ hX).Backs .pos _ _ at h
  rw [interp_ccanon hX (Term.diatm y hy (Term.boxtm bd)) (Model.Env.Agree.refl' _)
    (Ctx.Presented.noProjLast _)] at h
  change cRet hM₀ hX (cTag hM₀ hX .pos _) (cData hM₀ hX .pos _).1 (cData hM₀ hX .pos _).2 _ at h
  rcases h with ⟨-, -, hA' | ⟨hS', i', L, c, ct, a', t', hmem, hdata, htag, hval⟩⟩
  · exact absurd hA' hA
  revert c ct hmem hdata htag
  cases L with
  | nec =>
      intro c ct _ _ htag
      have htag' : cTag hM₀ hX .pos (ctoDom hM₀ hX _ s (cden hM₀ hX s i (Ctx.Le.refl _)
          (Term.diatm y hy (Term.boxtm bd))) (cdefinable_den hX _ _)) = none := htag.symm
      simp [cTag, hSh] at htag'
  | pos =>
      intro c ct
      cases ct with
      | diatm y' hy' u =>
          cases u with
          | boxtm bd' =>
              intro hmem hdata htag
              have hsh : crawShape hT (cden hM₀ hX s i' (Ctx.Le.refl _)
                    (Term.diatm y' hy' (Term.boxtm bd'))) =
                  crawShape hT (cden hM₀ hX s i (Ctx.Le.refl _)
                    (Term.diatm y hy (Term.boxtm bd))) := by
                simp only [cTag, dif_pos hSh] at htag
                exact Option.some.inj htag
              have hann := ann_eq_of_crawShapeL hX hT _ _ hsh
              obtain ⟨rfl, hbd⟩ := Ann.dia.inj hann
              obtain rfl := Ann.box.inj hbd
              obtain ⟨-, hval'⟩ := Sigma.mk.inj_iff.mp hdata
              have hfun := eq_of_heq hval'
              have hraw : cden hM₀ hX s i' (Ctx.Le.refl _) (Term.diatm y' hy' (Term.boxtm bd')) =
                  cden hM₀ hX s i (Ctx.Le.refl _) (Term.diatm y' hy (Term.boxtm bd)) :=
                CRPos.congr_cont (funext fun a₁ => ctoDom_inj hX ((cmodel hF hM₀ hX).nec_inj
                  (funext fun b => congrFun (congrFun hfun a₁) b))) fun _ => rfl
              have hc := ctoDom_congr (hM₀ := hM₀) hX hraw (cdefinable_den hX _ _)
                (cdefinable_den hX _ _)
              have hv : ctoDom hM₀ hX A s (cden hM₀ hX s i' (Ctx.Le.refl _) t')
                    (cdefinable_den hX _ _) =
                  ctoDom hM₀ hX A s (cden hM₀ hX s i (Ctx.Le.refl _) t)
                    (cdefinable_den hX _ _) := by
                rw [hval, interp_ccanon hX t (Model.Env.Agree.refl' _)
                  (Ctx.Presented.noProjLast _)]
              obtain rfl := ann_eq_of_toDomC hX hT _ _ hv
              have hK : i ≤ max i i' := le_max_left _ _
              have hK' : i' ≤ max i i' := le_max_right _ _
              have hmc := (IH _ _ (by
                rw [WFF.size_eqRec]; simp only [VarType.eqRecSize] at hsz ⊢; omega)).mp
                (sat_eqRec_liftC hX hK' hK _ _ hc)
              have hmv := (IH _ _ (by rw [WFF.size_eqRec]; omega)).mp
                (sat_eqRec_liftC hX hK' hK _ _ hv)
              refine (BWorld.mem_lift hK).mpr (BWorld.mem_of_provable (Δ := [_, _, _])
                (fun ψ hψ => by
                  rcases List.mem_cons.mp hψ with rfl | hψ
                  · exact (BWorld.mem_lift hK').mp hmem
                  rcases List.mem_cons.mp hψ with rfl | hψ
                  · exact hmc
                  · rw [List.mem_singleton.mp hψ]; exact hmv)
                ⟨Proof.back_eq hS .pos _ _ _ (Proof.back_eqC hS .pos _ _ _
                  (Proof.lookup List.mem_cons_self)
                  (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))
                  (Proof.lookup (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ List.mem_cons_self)))⟩)

/-! ## The truth lemma -/

/-- ⭐**The truth lemma below a size, at every world and stage.** -/
theorem ctruth_lt (hX : CluFlags) (hNS : ModalSys.BStrong = false) :
    ∀ (n : ℕ) (s : GW hF M₀) (i : ℕ) (φ : WFF σ (ctxOf (glat s i)) 0), φ.size < n →
    ((cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s i) φ ↔ φ ∈ (gw hM₀ s).M i)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, i, φ, hφ => by
      cases φ with
      | atom ρ =>
          change Model.relSat (ccanonEnv hM₀ hX s i) ρ Fin.elim0 ↔ _
          rw [relSat_ccanon hX ρ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)
            Fin.elim0 Fin.elim0 (fun k => k.elim0)]
          change WFF.mono (Ctx.Le.refl _) (.atom ρ) ∈ (gw hM₀ s).M i ↔ _
          rw [WFF.mono_refl]
      | eq t u =>
          change Model.interp (ccanonEnv hM₀ hX s i) t =
            Model.interp (ccanonEnv hM₀ hX s i) u ↔ _
          rw [interp_ccanon hX t (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _),
            interp_ccanon hX u (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)]
          change cden hM₀ hX s i (Ctx.Le.refl _) t = cden hM₀ hX s i (Ctx.Le.refl _) u ↔ _
          rw [cden_var_cls, cden_var_cls, BWorld.cls_eq_iff (le_refl i) (le_refl i)]
          change WFF.eq (Term.mono ((gw hM₀ s).le (le_refl i)) t)
            (Term.mono ((gw hM₀ s).le (le_refl i)) u) ∈ (gw hM₀ s).M i ↔ _
          rw [Term.mono_refl, Term.mono_refl]
      | top => exact ⟨fun _ => ((gw hM₀ s).mcs i).top_mem, fun _ => trivial⟩
      | bot => exact ⟨False.elim, fun h => ((gw hM₀ s).mcs i).bot_not_mem h⟩
      | here hT S t =>
          cases S with
          | diatm x hx bd =>
              exact chere_truth hX hT hx bd t
                (fun K _ u u' => ctruth_lt hX hNS n s K _ (by
                  rw [WFF.size_eqRec]; simp only [WFF.size] at hφ; omega))
      | back hB L c t =>
          cases L with
          | pos =>
              cases c with
              | diatm y hy u =>
                  cases u with
                  | boxtm bd =>
                      obtain ⟨Y, hr⟩ := id hy
                      have hle : ((OutLeg.pos y hy : OutLeg (ctxOf (glat s i))).back hB bd t :
                          WFF σ _ 0).size ≤ n := Nat.le_of_lt_succ hφ
                      refine ⟨fun h => mem_back_of_sat_posC hX hB hy bd t (fun K ψ hψ =>
                        ctruth_lt hX hNS n s K ψ (Nat.lt_of_lt_of_le hψ hle)) h, fun hm => ?_⟩
                      have hdia : (OutLeg.pos y hy : OutLeg (ctxOf (glat s i))).dia
                          (.top : WFF σ _ 0) ∈ (gw hM₀ s).M i :=
                        BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by
                          rw [List.mem_singleton.mp hψ]
                          exact hm)
                          ⟨Proof.back_ne hB (.pos y hy) bd t (Proof.lookup List.mem_cons_self)⟩
                      have hsz := BData.size_back_ge hB (.pos y hy) bd t
                      have hs3 := BData.size_dia_top (σ := σ) (OutLeg.pos y hy :
                        OutLeg (ctxOf (glat s i)))
                      obtain ⟨b, -⟩ := (OutLeg.sat_dia _ (.pos y hy) _).mp
                        ((ctruth_lt hX hNS n s i _ (by omega)).mpr hdia)
                      change (cmodel hF hM₀ hX).Backs .pos _ _
                      rw [interp_ccanon hX (Term.diatm y hy (Term.boxtm bd))
                        (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _),
                        interp_ccanon hX t (Model.Env.Agree.refl' _)
                          (Ctx.Presented.noProjLast _)]
                      exact cRet_of_mem_pos hM₀ hX hB s i hr bd t hm
                        ⟨b.1, (ccanon_mem_iff hX s i hy.choose_spec b.1).mp b.2⟩
          | nec =>
              cases c with
              | boxtm u =>
                  cases u with
                  | boxtm bd =>
                      refine ⟨fun h => mem_back_of_sat_necC hX hB bd t (fun K ψ hψ =>
                        ctruth_lt hX hNS n s K ψ (Nat.lt_of_lt_of_le hψ (Nat.le_of_lt_succ hφ)))
                        h, fun hm => ?_⟩
                      change (cmodel hF hM₀ hX).Backs .nec _ _
                      rw [interp_ccanon hX (Term.boxtm (Term.boxtm bd))
                        (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _),
                        interp_ccanon hX t (Model.Env.Agree.refl' _)
                          (Ctx.Presented.noProjLast _)]
                      exact cRet_of_mem_nec hM₀ hX hB s i bd t hm
      | retS hB _ _ _ => exact absurd (hNS.symm.trans hB) (by decide)
      | retxS hB _ _ _ _ _ => exact absurd (hNS.symm.trans hB) (by decide)
      | and φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change _ ∧ _ ↔ _
          rw [ctruth_lt hX hNS n s i φ h₁, ctruth_lt hX hNS n s i ψ h₂,
            ((gw hM₀ s).mcs i).and_mem_iff]
      | or φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change _ ∨ _ ↔ _
          rw [ctruth_lt hX hNS n s i φ h₁, ctruth_lt hX hNS n s i ψ h₂,
            ((gw hM₀ s).mcs i).or_mem_iff]
      | imp φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (_ → _) ↔ _
          rw [ctruth_lt hX hNS n s i φ h₁, ctruth_lt hX hNS n s i ψ h₂,
            ((gw hM₀ s).mcs i).imp_mem_iff]
      | all A ψ =>
          have hψ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (∀ o : (cframe hF hM₀ hX).Dom A s,
            (cmodel hF hM₀ hX).sat ((ccanonEnv hM₀ hX s i).extend (.bnd 0) o) ψ) ↔ _
          constructor
          · intro hsat
            by_contra hnot
            obtain ⟨i', hi, a, t, hmem⟩ := (gw hM₀ s).allW (((gw hM₀ s).mcs i).neg_mem_iff.mpr hnot)
            have hs₁ := (Model.sat_mono (Model.Env.extend_agree (ccanonEnv_le hX s hi) (.bnd 0)
              (Model.interp (ccanonEnv hM₀ hX s i') t)) ψ).mpr (hsat _)
            have hs₂ := (Model.sat_instantiate (ccanonEnv hM₀ hX s i')
              (Ctx.Presented.noProjLast _) Ctx.NoSlots.slots t _).mpr hs₁
            have hs₃ := (ctruth_lt hX hNS n s i' _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mp hs₂
            exact (((gw hM₀ s).mcs i').neg_mem_iff.mp hmem) hs₃
          · intro hmem o
            obtain ⟨i', a, t', ht'⟩ := cdefinable_fromDom hM₀ hX A s o
            have hK : i ≤ i ⊔ i' := le_sup_left
            have hK' : i' ≤ i ⊔ i' := le_sup_right
            have hinst : WFF.instantiate Ctx.NoSlots.slots ((gw hM₀ s).liftT hK' t')
                (WFF.mono (((gw hM₀ s).le hK).insert (.bnd 0) A) ψ) ∈ (gw hM₀ s).M (i ⊔ i') :=
              BWorld.mem_of_provable
                (Δ := [WFF.all A (WFF.mono (((gw hM₀ s).le hK).insert (.bnd 0) A) ψ)])
                (fun χ hχ => by
                  rw [List.mem_singleton.mp hχ]
                  exact (BWorld.mem_lift hK).mp hmem)
                ⟨Proof.all_elim A ((gw hM₀ s).liftT hK' t') (Proof.lookup List.mem_cons_self)⟩
            have hs := (ctruth_lt hX hNS n s (i ⊔ i') _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mpr hinst
            have hs₁ := (Model.sat_instantiate (ccanonEnv hM₀ hX s (i ⊔ i'))
              (Ctx.Presented.noProjLast _) Ctx.NoSlots.slots ((gw hM₀ s).liftT hK' t') _).mp hs
            rw [cinterp_lift hX ht' hK'] at hs₁
            exact (Model.sat_mono (Model.Env.extend_agree (ccanonEnv_le hX s hK) (.bnd 0) o)
              ψ).mp hs₁
      | ex A ψ =>
          have hψ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (∃ o : (cframe hF hM₀ hX).Dom A s,
            (cmodel hF hM₀ hX).sat ((ccanonEnv hM₀ hX s i).extend (.bnd 0) o) ψ) ↔ _
          constructor
          · rintro ⟨o, hsat⟩
            obtain ⟨i', a, t', ht'⟩ := cdefinable_fromDom hM₀ hX A s o
            have hK : i ≤ i ⊔ i' := le_sup_left
            have hK' : i' ≤ i ⊔ i' := le_sup_right
            have hs₁ := (Model.sat_mono (Model.Env.extend_agree (ccanonEnv_le hX s hK) (.bnd 0) o)
              ψ).mpr hsat
            rw [← cinterp_lift hX ht' hK'] at hs₁
            have hs₂ := (Model.sat_instantiate (ccanonEnv hM₀ hX s (i ⊔ i'))
              (Ctx.Presented.noProjLast _) Ctx.NoSlots.slots ((gw hM₀ s).liftT hK' t') _).mpr hs₁
            have hmemK := (ctruth_lt hX hNS n s (i ⊔ i') _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mp hs₂
            exact (BWorld.mem_lift hK).mpr (BWorld.mem_of_provable
              (Δ := [WFF.instantiate Ctx.NoSlots.slots ((gw hM₀ s).liftT hK' t')
                (WFF.mono (((gw hM₀ s).le hK).insert (.bnd 0) A) ψ)])
              (fun χ hχ => by
                rw [List.mem_singleton.mp hχ]
                exact hmemK)
              ⟨Proof.ex_intro A ((gw hM₀ s).liftT hK' t') (Proof.lookup List.mem_cons_self)⟩)
          · intro hmem
            obtain ⟨i', hi, a, t, hmem'⟩ := (gw hM₀ s).exW_term hmem
            refine ⟨Model.interp (ccanonEnv hM₀ hX s i') t, ?_⟩
            have hs := (ctruth_lt hX hNS n s i' _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mpr hmem'
            have hs₁ := (Model.sat_instantiate (ccanonEnv hM₀ hX s i') (Ctx.Presented.noProjLast _)
              Ctx.NoSlots.slots t _).mp hs
            exact (Model.sat_mono (Model.Env.extend_agree (ccanonEnv_le hX s hi) (.bnd 0) _)
              ψ).mp hs₁
      | box χ =>
          have hχs : χ.size < n := by simp only [WFF.size] at hφ; omega
          have hpath := box_pathO_iff hX.five hX.fourS hX.fourSW hM₀ (rpath s)
            (groot hF M₀) s (rpath_eq s) i χ
          change (∀ a : CAcc hF M₀,
            (cmodel hF hM₀ hX).sat ((ccanonEnv hM₀ hX s i).boxPush a) χ) ↔ _
          constructor
          · intro hsat
            by_contra hnot
            have hn' : WFF.box (preWP (rpre hX hM₀ s i) χ) ∉
                (gw hM₀ (groot hF M₀)).M (rstg s i) := fun h => hnot (hpath.mp h)
            obtain ⟨t, ⟨c, hc⟩, -, hneg⟩ := glex hM₀ (groot hF M₀) (rstg s i) _ hn'
            have hR : GR (groot hF M₀) t := ⟨[c], pathOk_cons, hc⟩
            have h1 := (sat_boxPush_c hX s i ⟨t, ⟨hR⟩⟩ [c] hc pathOk_cons (pathOf_of hR hc)
              χ).mp (hsat ⟨t, ⟨hR⟩⟩)
            have h2 := (ctruth_lt hX hNS n t _ _ (by
              rw [size_pTrW, size_preWP (hM₀ := hM₀) hX]; exact hχs)).mp h1
            exact ((gw hM₀ t).mcs _).neg_mem_iff.mp hneg h2
          · intro hmem a
            refine (sat_boxPush_c hX s i a (pathOf a.2.down) (pathOf_eq a.2.down)
              (pathOf_ok a.2.down) rfl χ).mpr ?_
            exact (ctruth_lt hX hNS n a.1 _ _ (by
              rw [size_pTrW, size_preWP (hM₀ := hM₀) hX]; exact hχs)).mpr
              (box_mem_path hM₀ (groot hF M₀) a.1 _ (pathOf_eq a.2.down) (pathOf_ok a.2.down)
                (rstg s i) _ (hpath.mpr hmem))
      | dia x hx χ =>
          have hχs : χ.size < n := by simp only [WFF.size] at hφ; omega
          change (∃ (X : VarType) (h : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
            (a : ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s i).ref x h)).1),
              (cmodel hF hM₀ hX).sat ((ccanonEnv hM₀ hX s i).diaPush x h a) χ) ↔ _
          have IH : CTruthBelow hF hM₀ hX n := fun t j φ hφ => ctruth_lt hX hNS n t j φ hφ
          constructor
          · rintro ⟨X, h, a, hsat⟩
            by_contra hnot
            have hpath := dia_pathO_iff hX.five hX.fourS hX.fourSW hM₀
              (rpath s) (groot hF M₀) s (rpath_eq s) i h χ
            have hnot' : ¬ WFF.dia (rorig s x) (rorig_ref hX hM₀ s i ⟨X, h⟩)
                (preWPX (rpre hX hM₀ s i) h χ) ∈
                (gw hM₀ (groot hF M₀)).M (rstg s i) := fun hd => hnot (hpath.mp hd)
            have hbx : WFF.boxx (rorig s x) (rorig_ref hX hM₀ s i ⟨X, h⟩)
                (preWPX (rpre hX hM₀ s i) h χ).neg ∈
                (gw hM₀ (groot hF M₀)).M (rstg s i) :=
              BWorld.mem_of_provable (Δ := [(WFF.dia (rorig s x) (rorig_ref hX hM₀ s i ⟨X, h⟩)
                  (preWPX (rpre hX hM₀ s i) h χ)).neg])
                (fun ψ hψ => by
                  rw [List.mem_singleton.mp hψ]
                  exact ((gw hM₀ (groot hF M₀)).mcs _).neg_mem_iff.mpr hnot')
                ⟨Proof.boxx_neg_of_not_dia (Γ := (gw hM₀ (groot hF M₀)).ctx (rstg s i)) _ _ _⟩
            have hg := (ccanon_mem_iff hX s i h a.1).mp a.2
            by_cases hrl : (gw hM₀ a.1.1).Realised (kw (groot hF M₀) a.1.1 (pathOf a.1.2.down)
                (pathOf_eq a.1.2.down) (rorig s x))
            · exact cdia_real_not_boxx hX hrl.T IH s i h a hrl χ hχs hsat hbx
            obtain ⟨-, hm⟩ := Or.resolve_left hg hrl
            have h1 := (sat_diaPush_c hX s i h a _ (pathOf_eq a.1.2.down) rfl hrl hm χ).mp hsat
            have h2 := (ctruth_lt hX hNS n a.1.1 _ _ (by
              rw [size_pTrXW, size_preWPX (hM₀ := hM₀) hX]; exact hχs)).mp h1
            have hneg := boxx_mem_path (hM₀ := hM₀) (groot hF M₀) a.1.1 _ (pathOf_eq a.1.2.down)
              (rstg s i) (rorig s x) _ hm _ hbx
            rw [pTrXW_neg] at hneg
            exact ((gw hM₀ a.1.1).mcs _).neg_mem_iff.mp hneg h2
          · intro hmem
            obtain ⟨X, h⟩ := id hx
            have hpath := dia_pathO_iff hX.five hX.fourS hX.fourSW hM₀
              (rpath s) (groot hF M₀) s (rpath_eq s) i h χ
            by_cases hT : ModalSys.T = true
            · obtain ⟨a, ha⟩ := cdia_sat_child hX hT IH s i h χ hχs (hpath.mpr hmem)
              exact ⟨X, h, a, ha⟩
            have hnT : ModalSys.T = false := Bool.eq_false_iff.mpr hT
            obtain ⟨t, ⟨c, hc⟩, hk, -, -, hm'⟩ := glexX hM₀ (groot hF M₀) (rstg s i) (rorig s x) X
              (rpre hX hM₀ s i x _ h rfl) _ (hpath.mpr hmem)
            have hR : GR (groot hF M₀) t := ⟨[c], pathOk_cons, hc⟩
            have hmt : (⟨t, ⟨hR⟩⟩ : CAcc hF M₀) ∈
                ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s i).ref x h)).1 :=
              (ccanon_mem_iff hX s i h _).mpr (.inr ⟨hnT,
                inExt_pathOf hR (show InExt (groot hF M₀) t [c] hc (rorig s x) from hk)⟩)
            exact ⟨X, h, ⟨_, hmt⟩, (sat_diaPush_c hX s i h ⟨_, hmt⟩ [c] hc (pathOf_of hR hc)
              ((gw hM₀ t).not_realised hnT) hk χ).mpr ((ctruth_lt hX hNS n t _ _ (by
                rw [size_pTrXW, size_preWPX (hM₀ := hM₀) hX]; exact hχs)).mpr hm')⟩

/-- ⭐**The truth lemma** for the cluster model. -/
theorem ctruth (hX : CluFlags) (hNS : ModalSys.BStrong = false) (s : GW hF M₀) (i : ℕ)
    (φ : WFF σ (ctxOf (glat s i)) 0) :
    (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s i) φ ↔ φ ∈ (gw hM₀ s).M i :=
  ctruth_lt hX hNS (φ.size + 1) s i φ (Nat.lt_succ_self _)

end GArrow

end V12M
