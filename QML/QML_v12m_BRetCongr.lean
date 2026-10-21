import QML.QML_v12m_BTruthS
import QML.QML_v12m_BInd

/-!
# QML v12m — B's canonical model: "comes back as" is a congruence (strong B)

`Model.IndInvariant.ret` asks the canonical `Ret` to be preserved by a hole term (`map`) and by
pairing two carriers' data (`pair`).  The canonical `Ret` (`BData.Ret`) is a round trip at a
`◇`-free content or what a `Back` atom of the theory says.

* *Round trips* map to round trips (`ind_map`): a hole term over a `◇`-free type has a `◇`-free
  type (`Term.diaFree_of`).
* *Atoms* map by the rule `back_beta`: the new atom is in the theory, so true (the truth lemma),
  and its data is the mapped data (`OutLeg.sat_back`, `interp_holeRead`).
* *Pairs*: each component is an atom (`toAtom`: a carrier's round trip at a `◇`-free content is
  true, so its atom is in the theory), the two atoms have one leg (`leg_unique`: a nonempty leg
  is all arrows out or one witness's extent, never both, never two witnesses'), and `back_pair`
  pairs them.
-/

namespace V12M

variable [ModalSys]

/-! ## `◇`-free contexts -/

/-- A context whose declared items are all `◇`-free. -/
def Ctx.DiaFree (Γ : Ctx) : Prop := ∀ v T, Γ v = some T → T.diaFree = true

theorem VarType.diaFree_step {T U : VarType} (hT : T.diaFree = true) {s : Step}
    (h : T.step s = some U) : U.diaFree = true := by
  cases T <;> cases s <;> simp only [VarType.step, reduceCtorEq] at h
  all_goals first
    | (obtain rfl := Option.some.inj h; simp_all [VarType.diaFree])
    | (split_ifs at h; obtain rfl := Option.some.inj h; simp_all [VarType.diaFree])

theorem Ctx.DiaFree.ref {Γ : Ctx} (h : Γ.DiaFree) : ∀ {v : VarSymb} {T : VarType},
    Γ.ref v = some T → T.diaFree = true
  | .root _, _, hv => h _ _ hv
  | .step v s, _, hv => by
      simp only [Ctx.ref] at hv
      split_ifs at hv
      · obtain ⟨U, hU, hs⟩ := Option.bind_eq_some_iff.mp hv
        exact VarType.diaFree_step (h.ref hU) hs
      · exact h _ _ hv

theorem Ctx.DiaFree.boxIn {Γ : Ctx} (h : Γ.DiaFree) : Γ.boxIn.DiaFree := by
  intro v T hv
  match v with
  | .step u .box =>
      change (if ModalSys.keepOnly then none else
        match Γ.ref u with | some (.VTypeBox A) => some A | _ => none) = some T at hv
      split_ifs at hv
      cases hr : Γ.ref u with
      | none => rw [hr] at hv; cases hv
      | some U =>
          rw [hr] at hv
          cases U <;> cases hv
          exact (h.ref hr : (VarType.VTypeBox _).diaFree = true)
  | .step u .keep =>
      change (if ModalSys.Four then
        match Γ.ref u with | some (.VTypeBox A) => some (.VTypeBox A) | _ => none
        else none) = some T at hv
      split_ifs at hv
      cases hr : Γ.ref u with
      | none => rw [hr] at hv; cases hv
      | some U =>
          rw [hr] at hv
          cases U <;> cases hv
          exact (h.ref hr : (VarType.VTypeBox _).diaFree = true)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv
  | .step _ .dia => cases hv

omit [ModalSys] in
theorem Ctx.DiaFree.insert {Γ : Ctx} (h : Γ.DiaFree) (r : Root) {T : VarType}
    (hT : T.diaFree = true) : (Γ.insert r T).DiaFree := by
  intro v U hv
  simp only [Ctx.insert] at hv
  split_ifs at hv
  · obtain rfl := Option.some.inj hv
    exact hT
  · exact h _ _ hv

omit [ModalSys] in
theorem Ctx.diaFree_empty : Ctx.empty.DiaFree := fun _ _ h => nomatch h

/-- ⭐A term over a `◇`-free context has a `◇`-free type: `◇` types come only from witnesses. -/
theorem Term.diaFree_of {σ : Signature} : ∀ {Γ : Ctx} {T : VarType} {a : Ann T},
    Γ.DiaFree → Term σ Γ T a → T.diaFree = true
  | _, _, _, _, .var _ _ => rfl
  | _, _, _, _, .func _ => rfl
  | _, _, _, _, .unit => rfl
  | _, _, _, h, .pair s t => VarType.diaFree_prod (Term.diaFree_of h s) (Term.diaFree_of h t)
  | _, _, _, h, .boxtm t => VarType.diaFree_box (Term.diaFree_of h.boxIn t)
  | _, _, _, h, .diatm _ ⟨_, hx⟩ _ => absurd (h.ref hx) (by simp [VarType.diaFree])

/-- A hole term over a `◇`-free slot has a `◇`-free type. -/
theorem Term.diaFree_hole {σ : Signature} {A B : VarType} (hA : A.diaFree = true) {b : Ann B}
    (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) : B.diaFree = true :=
  Term.diaFree_of (Ctx.diaFree_empty.insert _ hA) s

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

namespace BData

variable {B : BData σ}

/-- ⭐**An atom's data is its body's** at the canonical environment: the carrier `□□bd` or
    `◇_y□bd` of a `Back` atom has round-trip data the leg's arrows with `bd` read at their far
    end (as `OutLeg.isCarrierData`). -/
theorem atom_data (hS : ModalSys.BStrong = true) {s : B.W} {i : ℕ} {L : BLeg} {A : VarType}
    {c : Ann (L.carrier A)} (ct : Term σ ((B.w s).ctx i) (L.carrier A) c) {a : Ann A}
    (t : Term σ ((B.w s).ctx i) A a) {S : Set (B.frame.Acc s)}
    {val : (x : S) → (y : B.frame.Acc x.1.1) → B.frame.Dom A y.1}
    (hdata : B.cData L (B.toDom _ s (B.rden s i (Ctx.Le.refl _) ct) (definable_rden _ _)) =
      ⟨S, val⟩) :
    ∃ (O : OutLeg ((B.w s).ctx i)) (a₀ : Ann A) (bd : Term σ O.view.boxIn A a₀),
      (WFF.back hS L ct t : WFF σ _ 0) = O.back hS bd t ∧
      (⟨S, val⟩ : Σ S : Set (B.frame.Acc s), (x : S) → (y : B.frame.Acc x.1.1) →
        B.frame.Dom A y.1) =
        ⟨O.legSet (B.canonEnv s i),
          fun x y => Model.interp ((O.pushS (B.canonEnv s i) x).boxPush y) bd⟩ := by
  rw [← interp_canon ct (Model.Env.Agree.refl' _)] at hdata
  cases L with
  | necW hW => exact (ModalSys.NoFour.absurdW hW).elim
  | posW hW => exact (ModalSys.NoFour.absurdW hW).elim
  | nec =>
      match ct, hdata with
      | .boxtm (.boxtm bd), hdata =>
          refine ⟨.nec, _, bd, rfl, hdata.symm.trans ?_⟩
          refine Sigma.ext rfl (heq_of_eq (funext fun x => funext fun y => ?_))
          change B.model.necEval (B.model.necEval (Model.interp (B.canonEnv s i)
            (Term.boxtm (Term.boxtm bd)) : B.model.frame.Nec (.VTypeBox A) s) x.1) y = _
          rw [Model.box_beta (M := B.model) (B.canonEnv s i) (Term.boxtm bd) x.1,
            Model.box_beta (M := B.model) ((B.canonEnv s i).boxPush x.1) bd y]
          rfl
  | pos =>
      match ct, hdata with
      | .diatm y hy (.boxtm bd), hdata =>
          refine ⟨.pos y hy, _, bd, rfl, hdata.symm.trans ?_⟩
          change (⟨(B.model.posEval
              (Model.interp (B.canonEnv s i) (Term.diatm y hy (Term.boxtm bd)))).1,
            fun x z => B.model.necEval ((B.model.posEval
              (Model.interp (B.canonEnv s i) (Term.diatm y hy (Term.boxtm bd)))).2 x) z⟩ :
              Σ S : Set (B.frame.Acc s), (x : S) → (y : B.frame.Acc x.1.1) → B.frame.Dom A y.1) = _
          rw [Model.dia_beta (M := B.model) (B.canonEnv s i) hy hy.choose_spec (Term.boxtm bd)]
          refine Sigma.ext rfl (heq_of_eq (funext fun x => funext fun z => ?_))
          exact Model.box_beta (M := B.model) _ bd z

/-- ⭐**A nonempty leg has one name**: every arrow out is never a witness's extent
    (`univ_ne_extent`; a world with an arrow has a network one, by `T` at the own arrow), and two
    witnesses' extents meet only if the witnesses are one: they share a network arrow (a realised
    witness labels one, `exists_kd_of_realised`), which has one label. -/
theorem leg_unique {s : B.W} {i : ℕ}
    {O O' : OutLeg ((B.w s).ctx i)} (hne : Nonempty (O.legSet (B.canonEnv s i)))
    (h : O.legSet (B.canonEnv s i) = O'.legSet (B.canonEnv s i)) : O = O' := by
  obtain ⟨⟨a, ha⟩⟩ := hne
  have harr : ∃ k, B.R s k := by
    rcases a.2.down with hR | ⟨hT, -⟩
    · exact ⟨a.1, hR⟩
    · exact exists_R_of_T hT s
  cases O with
  | nec =>
      cases O' with
      | nec => rfl
      | pos y hy =>
          exact absurd (h.trans (canonEnv_extent s i hy.choose_spec)) (univ_ne_extent harr y)
  | pos y hy =>
      cases O' with
      | nec =>
          exact absurd ((h.symm.trans (canonEnv_extent s i hy.choose_spec)))
            (univ_ne_extent harr y)
      | pos y' hy' =>
          have hext : B.extent s y = B.extent s y' :=
            (canonEnv_extent s i hy.choose_spec).symm.trans
              (h.trans (canonEnv_extent s i hy'.choose_spec))
          have h₁ : a ∈ B.extent s y := canonEnv_extent s i hy.choose_spec ▸ ha
          obtain ⟨t₀, X, hX⟩ : ∃ t₀ X, B.lb s t₀ y = some X := by
            rcases h₁ with ⟨X, hX⟩ | ⟨-, hr⟩
            · exact ⟨a.1, X, hX⟩
            · obtain ⟨t₀, ht₀⟩ := exists_kd_of_realised hr hy.choose_spec
              exact ⟨t₀, _, B.kd_lb ht₀⟩
          obtain rfl := eq_of_extent_eq hX hext
          rfl

section Congr

variable (hST : ∀ hS : ModalSys.BStrong = true, B.StrongTruth hS)
include hST

/-- ⭐**Canonical `Ret` is preserved by a hole term**: a round trip by `ind_map` (the type stays
    `◇`-free, `Term.diaFree_hole`); an atom by `back_beta`, whose new atom is true (the truth
    lemma) with the mapped data (`OutLeg.sat_back`, `interp_holeRead`). -/
theorem ret_map {A C : VarType} {b : Ann C}
    (sh : Term σ (Ctx.empty.insert (.bnd 0) A) C b) {s : B.W} {S : Set (B.frame.Acc s)}
    {val : (x : S) → (y : B.frame.Acc x.1.1) → B.frame.Dom A y.1} {o : B.frame.Dom A s}
    (h : B.Ret S val o) :
    B.Ret S (fun x y => B.model.holeVal sh (val x y)) (B.model.holeVal sh o) := by
  rcases h with ⟨hA, hne, hrt⟩ | ⟨hS', i, L, c, ct, a, t, hmem, hdata, rfl⟩
  · exact Or.inl ⟨Term.diaFree_hole hA sh, hne, fun x => (hrt x).imp fun _ hI => ind_map sh hI⟩
  obtain ⟨O, a₀, bd, hO, hSV⟩ := atom_data hS' ct t hdata
  cases hSV
  rw [hO] at hmem
  have hm2 : (O.back hS' (Term.holeRead bd sh) (Term.holeRead t sh) : WFF σ _ 0) ∈
      (B.w s).M i :=
    BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hmem)
      ⟨Proof.back_beta hS' O .nec trivial bd t sh (Proof.lookup List.mem_cons_self)⟩
  have hsat := retD_all.mp ((OutLeg.sat_back hS' _ O _ _).mp ((truth hST s i _).mpr hm2))
  have hval : (fun (x : O.legSet (B.canonEnv s i)) (y : B.model.frame.Acc x.1.1) =>
      Model.interp ((O.pushS (B.canonEnv s i) x).boxPush y) (Term.holeRead bd sh)) =
      fun x y => B.model.holeVal sh (Model.interp ((O.pushS (B.canonEnv s i) x).boxPush y) bd) := by
    funext x y
    exact Model.interp_holeRead (Ctx.noProjLast_boxIn _) _ bd sh
  rw [hval, Model.interp_holeRead (noProjLast s i), interp_canon t (Model.Env.Agree.refl' _)]
    at hsat
  exact hsat

/-- ⭐**A carrier's `Ret` is an atom of the theory**: an atom already, or a round trip at a
    `◇`-free content, whose carrier and value are denotable and whose atom is then true, so in the
    theory (the truth lemma). -/
theorem toAtom (hS : ModalSys.BStrong = true) {A : VarType} {s : B.W} {S : Set (B.frame.Acc s)}
    {val : (x : S) → (y : B.frame.Acc x.1.1) → B.frame.Dom A y.1} {o : B.frame.Dom A s}
    (hc : B.model.IsCarrierData (.all S val)) (h : B.Ret S val o) :
    ∃ (i : ℕ) (L : BLeg) (c : Ann (L.carrier A)) (ct : Term σ ((B.w s).ctx i) (L.carrier A) c)
      (a : Ann A) (t : Term σ ((B.w s).ctx i) A a),
      WFF.back hS L ct t ∈ (B.w s).M i ∧
      B.cData L (B.toDom _ s (B.rden s i (Ctx.Le.refl _) ct) (definable_rden _ _)) = ⟨S, val⟩ ∧
      B.toDom A s (B.rden s i (Ctx.Le.refl _) t) (definable_rden _ _) = o := by
  rcases h with h₀ | ⟨_, h⟩
  · obtain ⟨L, c, hcd⟩ := hc
    obtain ⟨i₁, c₁, ct, hct⟩ := B.definable_fromDom _ s c
    obtain ⟨i₂, a₂, t, ht⟩ := B.definable_fromDom _ s o
    have h₁ : i₁ ≤ max i₁ i₂ := le_max_left _ _
    have h₂ : i₂ ≤ max i₁ i₂ := le_max_right _ _
    have ec : B.toDom _ s (B.rden s _ (Ctx.Le.refl _) (Term.mono ((B.w s).le h₁) ct))
        (definable_rden _ _) = c :=
      (toDom_congr ((rden_lift h₁ ct).trans hct) _ _).trans (B.toDom_fromDom _ s c)
    have et : B.toDom _ s (B.rden s _ (Ctx.Le.refl _) (Term.mono ((B.w s).le h₂) t))
        (definable_rden _ _) = o :=
      (toDom_congr ((rden_lift h₂ t).trans ht) _ _).trans (B.toDom_fromDom _ s o)
    have hcd' : B.cData L c = ⟨S, val⟩ := by
      cases L with
      | necW hW => exact (ModalSys.NoFour.absurdW hW).elim
      | posW hW => exact (ModalSys.NoFour.absurdW hW).elim
      | _ => exact Frame.RTData.all_inj hcd
    refine ⟨max i₁ i₂, L, c₁, Term.mono ((B.w s).le h₁) ct, a₂, Term.mono ((B.w s).le h₂) t,
      (truth hST s _ _).mp ?_, by rw [ec, hcd'], et⟩
    change B.model.Backs L _ _
    rw [backs_iff, interp_canon _ (Model.Env.Agree.refl' _),
      interp_canon _ (Model.Env.Agree.refl' _), ec, et, hcd']
    exact Or.inl h₀
  · exact h

/-- ⭐**Canonical `Ret` is preserved by pairing carriers' data**: both are atoms (`toAtom`), at
    a common stage, of one leg (`leg_unique`), so `back_pair` pairs them and the paired atom is
    true with the paired data. -/
theorem ret_pair (hS : ModalSys.BStrong = true) {A C : VarType} {s : B.W}
    {S : Set (B.frame.Acc s)} {val : (x : S) → (y : B.frame.Acc x.1.1) → B.frame.Dom A y.1}
    {val' : (x : S) → (y : B.frame.Acc x.1.1) → B.frame.Dom C y.1} {o : B.frame.Dom A s}
    {o' : B.frame.Dom C s} (hc : B.model.IsCarrierData (.all S val))
    (hc' : B.model.IsCarrierData (.all S val'))
    (h : B.Ret S val o) (h' : B.Ret S val' o') :
    B.Ret (A := .VTypeProd A C) S (fun x y => ((val x y, val' x y) :
      B.frame.Dom (.VTypeProd A C) y.1)) ((o, o') : B.frame.Dom (.VTypeProd A C) s) := by
  have hne : Nonempty S := (B.ret_fwd hS h).1
  obtain ⟨i, L, c, ct, a, t, hm, hd, rfl⟩ := toAtom hST hS hc h
  obtain ⟨i', L', c', ct', a', t', hm', hd', rfl⟩ := toAtom hST hS hc' h'
  have hK : i ≤ max i i' := le_max_left _ _
  have hK' : i' ≤ max i i' := le_max_right _ _
  have hmK : (WFF.back hS L (Term.mono ((B.w s).le hK) ct) (Term.mono ((B.w s).le hK) t) :
      WFF σ _ 0) ∈ (B.w s).M (max i i') := (BWorld.mem_lift hK).mp hm
  have hmK' : (WFF.back hS L' (Term.mono ((B.w s).le hK') ct') (Term.mono ((B.w s).le hK') t') :
      WFF σ _ 0) ∈ (B.w s).M (max i i') := (BWorld.mem_lift hK').mp hm'
  have hdK : B.cData L (B.toDom _ s (B.rden s _ (Ctx.Le.refl _) (Term.mono ((B.w s).le hK) ct))
      (definable_rden _ _)) = ⟨S, val⟩ := by
    rw [toDom_congr (rden_lift hK ct) _ (definable_rden _ _)]
    exact hd
  have hdK' : B.cData L' (B.toDom _ s (B.rden s _ (Ctx.Le.refl _)
      (Term.mono ((B.w s).le hK') ct')) (definable_rden _ _)) = ⟨S, val'⟩ := by
    rw [toDom_congr (rden_lift hK' ct') _ (definable_rden _ _)]
    exact hd'
  obtain ⟨O, a₀, bd, hO, hSV⟩ := atom_data hS _ (Term.mono ((B.w s).le hK) t) hdK
  obtain ⟨O', a₀', bd', hO', hSV'⟩ := atom_data hS _ (Term.mono ((B.w s).le hK') t') hdK'
  have hlS : S = O.legSet (B.canonEnv s (max i i')) := congrArg Sigma.fst hSV
  have hlS' : S = O'.legSet (B.canonEnv s (max i i')) := congrArg Sigma.fst hSV'
  obtain rfl : O = O' := leg_unique (hlS ▸ hne) (hlS.symm.trans hlS')
  rw [hO] at hmK
  rw [hO'] at hmK'
  have hm2 : (O.back hS (Term.pair bd bd')
      (Term.pair (Term.mono ((B.w s).le hK) t) (Term.mono ((B.w s).le hK') t')) : WFF σ _ 0) ∈
        (B.w s).M (max i i') :=
    BWorld.mem_of_provable (Δ := [_, _]) (fun ψ hψ => by
      rcases List.mem_pair.mp hψ with rfl | rfl
      · exact hmK
      · exact hmK')
      ⟨Proof.back_pair hS O .nec trivial bd _ bd' _ (Proof.lookup List.mem_cons_self)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  have hsat := retD_all.mp ((OutLeg.sat_back hS _ O _ _).mp ((truth hST s _ _).mpr hm2))
  cases hSV
  obtain ⟨-, hv'⟩ := Sigma.mk.inj hSV'
  cases eq_of_heq hv'
  have e1 : Model.interp (B.canonEnv s (max i i')) (Term.mono ((B.w s).le hK) t) =
      B.toDom A s (B.rden s i (Ctx.Le.refl _) t) (definable_rden _ _) :=
    (interp_canon _ (Model.Env.Agree.refl' _)).trans (toDom_congr (rden_lift hK t) _ _)
  have e2 : Model.interp (B.canonEnv s (max i i')) (Term.mono ((B.w s).le hK') t') =
      B.toDom C s (B.rden s i' (Ctx.Le.refl _) t') (definable_rden _ _) :=
    (interp_canon _ (Model.Env.Agree.refl' _)).trans (toDom_congr (rden_lift hK' t') _ _)
  have hv : Model.interp (B.canonEnv s (max i i'))
      (Term.pair (Term.mono ((B.w s).le hK) t) (Term.mono ((B.w s).le hK') t')) =
      ((B.toDom A s (B.rden s i (Ctx.Le.refl _) t) (definable_rden _ _),
        B.toDom C s (B.rden s i' (Ctx.Le.refl _) t') (definable_rden _ _)) :
          B.frame.Dom (.VTypeProd A C) s) := Prod.ext e1 e2
  rw [hv] at hsat
  exact hsat

end Congr

/-- ⭐⭐**Canonical "comes back as" is a congruence** (strong B): `Model.RetCongr`. -/
theorem retCongr (hS : ModalSys.BStrong = true)
    (hST : ∀ hS : ModalSys.BStrong = true, B.StrongTruth hS) : B.model.RetCongr where
  map := by
    rintro _ _ _ sh _ _ _ ⟨S, val, rfl, h⟩
    exact ⟨S, _, rfl, ret_map hST sh h⟩
  pair := by
    rintro _ _ _ _ _ _ _ _ _ hc hc' ⟨S, val, e, h⟩ ⟨S', val', e', h'⟩
    cases e
    cases e'
    exact ⟨_, _, rfl, ret_pair hST hS hc hc' h h'⟩

end BData

section Limit

variable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} {hS : ModalSys.BStrong = true}
  (C : StrongChain hS M₀)

/-- ⭐⭐**The limit of a strong chain is a model proper**. -/
theorem bdataS_indInvariant (hB : ModalSys.B = true) :
    (bdataS C).model.IndInvariant :=
  BData.indInvariant (bdataS_strongTruth C hB)
    fun hS' => BData.retCongr hS' (bdataS_strongTruth C hB)

end Limit

end BArrow

end V12M
