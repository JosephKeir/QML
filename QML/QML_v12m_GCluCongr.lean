import QML.QML_v12m_GCluTruth
import QML.QML_v12m_BRetCongr

/-!
# QML v12m — 5 on the growing tree: "comes back as" is a congruence (strong B)

`Model.IndInvariant.ret` on the cluster, after the truth lemma, which supplies the laws' atoms'
`Ret` whole: each law builds an atom of the theory and reads it true.

* `Model.carrier_leg`: a carrier term's data and tag are its leg's (`BData.atom_data`).
* `witness_of_label`, `leg_of_label`: one label is one witness, so one leg.
* `catom`: a carrier's `Ret` is an atom of the theory (`BData.toAtom`).
* ⭐`cret_map`, ⭐`cret_pair`, ⭐`cret_keep`, ⭐⭐`cmodel_retCongr`.
-/

namespace V12M

variable [ModalSys]

open BArrow GArrow

omit [ModalSys] in
theorem Shp.eq_of_label_inner {L : Type*} {A : VarType} {p q : Shp L (.VTypeDia (.VTypeBox A))}
    (h₁ : p.label = q.label) (h₂ : p.body.inner = q.body.inner) : p = q := by
  match p, q, h₁, h₂ with
  | .dia _ (.box _), .dia _ (.box _), h₁, h₂ =>
      obtain rfl : _ = _ := h₁
      obtain rfl : _ = _ := h₂
      rfl

namespace Model

variable {σ : Signature} {M : Model σ}

/-- ⭐**A carrier term has a leg**, and its data and tag are the leg's at its body
    (`BData.atom_data`, with the tag). -/
theorem carrier_leg {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (L : BLeg) {A : VarType}
    {c₀ : Ann (L.carrier A)} (ct : Term σ Γ (L.carrier A) c₀) :
    ∃ (O : OutLeg Γ) (a₀ : Ann A) (bd : Term σ O.view.boxIn A a₀),
      (∀ (hS : ModalSys.BStrong = true) {a : Ann A} (t : Term σ Γ A a),
        (WFF.back hS L ct t : WFF σ Γ 0) = O.back hS bd t) ∧
      M.carrierData L (interp env ct) =
        ⟨O.legSet env, fun x y => interp ((O.pushS env x).boxPush y) bd⟩ ∧
      M.carrierTag L (interp env ct) = O.tag env bd := by
  cases L with
  | nec =>
      match ct with
      | .boxtm (.boxtm bd) =>
          refine ⟨.nec, _, bd, fun _ _ _ => rfl, ?_, rfl⟩
          refine Sigma.ext rfl (heq_of_eq (funext fun x => funext fun y => ?_))
          change M.necEval (M.necEval (interp env (Term.boxtm (Term.boxtm bd)) :
            M.frame.Nec (.VTypeBox A) w) x.1) y = _
          rw [box_beta env (Term.boxtm bd) x.1, box_beta (env.boxPush x.1) bd y]
          rfl
  | pos =>
      match ct with
      | .diatm y hy (.boxtm bd) =>
          refine ⟨.pos y hy, _, bd, fun _ _ _ => rfl, ?_, rfl⟩
          dsimp only [carrierData]
          rw [dia_beta env hy hy.choose_spec (Term.boxtm bd)]
          refine Sigma.ext rfl (heq_of_eq (funext fun x => funext fun z => ?_))
          exact box_beta _ bd z

/-- A kept body, read out along a leg, is the kept object read along the composite (`Model`'s
    `back_keep`). -/
theorem keep_val {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (hF : ModalSys.Four = true)
    (O : OutLeg Γ) {A : VarType} {a : Ann A} (b : Term σ Γ.boxIn A a) (a' : O.legSet env)
    (c : M.frame.Acc a'.1.1) :
    interp ((O.pushS env a').boxPush c)
      (Term.mono O.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b)) =
    M.necEval (interp env (Term.boxtm b) : M.frame.Nec A w)
      ⟨c.1, ⟨M.frame.trans hF a'.1.2.down c.2.down⟩⟩ := by
  rw [box_beta env b, ← interp_shift (Env.shiftAgree_twoBox hF env a'.1 c)]
  cases O with
  | nec =>
      change interp ((env.boxPush a'.1).boxPush c) (Term.mono (Ctx.Le.refl _).boxIn _) = _
      rw [Term.mono_refl]
  | pos y hy =>
      exact interp_mono (Env.boxPush_agree (Env.diaPush_boxIn env hy.choose_spec a') c) _

/-- A nonempty leg has an arrow. -/
theorem sat_dia_top_of_leg {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (O : OutLeg Γ)
    (h : Nonempty (O.legSet env)) : M.sat env (O.dia (.top : WFF σ O.view 0)) := by
  obtain ⟨⟨a, ha⟩⟩ := h
  cases O with
  | nec => exact (OutLeg.sat_dia env .nec _).mpr ⟨a, trivial⟩
  | pos y hy => exact (OutLeg.sat_dia env (.pos y hy) _).mpr ⟨⟨a, ha⟩, trivial⟩

end Model

namespace GArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

variable (hM₀ : Theory.IsMCS M₀)

/-! ## One label, one leg -/

/-- ⭐**One label is one witness** (`cLab_inj`, `postIx_preIx`; the step inside
    `ann_eq_of_termShpW`). -/
theorem witness_of_label (hX : CluFlags) (hSh : ModalSys.shaped = true) (s : GW hF M₀) (i : ℕ)
    {x x' : VarSymb} {X X' : VarType} (hr : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hr' : (ctxOf (glat s i)).ref x' = some (.VTypeDia X'))
    (hl : ((Model.envShape hSh (ccanonEnv hM₀ hX s i)).ref 0 x hr).label =
      ((Model.envShape hSh (ccanonEnv hM₀ hX s i)).ref 0 x' hr').label) : x = x' := by
  have hT := hX.T_of_shaped hSh
  have hI := cInvW_canon (hM₀ := hM₀) hX hSh s i
  obtain ⟨-, hw₁, hv₁⟩ := hI x hr
  obtain ⟨-, hw₂, hv₂⟩ := hI x' hr'
  obtain ⟨hf, he⟩ := hv₁ (.inr rfl)
  obtain ⟨hf', he'⟩ := hv₂ (.inr rfl)
  have hl' : ((cEw hM₀ hX hSh s i).ref 0 x hr).label = ((cEw hM₀ hX hSh s i).ref 0 x' hr').label :=
    hl
  rw [he, he'] at hl'
  have e := cLab_inj hX.five hX.fourS hX.fourSW hM₀ hT 0 hf hf' _ hl'
  rw [← postIx_preIx hX.five hX.fourS hX.fourSW hM₀ hT s hw₁,
    ← postIx_preIx hX.five hX.fourS hX.fourSW hM₀ hT s hw₂, e]

/-- ⭐**Two tags with one label have one leg**: a necessary leg has no tag, and a possible one has
    its witness's label. -/
theorem leg_of_label (hX : CluFlags) (hSh : ModalSys.shaped = true) (s : GW hF M₀) (i : ℕ)
    {O O' : OutLeg (ctxOf (glat s i))} {A B : VarType} {a₀ : Ann A} {b₀ : Ann B}
    (bd : Term σ O.view.boxIn A a₀) (bd' : Term σ O'.view.boxIn B b₀)
    (h : (O.tag (ccanonEnv hM₀ hX s i) bd).map Shp.label =
      (O'.tag (ccanonEnv hM₀ hX s i) bd').map Shp.label) : O = O' := by
  cases O with
  | nec =>
      cases O' with
      | nec => rfl
      | pos y hy =>
          rw [OutLeg.tag_pos hSh _ y hy] at h
          cases h
  | pos y hy =>
      cases O' with
      | nec =>
          rw [OutLeg.tag_pos hSh _ y hy] at h
          cases h
      | pos y' hy' =>
          rw [OutLeg.tag_pos hSh _ y hy, OutLeg.tag_pos hSh _ y' hy'] at h
          obtain rfl := witness_of_label hM₀ hX hSh s i _ _ (Option.some.inj h)
          rfl

/-! ## Atoms -/

theorem cData_eq (hX : CluFlags) (L : BLeg) {A : VarType} {s : GW hF M₀}
    (c : (cframe hF hM₀ hX).Dom (L.carrier A) s) :
    cData hM₀ hX L c = (cmodel hF hM₀ hX).carrierData L c := by
  cases L <;> rfl

theorem cTag_eq (hX : CluFlags) (L : BLeg) {A : VarType} {s : GW hF M₀}
    (c : (cframe hF hM₀ hX).Dom (L.carrier A) s) :
    cTag hM₀ hX L c = (cmodel hF hM₀ hX).carrierTag L c := by
  cases L <;> rfl

/-- A term's value at a later stage is its value. -/
theorem interp_gle (hX : CluFlags) (s : GW hF M₀) {i I : ℕ} (h : i ≤ I) {A : VarType} {a : Ann A}
    (t : Term σ (ctxOf (glat s i)) A a) :
    Model.interp (ccanonEnv hM₀ hX s I) (Term.mono (gle hM₀ s h) t) =
      Model.interp (ccanonEnv hM₀ hX s i) t :=
  Model.interp_mono (ccanonEnv_le hX s h) t

/-- ⭐**A carrier's `Ret` is an atom of the theory** (`BData.toAtom`): an atom already, or at a
    `◇`-free content a true one, carrier and value being denotable. -/
theorem catom (hX : CluFlags) (hS : ModalSys.BStrong = true) {A : VarType} {s : GW hF M₀}
    {ℓ : (cmodel hF hM₀ hX).CarrierTag A s} {S : Set ((cframe hF hM₀ hX).Acc s)}
    {val : (a : S) → (b : (cframe hF hM₀ hX).Acc a.1.1) → (cframe hF hM₀ hX).Dom A b.1}
    {o : (cframe hF hM₀ hX).Dom A s} (hc : (cmodel hF hM₀ hX).IsCarrierData ℓ S val)
    (h : (cmodel hF hM₀ hX).Ret ℓ S val o) :
    ∃ (i : ℕ) (L : BLeg) (c : Ann (L.carrier A)) (ct : Term σ (ctxOf (glat s i)) (L.carrier A) c)
      (a : Ann A) (t : Term σ (ctxOf (glat s i)) A a),
      WFF.back hS L ct t ∈ (gw hM₀ s).M i ∧
      (cmodel hF hM₀ hX).carrierData L (Model.interp (ccanonEnv hM₀ hX s i) ct) = ⟨S, val⟩ ∧
      (cmodel hF hM₀ hX).carrierTag L (Model.interp (ccanonEnv hM₀ hX s i) ct) = ℓ ∧
      Model.interp (ccanonEnv hM₀ hX s i) t = o := by
  obtain ⟨hne, hrt, h₃⟩ : cRet hM₀ hX ℓ S val o := h
  rcases h₃ with hA | ⟨_, i, L, c, ct, a, t, hm, hd, hl, ho⟩
  · obtain ⟨L, c, hcd, htag⟩ := hc
    obtain ⟨i₁, c₁, ct, hct⟩ := cdefinable_fromDom hM₀ hX _ s c
    obtain ⟨i₂, a₂, t, ht⟩ := cdefinable_fromDom hM₀ hX A s o
    have h₁ : i₁ ≤ max i₁ i₂ := le_max_left _ _
    have h₂ : i₂ ≤ max i₁ i₂ := le_max_right _ _
    have ec : Model.interp (ccanonEnv hM₀ hX s (max i₁ i₂)) (Term.mono (gle hM₀ s h₁) ct) = c :=
      (interp_ccanon hX _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)).trans
        ((ctoDom_congr hX ((cden_lift hX h₁ ct).trans hct) _ _).trans
          (ctoDom_fromDom hM₀ hX _ s c))
    have et : Model.interp (ccanonEnv hM₀ hX s (max i₁ i₂)) (Term.mono (gle hM₀ s h₂) t) = o :=
      (interp_ccanon hX _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)).trans
        ((ctoDom_congr hX ((cden_lift hX h₂ t).trans ht) _ _).trans
          (ctoDom_fromDom hM₀ hX _ s o))
    refine ⟨_, L, c₁, Term.mono (gle hM₀ s h₁) ct, a₂, Term.mono (gle hM₀ s h₂) t,
      (ctruth (hM₀ := hM₀) hX s _ _).mp ?_, by rw [ec]; exact hcd, by rw [ec]; exact htag, et⟩
    change (cmodel hF hM₀ hX).Backs L _ _
    unfold Model.Backs
    rw [ec, et, hcd, htag]
    exact ⟨hne, hrt, .inl hA⟩
  · have ec := interp_ccanon (hM₀ := hM₀) hX ct (Model.Env.Agree.refl' (ccanonEnv hM₀ hX s i))
      (Ctx.Presented.noProjLast _)
    refine ⟨i, L, c, ct, a, t, hm, ?_, ?_, ?_⟩
    · rw [ec, ← cData_eq]
      exact hd
    · rw [ec, ← cTag_eq]
      exact hl
    · exact (interp_ccanon hX t (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)).trans ho

/-! ## The laws -/

/-- ⭐**`Ret` is preserved by a hole term** (`BData.ret_map`): a `◇`-free round trip by
    `cindCongr`; an atom by `back_beta`, whose new atom is true with the mapped data, and whose tag
    is moved (`OutLeg.tag_holeRead`). -/
theorem cret_map (hX : CluFlags) (hS : ModalSys.BStrong = true) {A C : VarType} {b : Ann C}
    (sh : Term σ (Ctx.empty.insert (.bnd 0) A) C b) {s : GW hF M₀}
    {ℓ : (cmodel hF hM₀ hX).CarrierTag A s} {S : Set ((cframe hF hM₀ hX).Acc s)}
    {val : (a : S) → (c : (cframe hF hM₀ hX).Acc a.1.1) → (cframe hF hM₀ hX).Dom A c.1}
    {o : (cframe hF hM₀ hX).Dom A s} (h : (cmodel hF hM₀ hX).Ret ℓ S val o) :
    (cmodel hF hM₀ hX).Ret (ℓ.map (Model.tagMap ((cmodel hF hM₀ hX).holeShp sh))) S
      (fun a c => (cmodel hF hM₀ hX).holeVal sh (val a c)) ((cmodel hF hM₀ hX).holeVal sh o) := by
  obtain ⟨hne, hrt, h₃⟩ : cRet hM₀ hX ℓ S val o := h
  rcases h₃ with hA | ⟨_, i, L, c, ct, a, t, hm, hd, hl, rfl⟩
  · exact ⟨hne, fun x => (hrt x).imp fun _ hI => (cindCongr hM₀ hX).map sh hI,
      .inl (Term.diaFree_hole hA sh)⟩
  have ec := interp_ccanon (hM₀ := hM₀) hX ct (Model.Env.Agree.refl' (ccanonEnv hM₀ hX s i))
    (Ctx.Presented.noProjLast _)
  obtain ⟨O, a₀, bd, hO, hdO, hlO⟩ := Model.carrier_leg (ccanonEnv hM₀ hX s i) L ct
  rw [ec, ← cData_eq] at hdO
  rw [ec, ← cTag_eq] at hlO
  cases hd.symm.trans hdO
  cases hl.symm.trans hlO
  rw [hO hS t] at hm
  have hm2 : (O.back hS (Term.holeRead bd sh) (Term.holeRead t sh) : WFF σ _ 0) ∈
      (gw hM₀ s).M i :=
    BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hm)
      ⟨Proof.back_beta hS O bd t sh (Proof.lookup List.mem_cons_self)⟩
  have hsat := (OutLeg.sat_back hS _ O _ _).mp ((ctruth (hM₀ := hM₀) hX s i _).mpr hm2)
  have hval : (fun (x : O.legSet (ccanonEnv hM₀ hX s i))
      (y : (cmodel hF hM₀ hX).frame.Acc x.1.1) =>
      Model.interp ((O.pushS (ccanonEnv hM₀ hX s i) x).boxPush y) (Term.holeRead bd sh)) =
      fun x y => (cmodel hF hM₀ hX).holeVal sh
        (Model.interp ((O.pushS (ccanonEnv hM₀ hX s i) x).boxPush y) bd) := by
    funext x y
    exact Model.interp_holeRead (Ctx.noProjLast_boxIn _) _ bd sh
  rw [hval, Model.interp_holeRead (Ctx.Presented.noProjLast _),
    interp_ccanon hX t (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _),
    OutLeg.tag_holeRead (ModalSys.shaped_of_BStrong hS)] at hsat
  exact hsat

/-- ⭐**`Ret` is preserved by pairing carriers' data** (`BData.ret_pair`): both are atoms, at a
    common stage, of one leg, their labels being one (`leg_of_label`), so `back_pair` pairs them,
    and the paired atom is true with the paired data and tag (`OutLeg.tag_pair`). -/
theorem cret_pair (hX : CluFlags) (hS : ModalSys.BStrong = true) {A C : VarType} {s : GW hF M₀}
    {ℓ : (cmodel hF hM₀ hX).CarrierTag A s} {ℓ' : (cmodel hF hM₀ hX).CarrierTag C s}
    {S : Set ((cframe hF hM₀ hX).Acc s)}
    {val : (a : S) → (c : (cframe hF hM₀ hX).Acc a.1.1) → (cframe hF hM₀ hX).Dom A c.1}
    {val' : (a : S) → (c : (cframe hF hM₀ hX).Acc a.1.1) → (cframe hF hM₀ hX).Dom C c.1}
    {o : (cframe hF hM₀ hX).Dom A s} {o' : (cframe hF hM₀ hX).Dom C s}
    (hlab : ℓ.map Shp.label = ℓ'.map Shp.label) (hc : (cmodel hF hM₀ hX).IsCarrierData ℓ S val)
    (hc' : (cmodel hF hM₀ hX).IsCarrierData ℓ' S val') (h : (cmodel hF hM₀ hX).Ret ℓ S val o)
    (h' : (cmodel hF hM₀ hX).Ret ℓ' S val' o') :
    (cmodel hF hM₀ hX).Ret (A := .VTypeProd A C) (Model.tagPair ℓ ℓ') S
      (fun a c => ((val a c, val' a c) : (cframe hF hM₀ hX).Dom (.VTypeProd A C) c.1))
      ((o, o') : (cframe hF hM₀ hX).Dom (.VTypeProd A C) s) := by
  have hSh := ModalSys.shaped_of_BStrong hS
  obtain ⟨i, L, c, ct, a, t, hm, hd, hl, rfl⟩ := catom hM₀ hX hS hc h
  obtain ⟨i', L', c', ct', a', t', hm', hd', hl', rfl⟩ := catom hM₀ hX hS hc' h'
  have hK : i ≤ max i i' := le_max_left _ _
  have hK' : i' ≤ max i i' := le_max_right _ _
  have hmK : (WFF.back hS L (Term.mono (gle hM₀ s hK) ct) (Term.mono (gle hM₀ s hK) t) :
      WFF σ _ 0) ∈ (gw hM₀ s).M (max i i') := (BWorld.mem_lift hK).mp hm
  have hmK' : (WFF.back hS L' (Term.mono (gle hM₀ s hK') ct') (Term.mono (gle hM₀ s hK') t') :
      WFF σ _ 0) ∈ (gw hM₀ s).M (max i i') := (BWorld.mem_lift hK').mp hm'
  obtain ⟨O, a₀, bd, hO, hdO, hlO⟩ :=
    Model.carrier_leg (ccanonEnv hM₀ hX s (max i i')) L (Term.mono (gle hM₀ s hK) ct)
  obtain ⟨O', a₀', bd', hO', hdO', hlO'⟩ :=
    Model.carrier_leg (ccanonEnv hM₀ hX s (max i i')) L' (Term.mono (gle hM₀ s hK') ct')
  rw [interp_gle hM₀ hX s hK ct] at hdO hlO
  rw [interp_gle hM₀ hX s hK' ct'] at hdO' hlO'
  have hl₁ := hl.symm.trans hlO
  have hl₂ := hl'.symm.trans hlO'
  obtain rfl : O = O' := leg_of_label hM₀ hX hSh s _ bd bd' (by rw [← hl₁, ← hl₂]; exact hlab)
  rw [hO hS _] at hmK
  rw [hO' hS _] at hmK'
  have hm2 : (O.back hS (Term.pair bd bd')
      (Term.pair (Term.mono (gle hM₀ s hK) t) (Term.mono (gle hM₀ s hK') t')) : WFF σ _ 0) ∈
        (gw hM₀ s).M (max i i') :=
    BWorld.mem_of_provable (Δ := [_, _]) (fun ψ hψ => by
      rcases List.mem_pair.mp hψ with rfl | rfl
      · exact hmK
      · exact hmK')
      ⟨Proof.back_pair hS O bd _ bd' _ (Proof.lookup List.mem_cons_self)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  have hsat := (OutLeg.sat_back hS _ O _ _).mp ((ctruth (hM₀ := hM₀) hX s _ _).mpr hm2)
  have hSV := hd.symm.trans hdO
  have hSV' := hd'.symm.trans hdO'
  cases hSV
  obtain ⟨-, hv'⟩ := Sigma.mk.inj hSV'
  cases eq_of_heq hv'
  subst hl₁
  subst hl₂
  rw [OutLeg.tag_pair hSh] at hsat
  have hv : Model.interp (ccanonEnv hM₀ hX s (max i i'))
      (Term.pair (Term.mono (gle hM₀ s hK) t) (Term.mono (gle hM₀ s hK') t')) =
      ((Model.interp (ccanonEnv hM₀ hX s i) t, Model.interp (ccanonEnv hM₀ hX s i') t') :
        (cframe hF hM₀ hX).Dom (.VTypeProd A C) s) :=
    Prod.ext (interp_gle hM₀ hX s hK t) (interp_gle hM₀ hX s hK' t')
  rw [hv] at hsat
  exact hsat

/-- ⭐⭐**A kept carrier comes back as its own value** on the cluster.  The given carrier and the
    object have terms at a common stage; the carrier's names the leg, and `back_keep` along it at
    the object's body is true.  That atom's carrier need not be the given one, whose body may be
    another term, but it has the same data (`Model.keep_val`) and tag: one label (`tag_label`),
    and one body shape, `tag_keep`'s and the law's premise's. -/
theorem cret_keep (hX : CluFlags) (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF' : ModalSys.Four = true) {A : VarType} {s : GW hF M₀}
    {ℓ : (cmodel hF hM₀ hX).CarrierTag A s} {S : Set ((cframe hF hM₀ hX).Acc s)}
    (n : (cframe hF hM₀ hX).Nec A s) (hne : Nonempty S)
    (hcd : (cmodel hF hM₀ hX).IsCarrierData ℓ S (fun a c => (cmodel hF hM₀ hX).necEval n
      ⟨c.1, ⟨(cframe hF hM₀ hX).trans hF' a.1.2.down c.2.down⟩⟩))
    (hsh : ∀ sh, ℓ = some sh → sh.body.inner =
      (Model.domSh (M := cmodel hF hM₀ hX) (ModalSys.shaped_of_T hT) (A := .VTypeBox A) n).inner.map
        (Arrows.Leaf.shift hF' 0)) :
    (cmodel hF hM₀ hX).Ret ℓ S (fun a c => (cmodel hF hM₀ hX).necEval n
        ⟨c.1, ⟨(cframe hF hM₀ hX).trans hF' a.1.2.down c.2.down⟩⟩)
      ((cmodel hF hM₀ hX).necEval n ((cframe hF hM₀ hX).reflAcc hT s)) := by
  have hSh := ModalSys.shaped_of_T hT
  obtain ⟨L, c, hd, hl⟩ := hcd
  obtain ⟨i₁, c₁, ct, hct⟩ := cdefinable_fromDom hM₀ hX _ s c
  obtain ⟨i₂, _, nt, hnt⟩ := cdefinable_fromDom hM₀ hX (.VTypeBox A) s n
  cases nt with
  | boxtm b =>
      have h₁ : i₁ ≤ max i₁ i₂ := le_max_left _ _
      have h₂ : i₂ ≤ max i₁ i₂ := le_max_right _ _
      let env := ccanonEnv hM₀ hX s (max i₁ i₂)
      let b' := Term.mono (gle hM₀ s h₂).boxIn b
      have ec : Model.interp env (Term.mono (gle hM₀ s h₁) ct) = c :=
        (interp_ccanon hX _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)).trans
          ((ctoDom_congr hX ((cden_lift hX h₁ ct).trans hct) _ _).trans
            (ctoDom_fromDom hM₀ hX _ s c))
      have en : Model.interp env (Term.boxtm b') = n :=
        (interp_ccanon hX _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)).trans
          ((ctoDom_congr hX ((cden_lift hX h₂ (Term.boxtm b)).trans hnt) _ _).trans
            (ctoDom_fromDom hM₀ hX (.VTypeBox A) s n))
      obtain ⟨O, a₀, bd, -, hdO, hlO⟩ := Model.carrier_leg env L (Term.mono (gle hM₀ s h₁) ct)
      rw [ec] at hdO hlO
      have hSV := hd.symm.trans hdO
      obtain rfl : S = O.legSet env := congrArg Sigma.fst hSV
      have hl₁ : O.tag env bd = ℓ := hlO.symm.trans hl
      have hne' : O.dia (.top : WFF σ O.view 0) ∈ (gw hM₀ s).M (max i₁ i₂) :=
        (ctruth (hM₀ := hM₀) hX s _ _).mp (Model.sat_dia_top_of_leg env O hne)
      have hm : (O.back hS (Term.mono O.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b'))
          (Term.collapse (Ctx.collapses_boxIn_self hT _) b') : WFF σ _ 0) ∈
          (gw hM₀ s).M (max i₁ i₂) :=
        BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by
          rw [List.mem_singleton.mp hψ]
          exact hne') ⟨Proof.back_keep hS hT hF O b' (Proof.lookup List.mem_cons_self)⟩
      have hR := (OutLeg.sat_back hS env O _ _).mp ((ctruth (hM₀ := hM₀) hX s _ _).mpr hm)
      have hfun : (fun (a' : O.legSet env) (c' : (cmodel hF hM₀ hX).frame.Acc a'.1.1) =>
          Model.interp ((O.pushS env a').boxPush c')
            (Term.mono O.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b'))) =
          fun (a' : O.legSet env) (c' : (cmodel hF hM₀ hX).frame.Acc a'.1.1) =>
            (cmodel hF hM₀ hX).necEval n
              ⟨c'.1, ⟨(cframe hF hM₀ hX).trans hF' a'.1.2.down c'.2.down⟩⟩ :=
        funext fun a' => funext fun c' => (Model.keep_val env hF O b' a' c').trans (by rw [en])
      have hv : Model.interp env (Term.collapse (Ctx.collapses_boxIn_self hT _) b') =
          (cmodel hF hM₀ hX).necEval n ((cframe hF hM₀ hX).reflAcc hT s) := by
        rw [Model.interp_collapse (Model.Env.collapseAgree_self hT env),
          ← Model.box_beta env b' ((cframe hF hM₀ hX).reflAcc hT s), en]
      have htag : O.tag env (Term.mono O.le_view.boxIn
          (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b')) = ℓ := by
        have hlab := OutLeg.tag_label hSh env O (Term.mono O.le_view.boxIn
          (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b')) bd
        rw [hl₁] at hlab
        cases hκ : O.tag env (Term.mono O.le_view.boxIn
            (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b')) with
        | none =>
            rw [hκ] at hlab
            cases hℓ : ℓ with
            | none => rfl
            | some sh =>
                rw [hℓ] at hlab
                cases hlab
        | some κ =>
            rw [hκ] at hlab
            cases hℓ : ℓ with
            | none =>
                rw [hℓ] at hlab
                cases hlab
            | some sh =>
                rw [hℓ] at hlab
                have i₁' := OutLeg.tag_keep hT hF env O b' κ hκ
                rw [en] at i₁'
                exact congrArg some (Shp.eq_of_label_inner (Option.some.inj hlab)
                  (i₁'.trans (hsh sh hℓ).symm))
      rw [hfun, hv, htag] at hR
      exact hR

/-- ⭐⭐**Canonical "comes back as" is a congruence** (strong B). -/
theorem cmodel_retCongr (hX : CluFlags) (hS : ModalSys.BStrong = true) :
    (cmodel hF hM₀ hX).RetCongr where
  map := by
    intro _ _ _ sh _ _ _ _ _ h
    exact cret_map hM₀ hX hS sh h
  pair := by
    intro _ _ _ _ _ _ _ _ _ _ hl hc hc' h h'
    exact cret_pair hM₀ hX hS hl hc hc' h h'
  keep := by
    intro hT hF' _ _ _ _ n hne hcd hsh
    exact cret_keep hM₀ hX hS hT hF' n hne hcd hsh

end GArrow

end V12M
