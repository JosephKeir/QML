import QML.QML_v12m_GCluRet

/-!
# QML v12m — 5 on the growing tree: returning possibilities come true

Membership ⇒ truth at `retS` and `retxS`, at necessary shapes (`docs/v12-modal-extensions.md`,
"`retS` on the cluster").

* `WFF.instantiate_bindFree`, `WFF.subst_lifted`, ⭐`BWorld.ret_term`: `Proof.retN_lift`, read at a
  term of a later stage.
* `Proof.back_of_tieV`: `Proof.back_of_tie` from a `Back` along the plain leg.
* `kept2_path`, `kept2_real`: a home term's kept carrier, at the far world.
* `FarUp`, `farUpNec`, `farUpPos`: a leg's far world, from a later stage here.
* ⭐`exists_far`: what is possible along a leg is in the theory at the far end of an arrow.
* ⭐`back_home`: a tie in the far world's theory is a `Back` here, of the far term's home term.
* `ind_of_back`, `comp_home`: what such a `Back` says of the far object's readings home.
* ⭐`comps_ind`: a value and a far object tied to it agree, read home.
* ⭐⭐`sat_ret_of_memC`, `sat_ret_of_memN`: a returning possibility in the theory is true.
-/

namespace V12M

variable [ModalSys]

open BArrow GArrow

section LiftRead

variable {σ : Signature} {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] {A : VarType}

/-- Filling a bound variable, at a later context, is substituting the variable. -/
theorem WFF.instantiate_bindFree (h : Γ.Le Γ') (c : ℕ) (hc : Γ.RootFresh (.free c)) {T : VarType}
    {x₀ : Ann T} (x : Term σ Γ' T x₀) (ψ : WFF σ (Γ.insert (.free c) T) 0) :
    WFF.instantiate Ctx.NoSlots.slots x (WFF.mono (h.insert (.bnd 0) T)
        (WFF.bindFree c hc Ctx.NoSlots.slots T ψ)) =
      WFF.subst (Subst.singleIdx (.free c) (.tm x)) (Subst.single (.free c) (.tm x))
        (Subst.ok_single h rfl) (Subst.coh_single hc h rfl)
        ((Ctx.NoSlots.slots (Γ := Γ)).insertFree c T) Ctx.NoSlots.slots ψ := by
  have hfr : Γ.RootFresh (.bnd 0) := (Ctx.NoSlots.slots (Γ := Γ)).rootFresh le_rfl
  unfold WFF.instantiate WFF.substRoot
  refine (WFF.subst_mono (h.insert (.bnd 0) T) _ _ _
    ((Ctx.NoSlots.slots (Γ := Γ)).insert T) _ _ _).trans ?_
  unfold WFF.bindFree WFF.renameRoot
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ ψ
  refine Subst.sim_of ?_
  intro v U hlp hv
  rw [Subst.comp_apply]
  by_cases hvr : v = .root (.free c)
  · subst hvr
    rw [Subst.single_root, Subst.single_root, SubE.comp_ren, Subst.at_single_root]
    exact .refl _
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    rw [Subst.single_ne _ hvr, Subst.single_ne _ hvr, SubE.comp_ren,
      Subst.single_at_ne (Ctx.ref_rt_ne hfr ((Ctx.ref_nonproj Γ hlp).trans hv'))]
    exact .refl _

/-- A substitution that is the identity on a view, into an instantiation weakened from the view. -/
theorem WFF.subst_instantiate_ren {ι : VarSymb → VarSymb} {V V₁ V' : Ctx} [V.NoSlots]
    (hl : V.Le V₁) (hV : V.Le V') (θ : Subst σ V') (hθ : Subst.Ok V₁ θ) (hc : Subst.Coh ι V₁ θ)
    (hs : V₁.SlotsFrom 0) (hs' : V'.SlotsFrom 0)
    (hid : ∀ v U, V.ref v = some U → θ.at v = .ren v) {T : VarType} {u₀ : Ann T}
    (u : Term σ V₁ T u₀) {u₁ : Ann T} (u' : Term σ V' T u₁)
    (hu : (⟨_, Term.subst ι θ hθ hc u⟩ : Σ b, Term σ V' T b) = ⟨_, u'⟩)
    (Φ : WFF σ (V.insert (.bnd 0) T) 1) :
    WFF.subst ι θ hθ hc hs hs' (WFF.instantiate hs u (WFF.mono (hl.insert (.bnd 0) T) Φ)) =
      WFF.instantiate hs' u' (WFF.mono (hV.insert (.bnd 0) T) Φ) := by
  rw [WFF.subst_instantiate, WFF.subst_mono (hl.insert (.bnd 0) T) _ _ _
    ((Ctx.NoSlots.slots (Γ := V)).insert T),
    WFF.subst_ren (hV.insert (.bnd 0) T) _ _ _ _ _ (Subst.ren_under hid T hs'.root) Φ]
  exact WFF.instantiate_congr_sig _ hu _

/-- ⭐What `Proof.ret_lift` says, of a term in place of its fresh variable. -/
theorem WFF.subst_lifted (h : Γ.Le Γ') (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true)
    (O : OutLeg Γ) {a₁ : Ann A} (t : Term σ Γ A a₁)
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1) (c : ℕ) (hc : Γ.RootFresh (.free c))
    {b₀ : Ann A} (b : Term σ Γ'.boxIn A b₀) :
    WFF.subst (Subst.singleIdx (.free c) (.tm (Term.boxtm b)))
        (Subst.single (.free c) (.tm (Term.boxtm b)))
        (Subst.ok_single h rfl) (Subst.coh_single hc h rfl)
        ((Ctx.NoSlots.slots (Γ := Γ)).insertFree c _) Ctx.NoSlots.slots
        (WFF.lifted hS hF O t Φ c hc) =
      WFF.and (WFF.back hS .nec (Term.boxtm (Term.boxtm
          (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ') b))) (Term.mono h t))
        ((O.mono h).dia (WFF.instantiate Ctx.NoSlots.slots
          (Term.boxtm (Term.mono (O.mono h).le_view.boxIn
            (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ') b)))
          (WFF.mono ((O.le_view_mono h).insert (.bnd 0) _) Φ))) := by
  let θ := Subst.single (σ := σ) (Δ := Γ') (.free c) (.tm (Term.boxtm b))
  have hat : θ.at (.root (.free c)) = .tm (Term.boxtm b) := Subst.at_single_root _ _
  have hid : ∀ v U, Γ.ref v = some U → θ.at v = .ren v :=
    fun v _ hv => Subst.single_at_ne (Ctx.ref_rt_ne hc hv)
  have hθ : Subst.Ok (Γ.insert (.free c) (.VTypeBox A)) θ := Subst.ok_single h rfl
  have hc' : Subst.Coh (Subst.singleIdx (.free c) (.tm (Term.boxtm b)))
    (Γ.insert (.free c) (.VTypeBox A)) θ := Subst.coh_single hc h rfl
  have e₀ := Term.subst_eta_tm θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc')
    A (VarSymb.root (.free c)).inner (Ctx.ref_inner (Ctx.ref_insert_root Γ (.free c) _)) b
    (Subst.box_at_inner_boxtm θ hat)
  have e₁ := (Term.shift_subst (Ctx.shifts_boxIn_boxIn hF _) (Ctx.shifts_boxIn_boxIn hF Γ')
    θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc') θ.box.box (Subst.ok_box (Subst.ok_box hθ))
    (Subst.coh_box (Subst.ok_box hθ) (Subst.coh_box hθ hc'))
    (Subst.shiftCorr_box_box hF hθ) (Term.eta (VarSymb.root (.free c)).inner A
      (Ctx.ref_inner (Ctx.ref_insert_root Γ (.free c) _)))).symm.trans (sig_shift_cong _ e₀)
  refine congrArg₂ WFF.and (WFF.back_congr hS .nec (sig_boxtm (sig_boxtm e₁)) ?_) ?_
  · unfold Term.weaken
    rw [Term.subst_mono]
    exact Term.subst_ren h _ _ _ hid t
  · have hu : (⟨_, Term.subst _ θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc') (Term.boxtm
        (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (Term.eta (VarSymb.root (.free c)).inner A
          (Ctx.ref_inner (Ctx.ref_insert_root Γ (.free c) _)))))⟩ :
        Σ e, Term σ Γ'.boxIn (.VTypeBox A) e) =
        ⟨_, Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ') b)⟩ := sig_boxtm e₁
    cases O with
    | nec =>
        refine (OutLeg.subst_dia θ hθ hc' _ _ .nec _).trans (congrArg (OutLeg.nec).dia ?_)
        exact WFF.subst_instantiate_ren (Ctx.le_insert hc.root _).boxIn h.boxIn θ.box _ _ _ _
          (Subst.ren_box hid) _ _
          ((OutLeg.subst_mono_le_view θ hθ hc' .nec _).trans (sig_mono _ hu)) Φ
    | pos y hy =>
        have hιy : Subst.singleIdx (.free c) (.tm (Term.boxtm b)) y = y :=
          if_neg (Ctx.ref_rt_ne hc hy.choose_spec)
        have hy₁ : ∃ Y, (Γ.insert (.free c) (.VTypeBox A)).ref y = some (.VTypeDia Y) :=
          hy.imp fun _ e => (Ctx.le_insert hc.root _).ref e
        have hθy : Subst.Ok ((Γ.insert (.free c) (.VTypeBox A)).diaIn y) (θ.dia y y) :=
          Subst.ok_dia hθ hy₁ ((hy₁.elim fun _ hY => hc' y _ hY []).trans hιy)
        have hcy : Subst.Coh (Subst.singleIdx (.free c) (.tm (Term.boxtm b)))
            ((Γ.insert (.free c) (.VTypeBox A)).diaIn y) (θ.dia y y) := by
          have := Subst.coh_dia hθ hc' hy₁
          rwa [hιy] at this
        refine (WFF.subst_dia θ hθ hc' _ _ hy₁ y hιy (hy.imp fun _ e => h.ref e) hθy hcy
          ((Ctx.NoSlots.slots (Γ := Γ')).diaIn y) _).trans (congrArg (WFF.dia y _) ?_)
        exact WFF.subst_instantiate_ren ((Ctx.le_insert hc.root _).diaIn y) (h.diaIn y) (θ.dia y y)
          _ _ _ _ (Subst.ren_dia hid y)
          _ _ ((Term.subst_diaIn_mono θ hθ hc' y y hθy hcy _).trans (sig_mono _ hu)) Φ

end LiftRead

/-- ⭐⭐**A returning possibility in a world's theory, at a term** (T + 4, strong B):
    `Proof.retN_lift` at a fresh variable, as an `∃`, witnessed (`exW_term`). -/
theorem BArrow.BWorld.ret_term {σ : Signature} (w : BWorld σ) (hS : ModalSys.BStrong = true)
    (hT : ModalSys.T = true) (hF : ModalSys.Four = true) {i : ℕ} (O : OutLeg (w.ctx i))
    {A : VarType} {cs : List (List Step)} (h : A.CompOk cs) {a : Ann (A.compsFlat cs)}
    (t : Term σ (w.ctx i) (A.compsFlat cs) a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1)
    (hm : O.retS hS (.nec (.boxC A cs h)) t Φ ∈ w.M i) :
    ∃ (j : ℕ) (hij : i ≤ j) (b₀ : Ann (A.compsFlat cs))
      (b : Term σ (w.ctx j).boxIn (A.compsFlat cs) b₀),
      WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b)))
        (Term.mono (w.le hij) t) ∈ w.M j ∧
      (O.mono (w.le hij)).dia (WFF.instantiate Ctx.NoSlots.slots
        (Term.boxtm (Term.mono (O.mono (w.le hij)).le_view.boxIn
          (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b)))
        (WFF.packedBody (N := .boxC A cs h) hS hF
          (WFF.mono ((O.le_view_mono (w.le hij)).insert (.bnd 0) _) Φ))) ∈ w.M j := by
  have hc : (w.ctx i).RootFresh (.free (w.l i).length) := ctxOf_fresh le_rfl
  have hc₁ : (w.ctx i).RootFresh (.free ((w.l i).length + 1)) := ctxOf_fresh (by omega)
  have hc₂ : (w.ctx i).RootFresh (.free ((w.l i).length + 2)) := ctxOf_fresh (by omega)
  have hex : WFF.ex (.VTypeBox (A.compsFlat cs)) (WFF.bindFree (w.l i).length hc
      Ctx.NoSlots.slots _ (WFF.lifted hS hF O t (WFF.packedBody (N := .boxC A cs h) hS hF Φ)
        (w.l i).length hc)) ∈ w.M i :=
    BWorld.mem_of_provable (Δ := [_]) (fun φ hφ => by rw [List.mem_singleton.mp hφ]; exact hm)
      ⟨Proof.retN_lift hS hT hF O (.boxC A cs h) t Φ _ hc hc₁ hc₂
        (Proof.lookup List.mem_cons_self)
        (Proof.ex_intro _ (Term.eta (.root (.free (w.l i).length)) _
          (Ctx.ref_insert_root _ _ _)) (Proof.conv ?_ (Proof.lookup List.mem_cons_self)))⟩
  · obtain ⟨j, hij, x₀, x, hm'⟩ := w.exW_term hex
    cases x with
    | boxtm b =>
        refine ⟨j, hij, _, b, ?_⟩
        rw [WFF.instantiate_bindFree (w.le hij) _ hc, WFF.subst_lifted (w.le hij),
          WFF.mono_packedBody (O.le_view_mono (w.le hij))] at hm'
        exact (w.mcs j).and_mem_iff.mp hm'
  · exact ((WFF.instantiate_eta_openFree _ hc Ctx.NoSlots.slots Ctx.NoSlots.slots _).trans
      (WFF.openFree_bindFree _ hc Ctx.NoSlots.slots _)).symm

/-- `Proof.back_of_tie` from a `Back` along the plain leg, kept to the leg: what comes back as `u`
    and is tied at the end of an arrow out to `k` comes back with `k` (`Proof.ret_unlift`). -/
def Proof.back_of_tieV {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {A : VarType}
    (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ) {k₀ : Ann A} (k : Term σ Γ.boxIn A k₀) {y₀ : Ann A}
    (y : Term σ Γ.boxIn A y₀) {a : Ann A} (u : Term σ Γ A a)
    (hb : Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm
      (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) y))) u))
    (hd : Proof σ Γ Δ (O.dia (WFF.box (WFF.holeAt Ctx.NoSlots.slots
      (Term.pair (Term.mono O.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) y))
        (compBd hF O k).2) (WFF.backDup hS hF A))))) :
    Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm
      (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) k))) u) := by
  have hne : Proof σ Γ Δ (O.dia .top) := Proof.leg_dia O Proof.top_intro hd
  have B₀ : Proof σ Γ Δ (O.back hS (compBd hF O k).2 (Term.boxtm k)) :=
    Proof.conv (OutLeg.back_congr hS O rfl (Term.collapse_boxtm_shift hT hF k))
      (Proof.back_keep hS hT hF O (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) k)) hne)
  have hd' : Proof σ Γ Δ (O.dia (WFF.instantiate Ctx.NoSlots.slots
      (Term.mono O.le_view (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) y)))
      (counitBodyC (compBd hF O k).2 (WFF.backDup hS hF A)))) :=
    Proof.conv (congrArg O.dia (instantiate_counitBodyC _ _ _).symm) hd
  have H := Proof.ret_counitC hS O u (compBd hF O k).2 (Term.boxtm k) (WFF.backDup hS hF A)
    (Proof.ret_unlift hS hT hF O y u _ hb hd') B₀
  exact Proof.conv ((WFF.holeRead_eq_holeAt _ _).trans (WFF.holeAt_backDup hS hF _ u k)) H

namespace Model

variable {σ : Signature} {M : Model σ}

/-- `Ind` passes to first components, given that it is a congruence. -/
theorem ind_fstC (hC : M.IndCongr) {A B : VarType} {w : M.frame.W}
    {x y : M.frame.Dom (.VTypeProd A B) w} (h : M.Ind x y) : M.Ind x.1 y.1 := by
  have := hC.map (Term.eta (σ := σ) (.step (.root (.bnd 0)) .fst) A
    (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))) h
  simpa only [holeVal, interp_eta_slot_fst] using this

/-- `Ind` passes to second components, given that it is a congruence. -/
theorem ind_sndC (hC : M.IndCongr) {A B : VarType} {w : M.frame.W}
    {x y : M.frame.Dom (.VTypeProd A B) w} (h : M.Ind x y) : M.Ind x.2 y.2 := by
  have := hC.map (Term.eta (σ := σ) (.step (.root (.bnd 0)) .snd) B
    (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))) h
  simpa only [holeVal, interp_eta_slot_snd] using this

/-- A necessary object whose readings with companions are `Ind` to `o` comes back as `o`
    (`BData.compsBack_of_ind`). -/
theorem compsBack_of_indC (hC : M.IndCongr) (A : VarType) {v w : M.frame.W}
    (e : M.frame.Dom (.VTypeBox A) v) (r : M.frame.R v w) :
    ∀ (cs : List (List Step)) (h : A.CompOk cs) (o : M.frame.Dom (A.compsFlat cs) w),
      M.Ind (M.compsRead A cs h e r) o → M.compsBack A cs e r o
  | [], _, _, hI => hI
  | p :: ps, h, o, hI => by
      obtain ⟨hT, hall, -⟩ := h.resolve_left (List.cons_ne_nil _ _)
      refine ⟨compsBack_of_indC hC A e r ps h.tail o.1 (ind_fstC hC hI), ?_⟩
      rw [dif_pos hT]
      exact compBack_of_ind hT (.VTypeBox A) (.here :: p) e r o.2
        (hall p List.mem_cons_self) (ind_sndC hC hI)

end Model

namespace GArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

variable (hM₀ : Theory.IsMCS M₀)

/-! ## A home term's kept carrier, at the far world -/

/-- A home term's kept carrier along a path is the kept carrier of what it was made from. -/
theorem kept2_path (hX : CluFlags) (s : GW hF M₀) (I : ℕ) (v : GW hF M₀) (P : List ℕ)
    (h : v.1 = nodeOf (groot hF M₀).1 P) (hP : PathOk P) {K : ℕ} {A : VarType} {c₀ : Ann A}
    (c : Term σ (ctxOf (glat v K)).boxIn A c₀)
    (hJI : pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K) ≤ I) :
    ∃ (L' : ℕ) (hL : pstg (groot hF M₀) v P h (rstg s I) ≤ L') (hK : K ≤ L'),
      (⟨_, Term.mono (gle hM₀ v hL) (pTr hM₀ (groot hF M₀) v P h hP (rstg s I)
        (preTB hX hM₀ s I (.boxtm (compBd hF .nec
          (Term.mono (gle hM₀ s hJI).boxIn (homeT hM₀ hX s v c).2)).2)).2).2⟩ :
        Σ e, Term σ (ctxOf (glat v L')) (.VTypeBox (.VTypeBox A)) e) =
      ⟨_, .boxtm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _)
        (Term.mono (gle hM₀ v hK).boxIn c)))⟩ := by
  obtain rfl : P = rpath v := nodeOf_inj (h.symm.trans (rpath_eq v))
  let R := max (rstg s I) (rstg v K)
  have hRI : rstg s I ≤ R := le_max_left _ _
  have hR₀ : rstg v K ≤ R := le_max_right _ _
  have hL := pstg_monotone hM₀ (groot hF M₀) v (rpath v) h hRI
  have hK : K ≤ pstg (groot hF M₀) v (rpath v) h R :=
    (le_pstg_pstgO hX.five hX.fourS hX.fourSW hM₀ (rpath v) (groot hF M₀) v (rpath_eq v) K).trans
      (pstg_monotone hM₀ (groot hF M₀) v (rpath v) h hR₀)
  refine ⟨_, hL, hK, ?_⟩
  refine (pTr_mono hM₀ _ _ _ h hP hRI _).trans ?_
  refine (pTr_sigma hM₀ _ _ _ _ hP _ ((preTB_compBd hM₀ hX s I hRI _).trans (sig_boxtm
    (sig_shift_cong _ (sig_boxtm (sig_shift_cong _
      (preTB_pTrK hM₀ hX s hRI hR₀ (gle hM₀ s hJI) (preTB hX hM₀ v K c).2))))))).trans ?_
  exact (tr_kept hM₀ hX (rpath v) _ _ h hP R _).trans
    (sig_boxtm (sig_boxtm (sig_shift_cong _ (pTrK_home hM₀ hX v h hR₀ hK c))))

/-- A home term's kept carrier along a witness whose arrow is realised. -/
theorem kept2_real (hX : CluFlags) (hT : ModalSys.T = true) (s : GW hF M₀) (I : ℕ) {y : VarSymb}
    (hy : ∃ Y, (ctxOf (glat s I)).ref y = some (.VTypeDia Y)) (v : GW hF M₀) (P : List ℕ)
    (h : v.1 = nodeOf (groot hF M₀).1 P)
    (hrl : (gw hM₀ v).Realised (kw (groot hF M₀) v P h (rorig s y))) {K : ℕ} {A : VarType}
    {c₀ : Ann A} (c : Term σ (ctxOf (glat v K)).boxIn A c₀)
    (hJI : pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K) ≤ I) :
    ∃ (L' : ℕ) (hL : max (pstg (groot hF M₀) v P h (rstg s I)) hrl.data.i₀ ≤ L') (hK : K ≤ L'),
      (⟨_, Term.mono (gle hM₀ v hL) (grealT hrl (Ctx.Le.refl _)
        (kw_decl hM₀ (groot hF M₀) v P h (rstg s I) (rorig_ref hX hM₀ s I hy))
        (pTrXK hM₀ (groot hF M₀) v P h (rstg s I) (rorig s y) (rorig_ref hX hM₀ s I hy)
          (preTD hX hM₀ s I hy (Term.mono (Ctx.le_boxIn_diaIn _ y)
            (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (.boxtm (Term.shift
              (Ctx.shifts_boxIn_boxIn hF _)
              (Term.mono (gle hM₀ s hJI).boxIn (homeT hM₀ hX s v c).2))))))).2).2).2⟩ :
        Σ e, Term σ (ctxOf (glat v L')) (.VTypeBox (.VTypeBox A)) e) =
      ⟨_, .boxtm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _)
        (Term.mono (gle hM₀ v hK).boxIn c)))⟩ := by
  obtain rfl : P = rpath v := nodeOf_inj (h.symm.trans (rpath_eq v))
  let R := max (rstg s I) (rstg v K)
  have hRI : rstg s I ≤ R := le_max_left _ _
  have hR₀ : rstg v K ≤ R := le_max_right _ _
  have hLm := pstg_monotone hM₀ (groot hF M₀) v (rpath v) h hRI
  have hKm : K ≤ pstg (groot hF M₀) v (rpath v) h R :=
    (le_pstg_pstgO hX.five hX.fourS hX.fourSW hM₀ (rpath v) (groot hF M₀) v (rpath_eq v) K).trans
      (pstg_monotone hM₀ (groot hF M₀) v (rpath v) h hR₀)
  have hx₀ := rorig_ref hX hM₀ s I hy
  have hxR : ∃ X, (ctxOf (glat (groot hF M₀) R)).ref (rorig s y) = some (.VTypeDia X) :=
    hx₀.imp fun _ e => (gle hM₀ (groot hF M₀) hRI).ref e
  have hy₀ := kw_decl hM₀ (groot hF M₀) v (rpath v) h (rstg s I) hx₀
  have hyR := kw_decl hM₀ (groot hF M₀) v (rpath v) h R hxR
  have hLL : pstg (groot hF M₀) v (rpath v) h R ≤
      max (pstg (groot hF M₀) v (rpath v) h R) hrl.data.i₀ := le_max_left _ _
  refine ⟨_, max_le_max hLm (le_refl _), hKm.trans hLL, ?_⟩
  let bk := Term.mono (gle hM₀ s hJI).boxIn (homeT hM₀ hX s v c).2
  let Xs := Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat s I)))
    (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat s I))) bk)))
  let rr := Term.mono (gle hM₀ (groot hF M₀) hR₀).boxIn (preTB hX hM₀ v K c).2
  let Xr := Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat (groot hF M₀) R)))
    (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat (groot hF M₀) R))) rr)))
  have e₀ := preTD_box hX hM₀ (Ctx.Le.refl _) hy Xs
  rw [Term.mono_refl, Term.mono_refl] at e₀
  have hb : (⟨_, Term.mono (gle hM₀ (groot hF M₀) hRI).boxIn (preTB hX hM₀ s I Xs).2⟩ :
      Σ c, Term σ _ _ c) = ⟨_, Xr⟩ :=
    (preTB_kept hM₀ hX s I hRI bk).trans (sig_boxtm (sig_shift_cong _ (sig_boxtm
      (sig_shift_cong _ (preTB_pTrK hM₀ hX s hRI hR₀ (gle hM₀ s hJI) (preTB hX hM₀ v K c).2)))))
  have hd : (⟨_, Term.mono ((gle hM₀ (groot hF M₀) hRI).kView (some (rorig s y)))
        (preTD hX hM₀ s I hy (Term.mono (Ctx.le_boxIn_diaIn _ y) Xs)).2⟩ :
        Σ c, Term σ _ _ c) = ⟨_, Term.mono (Ctx.le_boxIn_diaIn _ (rorig s y)) Xr⟩ := by
    refine (sig_mono _ e₀).trans ?_
    refine Eq.trans ?_ (sig_mono (Ctx.le_boxIn_diaIn _ (rorig s y)) hb)
    rw [Term.mono_mono, Term.mono_mono]
  have e₂ := (pTrXK_mono hM₀ (groot hF M₀) v (rpath v) h hRI (rorig s y) hx₀
    (preTD hX hM₀ s I hy (Term.mono (Ctx.le_boxIn_diaIn _ y) Xs)).2).trans
    ((pTrXK_sigma hM₀ (groot hF M₀) v (rpath v) h R (rorig s y) hxR hd).trans
      ((pTrXK_box (hM₀ := hM₀) (groot hF M₀) v (rpath v) h R (rorig s y) hxR Xr).trans
        (sig_mono _ (tr_keptK hM₀ hX (rpath v) (groot hF M₀) v h R rr))))
  refine (grealT_mono hrl hLm _ hyR _ _ e₂).trans ?_
  refine (grealT_box hM₀ hrl hyR _).trans ?_
  have hpk := (sig_mono (gle hM₀ v hLL).boxIn (pTrK_home hM₀ hX v h hR₀ hKm c)).trans
    (congrArg (Sigma.mk _) (Term.mono_mono _ _ c))
  exact (sig_collapse_cong _ (mono_kept (hF := hF) (gle hM₀ v hLL) _)).trans
    ((Term.collapse_boxtm_shift hT hF _).trans
      (sig_boxtm (sig_boxtm (sig_shift_cong _ hpk))))

/-! ## The far world, from a later stage here -/

/-- ⭐**A leg's far world, from a later stage here**: the same arrow read from stage `I`, agreeing
    with `C` at some later far stage; hole formulas go home from it; and a far term's home term
    has its kept carrier read as the far term's. -/
structure FarUp (hX : CluFlags) (s : GW hF M₀) {i I : ℕ} (hI : i ≤ I)
    (O : OutLeg (ctxOf (glat s i))) (v : GW hF M₀) {L : ℕ}
    (C : GTr σ O.view (ctxOf (glat v L))) where
  /-- The far stage. -/
  L' : ℕ
  /-- The chain from stage `I`. -/
  C' : GTr σ (O.mono (gle hM₀ s hI)).view (ctxOf (glat v L'))
  stage : ∃ (L₁ : ℕ) (h₁ : L ≤ L₁) (h₂ : L' ≤ L₁), ∀ {X : VarType} {x₀ : Ann X}
    (u : Term σ O.view X x₀),
    (⟨_, Term.mono (gle hM₀ v h₁) (C.app u).2⟩ : Σ c, Term σ (ctxOf (glat v L₁)) X c) =
      ⟨_, Term.mono (gle hM₀ v h₂) (C'.app (Term.mono (O.le_view_mono (gle hM₀ s hI)) u)).2⟩
  dia_hole : ∀ {X : VarType} {x₀ : Ann X} (u : Term σ (O.mono (gle hM₀ s hI)).view X x₀)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) X) 1),
    WFF.holeAt Ctx.NoSlots.slots (C'.app u).2 ψ ∈ (gw hM₀ v).M L' →
      (O.mono (gle hM₀ s hI)).dia (WFF.holeAt Ctx.NoSlots.slots u ψ) ∈ (gw hM₀ s).M I
  kept₂ : ∀ {K : ℕ} {A : VarType} {c₀ : Ann A} (c : Term σ (ctxOf (glat v K)).boxIn A c₀)
    (hJI : pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K) ≤ I),
    ∃ (L₂ : ℕ) (h₂ : L' ≤ L₂) (hK : K ≤ L₂),
      (⟨_, Term.mono (gle hM₀ v h₂) (C'.app (.boxtm (compBd hF (O.mono (gle hM₀ s hI))
        (Term.mono (gle hM₀ s hJI).boxIn (homeT hM₀ hX s v c).2)).2)).2⟩ :
        Σ e, Term σ (ctxOf (glat v L₂)) (.VTypeBox (.VTypeBox A)) e) =
      ⟨_, .boxtm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _)
        (Term.mono (gle hM₀ v hK).boxIn c)))⟩

/-- The plain leg's far world, from a later stage. -/
noncomputable def farUpNec (hX : CluFlags) (s : GW hF M₀) {i I : ℕ} (hI : i ≤ I)
    (a : CAcc hF M₀) : FarUp hM₀ hX s hI .nec a.1 (farNec hM₀ hX s i a).C where
  L' := (farNec hM₀ hX s I a).L
  C' := (farNec hM₀ hX s I a).C
  stage := by
    have hRi : rstg s i ≤ max (rstg s i) (rstg s I) := le_max_left _ _
    have hRI : rstg s I ≤ max (rstg s i) (rstg s I) := le_max_right _ _
    refine ⟨_, pstg_monotone hM₀ _ _ _ (pathOf_eq a.2.down) hRi,
      pstg_monotone hM₀ _ _ _ (pathOf_eq a.2.down) hRI, fun u => ?_⟩
    refine (sig_mono _ (preC_app hM₀ hX s i a u)).trans ?_
    refine Eq.trans ?_ (sig_mono _ (preC_app hM₀ hX s I a _)).symm
    exact (pTr_mono hM₀ _ _ _ _ (pathOf_ok a.2.down) hRi _).trans
      ((pTr_sigma hM₀ _ _ _ _ (pathOf_ok a.2.down) _
        (preTB_lift hM₀ hX s hI hRi hRI u).symm).trans
        (pTr_mono hM₀ _ _ _ _ (pathOf_ok a.2.down) hRI _).symm)
  dia_hole u ψ h := (farNec hM₀ hX s I a).dia_of _ (by
    rw [(farNec hM₀ hX s I a).trW_hole]
    exact h)
  kept₂ c hJI := by
    obtain ⟨L', hL, hK, e⟩ := kept2_path hM₀ hX s I a.1 _ (pathOf_eq a.2.down)
      (pathOf_ok a.2.down) c hJI
    exact ⟨L', hL, hK, (sig_mono _ (preC_app hM₀ hX s I a _)).trans e⟩

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- An arrow of a witness's extent is one at a later context. -/
theorem mem_ext_lift {M : Model σ} {Γ Γ' : Ctx} (h : Γ.Le Γ') {w : M.frame.W}
    {env : M.Env Γ w} {env' : M.Env Γ' w} (hag : Model.Env.Agree h env env') {y : VarSymb}
    {X X' : VarType} (h₁ : Γ.ref y = some (.VTypeDia X)) (h₂ : Γ'.ref y = some (.VTypeDia X'))
    (a₁ : (M.posEval (env.ref y h₁)).1) : a₁.1 ∈ (M.posEval (env'.ref y h₂)).1 := by
  obtain rfl : X = X' := by
    have e' := (h.ref h₁).symm.trans h₂
    simpa using e'
  rw [← Model.Env.ref_agree hag y h₁]
  exact a₁.2

/-- A witness's far world, from a later stage. -/
noncomputable def farUpPos (hX : CluFlags) (hT : ModalSys.T = true) (s : GW hF M₀) {i I : ℕ}
    (hI : i ≤ I) {y : VarSymb} (hy : ∃ Y, (ctxOf (glat s i)).ref y = some (.VTypeDia Y))
    (a : ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s i).ref y hy.choose_spec)).1)
    (hy' : ∃ Y, (ctxOf (glat s I)).ref y = some (.VTypeDia Y))
    (a' : ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s I).ref y hy'.choose_spec)).1)
    (ha : a'.1 = a.1) :
    FarUp hM₀ hX s hI (.pos y hy) a.1.1 (farPos hM₀ hX hT s i hy a).C := by
  obtain ⟨a₁, hm⟩ := a'
  obtain rfl : a₁ = a.1 := ha
  exact {
    L' := (farPos hM₀ hX hT s I hy' ⟨a.1, hm⟩).L
    C' := (farPos hM₀ hX hT s I hy' ⟨a.1, hm⟩).C
    stage := by
      have hRi : rstg s i ≤ max (rstg s i) (rstg s I) := le_max_left _ _
      have hRI : rstg s I ≤ max (rstg s i) (rstg s I) := le_max_right _ _
      have hrl := real_of_ext hM₀ hX hT s i hy.choose_spec a
      have hx₀ := rorig_ref hX hM₀ s i hy
      have hxI := rorig_ref hX hM₀ s I hy'
      have hxR : ∃ X, (ctxOf (glat (groot hF M₀) (max (rstg s i) (rstg s I)))).ref (rorig s y) =
          some (.VTypeDia X) := hx₀.imp fun _ e => (gle hM₀ (groot hF M₀) hRi).ref e
      have he := pathOf_eq a.1.2.down
      have hyi := kw_decl hM₀ (groot hF M₀) a.1.1 _ he (rstg s i) hx₀
      have hyI := kw_decl hM₀ (groot hF M₀) a.1.1 _ he (rstg s I) hxI
      have hyL := kw_decl hM₀ (groot hF M₀) a.1.1 _ he _ hxR
      refine ⟨_, max_le_max (pstg_monotone hM₀ _ _ _ he hRi) (le_refl _),
        max_le_max (pstg_monotone hM₀ _ _ _ he hRI) (le_refl _), fun u => ?_⟩
      have e₂ := pTrXK_sigma hM₀ (groot hF M₀) a.1.1 _ he _ (rorig s y) hxR
        (preTD_stage hM₀ hX s hI hRi hRI hy u)
      have e₃ := pTrXK_mono hM₀ (groot hF M₀) a.1.1 _ he hRi (rorig s y) hx₀
        (preTD hX hM₀ s i hy u).2
      have e₃' := pTrXK_mono hM₀ (groot hF M₀) a.1.1 _ he hRI (rorig s y) hxI
        (preTD hX hM₀ s I hy' (Term.mono ((gle hM₀ s hI).diaIn y) u)).2
      have e₄ := grealT_mono hrl (pstg_monotone hM₀ _ _ _ he hRi) hyi hyL _ _ e₃
      have e₄' := grealT_mono hrl (pstg_monotone hM₀ _ _ _ he hRI) hyI hyL _ _ e₃'
      refine (sig_mono _
        (real_app hM₀ (groot hF M₀) _ _ (rstg s i) (rorig s y) _ hrl _ _).symm).trans ?_
      refine Eq.trans ?_
        (sig_mono _ (real_app hM₀ (groot hF M₀) _ _ (rstg s I) (rorig s y) _ hrl _ _))
      exact e₄.trans ((grealT_sigma hrl _ hyL e₂).symm.trans e₄'.symm)
    dia_hole := fun u ψ h => (farPos hM₀ hX hT s I hy' ⟨a.1, hm⟩).dia_of _ (by
      rw [(farPos hM₀ hX hT s I hy' ⟨a.1, hm⟩).trW_hole]
      exact h)
    kept₂ := fun c hJI => by
      obtain ⟨L', hL, hK, e⟩ := kept2_real hM₀ hX hT s I hy' a.1.1 _ (pathOf_eq a.1.2.down)
        (real_of_ext hM₀ hX hT s i hy.choose_spec a) c hJI
      refine ⟨L', hL, hK, Eq.trans ?_ e⟩
      exact sig_mono _ (real_app hM₀ (groot hF M₀) _ _ (rstg s I) (rorig s y) _ _ _ _).symm }

/-- ⭐**What is possible along a leg is in the theory at the far end of an arrow** (T): the root's
    witnesses (`glex`, `cdia_mem_child`), with no induction hypothesis. -/
theorem exists_far (hX : CluFlags) (hT : ModalSys.T = true) (s : GW hF M₀) (I : ℕ)
    (O : OutLeg (ctxOf (glat s I))) (χ : WFF σ O.view 0) (hmem : O.dia χ ∈ (gw hM₀ s).M I) :
    ∃ (a : O.Arr (ccanonEnv hM₀ hX s I)) (F : FarLeg hM₀ hX s I O a),
      F.trW χ ∈ (gw hM₀ (O.acc (ccanonEnv hM₀ hX s I) a).1).M F.L ∧
      ∀ {I' : ℕ} (hI : I ≤ I'),
        Nonempty (FarUp hM₀ hX s hI O (O.acc (ccanonEnv hM₀ hX s I) a).1 F.C) := by
  cases O with
  | nec =>
      have hpath := box_pathO_iff hX.five hX.fourS hX.fourSW hM₀ (rpath s)
        (groot hF M₀) s (rpath_eq s) I χ.neg
      have hn' : WFF.box (preWP (rpre hX hM₀ s I) χ.neg) ∉
          (gw hM₀ (groot hF M₀)).M (rstg s I) :=
        fun h => ((gw hM₀ s).mcs I).neg_mem_iff.mp hmem (hpath.mp h)
      obtain ⟨t, ⟨c, hc⟩, -, hneg⟩ := glex hM₀ (groot hF M₀) (rstg s I) _ hn'
      have hR : GR (groot hF M₀) t := ⟨[c], pathOk_cons, hc⟩
      refine ⟨⟨t, ⟨hR⟩⟩, farNec hM₀ hX s I ⟨t, ⟨hR⟩⟩, ?_,
        fun hI => ⟨farUpNec hM₀ hX s hI ⟨t, ⟨hR⟩⟩⟩⟩
      have key : ∀ (P : List ℕ) (he : t.1 = nodeOf (groot hF M₀).1 P) (hok : PathOk P), P = [c] →
          pTrW hM₀ (groot hF M₀) t P he hok (rstg s I) (preWP (rpre hX hM₀ s I) χ) ∈
            (gw hM₀ t).M (pstg (groot hF M₀) t P he (rstg s I)) := by
        intro P he hok e
        subst e
        by_contra hnot
        have hneg' : (pTrW hM₀ (groot hF M₀) t [c] hc pathOk_cons (rstg s I)
            (preWP (rpre hX hM₀ s I) χ).neg).neg ∈ (gw hM₀ t).M _ := hneg
        rw [pTrW_neg hM₀] at hneg'
        exact ((gw hM₀ t).mcs _).neg_mem_iff.mp hneg' (((gw hM₀ t).mcs _).neg_mem_iff.mpr hnot)
      exact key _ _ _ (pathOf_of hR hc)
  | pos y hy =>
      have hpath := dia_pathO_iff hX.five hX.fourS hX.fourSW hM₀ (rpath s) (groot hF M₀) s
        (rpath_eq s) I hy.choose_spec χ
      obtain ⟨t, c, hc, hrl, hwd, hdecl, hR₂⟩ := cdia_mem_child hX hT s I hy.choose_spec χ
        (hpath.mpr hmem)
      have hR : GR (groot hF M₀) t := ⟨[c], pathOk_cons, hc⟩
      have hmt : (⟨t, ⟨hR⟩⟩ : CAcc hF M₀) ∈
          ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s I).ref y hy.choose_spec)).1 :=
        (ccanon_mem_iff hX s I hy.choose_spec _).mpr ((gmem_path hR (P := [c]) hc).mpr (Or.inl hrl))
      refine ⟨⟨⟨t, ⟨hR⟩⟩, hmt⟩, farPos hM₀ hX hT s I hy ⟨⟨t, ⟨hR⟩⟩, hmt⟩, ?_, fun {I'} hI => ?_⟩
      · have key : ∀ (P : List ℕ) (he : t.1 = nodeOf (groot hF M₀).1 P), P = [c] →
            ∀ (hrl' : (gw hM₀ t).Realised (kw (groot hF M₀) t P he (rorig s y))),
            grealW hM₀ hrl' (kw_decl hM₀ (groot hF M₀) t P he (rstg s I)
                (rorig_ref hX hM₀ s I hy))
              (pTrXKW hM₀ (groot hF M₀) t P he (rstg s I) (rorig s y) (rorig_ref hX hM₀ s I hy)
                (preWPX (rpre hX hM₀ s I) hy.choose_spec χ)) ∈ (gw hM₀ t).M _ := by
          intro P he e hrl'
          subst e
          exact hR₂
        exact key _ _ (pathOf_of hR hc) _
      · have hy' : ∃ Y, (ctxOf (glat s I')).ref y = some (.VTypeDia Y) :=
          hy.imp fun _ e => (gle hM₀ s hI).ref e
        exact ⟨farUpPos hM₀ hX hT s hI hy ⟨⟨t, ⟨hR⟩⟩, hmt⟩ hy'
          ⟨⟨t, ⟨hR⟩⟩, mem_ext_lift (gle hM₀ s hI) (ccanonEnv_le hX s hI) hy.choose_spec
            hy'.choose_spec ⟨⟨t, ⟨hR⟩⟩, hmt⟩⟩ rfl⟩

/-! ## From the far world's theory to here -/

/-- Weakening twice along a world's stages. -/
theorem sig_mono_gle (v : GW hF M₀) {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : a ≤ c)
    {T : VarType} {t₀ : Ann T} (t : Term σ (ctxOf (glat v a)) T t₀) :
    (⟨_, Term.mono (gle hM₀ v h₂) (Term.mono (gle hM₀ v h₁) t)⟩ :
      Σ e, Term σ (ctxOf (glat v c)) T e) = ⟨_, Term.mono (gle hM₀ v h₃) t⟩ := by
  rw [Term.mono_mono]

/-- ⭐⭐**A tie in the far world's theory is a `Back` here**: `y`, read at the far world, tied there
    to the far term `w`, so at a later stage here the `Back` of `y` is one of `w`'s home term
    (`Proof.back_of_tieV`); the home term's carrier reads there as `w`'s (`FarUp.kept₂`). -/
theorem back_home (hX : CluFlags) (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    {s : GW hF M₀} {i I : ℕ} (hI : i ≤ I) (O : OutLeg (ctxOf (glat s i))) {v : GW hF M₀} {L : ℕ}
    {C : GTr σ O.view (ctxOf (glat v L))} (U : FarUp hM₀ hX s hI O v C) {A : VarType} {K : ℕ}
    {y₀ a w₀ : Ann A} (y : Term σ (ctxOf (glat s i)).boxIn A y₀)
    (u : Term σ (ctxOf (glat s i)) A a) (w : Term σ (ctxOf (glat v K)).boxIn A w₀)
    (hJI : pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K) ≤ I)
    (hb : WFF.back hS .nec (Term.boxtm (Term.boxtm
      (Term.shift (Ctx.shifts_boxIn_boxIn hF _) y))) u ∈ (gw hM₀ s).M i)
    (htie : ∀ (L₃ : ℕ) (h : L ≤ L₃) (hK : K ≤ L₃), WFF.box (WFF.holeAt Ctx.NoSlots.slots
      (Term.pair (Term.mono (gle hM₀ v h).boxIn
          (C.box.app (Term.mono O.le_view.boxIn
            (Term.shift (Ctx.shifts_boxIn_boxIn hF _) y))).2)
        (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (Term.mono (gle hM₀ v hK).boxIn w))))
      (WFF.backDup hS hF A)) ∈ (gw hM₀ v).M L₃) :
    WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _)
      (Term.mono (gle hM₀ s hJI).boxIn (homeT hM₀ hX s v w).2))))
      (Term.mono (gle hM₀ s hI) u) ∈ (gw hM₀ s).M I := by
  obtain ⟨L₁, h₁, h₂, hst⟩ := U.stage
  obtain ⟨L₂, h₃, hK, ek⟩ := U.kept₂ w hJI
  have h₁₃ : L₁ ≤ max L₁ L₂ := le_max_left _ _
  have h₂₃ : L₂ ≤ max L₁ L₂ := le_max_right _ _
  have hL' : U.L' ≤ max L₁ L₂ := h₂.trans h₁₃
  have hL : L ≤ max L₁ L₂ := h₁.trans h₁₃
  have hK₃ : K ≤ max L₁ L₂ := hK.trans h₂₃
  let k := Term.mono (gle hM₀ s hJI).boxIn (homeT hM₀ hX s v w).2
  let O' := O.mono (gle hM₀ s hI)
  let Y := Term.mono (gle hM₀ s hI).boxIn y
  have hsh : Term.shift (Ctx.shifts_boxIn_boxIn hF _) Y =
      Term.mono (gle hM₀ s hI).boxIn.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF _) y) :=
    Term.shift_mono _ _ _ _ y
  have hbI : WFF.back hS .nec (Term.boxtm (Term.boxtm
      (Term.shift (Ctx.shifts_boxIn_boxIn hF _) Y))) (Term.mono (gle hM₀ s hI) u) ∈
      (gw hM₀ s).M I := by
    rw [hsh]
    exact (gw hM₀ s).sub hI _ hb
  let u₀ := Term.boxtm (Term.mono O.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF _) y))
  let x := Term.mono O'.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF _) Y)
  have hu : (⟨_, Term.mono (O.le_view_mono (gle hM₀ s hI)) u₀⟩ : Σ e, Term σ _ _ e) =
      ⟨_, Term.boxtm x⟩ := by
    refine sig_boxtm ?_
    change (⟨_, Term.mono _ (Term.mono _ _)⟩ : Σ e, Term σ _ _ e) = ⟨_, Term.mono _ _⟩
    rw [hsh, Term.mono_mono, Term.mono_mono]
  have hx₀ : (⟨_, Term.mono (gle hM₀ v h₂) (U.C'.app (Term.boxtm x)).2⟩ : Σ e, Term σ _ _ e) =
      ⟨_, Term.mono (gle hM₀ v h₁) (Term.boxtm (C.box.app (Term.mono O.le_view.boxIn
        (Term.shift (Ctx.shifts_boxIn_boxIn hF _) y))).2)⟩ :=
    (congrArg (fun p => (⟨_, Term.mono (gle hM₀ v h₂) (U.C'.app p.2).2⟩ : Σ e, Term σ _ _ e))
      hu.symm).trans ((hst u₀).symm.trans (sig_mono _ (GTr.app_boxtm C _)))
  let C₃ := U.C'.comp (.mono (gle hM₀ v hL') (.nil _))
  have hC₃ : ∀ {X : VarType} {x₀ : Ann X} (t : Term σ O'.view X x₀),
      C₃.app t = ⟨_, Term.mono (gle hM₀ v hL') (U.C'.app t).2⟩ := fun t => GTr.app_comp _ _ t
  have hx : C₃.app (Term.boxtm x) = ⟨_, Term.boxtm (Term.mono (gle hM₀ v hL).boxIn
      (C.box.app (Term.mono O.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF _) y))).2)⟩ :=
    (hC₃ _).trans ((sig_mono_gle hM₀ v h₂ h₁₃ hL' _).symm.trans
      ((sig_mono (gle hM₀ v h₁₃) hx₀).trans
      (sig_mono_gle hM₀ v h₁ h₁₃ hL _)))
  have hy : C₃.app (Term.boxtm (compBd hF O' k).2) = ⟨_, Term.boxtm (Term.boxtm (Term.shift
      (Ctx.shifts_boxIn_boxIn hF _) (Term.mono (gle hM₀ v hK₃).boxIn w)))⟩ := by
    refine (hC₃ _).trans ((sig_mono_gle hM₀ v h₃ h₂₃ hL' _).symm.trans
      ((sig_mono (gle hM₀ v h₂₃) ek).trans (sig_boxtm (sig_boxtm ?_))))
    rw [← Term.shift_mono (Ctx.shifts_boxIn_boxIn hF _) (Ctx.shifts_boxIn_boxIn hF _)
      (gle hM₀ v h₂₃).boxIn (gle hM₀ v h₂₃).boxIn.boxIn, Term.mono_mono]
  have hd : O'.dia (WFF.box (WFF.holeAt Ctx.NoSlots.slots (Term.pair x (compBd hF O' k).2)
      (WFF.backDup hS hF A))) ∈ (gw hM₀ s).M I := by
    rw [← WFF.holeAt_boxHole Ctx.NoSlots.slots]
    refine U.dia_hole _ _ ?_
    refine (BWorld.mem_lift hL').mpr ?_
    rw [WFF.mono_holeAt _ Ctx.NoSlots.slots Ctx.NoSlots.slots]
    refine (congrArg (· ∈ _) (WFF.holeAt_congr Ctx.NoSlots.slots
      ((hC₃ _).symm.trans (GTr.app_boxtm_pair C₃ hx hy)) _)).mpr ?_
    rw [WFF.holeAt_boxHole]
    exact htie _ hL hK₃
  exact (gw hM₀ s).mem_of_provable (Δ := [_, _]) (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hbI
      · rw [List.mem_singleton.mp hψ]
        exact hd)
    ⟨Proof.back_of_tieV hS hT hF O' k Y _ (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩

/-- What a `Back` along the plain leg says of its home term: it is related to the value. -/
theorem ind_of_back (hX : CluFlags) (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    {s : GW hF M₀} {I : ℕ} {A : VarType} {k₀ : Ann A} (k : Term σ (ctxOf (glat s I)).boxIn A k₀)
    {a : Ann A} (t : Term σ (ctxOf (glat s I)) A a)
    (hb : WFF.back hS .nec (Term.boxtm (Term.boxtm
      (Term.shift (Ctx.shifts_boxIn_boxIn hF _) k))) t ∈ (gw hM₀ s).M I) :
    cInd hM₀ hX (ctoDom hM₀ hX A s (cden hM₀ hX s I (Ctx.Le.refl _)
        (Term.collapse (Ctx.collapses_boxIn_self hT _) k)) (cdefinable_den hX _ _))
      (ctoDom hM₀ hX A s (cden hM₀ hX s I (Ctx.Le.refl _) t) (cdefinable_den hX _ _)) := by
  refine ⟨⟨I, _, Term.collapse (Ctx.collapses_boxIn_self hT _) (Term.collapse
      (Ctx.collapses_boxIn_self hT _) (Term.shift (Ctx.shifts_boxIn_boxIn hF _) k))⟩,
    ⟨I, _, t⟩, ?_, ?_, BWorld.back_here_rel (gw hM₀ s) hS hT _ _ hb⟩
  · change _ = cfromDom hM₀ hX A s (ctoDom hM₀ hX A s _ _)
    rw [cfromDom_toDom]
    exact cden_sigma (hM₀ := hM₀) hX (s := s) (i := I) (Ctx.Le.refl _)
      (sig_collapse_cong (Ctx.collapses_boxIn_self hT _) (Term.collapse_shift_boxIn hT hF k))
  · exact (cfromDom_toDom hM₀ hX A s _ _).symm

/-- A companion of a far object, read home, is what its contents' home term denotes
    (`comps_home`, one companion). -/
theorem comp_home (hX : CluFlags) (hT : ModalSys.T = true) (s v : GW hF M₀)
    (r : (cframe hF hM₀ hX).R v s) {A : VarType} {q : List Step} {ps : List (List Step)}
    (h : A.CompOk (q :: ps)) {K I : ℕ} {e₀ : Ann A}
    (E₀ : Term σ (ctxOf (glat v K)).boxIn A e₀)
    (hJI : pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K) ≤ I) :
    (cmodel hF hM₀ hX).compRead hT (.VTypeBox A) (.here :: q)
        (ctoDom hM₀ hX _ _ (cden hM₀ hX v K (Ctx.Le.refl _) (.boxtm E₀)) (cdefinable_den hX _ _))
        r =
      ctoDom hM₀ hX _ s (cden hM₀ hX s I (Ctx.Le.refl _) (Term.collapse
        (Ctx.collapses_boxIn_self hT _) (Term.mono (gle hM₀ s hJI).boxIn
          (homeT hM₀ hX s v (compVal E₀ q h).2).2))) (cdefinable_den hX _ _) := by
  have hR : GR (groot hF M₀) s := (carrows hF M₀).refl hT s
  have e : Model.interp ((ccanonEnv hM₀ hX v K).boxPush ⟨s, ⟨r⟩⟩) (compVal E₀ q h).2 =
      (cmodel hF hM₀ hX).compRead hT (.VTypeBox A) (.here :: q)
        (Model.interp (ccanonEnv hM₀ hX v K) (.boxtm E₀)) r :=
    congrArg Prod.snd (Model.interp_compsVal (ccanonEnv hM₀ hX v K) E₀ s r (q :: ps) h)
  rw [← interp_ccanon hX (.boxtm E₀) (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _), ← e,
    ← Model.box_beta (ccanonEnv hM₀ hX v K) (compVal E₀ q h).2 ⟨s, ⟨r⟩⟩,
    interp_ccanon hX (.boxtm (compVal E₀ q h).2) (Model.Env.Agree.refl' _)
      (Ctx.Presented.noProjLast _)]
  refine ctoDom_congr hX ?_ _ _
  exact (congrFun (cden_home hM₀ hX s v hJI (compVal E₀ q h).2).symm ⟨s, ⟨hR⟩⟩).trans
    (cden_boxtm_own hX hT s I _ hR)

/-- A `Back` of a home term at a later stage relates the home term to the value's meaning. -/
theorem indM_of_back (hX : CluFlags) (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    {s : GW hF M₀} {j I : ℕ} (hI : j ≤ I) {A : VarType} {k₀ : Ann A}
    (k : Term σ (ctxOf (glat s I)).boxIn A k₀) {a : Ann A} (u : Term σ (ctxOf (glat s j)) A a)
    (hb : WFF.back hS .nec (Term.boxtm (Term.boxtm
      (Term.shift (Ctx.shifts_boxIn_boxIn hF _) k))) (Term.mono (gle hM₀ s hI) u) ∈
        (gw hM₀ s).M I) :
    (cmodel hF hM₀ hX).Ind (ctoDom hM₀ hX A s (cden hM₀ hX s I (Ctx.Le.refl _)
        (Term.collapse (Ctx.collapses_boxIn_self hT _) k)) (cdefinable_den hX _ _))
      (Model.interp (ccanonEnv hM₀ hX s j) u) := by
  have e : Model.interp (ccanonEnv hM₀ hX s j) u = ctoDom hM₀ hX A s (cden hM₀ hX s I
      (Ctx.Le.refl _) (Term.mono (gle hM₀ s hI) u)) (cdefinable_den hX _ _) :=
    (Model.interp_mono (ccanonEnv_le hX s hI) u).symm.trans
      (interp_ccanon hX _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _))
  rw [e]
  exact ⟨fun _ => ind_of_back hM₀ hX hS hT k _ hb, fun hn => absurd (hT.symm.trans hn) (by decide)⟩

/-- ⭐⭐**A value and a far object tied to it agree, read home**, with companions.  `b`, read at the
    far world, has `E₀` as its base, so the base goes home by `back_home` with `Proof.back_shift`
    for the tie; each companion's tie is in the far world's theory (`cTies_step`). -/
theorem comps_ind (hX : CluFlags) (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    {s : GW hF M₀} {j I : ℕ} (hI : j ≤ I) (O : OutLeg (ctxOf (glat s j))) {v : GW hF M₀} {L : ℕ}
    {C : GTr σ O.view (ctxOf (glat v L))} (U : FarUp hM₀ hX s hI O v C)
    (r : (cframe hF hM₀ hX).R v s) {A : VarType} {e₀ : Ann A}
    (E₀ : Term σ (ctxOf (glat v L)).boxIn A e₀)
    (hJI : pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v L) ≤ I) {Ω : Ctx} {d : ℕ}
    {ι : VarSymb → VarSymb} (θ : Subst σ (ctxOf (glat v L))) (hθ : Subst.Ok Ω θ)
    (hc : Subst.Coh ι Ω θ) (hs : Ω.SlotsFrom d) (hs' : (ctxOf (glat v L)).SlotsFrom 0)
    (e : VarSymb) (he : Ω.ref e = some (.VTypeBox A)) (hat : θ.at e = .tm (.boxtm E₀)) :
    ∀ (cs : List (List Step)) (h : A.CompOk cs) (z : VarSymb)
      (hz : Ω.boxIn.ref z = some (A.compsFlat cs)) {b₀ : Ann (A.compsFlat cs)}
      (b : Term σ (ctxOf (glat s j)).boxIn (A.compsFlat cs) b₀) {a : Ann (A.compsFlat cs)}
      (t : Term σ (ctxOf (glat s j)) (A.compsFlat cs) a),
      WFF.back hS .nec (Term.boxtm (Term.boxtm
        (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b))) t ∈ (gw hM₀ s).M j →
      θ.box.at z = .tm (C.box.app (Term.mono O.le_view.boxIn
        (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b))).2 →
      compsBase cs (C.box.app (Term.mono O.le_view.boxIn
        (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b))).2 = ⟨_, E₀⟩ →
      WFF.subst ι θ hθ hc hs hs' (WFF.cTies hS hF hs e he cs h z hz) ∈ (gw hM₀ v).M L →
      (cmodel hF hM₀ hX).Ind ((cmodel hF hM₀ hX).compsRead A cs h
          (ctoDom hM₀ hX _ _ (cden hM₀ hX v L (Ctx.Le.refl _) (.boxtm E₀))
            (cdefinable_den hX _ _)) r)
        (Model.interp (ccanonEnv hM₀ hX s j) t)
  | [], h, _, _, _, b, _, t, hb, _, hbase, _ => by
      rw [comps_home hM₀ hX hT s v r h E₀ hJI]
      refine indM_of_back hM₀ hX hS hT hI _ t (back_home hM₀ hX hS hT hI O U b t E₀ hJI hb ?_)
      intro L₃ h' hK
      refine (congrArg (· ∈ _) (congrArg WFF.box (WFF.holeAt_congr _
        (sig_pair (sig_mono (gle hM₀ v h').boxIn hbase) rfl) _))).mpr ?_
      rw [WFF.holeAt_backDup]
      exact (gw hM₀ v).mem_of_provable (Δ := []) (fun _ hψ => by cases hψ)
        ⟨Proof.K_box (Δ := []) (Proof.back_shift hS hT hF _)⟩
  | q :: ps, h, z, hz, _, .pair b₁ y, _, .pair t₁ u, hb, hzat, hbase, hties => by
      have hp := GTr.app_pair C.box (Term.mono O.le_view.boxIn
        (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b₁)) (Term.mono O.le_view.boxIn
        (Term.shift (Ctx.shifts_boxIn_boxIn hF _) y))
      have hzat' : θ.box.at z = .tm (Term.pair (C.box.app (Term.mono O.le_view.boxIn
          (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b₁))).2 (C.box.app (Term.mono O.le_view.boxIn
          (Term.shift (Ctx.shifts_boxIn_boxIn hF _) y))).2) :=
        hzat.trans (congrArg (fun p => SubE.tm p.2) hp)
      rw [cTies_step θ hθ hc hs hs' hS hT hF E₀ e he hat q ps h z hz _ _ hzat'] at hties
      obtain ⟨hq, hrest⟩ := ((gw hM₀ v).mcs L).and_mem_iff.mp hties
      have hb₁ := (gw hM₀ s).mem_of_provable (Δ := [_]) (fun ψ hψ => by
        rw [List.mem_singleton.mp hψ]
        exact hb) ⟨Proof.back_fst hS _ _ _ _ (Proof.lookup List.mem_cons_self)⟩
      have hb₂ := (gw hM₀ s).mem_of_provable (Δ := [_]) (fun ψ hψ => by
        rw [List.mem_singleton.mp hψ]
        exact hb) ⟨Proof.back_snd hS _ _ _ _ (Proof.lookup List.mem_cons_self)⟩
      have I₁ := comps_ind hX hS hT hI O U r E₀ hJI θ hθ hc hs hs' e he hat ps h.tail _
        (Ctx.ref_fst_of hz) b₁ t₁ hb₁ (by rw [Subst.at_proj _ _ rfl, hzat']; rfl)
        ((compsBase_sig (q :: ps) hp).symm.trans hbase) hrest
      have I₂ := indM_of_back hM₀ hX hS hT hI _ u (back_home hM₀ hX hS hT hI O U y u
        (compVal E₀ q h).2 hJI hb₂ (fun L₃ h' hK => by
          have h₁ := (BWorld.mem_lift h').mp hq
          change WFF.box (WFF.mono _ (WFF.holeAt _ _ _)) ∈ _ at h₁
          rw [WFF.mono_holeAt _ Ctx.NoSlots.slots Ctx.NoSlots.slots] at h₁
          exact (congrArg (· ∈ _) (congrArg WFF.box (WFF.holeAt_congr _ (sig_pair rfl
            (sig_boxtm (congrArg (Sigma.mk _) (Term.shift_mono (Ctx.shifts_boxIn_boxIn hF _)
              (Ctx.shifts_boxIn_boxIn hF _) (gle hM₀ v h').boxIn (gle hM₀ v h').boxIn.boxIn
              _).symm))) _))).mp h₁))
      rw [← comp_home hM₀ hX hT s v r h E₀ hJI] at I₂
      exact (cindCongr hM₀ hX).pair I₁ I₂

/-- ⭐⭐**A returning possibility in the theory comes true** (strong B), at a boxed object with
    companions, along either leg.  `BWorld.ret_term` names the object; `exists_far` gives an arrow
    with the body and the ties in the far theory; the body is true there by the induction, and the
    ties bring the far object home (`comps_ind`). -/
theorem sat_ret_of_memC (hX : CluFlags) (hS : ModalSys.BStrong = true) {s : GW hF M₀} {i : ℕ}
    (O : OutLeg (ctxOf (glat s i))) {A : VarType} {cs : List (List Step)} (h : A.CompOk cs)
    {a : Ann (A.compsFlat cs)} (t : Term σ (ctxOf (glat s i)) (A.compsFlat cs) a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1)
    (IH : ∀ (s' : GW hF M₀) (K : ℕ) (φ : WFF σ (ctxOf (glat s' K)) 0), φ.size ≤ Φ.size →
      ((cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s' K) φ ↔ φ ∈ (gw hM₀ s').M K))
    (hmem : O.retS hS (.nec (.boxC A cs h)) t Φ ∈ (gw hM₀ s).M i) :
    (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s i)
      (O.retS hS (.nec (.boxC A cs h)) t Φ : WFF σ _ 0) := by
  have hT := hX.bT (hX.bS hS)
  obtain ⟨j, hij, b₀, b, hB, hD⟩ := (gw hM₀ s).ret_term hS hT hF O h t Φ hmem
  rw [WFF.instantiate_packedBody_boxC hS hF h] at hD
  obtain ⟨a₀, F, hm, hU⟩ := exists_far hM₀ hX hT s j _ _ hD
  rw [F.trW_and] at hm
  obtain ⟨hm₁, hm₂⟩ := ((gw hM₀ _).mcs _).and_mem_iff.mp hm
  rw [F.trW_hole] at hm₂
  let O₁ := O.mono (gle hM₀ s hij)
  let s₀ := Term.mono O₁.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b)
  let bs := (compsBase cs s₀).2
  let E₀ := (compsBase cs (F.C.box.app s₀).2).2
  let v := (O₁.acc (ccanonEnv hM₀ hX s j) a₀).1
  have hB₀ : F.C.app (Term.boxtm bs) = ⟨_, Term.boxtm E₀⟩ :=
    (GTr.app_boxtm F.C bs).trans (sig_boxtm (app_compsBase F.C.box cs s₀))
  have hP : F.C.app (Term.pair (Term.boxtm bs) (Term.boxtm s₀)) =
      ⟨_, Term.pair (Term.boxtm E₀) (Term.boxtm (F.C.box.app s₀).2)⟩ := by
    rw [GTr.app_pair]
    exact sig_pair hB₀ (GTr.app_boxtm F.C s₀)
  have hties := (congrArg (· ∈ _) (WFF.holeAt_congr Ctx.NoSlots.slots hP _)).mp hm₂
  have hval : Model.interp (O₁.push (ccanonEnv hM₀ hX s j) a₀) (Term.boxtm bs) =
      ctoDom hM₀ hX _ _ (cden hM₀ hX v F.L (Ctx.Le.refl _) (Term.boxtm E₀))
        (cdefinable_den hX _ _) := by
    rw [interp_ctr hX (Term.boxtm bs) F.C F.ag F.npl O₁.noProjLast]
    exact ctoDom_congr hX (cden_sigma hX _ hB₀) _ _
  have hsat := (Model.sat_instantiate _ O₁.noProjLast _ _ _).mp ((F.sat_trW _).mpr
    ((IH _ _ _ (by rw [F.size_trW, WFF.size_instantiate, WFF.size_mono])).mpr hm₁))
  have hR : GR (groot hF M₀) s := (carrows hF M₀).refl hT s
  refine (Model.sat_mono (ccanonEnv_le hX s hij) _).mp ?_
  rw [OutLeg.mono_retS]
  refine (OutLeg.sat_retS (M := cmodel hF hM₀ hX) (d := 0) hS (ccanonEnv hM₀ hX s j) O₁
    (.nec (.boxC A cs h)) _ _).mpr ⟨a₀, _, hsat, hR, ?_⟩
  have hJI : pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v F.L) ≤
      max j (pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v F.L)) := le_max_right _ _
  obtain ⟨U⟩ := hU (le_max_left j (pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v F.L)))
  have hr := Subst.at_single_root (σ := σ) (Δ := ctxOf (glat v F.L)) (.bnd 0)
    (.tm (Term.pair (Term.boxtm E₀) (Term.boxtm (F.C.box.app s₀).2)))
  have hI := comps_ind hM₀ hX hS hT _ O₁ U hR E₀ hJI _ _ _ _ _ _ _
    (by rw [Subst.at_proj _ _ rfl, hr]; rfl) cs h _ _ b _ hB
    (Subst.box_at_inner_boxtm _ (by rw [Subst.at_proj _ _ rfl, hr]; rfl)) rfl hties
  change (cmodel hF hM₀ hX).compsBack A cs _ _ _
  rw [hval]
  exact Model.compsBack_of_indC (cindCongr hM₀ hX) A _ _ cs h _ hI

/-- ⭐⭐**A returning possibility of a necessary shape in the theory comes true** (strong B), along
    either leg: packed (`retS_packG`), true there (`sat_ret_of_memC`), and mapped back
    (`sat_ret_map` along `unpackG`). -/
theorem sat_ret_of_memN (hX : CluFlags) (hS : ModalSys.BStrong = true) {s : GW hF M₀} {i : ℕ}
    (O : OutLeg (ctxOf (glat s i))) (N : NShape) {a : Ann N.flat}
    (t : Term σ (ctxOf (glat s i)) N.flat a) (Φ : WFF σ (O.view.insert (.bnd 0) N.ty) 1)
    (IH : ∀ (s' : GW hF M₀) (K : ℕ) (φ : WFF σ (ctxOf (glat s' K)) 0), φ.size ≤ Φ.size →
      ((cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s' K) φ ↔ φ ∈ (gw hM₀ s').M K))
    (hmem : (O.retS hS (.nec N) t Φ : WFF σ _ 0) ∈ (gw hM₀ s).M i) :
    (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s i) (O.retS hS (.nec N) t Φ : WFF σ _ 0) := by
  have hp := (gw hM₀ s).mem_of_provable (Δ := [_]) (fun ψ hψ => by
    rw [List.mem_singleton.mp hψ]
    exact hmem) ⟨retS_packG hS O t Φ (Proof.lookup List.mem_cons_self)⟩
  have hsat := sat_ret_of_memC hM₀ hX hS O N.packOk _ _ (fun s' K φ hφ => IH s' K φ (by
    unfold WFF.bodyRepl at hφ
    rw [WFF.size_subst] at hφ
    exact hφ)) hp
  have hb := Model.sat_ret_map (ccanonEnv hM₀ hX s i) (Ctx.Presented.noProjLast _)
    (cindCongr hM₀ hX) hS O (S := .nec N.packed) (unpackG N) _ Φ hsat
  refine (congrArg ((cmodel hF hM₀ hX).sat _) (OutLeg.retS_congr hS O (.nec N) ?_ rfl)).mp hb
  rw [Term.holeRead_eq_holeAt, Term.holeRead_eq_holeAt]
  exact holeAt_packG_unpackG_val N t

end GArrow

end V12M
