import QML.QML_v12m_GCluRetOut
import QML.QML_v12m_BRetOutDC

/-!
# QML v12m — 5 on the growing tree: returning possibilities at witnessed shapes

A witnessed returning possibility is a necessary one, with a possible object kept, and that object
realised here (`Proof.ret_keep`), so both directions of the truth lemma at a witnessed shape come
from the necessary shapes and `Here`.

* `Term.collapse_keptDia`, `rnm_keepDia`, ⭐`cden_kept`, `interp_kept`: a kept possible object, read
  along an arrow, is the object: raw possible objects do not depend on the world.
* `WFF.subst_liftedW`, ⭐`BWorld.retW_term`, `WFF.instantiate_packedBodyW_boxC`: `Proof.retWN_lift`,
  read at a term of a later stage.
* `Model.interp_keepL`, `sat_nec_keep`, ⭐⭐`mem_ret_of_satW`: truth ⇒ membership, by
  `Proof.ret_keep`.
* ⭐⭐`sat_ret_of_memWC`, `sat_ret_of_memW`: membership ⇒ truth, by `Model.sat_ret_keep`.
-/

namespace V12M

variable [ModalSys]

open BArrow GArrow

section LiftRead

variable {σ : Signature} {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] {F X : VarType}

/-- ⭐What `Proof.retW_lift` says, of a term in place of its fresh variable. -/
theorem WFF.subst_liftedW (h : Γ.Le Γ') (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) (O : OutLeg Γ) {a₁ : Ann F} {a₂ : Ann X} (t₁ : Term σ Γ F a₁)
    (t₂ : Term σ Γ X a₂) (Ψ : WFF σ (O.view.insert (.bnd 0) (wTy F X)) 1) (c : ℕ)
    (hc : Γ.RootFresh (.free c)) {b₀ : Ann F} (b : Term σ Γ'.boxIn F b₀) {x : VarSymb}
    (hx : ∃ Y, Γ'.ref x = some (.VTypeDia Y)) {d₀ : Ann X} (bd : Term σ (Γ'.diaIn x) X d₀) :
    WFF.subst (Subst.singleIdx (.free c) (.tm (Term.pair (Term.boxtm b) (Term.diatm x hx bd))))
        (Subst.single (.free c) (.tm (Term.pair (Term.boxtm b) (Term.diatm x hx bd))))
        (Subst.ok_single h rfl) (Subst.coh_single hc h rfl)
        ((Ctx.NoSlots.slots (Γ := Γ)).insertFree c _) Ctx.NoSlots.slots
        (WFF.liftedW hS hT hF O t₁ t₂ Ψ c hc) =
      WFF.and (WFF.and (WFF.back hS .nec (Term.boxtm (Term.boxtm
          (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ') b))) (Term.mono h t₁))
          (WFF.here hT (Term.diatm x hx bd) (Term.mono h t₂)))
        ((O.mono h).dia (WFF.instantiate Ctx.NoSlots.slots
          (Term.pair (Term.boxtm (Term.mono (O.mono h).le_view.boxIn
              (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ') b)))
            (Term.mono (O.mono h).le_view (Term.keptDia hF hx bd).2))
          (WFF.mono ((O.le_view_mono h).insert (.bnd 0) _) Ψ))) := by
  let θ := Subst.single (σ := σ) (Δ := Γ') (.free c)
    (.tm (Term.pair (Term.boxtm b) (Term.diatm x hx bd)))
  have hat : θ.at (.root (.free c)) = .tm (Term.pair (Term.boxtm b) (Term.diatm x hx bd)) :=
    Subst.at_single_root _ _
  have hid : ∀ v U, Γ.ref v = some U → θ.at v = .ren v :=
    fun v _ hv => Subst.single_at_ne (Ctx.ref_rt_ne hc hv)
  have hθ : Subst.Ok (Γ.insert (.free c) (wTy F X)) θ := Subst.ok_single h rfl
  have hc' : Subst.Coh (Subst.singleIdx (.free c)
      (.tm (Term.pair (Term.boxtm b) (Term.diatm x hx bd))))
      (Γ.insert (.free c) (wTy F X)) θ := Subst.coh_single hc h rfl
  have h₀ := Ctx.ref_insert_root Γ (.free c) (wTy F X)
  have hf : θ.at (.step (.root (.free c)) .fst) = .tm (Term.boxtm b) := by
    rw [Subst.at_proj _ _ rfl, hat]
    rfl
  have hs : θ.at (.step (.root (.free c)) .snd) = .tm (Term.diatm x hx bd) := by
    rw [Subst.at_proj _ _ rfl, hat]
    rfl
  have ef := Term.subst_eta_tm θ hθ hc' _ _ (Ctx.ref_fst_of h₀) _ hf
  have es := Term.subst_eta_tm θ hθ hc' _ _ (Ctx.ref_snd_of h₀) _ hs
  have hk₁ : θ.box.at (.step (.step (.root (.free c)) .fst) .keep) =
      .tm (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ') b)) := by
    rw [Subst.box_at_keep, hf]
    exact SubE.keepE_tm b hF
  have hk₂ : θ.box.at (.step (.step (.root (.free c)) .snd) .keep) =
      .tm (Term.keptDia hF hx bd).2 := by
    rw [Subst.box_at_keep, hs]
    exact SubE.keepE_dia x hx bd hF
  have hu : (⟨_, Term.subst _ θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc')
      (wKeep hF (Ctx.ref_fst_of h₀) (Ctx.ref_snd_of h₀)).2⟩ : Σ e, Term σ Γ'.boxIn (wTy F X) e) =
      ⟨_, Term.pair (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ') b))
        (Term.keptDia hF hx bd).2⟩ :=
    sig_pair (Term.subst_eta_tm _ _ _ _ _ _ _ hk₁) (Term.subst_eta_tm _ _ _ _ _ _ _ hk₂)
  have hw : ∀ {T : VarType} {e : Ann T} (u : Term σ Γ T e),
      (⟨_, Term.subst _ θ hθ hc' (Term.weaken hc.root _ u)⟩ : Σ e', Term σ Γ' T e') =
        ⟨_, Term.mono h u⟩ := fun u => by
    unfold Term.weaken
    rw [Term.subst_mono]
    exact Term.subst_ren h _ _ _ hid u
  refine congrArg₂ WFF.and (congrArg₂ WFF.and ?_ (WFF.here_congr hT es (hw t₂))) ?_
  · exact (WFF.subst_holeAt θ hθ hc' _ _ _ _).trans ((WFF.holeAt_congr _
      (sig_pair (hw t₁) (sig_pair ef es)) _).trans (WFF.holeAt_backG hS Ctx.NoSlots.slots _ _ _))
  · cases O with
    | nec =>
        refine (OutLeg.subst_dia θ hθ hc' _ _ .nec _).trans (congrArg (OutLeg.nec).dia ?_)
        exact WFF.subst_instantiate_ren (Ctx.le_insert hc.root _).boxIn h.boxIn θ.box _ _ _ _
          (Subst.ren_box hid) _ _
          ((OutLeg.subst_mono_le_view θ hθ hc' .nec _).trans (sig_mono _ hu)) Ψ
    | pos y hy =>
        have hιy : Subst.singleIdx (.free c)
            (.tm (Term.pair (Term.boxtm b) (Term.diatm x hx bd))) y = y :=
          if_neg (Ctx.ref_rt_ne hc hy.choose_spec)
        have hy₁ : ∃ Y, (Γ.insert (.free c) (wTy F X)).ref y = some (.VTypeDia Y) :=
          hy.imp fun _ e => (Ctx.le_insert hc.root _).ref e
        have hθy : Subst.Ok ((Γ.insert (.free c) (wTy F X)).diaIn y) (θ.dia y y) :=
          Subst.ok_dia hθ hy₁ ((hy₁.elim fun _ hY => hc' y _ hY []).trans hιy)
        have hcy : Subst.Coh (Subst.singleIdx (.free c)
            (.tm (Term.pair (Term.boxtm b) (Term.diatm x hx bd))))
            ((Γ.insert (.free c) (wTy F X)).diaIn y) (θ.dia y y) := by
          have := Subst.coh_dia hθ hc' hy₁
          rwa [hιy] at this
        refine (WFF.subst_dia θ hθ hc' _ _ hy₁ y hιy (hy.imp fun _ e => h.ref e) hθy hcy
          ((Ctx.NoSlots.slots (Γ := Γ')).diaIn y) _).trans (congrArg (WFF.dia y _) ?_)
        exact WFF.subst_instantiate_ren ((Ctx.le_insert hc.root _).diaIn y) (h.diaIn y) (θ.dia y y)
          _ _ _ _ (Subst.ren_dia hid y)
          _ _ ((Term.subst_diaIn_mono θ hθ hc' y y hθy hcy _).trans (sig_mono _ hu)) Ψ

end LiftRead

/-- ⭐⭐**A witnessed returning possibility in a world's theory, at terms** (T + 4, strong B):
    `Proof.retWN_lift` at a fresh variable, as an `∃`, witnessed (`exW_term`). -/
theorem BArrow.BWorld.retW_term {σ : Signature} (w : BWorld σ) (hS : ModalSys.BStrong = true)
    (hT : ModalSys.T = true) (hF : ModalSys.Four = true) {i : ℕ} (O : OutLeg (w.ctx i))
    {A Z : VarType} {cs : List (List Step)} (h : A.CompOk cs) {a₁ : Ann (A.compsFlat cs)}
    {a₂ : Ann Z} (t₁ : Term σ (w.ctx i) (A.compsFlat cs) a₁) (t₂ : Term σ (w.ctx i) Z a₂)
    (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit (.boxC A cs h) Z).ty) 1)
    (hm : O.retS hS (.wit (.boxC A cs h) Z) (Term.pair t₁ t₂) Φ ∈ w.M i) :
    ∃ (j : ℕ) (hij : i ≤ j) (b₀ : Ann (A.compsFlat cs))
      (b : Term σ (w.ctx j).boxIn (A.compsFlat cs) b₀) (x : VarSymb)
      (hx : ∃ Y, (w.ctx j).ref x = some (.VTypeDia Y)) (d₀ : Ann Z)
      (bd : Term σ ((w.ctx j).diaIn x) Z d₀),
      WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b)))
        (Term.mono (w.le hij) t₁) ∈ w.M j ∧
      WFF.here hT (Term.diatm x hx bd) (Term.mono (w.le hij) t₂) ∈ w.M j ∧
      (O.mono (w.le hij)).dia (WFF.instantiate Ctx.NoSlots.slots
        (Term.pair (Term.boxtm (Term.mono (O.mono (w.le hij)).le_view.boxIn
            (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b)))
          (Term.mono (O.mono (w.le hij)).le_view (Term.keptDia hF hx bd).2))
        (WFF.packedBodyW (N := .boxC A cs h) hS hF
          (WFF.mono ((O.le_view_mono (w.le hij)).insert (.bnd 0) _) Φ))) ∈ w.M j := by
  have hc : (w.ctx i).RootFresh (.free (w.l i).length) := ctxOf_fresh le_rfl
  have hc₁ : (w.ctx i).RootFresh (.free ((w.l i).length + 1)) := ctxOf_fresh (by omega)
  have hc₂ : (w.ctx i).RootFresh (.free ((w.l i).length + 2)) := ctxOf_fresh (by omega)
  have hex : WFF.ex (wTy (A.compsFlat cs) Z) (WFF.bindFree (w.l i).length hc
      Ctx.NoSlots.slots _ (WFF.liftedW hS hT hF O t₁ t₂
        (WFF.packedBodyW (N := .boxC A cs h) hS hF Φ) (w.l i).length hc)) ∈ w.M i :=
    BWorld.mem_of_provable (Δ := [_]) (fun φ hφ => by rw [List.mem_singleton.mp hφ]; exact hm)
      ⟨Proof.retWN_lift hS hT hF O (.boxC A cs h) t₁ t₂ Φ _ hc hc₁ hc₂
        (Proof.lookup List.mem_cons_self)
        (Proof.ex_intro _ (Term.eta (.root (.free (w.l i).length)) _
          (Ctx.ref_insert_root _ _ _)) (Proof.conv ?_ (Proof.lookup List.mem_cons_self)))⟩
  · obtain ⟨j, hij, x₀, x, hm'⟩ := w.exW_term hex
    cases x with
    | pair u p =>
        cases u with
        | boxtm b =>
            cases p with
            | diatm y hy bd =>
                refine ⟨j, hij, _, b, y, hy, _, bd, ?_⟩
                rw [WFF.instantiate_bindFree (w.le hij) _ hc, WFF.subst_liftedW (w.le hij),
                  WFF.mono_packedBodyW (O.le_view_mono (w.le hij))] at hm'
                obtain ⟨h₁, h₂⟩ := (w.mcs j).and_mem_iff.mp hm'
                obtain ⟨h₃, h₄⟩ := (w.mcs j).and_mem_iff.mp h₁
                exact ⟨h₃, h₄, h₂⟩
  · exact ((WFF.instantiate_eta_openFree _ hc Ctx.NoSlots.slots Ctx.NoSlots.slots _).trans
      (WFF.openFree_bindFree _ hc Ctx.NoSlots.slots _)).symm

/-- The object read off a pack, at a boxed object with companions. -/
theorem holeAt_unpack₀_boxC {σ : Signature} {V : Ctx} {A : VarType} {cs : List (List Step)}
    (h : A.CompOk cs) {b : Ann (A.compsFlat cs)} (s : Term σ V.boxIn (A.compsFlat cs) b) :
    (⟨_, Term.holeAt (Term.boxtm s) (NShape.unpack₀ (σ := σ) (.boxC A cs h)).2⟩ :
      Σ b, Term σ V (.VTypeBox A) b) = ⟨_, Term.boxtm (compsBase cs s).2⟩ := by
  have hat := Subst.at_single_root (σ := σ) (Δ := V) (.bnd 0) (.tm (Term.boxtm s))
  exact sig_boxtm (Term.subst_eta_tm _ _ _ _ _ _ _
    (at_compsBase _ cs s _ (Subst.box_at_inner_boxtm _ hat)))

/-- ⭐The packed body at a witnessed boxed object: `Φ` of the base and the possible object, with the
    ties (`WFF.instantiate_packedBody_boxC`). -/
theorem WFF.instantiate_packedBodyW_boxC {σ : Signature} {V : Ctx} [V.NoSlots]
    (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) {A Z : VarType}
    {cs : List (List Step)} (h : A.CompOk cs)
    (Φ : WFF σ (V.insert (.bnd 0) (RShape.wit (.boxC A cs h) Z).ty) 1)
    {b : Ann (A.compsFlat cs)} (s : Term σ V.boxIn (A.compsFlat cs) b) {k₀ : Ann (.VTypeDia Z)}
    (k : Term σ V (.VTypeDia Z) k₀) :
    WFF.instantiate Ctx.NoSlots.slots (Term.pair (Term.boxtm s) k)
        (WFF.packedBodyW (N := .boxC A cs h) hS hF Φ) =
      WFF.and (WFF.instantiate Ctx.NoSlots.slots (Term.pair (Term.boxtm (compsBase cs s).2) k) Φ)
        (WFF.holeAt Ctx.NoSlots.slots (Term.pair (Term.boxtm (compsBase cs s).2) (Term.boxtm s))
          (WFF.packTies hS hF (.boxC A cs h))) := by
  have hat := Subst.at_single_root (σ := σ) (Δ := V) (.bnd 0) (.tm (Term.pair (Term.boxtm s) k))
  have hf : (Subst.single (σ := σ) (Δ := V) (.bnd 0)
      (.tm (Term.pair (Term.boxtm s) k))).at (.step (.root (.bnd 0)) .fst) =
      .tm (Term.boxtm s) := by
    rw [Subst.at_proj _ _ rfl, hat]
    rfl
  have hn : (Subst.single (σ := σ) (Δ := V) (.bnd 0)
      (.tm (Term.pair (Term.boxtm s) k))).at (.step (.root (.bnd 0)) .snd) = .tm k := by
    rw [Subst.at_proj _ _ rfl, hat]
    rfl
  have hU := (Term.subst_holeAt_sig (Subst.single (σ := σ) (Δ := V) (.bnd 0)
    (.tm (Term.pair (Term.boxtm s) k))) (Subst.ok_single (Ctx.empty_le V) rfl)
    (Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le V) rfl)
    (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox (A.compsFlat cs))
      (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))
    (NShape.unpack₀ (.boxC A cs h)).2).trans ((Term.holeAt_congr_sig
      (Term.subst_eta_tm _ _ _ _ _ _ _ hf) _).trans (holeAt_unpack₀_boxC h s))
  refine congrArg₂ WFF.and ((WFF.instantiate_bodyRepl _ _ _).trans
    (WFF.instantiate_congr_sig _ ?_ Φ)) ?_
  · rw [Term.subst_mono]
    exact sig_pair hU (Term.subst_eta_tm _ _ _ _ _ _ _ hn)
  · change WFF.subst _ _ _ _ _ _ (WFF.holeAt _ _ _) = _
    rw [WFF.subst_holeAt]
    refine WFF.holeAt_congr _ ?_ _
    rw [Term.subst_mono]
    exact sig_pair hU (Term.subst_eta_tm _ _ _ _ _ _ _ hf)

namespace Model

variable {σ : Signature} {M : Model σ}

/-- The witnessed slot of `ret_keep`'s premise, read: the object, and the possible object kept. -/
theorem interp_keepL {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W} (env : M.Env Γ w)
    (hF : ModalSys.Four = true) (O : OutLeg Γ) (N : NShape) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType} {b₀ : Ann A}
    (bd : Term σ (Γ.diaIn x) A b₀) (i : O.Arr env) (d : M.frame.Dom N.ty (O.acc env i).1) :
    interp ((O.push env i).extend (.bnd 0) d) (RShape.keepL hF O N hx bd).2 =
      ((d, interp (env.boxPush (O.acc env i)) (Term.keptDia hF hx bd).2) :
        M.frame.Dom (RShape.wit N A).ty (O.acc env i).1) := by
  have e₁ := interp_eta_slot (σ := σ) (T := N.ty) (O.push env i) d
    (Ctx.ref_insert_root O.view (.bnd 0) N.ty)
  have e₂ := (interp_mono (Env.agree_extend (O.push env i)
    (Ctx.NoSlots.slots (Γ := O.view)).root d) (Term.mono O.le_view
      (Term.keptDia hF hx bd).2)).trans (interp_mono (OutLeg.agree_push env O i) _)
  exact congrArg₂ (fun u v => ((u, v) : M.frame.Dom (RShape.wit N A).ty (O.acc env i).1)) e₁ e₂

end Model

/-- Under T, a kept possible object collapses to the object. -/
theorem Term.collapse_keptDia {σ : Signature} {Γ : Ctx} (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType}
    {a : Ann A} (bd : Term σ (Γ.diaIn x) A a) :
    (⟨_, Term.collapse (Ctx.collapses_boxIn_self hT Γ) (Term.keptDia hF hx bd).2⟩ :
      Σ e, Term σ Γ (.VTypeDia A) e) = ⟨_, Term.diatm x hx bd⟩ := by
  have key : ∀ (z : VarSymb) (_ : z = x) (hz : ∃ X, Γ.ref z = some (.VTypeDia X))
      (c : Ctx.Collapses 1 ((Γ.boxIn).diaIn (.step x .keep)) (Γ.diaIn z)),
      (⟨_, Term.diatm z hz (Term.collapse c (Term.shift (Ctx.shifts_diaIn_keep hF Γ x) bd))⟩ :
        Σ e, Term σ Γ (.VTypeDia A) e) = ⟨_, Term.diatm x hx bd⟩ := by
    rintro _ rfl hz c
    exact sig_diatm ((Term.collapse_shift_self _ c (Ctx.Le.refl _) bd).trans
      (congrArg (Sigma.mk _) (Term.mono_refl _ _)))
  exact key _ VarSymb.collapse_keep_zero _ _

namespace GArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

variable (hM₀ : Theory.IsMCS M₀)

/-! ## A kept possible object is the object -/

/-- The root's kept possible term named at a world is the named term, kept (`preTB_keepDia`). -/
theorem rnm_keepDia (v : GW hF M₀) {R J : ℕ}
    (hJ : ∀ z T, (ctxOf (glat (groot hF M₀) R)).ref z = some T → T.keepable = true →
      (ctxOf (glat v J)).ref (rnm v z) = some T)
    {y : VarSymb} {Y : VarType} (hY : (ctxOf (glat (groot hF M₀) R)).ref y = some (.VTypeDia Y))
    {A : VarType} {a : Ann A} (b : Term σ ((ctxOf (glat (groot hF M₀) R)).diaIn y) A a) :
    (⟨_, Term.subst (eIdx (ofRen (preI (rnm v)))) (eS σ (ctxOf (glat v J)).boxIn
        (ofRen (preI (rnm v)))) (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI hJ)))
        (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI hJ)))
        (Term.keptDia hF ⟨Y, hY⟩ b).2⟩ : Σ c, Term σ (ctxOf (glat v J)).boxIn (.VTypeDia A) c) =
      Term.keptDia hF ⟨Y, hJ y _ hY rfl⟩ (Term.subst (eIdx (ofRen (preIX (rnm v) y)))
        (eS σ ((ctxOf (glat v J)).diaIn (rnm v y)) (ofRen (preIX (rnm v) y)))
        (ok_eS_kView (k := some y) (entOk_ofRen (itemOk_preIX hY hJ)))
        (coh_eS_kView (k := some y) (entOk_ofRen (itemOk_preIX hY hJ))) b) := by
  have hθ := ok_eS_kView (k := none) (entOk_ofRen (σ := σ) (itemOk_preI hJ))
  have hc := coh_eS_kView (k := none) (entOk_ofRen (σ := σ) (itemOk_preI hJ))
  have hy : eIdx (ofRen (σ := σ) (preI (rnm v))) (.step y .keep) = .step (rnm v y) .keep := by
    rw [show (VarSymb.step y .keep) = (VarSymb.step y .keep).ext [] from rfl,
      eIdx_item _ (reach_ppath hY).1 rfl []]
    rfl
  have hw : ((eS σ (ctxOf (glat v J)).boxIn (ofRen (preI (rnm v)))).at
      (.step y .keep)).idxAlong [] = .step (rnm v y) .keep := by
    rw [Subst.at_nonproj _ rfl, eS_item _ rfl]
    rfl
  have hxk := Ctx.exists_keep_dia hF ⟨Y, hY⟩
  refine (sig_subst_diatm _ hθ hc hxk _ _ hy
    (Ctx.exists_keep_dia hF ⟨Y, hJ y _ hY rfl⟩) (Subst.ok_dia hθ hxk hw)
    (hy ▸ Subst.coh_dia hθ hc hxk)).trans (sig_diatm ?_)
  exact (Term.shift_subst (Ctx.shifts_diaIn_keep hF _ y) (Ctx.shifts_diaIn_keep hF _ (rnm v y))
    _ _ _ _ _ _ (shiftCorr_preIX (hF := hF) _ (ok_eS_kView (k := some y)
      (entOk_ofRen (itemOk_preIX hY hJ)))) b).symm

/-- ⭐⭐**A kept possible object, read along an arrow, is the object** (T + 4), raw possible objects
    not depending on the world.  Under `□` both are the root's (`cden_box_eq`, `preTB_keepDia`),
    named at the far world (`cden_named_box`, `rnm_keepDia`), where the own arrow reads the collapse
    (`cden_boxtm_own`, `Term.collapse_keptDia`), and that is the object (`cden_named_dia`). -/
theorem cden_kept (hX : CluFlags) (hT : ModalSys.T = true) (s : GW hF M₀) (I : ℕ) {x : VarSymb}
    {X : VarType} (hx : (ctxOf (glat s I)).ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (bd : Term σ ((ctxOf (glat s I)).diaIn x) A a) (b : CAcc hF M₀) :
    cden hM₀ hX b.1 _ (Ctx.Le.refl _)
        ((preC hM₀ hX s I b (cpathOk hT b.2.down)).app (Term.keptDia hF ⟨X, hx⟩ bd).2).2 =
      cden hM₀ hX s I (Ctx.Le.refl _) (.diatm x ⟨X, hx⟩ bd) := by
  have hY : (ctxOf (glat (groot hF M₀) (rstg s I))).ref (rorig s x) = some (.VTypeDia X) :=
    rpre hX hM₀ s I x _ hx rfl
  have hJ := pnm_ok hX hM₀ (rpath b.1) (groot hF M₀) b.1 (rpath_eq b.1) (rstg s I)
  have h₁ : cden hM₀ hX b.1 _ (Ctx.Le.refl _)
      ((preC hM₀ hX s I b (cpathOk hT b.2.down)).app (Term.keptDia hF ⟨X, hx⟩ bd).2).2 =
      cden hM₀ hX s I (Ctx.Le.refl _) (.boxtm (Term.keptDia hF ⟨X, hx⟩ bd).2) b := by
    exact cden_preC hM₀ hX s I b _ _
  have h₂ : cden hM₀ hX s I (Ctx.Le.refl _) (.boxtm (Term.keptDia hF ⟨X, hx⟩ bd).2) =
      cden hM₀ hX (groot hF M₀) (rstg s I) (Ctx.Le.refl _)
        (.boxtm (Term.keptDia hF ⟨X, hY⟩ (preTD hX hM₀ s I ⟨X, hx⟩ bd).2).2) := by
    rw [cden_box_eq, Term.mono_refl]
    exact cden_sigma hX _ (sig_boxtm (preTB_keepDia hX hM₀ s I hx bd))
  have h₃ := (cden_named_box hX hM₀ b.1 (rstg s I) _ hJ
    (Term.keptDia hF ⟨X, hY⟩ (preTD hX hM₀ s I ⟨X, hx⟩ bd).2).2).symm
  have h₄ := cden_boxtm_own (hM₀ := hM₀) hX hT b.1 _ (Term.subst (eIdx (ofRen (preI (rnm b.1))))
    (eS σ (ctxOf (glat b.1 _)).boxIn (ofRen (preI (rnm b.1))))
    (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI hJ)))
    (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI hJ)))
    (Term.keptDia hF ⟨X, hY⟩ (preTD hX hM₀ s I ⟨X, hx⟩ bd).2).2) b.2.down
  have h₅ := cden_sigma (hM₀ := hM₀) hX (s := b.1) (Ctx.Le.refl _)
    ((sig_collapse_cong (Ctx.collapses_boxIn_self hT _)
      (rnm_keepDia b.1 hJ hY (preTD hX hM₀ s I ⟨X, hx⟩ bd).2)).trans
      (Term.collapse_keptDia hT hF ⟨X, hJ _ _ hY rfl⟩ (Term.subst
        (eIdx (ofRen (preIX (rnm b.1) (rorig s x))))
        (eS σ ((ctxOf (glat b.1 _)).diaIn (rnm b.1 (rorig s x)))
          (ofRen (preIX (rnm b.1) (rorig s x))))
        (ok_eS_kView (k := some (rorig s x)) (entOk_ofRen (itemOk_preIX hY hJ)))
        (coh_eS_kView (k := some (rorig s x)) (entOk_ofRen (itemOk_preIX hY hJ)))
        (preTD hX hM₀ s I ⟨X, hx⟩ bd).2)))
  have h₆ := cden_named_dia hX hM₀ b.1 (rstg s I) _ hY hJ (preTD hX hM₀ s I ⟨X, hx⟩ bd).2
  have h₇ := cden_dia_eq (hM₀ := hM₀) hX s I (Ctx.Le.refl _) x ⟨X, hx⟩ bd
  rw [Term.mono_refl] at h₇
  exact h₁.trans ((congrFun h₂ b).trans ((congrFun h₃ b).trans (h₄.trans (h₅.trans
    (h₆.trans h₇.symm)))))

/-- The value of a kept possible object along an arrow is the object, there. -/
theorem interp_kept (hX : CluFlags) (hT : ModalSys.T = true) (s : GW hF M₀) (I : ℕ) {x : VarSymb}
    {X : VarType} (hx : (ctxOf (glat s I)).ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (bd : Term σ ((ctxOf (glat s I)).diaIn x) A a) (b : CAcc hF M₀)
    (h : CDefinable hM₀ hX (.VTypeDia A) b.1
      (cden hM₀ hX s I (Ctx.Le.refl _) (.diatm x ⟨X, hx⟩ bd))) :
    Model.interp ((ccanonEnv hM₀ hX s I).boxPush b) (Term.keptDia hF ⟨X, hx⟩ bd).2 =
      ctoDom hM₀ hX (.VTypeDia A) b.1 (cden hM₀ hX s I (Ctx.Le.refl _) (.diatm x ⟨X, hx⟩ bd)) h :=
  (interp_ctr hX _ (farNec hM₀ hX hT s I b).C (farNec hM₀ hX hT s I b).ag
    (farNec hM₀ hX hT s I b).npl (Ctx.noProjLast_boxIn _)).trans
    (ctoDom_congr hX (cden_kept hM₀ hX hT s I hx bd b) _ _)

/-! ## Truth ⇒ membership -/

/-- What a witnessed returning possibility says at a later stage where its possible object has a
    name: the necessary part, with the name kept. -/
theorem sat_nec_keep (hX : CluFlags) (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (s : GW hF M₀) {i I : ℕ} (hiI : i ≤ I) (O : OutLeg (ctxOf (glat s i))) (N : NShape)
    {Z : VarType} {a : Ann N.flat} (t : Term σ (ctxOf (glat s i)) N.flat a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit N Z).ty) 1)
    (a₀ : O.Arr (ccanonEnv hM₀ hX s i))
    (e : (cframe hF hM₀ hX).Dom (RShape.wit N Z).ty (O.acc (ccanonEnv hM₀ hX s i) a₀).1)
    (hΦ : (cmodel hF hM₀ hX).sat ((O.push (ccanonEnv hM₀ hX s i) a₀).extend (.bnd 0) e) Φ)
    (r : (cframe hF hM₀ hX).R (O.acc (ccanonEnv hM₀ hX s i) a₀).1 s)
    (hcb : (cmodel hF hM₀ hX).NComesBack N e.1 r
      (Model.interp (ccanonEnv hM₀ hX s i) t))
    {x : VarSymb} {X : VarType} (hx : (ctxOf (glat s I)).ref x = some (.VTypeDia X)) {b₀ : Ann Z}
    (bd : Term σ ((ctxOf (glat s I)).diaIn x) Z b₀)
    (hg : cden hM₀ hX s I (Ctx.Le.refl _) (.diatm x ⟨X, hx⟩ bd) =
      cfromDom hM₀ hX (.VTypeDia Z) _ e.2) :
    (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s I)
      ((O.mono (gle hM₀ s hiI)).retS hS (.nec N) (Term.mono (gle hM₀ s hiI) t)
        (WFF.bodyRepl (RShape.keepL hF (O.mono (gle hM₀ s hiI)) N ⟨X, hx⟩ bd).2
          (WFF.mono ((O.le_view_mono (gle hM₀ s hiI)).insert (.bnd 0) _) Φ)) : WFF σ _ 0) := by
  have hk : ∀ (b : CAcc hF M₀) (e₂ : (cframe hF hM₀ hX).Dom (.VTypeDia Z) b.1),
      (cden hM₀ hX s I (Ctx.Le.refl _) (.diatm x ⟨X, hx⟩ bd) : CRDom hM₀ (.VTypeDia Z) b.1) =
        cfromDom hM₀ hX (.VTypeDia Z) _ e₂ →
      Model.interp ((ccanonEnv hM₀ hX s I).boxPush b) (Term.keptDia hF ⟨X, hx⟩ bd).2 = e₂ := by
    intro b e₂ he
    refine (interp_kept hM₀ hX hT s I hx bd b (by
      rw [show (cden hM₀ hX s I (Ctx.Le.refl _) (.diatm x ⟨X, hx⟩ bd) :
        CRDom hM₀ (.VTypeDia Z) b.1) = _ from he]
      exact cdefinable_fromDom hM₀ hX _ _ e₂)).trans ?_
    exact (ctoDom_congr (s := b.1) hX he _ _).trans (ctoDom_fromDom hM₀ hX _ _ e₂)
  have hcb' := (Model.interp_mono (ccanonEnv_le hX s hiI) t).symm ▸ hcb
  cases O with
  | nec =>
      refine (OutLeg.sat_retS (M := cmodel hF hM₀ hX) (d := 0) hS (ccanonEnv hM₀ hX s I) .nec
        (.nec N) _ _).mpr ⟨a₀, e.1, ?_, r, hcb'⟩
      refine (Model.sat_bodyRepl (OutLeg.nec).noProjLast _ _ _ _).mpr ?_
      have hv := (Model.interp_keepL (M := cmodel hF hM₀ hX) (ccanonEnv hM₀ hX s I) hF .nec N
        ⟨X, hx⟩ bd a₀ e.1).trans (congrArg (fun z => ((e.1, z) :
          (cframe hF hM₀ hX).Dom (RShape.wit N Z).ty a₀.1)) (hk a₀ e.2 hg))
      exact (congrArg (fun z => (cmodel hF hM₀ hX).sat
        (((OutLeg.nec : OutLeg (ctxOf (glat s I))).push (ccanonEnv hM₀ hX s I) a₀).extend
          (.bnd 0) z) (WFF.mono (((OutLeg.nec : OutLeg (ctxOf (glat s i))).le_view_mono
            (gle hM₀ s hiI)).insert (.bnd 0) _) Φ)) hv).mpr
        ((Model.sat_mono (Model.Env.extend_agree (Model.Env.boxPush_agree
          (ccanonEnv_le hX s hiI) a₀) (.bnd 0) _) Φ).mpr hΦ)
  | pos y hy =>
      have hy' : ∃ Y, (ctxOf (glat s I)).ref y = some (.VTypeDia Y) :=
        hy.imp fun _ e => (gle hM₀ s hiI).ref e
      obtain ⟨hm, hΦ'⟩ := sat_diaPush_lift (gle hM₀ s hiI) (ccanonEnv_le hX s hiI)
        hy.choose_spec hy'.choose_spec a₀ _ Φ hΦ
      refine (OutLeg.sat_retS (M := cmodel hF hM₀ hX) (d := 0) hS (ccanonEnv hM₀ hX s I)
        (.pos y hy') (.nec N) _ _).mpr ⟨⟨a₀.1, hm⟩, e.1, ?_, r, hcb'⟩
      refine (Model.sat_bodyRepl (OutLeg.pos y hy').noProjLast _ _ _ _).mpr ?_
      have hv := (Model.interp_keepL (M := cmodel hF hM₀ hX) (ccanonEnv hM₀ hX s I) hF
        (.pos y hy') N ⟨X, hx⟩ bd ⟨a₀.1, hm⟩ e.1).trans (congrArg (fun z => ((e.1, z) :
          (cframe hF hM₀ hX).Dom (RShape.wit N Z).ty a₀.1.1)) (hk a₀.1 e.2 hg))
      exact (congrArg (fun z => (cmodel hF hM₀ hX).sat
        (((OutLeg.pos y hy' : OutLeg (ctxOf (glat s I))).push (ccanonEnv hM₀ hX s I)
          ⟨a₀.1, hm⟩).extend (.bnd 0) z) (WFF.mono ((((gle hM₀ s hiI).diaIn y).insert
            (.bnd 0) _)) Φ)) hv).mpr hΦ'

/-- ⭐⭐**A true witnessed returning possibility is in the theory** (strong B), along either leg.
    The possible object has a name here, raw possible objects not depending on the world; that name
    is realised (`chere_truth`) and kept is the object (`sat_nec_keep`), so the necessary part is
    in the theory (`mem_ret_of_satN`), and `Proof.ret_keep` gives the rest. -/
theorem mem_ret_of_satW (hX : CluFlags) (hS : ModalSys.BStrong = true) {s : GW hF M₀} {i : ℕ}
    (O : OutLeg (ctxOf (glat s i))) (N : NShape) {Z : VarType} {a₁ : Ann N.flat} {a₂ : Ann Z}
    (t₁ : Term σ (ctxOf (glat s i)) N.flat a₁) (t₂ : Term σ (ctxOf (glat s i)) Z a₂)
    (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit N Z).ty) 1)
    (IH : ∀ (s' : GW hF M₀) (K : ℕ) (φ : WFF σ (ctxOf (glat s' K)) 0),
      φ.size < Φ.size + N.flat.eqRecSize + 1 →
        ((cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s' K) φ ↔ φ ∈ (gw hM₀ s').M K))
    (IHe : CEqTruth hM₀ hX s Z)
    (hsat : (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s i)
      (O.retS hS (.wit N Z) (Term.pair t₁ t₂) Φ : WFF σ _ 0)) :
    (O.retS hS (.wit N Z) (Term.pair t₁ t₂) Φ : WFF σ _ 0) ∈ (gw hM₀ s).M i := by
  have hT := hX.bT hS
  obtain ⟨a₀, e, hΦ, r, hcb, hm, hind⟩ := (OutLeg.sat_retS (M := cmodel hF hM₀ hX) (d := 0) hS
    (ccanonEnv hM₀ hX s i) O (.wit N Z) _ Φ).mp hsat
  have hd₀ := cdefinable_fromDom hM₀ hX (.VTypeDia Z) _ e.2
  have hd₁ := (cdefinable_dia_iff hX _ _).mp hd₀
  obtain ⟨K, _, g, hg⟩ := (cdefinable_dia_iff hX s _).mpr hd₁
  cases g with
  | diatm x hx bd =>
      obtain ⟨X, hX'⟩ := id hx
      have hiI : i ≤ max i K := le_max_left _ _
      have hKI : K ≤ max i K := le_max_right _ _
      have hxI := (gle hM₀ s hKI).ref hX'
      let bd' := Term.mono ((gle hM₀ s hKI).diaIn x) bd
      have hg' : cden hM₀ hX s (max i K) (Ctx.Le.refl _) (.diatm x ⟨X, hxI⟩ bd') =
          cfromDom hM₀ hX (.VTypeDia Z) _ e.2 :=
        (cden_lift hX hKI (.diatm x hx bd)).trans hg
      have hn := mem_ret_of_satN hM₀ hX hS (O.mono (gle hM₀ s hiI)) N
        (Term.mono (gle hM₀ s hiI) t₁) _ (fun s' K' φ hφ => IH s' K' φ (by
          unfold WFF.bodyRepl at hφ
          rw [WFF.size_subst, WFF.size_mono] at hφ
          exact hφ))
        (sat_nec_keep hM₀ hX hS hT s hiI O N t₁ Φ a₀ e hΦ r hcb hxI bd' hg')
      let o : CRDom hM₀ (.VTypeDia Z) s :=
        cfromDom hM₀ hX (.VTypeDia Z) (O.acc (ccanonEnv hM₀ hX s i) a₀).1 e.2
      have hdef : CDefinable hM₀ hX (.VTypeDia Z) s o := (cdefinable_dia_iff hX s _).mpr hd₁
      have eS : Model.interp (ccanonEnv hM₀ hX s (max i K)) (.diatm x ⟨X, hxI⟩ bd') =
          ctoDom hM₀ hX (.VTypeDia Z) s o hdef :=
        (interp_ccanon hX _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)).trans
          (ctoDom_congr hX hg' _ _)
      have hsH : (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s (max i K))
          (WFF.here hT (.diatm x ⟨X, hxI⟩ bd') (Term.mono (gle hM₀ s hiI) t₂) : WFF σ _ 0) := by
        change (cmodel hF hM₀ hX).Realised hT _ _
        rw [eS, Model.interp_mono (ccanonEnv_le hX s hiI) t₂]
        exact ⟨hm, hind⟩
      have hh := (chere_truth hX hT ⟨X, hxI⟩ bd' _ IHe).mp hsH
      refine (BWorld.mem_lift hiI).mpr ?_
      rw [OutLeg.mono_retS]
      exact (gw hM₀ s).mem_of_provable (Δ := [_, _]) (fun ψ hψ => by
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact hh
          · rw [List.mem_singleton.mp hψ]
            exact hn)
        ⟨Proof.ret_keep hS hT hF _ N x _ bd' _ _ _ (Proof.lookup List.mem_cons_self)
          (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩

/-! ## Membership ⇒ truth -/

/-- ⭐⭐**A witnessed returning possibility in the theory comes true** (strong B), at a boxed object
    with companions, along either leg.  `BWorld.retW_term` names the possible object, realised
    here; the rest unlifts to the necessary part, kept (`Proof.retC_unlift`), which is true
    (`sat_ret_of_memC`), and so is the name's `Here` (`chere_truth`); `Model.sat_ret_keep` puts
    them together. -/
theorem sat_ret_of_memWC (hX : CluFlags) (hS : ModalSys.BStrong = true) {s : GW hF M₀} {i : ℕ}
    (O : OutLeg (ctxOf (glat s i))) {A Z : VarType} {cs : List (List Step)} (h : A.CompOk cs)
    {a₁ : Ann (A.compsFlat cs)} {a₂ : Ann Z} (t₁ : Term σ (ctxOf (glat s i)) (A.compsFlat cs) a₁)
    (t₂ : Term σ (ctxOf (glat s i)) Z a₂)
    (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit (.boxC A cs h) Z).ty) 1)
    (IH : ∀ (s' : GW hF M₀) (K : ℕ) (φ : WFF σ (ctxOf (glat s' K)) 0), φ.size ≤ Φ.size →
      ((cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s' K) φ ↔ φ ∈ (gw hM₀ s').M K))
    (IHe : CEqTruth hM₀ hX s Z)
    (hmem : O.retS hS (.wit (.boxC A cs h) Z) (Term.pair t₁ t₂) Φ ∈ (gw hM₀ s).M i) :
    (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s i)
      (O.retS hS (.wit (.boxC A cs h) Z) (Term.pair t₁ t₂) Φ : WFF σ _ 0) := by
  have hT := hX.bT hS
  obtain ⟨j, hij, b₀, b, x, hx, d₀, bd, hB, hH, hD⟩ :=
    (gw hM₀ s).retW_term hS hT hF O h t₁ t₂ Φ hmem
  let O₁ := O.mono (gle hM₀ s hij)
  let Φ₁ := WFF.mono ((O.le_view_mono (gle hM₀ s hij)).insert (.bnd 0) _) Φ
  let s₀ := Term.mono O₁.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b)
  have e : WFF.instantiate Ctx.NoSlots.slots (Term.boxtm s₀)
      (WFF.packedBody (N := .boxC A cs h) hS hF
        (WFF.bodyRepl (RShape.keepL hF O₁ (.boxC A cs h) hx bd).2 Φ₁)) =
      WFF.instantiate Ctx.NoSlots.slots (Term.pair (Term.boxtm s₀)
        (Term.mono O₁.le_view (Term.keptDia hF hx bd).2))
        (WFF.packedBodyW (N := .boxC A cs h) hS hF Φ₁) :=
    (WFF.instantiate_packedBody_boxC hS hF h _ s₀).trans ((congrArg (WFF.and · _)
      (RShape.instantiate_keepL hF O₁ (.boxC A cs h) hx bd _ Φ₁)).trans
      (WFF.instantiate_packedBodyW_boxC hS hF h Φ₁ s₀ _).symm)
  have hc : (ctxOf (glat s j)).RootFresh (.free (glat s j).length) := ctxOf_fresh le_rfl
  have hn := (gw hM₀ s).mem_of_provable (Δ := [_, _]) (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hB
      · rw [List.mem_singleton.mp hψ]
        exact hD)
    ⟨Proof.retC_unlift hS hT hF O₁ h b _ (WFF.bodyRepl (RShape.keepL hF O₁ (.boxC A cs h) hx bd).2
      Φ₁) _ hc _ (OutLeg.rootFresh hc O₁) (Proof.lookup List.mem_cons_self)
      (Proof.conv (congrArg O₁.dia e).symm
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
  have hsatN := sat_ret_of_memC hM₀ hX hS O₁ h _ _ (fun s' K φ hφ => IH s' K φ (by
    unfold WFF.bodyRepl at hφ
    rw [WFF.size_subst, WFF.size_mono] at hφ
    exact hφ)) hn
  have hsatH := (chere_truth hX hT hx bd _ IHe).mpr hH
  have hw := Model.sat_ret_keep (ccanonEnv hM₀ hX s j) hS hT hF O₁ (.boxC A cs h) hx bd _ _ Φ₁
    hsatH hsatN
  refine (Model.sat_mono (ccanonEnv_le hX s hij) _).mp ?_
  rw [OutLeg.mono_retS]
  exact hw

/-- ⭐⭐**A witnessed returning possibility in the theory comes true** (strong B), at every witnessed
    shape: packed (`retS_packGW`), true there (`sat_ret_of_memWC`), mapped back. -/
theorem sat_ret_of_memW (hX : CluFlags) (hS : ModalSys.BStrong = true) {s : GW hF M₀} {i : ℕ}
    (O : OutLeg (ctxOf (glat s i))) (N : NShape) {Z : VarType} {a : Ann (RShape.wit N Z).flat}
    (t : Term σ (ctxOf (glat s i)) (RShape.wit N Z).flat a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit N Z).ty) 1)
    (IH : ∀ (s' : GW hF M₀) (K : ℕ) (φ : WFF σ (ctxOf (glat s' K)) 0), φ.size ≤ Φ.size →
      ((cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s' K) φ ↔ φ ∈ (gw hM₀ s').M K))
    (IHe : CEqTruth hM₀ hX s Z)
    (hmem : (O.retS hS (.wit N Z) t Φ : WFF σ _ 0) ∈ (gw hM₀ s).M i) :
    (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s i) (O.retS hS (.wit N Z) t Φ : WFF σ _ 0) := by
  have hp := (gw hM₀ s).mem_of_provable (Δ := [_]) (fun ψ hψ => by
    rw [List.mem_singleton.mp hψ]
    exact hmem) ⟨retS_packGW hS O t Φ (Proof.lookup List.mem_cons_self)⟩
  obtain ⟨_, _, t₁, t₂, ht⟩ := Term.exists_pair
    (Term.holeRead t (ShapeMap.liftVal (σ := σ) (.wit N Z) (packG N)).2)
  have hp' := (congrArg (· ∈ (gw hM₀ s).M i)
    (OutLeg.retS_congr hS O (.wit N.packed Z) ht rfl)).mp hp
  have hsat := sat_ret_of_memWC hM₀ hX hS O N.packOk t₁ t₂ _ (fun s' K φ hφ => IH s' K φ (by
    unfold WFF.bodyRepl at hφ
    rw [WFF.size_subst] at hφ
    exact hφ)) IHe hp'
  have hsat' := (congrArg ((cmodel hF hM₀ hX).sat _)
    (OutLeg.retS_congr hS O (.wit N.packed Z) ht rfl)).mpr hsat
  have hb := Model.sat_ret_map (ccanonEnv hM₀ hX s i) (Ctx.Presented.noProjLast _)
    (cindCongr hM₀ hX) hS O (S := .wit N.packed Z) (unpackG N) _ Φ hsat'
  refine (congrArg ((cmodel hF hM₀ hX).sat _) (OutLeg.retS_congr hS O (.wit N Z) ?_ rfl)).mp hb
  rw [Term.holeRead_eq_holeAt, Term.holeRead_eq_holeAt]
  exact holeAt_packG_unpackGW_val N Z t

/-- `mem_ret_of_satW` at any value. -/
theorem mem_ret_of_satW' (hX : CluFlags) (hS : ModalSys.BStrong = true) {s : GW hF M₀} {i : ℕ}
    (O : OutLeg (ctxOf (glat s i))) (N : NShape) {Z : VarType} {a : Ann (RShape.wit N Z).flat}
    (t : Term σ (ctxOf (glat s i)) (RShape.wit N Z).flat a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit N Z).ty) 1)
    (IH : ∀ (s' : GW hF M₀) (K : ℕ) (φ : WFF σ (ctxOf (glat s' K)) 0),
      φ.size < Φ.size + N.flat.eqRecSize + 1 →
        ((cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s' K) φ ↔ φ ∈ (gw hM₀ s').M K))
    (IHe : CEqTruth hM₀ hX s Z)
    (hsat : (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s i)
      (O.retS hS (.wit N Z) t Φ : WFF σ _ 0)) :
    (O.retS hS (.wit N Z) t Φ : WFF σ _ 0) ∈ (gw hM₀ s).M i := by
  obtain ⟨_, _, t₁, t₂, ht⟩ := Term.exists_pair (A := N.flat) (B := Z) t
  have e := OutLeg.retS_congr hS O (.wit N Z) ht rfl (Φ := Φ) (d := 0)
  rw [e] at hsat ⊢
  exact mem_ret_of_satW hM₀ hX hS O N t₁ t₂ Φ IH IHe hsat

end GArrow

end V12M
