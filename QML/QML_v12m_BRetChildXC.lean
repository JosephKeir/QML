import QML.QML_v12m_BRetChildC
import QML.QML_v12m_BRetChildX

/-!
# QML v12m — strong B on the network: the witness child, for either T

The flag-generic replacement of `QML_v12m_BRetChildX` (docs §11.21, stage 3c): the child of an
obligation `◇_x^{S_A}[u ↦ W] Ξ` along a witness `x`, mirroring `QML_v12m_BRetChildC` along `x`'s
view.  It is born with the invariants with companions: `RetInvWB` out along `x`, `RetInvXB` home.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## The witness invariants with companions -/

/-- `RetInvX` with the tuple's companions (`tupShape`, `tupCompsImg`); `RetInvX` at `false`. -/
def RetInvXB (hS : ModalSys.BStrong = true) (b : Bool) (hb : ModalSys.T = b) (tk tp : NodeSt σ)
    (cls : List VarType) (imgs : ℕ → ℕ) (clt : List VarType) (imgt : ℕ → ℕ) (x : VarSymb)
    (X : VarType) (cx : ℕ) : Prop :=
  ∃ (hs : cls <:+ tk.l) (himgs : ImgOk cls (ctxOf tp.l) imgs) (ht : clt <:+ tp.l)
    (himgt : ImgOk clt (ctxOf tk.l) imgt) (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X),
    ∀ Φ : WFF σ (bodyCtxX cls clt x) 1, liftBodyX hs himgt hx hcx Φ ∈ tk.M →
      (OutLeg.pos x ⟨X, (ctxOf_le_of_suffix ht).ref hx⟩ : OutLeg (ctxOf tp.l)).retS hS
        (.nec (tupShape b hb cls))
        (tupCompsImg cls imgs himgs _ (VarType.compOk_compsAllB b hb _)).2
        (WFF.mono (((ctxOf_le_of_suffix ht).diaIn x).insert (.bnd 0) _) Φ) ∈ tp.M

theorem retInvXB_false {hS : ModalSys.BStrong = true} (hT : ModalSys.T = false)
    {tk tp : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType}
    {cx : ℕ} :
    RetInvXB hS false hT tk tp cls imgs clt imgt x X cx ↔
      RetInvX hS tk tp cls imgs clt imgt x X cx :=
  Iff.rfl

/-- The flag can be taken to be T itself. -/
theorem retInvXB_flag {hS : ModalSys.BStrong = true} {b : Bool} (hb : ModalSys.T = b)
    {tk tp : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType}
    {cx : ℕ} :
    RetInvXB hS ModalSys.T rfl tk tp cls imgs clt imgt x X cx ↔
      RetInvXB hS b hb tk tp cls imgs clt imgt x X cx := by
  cases hb
  exact Iff.rfl

/-- `RetInvW` with the tuple's companions; `RetInvW` at `false`. -/
def RetInvWB (hS : ModalSys.BStrong = true) (b : Bool) (hb : ModalSys.T = b) (tv tw : NodeSt σ)
    (cls : List VarType) (imgs : ℕ → ℕ) (clt : List VarType) (imgt : ℕ → ℕ) (x : VarSymb)
    (X : VarType) (cx : ℕ) : Prop :=
  ∃ (hs : cls <:+ tv.l) (himgs : ImgOk cls (ctxOf tw.l) imgs) (ht : clt <:+ tw.l)
    (himgt : ImgOk clt (ctxOf tv.l) imgt) (hx : (ctxOf cls).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tw.l).ref (.root (.free cx)) = some X),
    ∀ Φ : WFF σ (bodyCtxW cls clt X) 1, liftBodyW hs himgt hx Φ ∈ tv.M →
      WFF.retS hS (.wit (tupShape b hb cls) X)
        (Term.pair (tupCompsImg cls imgs himgs _ (VarType.compOk_compsAllB b hb _)).2
          (Term.eta (.root (.free cx)) X hcx))
        (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Φ) ∈ tw.M

theorem retInvWB_false {hS : ModalSys.BStrong = true} (hT : ModalSys.T = false)
    {tv tw : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType}
    {cx : ℕ} :
    RetInvWB hS false hT tv tw cls imgs clt imgt x X cx ↔
      RetInvW hS tv tw cls imgs clt imgt x X cx :=
  Iff.rfl

/-- The flag can be taken to be T itself. -/
theorem retInvWB_flag {hS : ModalSys.BStrong = true} {b : Bool} (hb : ModalSys.T = b)
    {tv tw : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType}
    {cx : ℕ} :
    RetInvWB hS ModalSys.T rfl tv tw cls imgs clt imgt x X cx ↔
      RetInvWB hS b hb tv tw cls imgs clt imgt x X cx := by
  cases hb
  exact Iff.rfl

/-! ## Reading a body along `x` over the born root at the witness child -/

omit [ModalSys.NoFour] in
theorem rclX_born_ref (l : List VarType) (A X : VarType) :
    (ctxOf (X :: rcl l A)).ref (.root (.free 0)) = some (.VTypeBox A) :=
  (ctxOf_le_of_suffix (rclX_suffix l A X)).ref (born_ref A)

/-- ⭐A body along `x` over the born root, read at the witness child: the parent's items and `x`'s
    content along the arrow, `u` the child's root `c`. -/
noncomputable def liftBodyXR (l : List VarType) (A : VarType) {x : VarSymb} {X : VarType}
    (hX : (ctxOf l).ref x = some (.VTypeDia X))
    (Ξ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox A)) 1) :
    WFF σ (ctxOf (X :: rcl l A)) 0 :=
  WFF.subst (Subst.setIdx (arrowXIdx Nat.succ x (l.length + 1)) (.bnd 0) (.ren (.root (.free 0))))
    ((arrowXS σ (ctxOf (X :: rcl l A)) Nat.succ x (l.length + 1)).set (.bnd 0)
      (.ren (.root (.free 0))))
    (Subst.ok_set (ok_arrowXS (rclXImg l A X) hX (rclX_cx l A X)) (rclX_born_ref l A X))
    (Subst.coh_set (ok_arrowXS (rclXImg l A X) hX (rclX_cx l A X))
      (coh_arrowXS (rclXImg l A X) hX (rclX_cx l A X))
      ((Ctx.NoSlots.slots (Γ := (ctxOf l).diaIn x)).rootFresh (le_refl 0)) (rclX_born_ref l A X))
    ((Ctx.NoSlots.slots (Γ := (ctxOf l).diaIn x)).insert _) Ctx.NoSlots.slots Ξ

/-! ## Pulling back into `x`'s view -/

section Pull

variable (l : List VarType) (A : VarType) {x : VarSymb} {X : VarType}
  (hX : (ctxOf l).ref x = some (.VTypeDia X))

omit [ModalSys.NoFour] in
include hX in
theorem okRef_diaC :
    (SubE.ren (.step x .dia) : SubE σ (pullCtxC ((ctxOf l).diaIn x) l A)).OkRef X :=
  (Ctx.le_insert (pullCtxX_fresh l x).root _).ref (Ctx.ref_diaIn_of hX)

include hX in
theorem ok_retPullCX :
    Subst.Ok (ctxOf (X :: rcl l A)) (retPullC σ l A (Ctx.le_boxIn_diaIn _ x)
      (pullCtxX_fresh l x) (.ren (.step x .dia))) :=
  ok_retPullC_X l A _ _ _ (okRef_diaC l A hX)

/-- ⭐**Pulling back opens the slot, along `x`**. -/
theorem subst_retPullC_liftBodyXR
    (Ξ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox A)) 1) :
    WFF.subst (retPullIdxC σ l A (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x)
          (.ren (.step x .dia)))
        (retPullC σ l A (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x) (.ren (.step x .dia)))
        (ok_retPullCX l A hX) (coh_retPullC_of l A _ _ _ (ok_retPullCX l A hX))
        Ctx.NoSlots.slots Ctx.NoSlots.slots (liftBodyXR l A hX Ξ) =
      WFF.openFree l.length (pullCtxX_fresh l x) Ctx.NoSlots.slots Ξ := by
  unfold liftBodyXR WFF.openFree
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Ξ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = .VTypeBox A := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    rw [Subst.toFree_root]
    dsimp only [Subst.comp]
    rw [Subst.set_root]
    exact .refl _
  · rw [Subst.toFree_ne _ _ _ _ hvr]
    dsimp only [Subst.comp]
    rw [Subst.set_ne _ _ hvr]
    have hv' : (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox (bcT [.VTypeBox A]))) v =
        some T := by
      change (if v = VarSymb.root (.bnd 0) then _ else _) = _
      change (if v = VarSymb.root (.bnd 0) then _ else _) = _ at hv
      rw [if_neg hvr] at hv ⊢
      exact hv
    rcases bodyX_item hv' hvr with ⟨w, rfl, hw⟩ | ⟨rfl, _⟩
    · change SubE.Sim T (((Subst.idRen _) (.step w .box)).mono _)
        ((retPullC σ l A (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x)
          (.ren (.step x .dia))).at (itemAt (imgRoot Nat.succ w.rt) w))
      rw [at_retPullC_item l A _ _ _ hw]
      exact .ren_eta _ _
    · change SubE.Sim T (((Subst.idRen _) (.step x .dia)).mono _)
        ((if x = x then SubE.ren (.root (.free (l.length + 1))) else .hide).comp _ _ _)
      rw [if_pos rfl]
      change SubE.Sim T _ (retPullC σ l A (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x)
        (.ren (.step x .dia)) (.root (.free (l.length + 1))))
      rw [retPullC_last]
      exact .refl _

end Pull

omit [ModalSys.NoFour] in
/-- A returning possibility along `x`, at any shape, whose body `x`'s view refutes is absurd. -/
def Proof.retx_refuteS {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)}
    (hS : ModalSys.BStrong = true) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (S : RShape) {a : Ann S.flat} (t : Term σ Γ S.flat a)
    (Ξ : WFF σ ((Γ.diaIn x).insert (.bnd 0) S.ty) 1)
    (q : Proof σ (Γ.diaIn x) [WFF.ex S.ty Ξ] .bot)
    (p : Proof σ Γ Δ (WFF.retxS hS x hx S t Ξ)) : Proof σ Γ Δ .bot :=
  Proof.dia_bot x hx (Proof.imp_elim (Proof.ofSubset (fun _ h => by simp at h)
    (Proof.imp_intro (Proof.K_dia x hx (Δ₁ := []) (Δ₂ := []) q)))
    (Proof.ret_diaS hS (.pos x hx) t _ p))

/-! ## The seed and its consistency -/

section Seed

variable (hS : ModalSys.BStrong = true) {l : List VarType} {A : VarType} {y : ℕ}
  (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) {x : VarSymb}
  {X : VarType} (hX : (ctxOf l).ref x = some (.VTypeDia X))

/-- ⭐The seed of the witness child of `◇_x^{S_A}[u ↦ W] Ξ`. -/
def retSeedXC (M : Set (WFF σ (ctxOf l) 0))
    (Ξ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox A)) 1) :
    Set (WFF σ (ctxOf (X :: rcl l A)) 0) :=
  {liftBodyXR l A hX Ξ} ∪
    {φ | ∃ Θ, WFF.neg (WFF.retxS hS x ⟨X, hX⟩ (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Θ)
      ∈ M ∧ φ = liftBodyXR l A hX (WFF.neg Θ)}

theorem retSeedXC_list {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.IsMCS M)
    {Ξ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox A)) 1}
    (hΞ : WFF.retxS hS x ⟨X, hX⟩ (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ ∈ M) :
    ∀ L : List (WFF σ (ctxOf (X :: rcl l A)) 0), (∀ δ ∈ L, δ ∈ retSeedXC hS hy hX M Ξ) →
      ∃ Ξ', WFF.retxS hS x ⟨X, hX⟩ (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ' ∈ M ∧
        Theory.Derives {liftBodyXR l A hX Ξ'} (liftBodyXR l A hX Ξ) ∧
        ∀ δ ∈ L, Theory.Derives {liftBodyXR l A hX Ξ'} δ
  | [], _ => ⟨Ξ, hΞ, Theory.Derives.of_mem rfl, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨Ξ₀, hΞ₀, hΦ₀, hL⟩ := retSeedXC_list hM hΞ L
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      rcases h δ List.mem_cons_self with hδ | ⟨Θ, hΘ, rfl⟩
      · refine ⟨Ξ₀, hΞ₀, hΦ₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · rw [Set.mem_singleton_iff.mp hδ]
          exact hΦ₀
        · exact hL d hd
      · have hand : ∀ φ, Proof σ _ [liftBodyXR l A hX (Ξ₀.and Θ.neg)] φ →
            Theory.Derives {liftBodyXR l A hX (Ξ₀.and Θ.neg)} φ :=
          fun φ p => ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; rfl, ⟨p⟩⟩
        have h₀ := hand _ (Proof.and_elim_l (ψ := liftBodyXR l A hX Θ.neg)
          (Proof.lookup List.mem_cons_self))
        have h₁ := hand _ (Proof.and_elim_r (φ := liftBodyXR l A hX Ξ₀)
          (Proof.lookup List.mem_cons_self))
        have htr : ∀ d, Theory.Derives {liftBodyXR l A hX Ξ₀} d →
            Theory.Derives {liftBodyXR l A hX (Ξ₀.and Θ.neg)} d :=
          fun d hd => Derives.trans (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact h₀) hd
        refine ⟨Ξ₀.and Θ.neg, hM.closed ⟨[_, _], fun x hx => ?_,
          ⟨Proof.retx_KC_node hS hX (bornComps A) (bornComps_ok A) _ Ξ₀ Θ
            (Proof.lookup List.mem_cons_self)
            (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩,
          htr _ hΦ₀, fun d hd => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hΞ₀
          · rw [List.mem_singleton.mp hx]; exact hΘ
        rcases List.mem_cons.mp hd with rfl | hd
        · exact h₁
        · exact htr d (hL d hd)

/-- ⭐**The witness child's seed is consistent**, for either value of T. -/
theorem retSeedXC_consistent {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.IsMCS M)
    {Ξ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox A)) 1}
    (hΞ : WFF.retxS hS x ⟨X, hX⟩ (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ ∈ M) :
    Theory.Consistent (retSeedXC hS hy hX M Ξ) := by
  rintro ⟨L, hL, hp⟩
  obtain ⟨Ξ', hΞ', -, hder⟩ := retSeedXC_list hS hy hX hM hΞ L hL
  obtain ⟨Δ, hΔ, ⟨p⟩⟩ := Derives.trans (fun x hx => hder x hx) ⟨L, fun x hx => hx, hp⟩
  have p' : Proof σ (ctxOf (X :: rcl l A)) [liftBodyXR l A hX Ξ'] .bot :=
    Proof.ofSubset (fun x hx => by
      rw [Set.mem_singleton_iff.mp (hΔ x hx)]; exact List.mem_cons_self) p
  haveI : (pullCtxC ((ctxOf l).diaIn x) l A).Presented :=
    Ctx.Presented.insertFree inferInstance _ (pullCtxX_fresh l x) _
  have q := Proof.subst p' (retPullC σ l A (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x)
    (.ren (.step x .dia))) (ok_retPullCX l A hX)
    (coh_retPullC_of l A _ _ _ (ok_retPullCX l A hX)) Ctx.NoSlots.slots
  simp only [List.map_cons, List.map_nil, subst_retPullC_liftBodyXR] at q
  refine hM.1 ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hΞ',
    ⟨Proof.retx_refuteS hS _ _ _ Ξ' ?_ (Proof.lookup List.mem_cons_self)⟩⟩
  refine Proof.ex_elim l.length _ (pullCtxX_fresh l x)
    (φ := WFF.openFree _ (pullCtxX_fresh l x) Ctx.NoSlots.slots Ξ') (ψ := .bot)
    (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
      (Proof.lookup List.mem_cons_self)) ?_
  exact Proof.ofSubset (fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_self) q

end Seed

/-! ## The births' identities along `x` -/

/-- `tupC`'s object with its slot sent to the born root `c`, by any substitution doing so: the
    tuple object of `c`'s items. -/
theorem subst_tupC_obj_gen {V Δ : Ctx} (A : VarType) (hcΔ : (ctxOf [VarType.VTypeBox A]).Le Δ)
    {ι : VarSymb → VarSymb} (θ : Subst σ Δ) (hθ : Subst.Ok (V.insert (.bnd 0) (.VTypeBox A)) θ)
    (hc : Subst.Coh ι (V.insert (.bnd 0) (.VTypeBox A)) θ)
    (h0 : θ.at (.root (.bnd 0)) = .ren (.root (.free 0))) : ∀ (b : Bool) (hb : ModalSys.T = b),
    (⟨_, Term.subst ι θ hθ hc (Term.mono ((Ctx.empty_le V).insert (.bnd 0) _)
        (ShapeMap.tupC (σ := σ) A b hb).obj.2)⟩ :
      Σ c, Term σ Δ (.VTypeBox (tupOneTy A b)) c) =
      ⟨_, Term.boxtm (Term.mono hcΔ.boxIn (tup1B A b hb).2)⟩
  | false, hb => by
      dsimp only [ShapeMap.obj]
      rw [Term.subst_mono]
      refine sig_boxtm (sig_pair rfl ((Term.subst_eta_renAt _ _ _ A _ _ _
        (Ctx.ref_inner (hcΔ.ref (born_ref A))) (Subst.box_at_inner_ren _ h0)).trans ?_))
      exact (eta_addr_congr (VarSymb.inner_box ModalSys.NoFour.keepOnly) _ _).trans
        (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm)
  | true, hb => by
      dsimp only [ShapeMap.obj]
      rw [Term.subst_mono]
      refine sig_boxtm (sig_pair rfl ((Term.subst_bcTree _ _ _ (.VTypeBox A) _).trans ?_))
      refine (congrArg (bcTree (.VTypeBox A)) (funext fun q => funext fun hq => ?_)).trans
        ((itemsTree_tupB hb (.VTypeBox A) (.root (.free 0)) (hcΔ.ref (born_ref A))).trans
          (congrArg (Sigma.mk _) (mono_tupB hcΔ _ _ _ _ _).symm))
      exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.box_at_inner_ren _
        (Subst.at_ext_ren _ q h0 (VarType.compAt_isProj _ q (VarType.compAt_hereChains _ q hq))))

/-- A body along `x` over the born root's tuple read at the witness child, at a flag value. -/
noncomputable def liftBodyX1B (l : List VarType) (A : VarType) (b : Bool) (hb : ModalSys.T = b)
    {x : VarSymb} {X : VarType} (hX : (ctxOf l).ref x = some (.VTypeDia X))
    (Φ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox (tupOneTy A b))) 1) :
    WFF σ (ctxOf (X :: rcl l A)) 0 :=
  WFF.subst (Subst.setIdx (arrowXIdx Nat.succ x (l.length + 1)) (.bnd 0)
      (.tm (Term.boxtm (Term.mono (ctxOf_le_of_suffix (rclX_suffix l A X)).boxIn
        (tup1B A b hb).2))))
    ((arrowXS σ (ctxOf (X :: rcl l A)) Nat.succ x (l.length + 1)).set (.bnd 0)
      (.tm (Term.boxtm (Term.mono (ctxOf_le_of_suffix (rclX_suffix l A X)).boxIn
        (tup1B A b hb).2))))
    (Subst.ok_set (ok_arrowXS (rclXImg l A X) hX (rclX_cx l A X)) rfl)
    (Subst.coh_set (ok_arrowXS (rclXImg l A X) hX (rclX_cx l A X))
      (coh_arrowXS (rclXImg l A X) hX (rclX_cx l A X))
      ((Ctx.NoSlots.slots (Γ := (ctxOf l).diaIn x)).rootFresh (le_refl 0)) rfl)
    ((Ctx.NoSlots.slots (Γ := (ctxOf l).diaIn x)).insert _) Ctx.NoSlots.slots Φ

theorem liftBodyX_born (l : List VarType) (A : VarType) {x : VarSymb} {X : VarType}
    (hX : (ctxOf l).ref x = some (.VTypeDia X))
    (Φ : WFF σ (bodyCtxX [VarType.VTypeBox A] l x) 1) :
    liftBodyX (rclX_suffix l A X) (rclXImg l A X) hX (rclX_cx l A X) Φ =
      liftBodyX1B l A ModalSys.T rfl hX Φ :=
  rfl

/-- ⭐**P2 along `x`**. -/
theorem liftBodyXR_tupC (l : List VarType) (A : VarType) {x : VarSymb} {X : VarType}
    (hX : (ctxOf l).ref x = some (.VTypeDia X)) (b : Bool) (hb : ModalSys.T = b)
    (Φ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox (tupOneTy A b))) 1) :
    liftBodyXR l A hX (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
        (ShapeMap.tupC (σ := σ) A b hb).obj.2) Φ) = liftBodyX1B l A b hb hX Φ := by
  unfold liftBodyXR WFF.bodyRepl liftBodyX1B
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = .VTypeBox (tupOneTy A b) := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp]
    rw [Subst.set_root, Subst.set_root]
    exact SubE.sim_tm_sigma (subst_tupC_obj_gen A (ctxOf_le_of_suffix (rclX_suffix l A X)) _ _ _
      (by rw [Subst.at_nonproj _ rfl, Subst.set_root]) b hb).symm
  · dsimp only [Subst.comp]
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr, show (Subst.idS σ _ v) = .ren v from rfl,
      SubE.comp_ren, Subst.at_nonproj _ hlp, Subst.set_ne _ _ hvr]
    exact .refl _

/-- The forward body as the unit's hole formula, for any rest of the hole: `thetaF` at a
    witnessed slot too. -/
def thetaG {U : VarType} (A : VarType) (Ψ : WFF σ ((ctxOf [VarType.VTypeBox A]).boxIn.insert
    (.bnd 0) U) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (A.compsFlat (bornComps A)) U)) 1 :=
  WFF.holeAt (Ctx.slotsFrom_empty.insert _)
    (Term.pair
      (Term.holeAt (Term.eta (.step (.root (.bnd 0)) .fst) (A.compsFlat (bornComps A))
        (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))) (arrT A).2)
      (Term.eta (.step (.root (.bnd 0)) .snd) U (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))
    (pack2 [.VTypeBox A] U Ψ)

/-- **F1** for any rest of the hole. -/
theorem holeRead_thetaG {l : List VarType} {A : VarType} {y : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) {U : VarType}
    {z : Ann U} (Z : Term σ (ctxOf l) U z)
    (Ψ : WFF σ ((ctxOf [VarType.VTypeBox A]).boxIn.insert (.bnd 0) U) 1) :
    WFF.holeRead (Term.pair (unarrT hy).2 Z) (thetaG A Ψ) =
      WFF.holeRead (Term.pair (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg l A hy)).2 Z)
        (pack2 [.VTypeBox A] U Ψ) := by
  rw [WFF.holeRead_eq_holeAt, WFF.holeRead_eq_holeAt]
  unfold thetaG
  refine (WFF.subst_holeAt _ _ _ _ _ _ _).trans (WFF.holeAt_congr _ (sig_pair ?_ ?_) _)
  · refine (Term.holeAt_holeAt_sig _ _ _).trans ((sig_holeAt (Term.holeAt_pair_fst _ _) _).trans ?_)
    exact holeAt_unarrT_arrT hy
  · exact Term.holeAt_pair_snd _ _

/-- **F2 along the witness**: the witnessed companion unit's conjunct at the parent's tuple and
    `x`, read at the witness child, is the forward witness arrow's returning possibility. -/
theorem liftBodyXR_unitBodyWC_thetaG (hS : ModalSys.BStrong = true) (l : List VarType)
    (A : VarType) {x : VarSymb} {X : VarType} (hX : (ctxOf l).ref x = some (.VTypeDia X))
    (Ψ : WFF σ (bodyCtxW l [.VTypeBox A] X) 1) (cs : List (List Step))
    (h : (bcT l).CompOk cs) :
    liftBodyXR l A hX (WFF.unitBodyWC hS (bornComps A) (bornComps_ok A) (tupT l).2
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) cs h (thetaG A Ψ)) =
      WFF.retS hS (.wit (.boxC (bcT l) cs h) X)
        (Term.pair (tupCompsImg l Nat.succ (rclXImg l A X) cs h).2
          (Term.eta (.root (.free (l.length + 1))) X (rclX_cx l A X)))
        (WFF.mono ((ctxOf_le_of_suffix (rclX_suffix l A X)).boxIn.insert (.bnd 0) _) Ψ) := by
  unfold liftBodyXR WFF.unitBodyWC
  refine WFF.retS_congr hS _ (sig_pair ?_ ?_) ?_
  · rw [Term.subst_mono]
    refine (Term.subst_congr _ (arrowS σ (ctxOf (X :: rcl l A)) Nat.succ) _
      (ok_arrowS (rclXImg l A X)) _ (coh_arrowS (rclXImg l A X)) ?_ _).trans
      (subst_arrow_compsVal l (rclXImg l A X) cs h)
    refine Subst.sim_of fun v T _ hv => ?_
    obtain ⟨u, rfl, _⟩ := boxIn_item hv
    rw [Subst.set_ne _ _ (fun h => by cases h)]
    exact .refl _
  · rw [Term.subst_mono]
    refine Term.subst_eta_renAt _ _ _ _ _ _ _ _ ?_
    rw [Subst.at_nonproj _ rfl, Subst.set_ne _ _ (fun h => by cases h)]
    exact if_pos rfl
  · rw [WFF.subst_holeAt]
    refine (WFF.holeAt_congr _ (sig_pair
      (Term.subst_compsSlot _ _ (rclX_born_ref l A X)
        (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf (X :: rcl l A)).boxIn)).root _) _ _ _
        (fun q _ hq _ => ?_) _ _)
      (Term.subst_eta_renAt _ _ _ _ _ (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)
        (Subst.under_at_slot _ (0 + 1) 0 _ _))) _).trans ?_
    · rw [Subst.at_under_ne _ _ _ (by
          rw [VarSymb.inner_rt, VarSymb.ext_rt]; exact fun h => by cases h),
        Subst.box_at_inner_ren _ (Subst.at_ext_ren _ q
          (by rw [Subst.at_nonproj _ rfl, Subst.set_root]) hq)]
      rfl
    · unfold thetaG
      refine (WFF.subst_holeAt _ _ _ _ _ _ _).trans ?_
      refine (WFF.holeAt_congr _ (sig_pair ?_ (Term.holeAt_pair_snd _ _)) _).trans
        (holeAt_tupT_pack2 (ctxOf_le_of_suffix (rclX_suffix l A X)).boxIn Ψ)
      refine (Term.holeAt_holeAt_sig _ _ _).trans
        ((sig_holeAt (Term.holeAt_pair_fst _ _) _).trans ?_)
      rw [compsSlot_home (rclX_born_ref l A X) _ (born_ref A)
        ((ctxOf_le_of_suffix (rclX_suffix l A X)).boxIn.trans
          (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf (X :: rcl l A)).boxIn)).root _))]
      refine (sig_holeAt (mono_compsSlot (born_ref A) (Ctx.Le.refl _)
        ((ctxOf_le_of_suffix (rclX_suffix l A X)).boxIn.trans
          (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf (X :: rcl l A)).boxIn)).root _))
        (bornComps A) (bornComps_ok A)).symm _).trans ?_
      refine (Term.mono_holeAt_sig _ _ _).symm.trans ?_
      exact sig_mono _ (holeAt_compsSlot_arrT A)

/-! ## The witness child, born with the invariants -/

section BirthXC

variable (hS : ModalSys.BStrong = true) {tp : NodeSt σ} {A : VarType} {y : ℕ}
  (hy : (ctxOf tp.l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) {x : VarSymb}
  {X : VarType} (hX : (ctxOf tp.l).ref x = some (.VTypeDia X))

/-- ⭐The witness child of the obligation `◇_x^{S_A}[u ↦ W] Ξ` of `tp`. -/
noncomputable def retChildXC
    (Ξ : WFF σ (((ctxOf tp.l).diaIn x).insert (.bnd 0) (.VTypeBox A)) 1) : NodeSt σ :=
  ⟨X :: rcl tp.l A, complete (retSeedXC hS hy hX tp.M Ξ)⟩

variable (hM : Theory.IsMCS tp.M)
  {Ξ : WFF σ (((ctxOf tp.l).diaIn x).insert (.bnd 0) (.VTypeBox A)) 1}
  (hΞ : WFF.retxS hS x ⟨X, hX⟩ (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ ∈ tp.M)

include hM hΞ

theorem retChildXC_spec : retSeedXC hS hy hX tp.M Ξ ⊆ (retChildXC hS hy hX Ξ).M ∧
    Theory.IsMCS (retChildXC hS hy hX Ξ).M :=
  complete_spec (retSeedXC_consistent hS hy hX hM hΞ)

theorem retChildXC_body : liftBodyXR tp.l A hX Ξ ∈ (retChildXC hS hy hX Ξ).M :=
  (retChildXC_spec hS hy hX hM hΞ).1 (Or.inl rfl)

/-- ⭐**The way home at birth, with companions**. -/
theorem retChildXC_back :
    RetInvXB hS ModalSys.T rfl (retChildXC hS hy hX Ξ) tp [.VTypeBox A] (fun _ => y) tp.l
      Nat.succ x X (tp.l.length + 1) := by
  obtain ⟨hsub, hmcs⟩ := retChildXC_spec hS hy hX hM hΞ
  refine ⟨rclX_suffix tp.l A X, retBackImg tp.l A hy, List.suffix_refl _, rclXImg tp.l A X, hX,
    rclX_cx tp.l A X, fun Φ hΦ => ?_⟩
  rw [WFF.mono_refl]
  by_contra hn
  have hn' : WFF.neg (WFF.retxS hS x ⟨X, hX⟩ (.nec (bornShape A)) (unarrT (σ := σ) hy).2
      (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
        (ShapeMap.tupC (σ := σ) A ModalSys.T rfl).obj.2) Φ)) ∈ tp.M := by
    refine hM.neg_mem_iff.mpr fun hr => hn ?_
    refine hM.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hr, ⟨?_⟩⟩
    exact Proof.conv (WFF.retxS_congr hS x _ _ (holeRead_unarrT_tupC hy) rfl)
      (Proof.ret_map hS (.pos x ⟨X, hX⟩) (S := .nec (bornShape A))
        (ShapeMap.tupC A ModalSys.T rfl) _ Φ (Proof.lookup List.mem_cons_self))
  have h₁ := hsub (Or.inr ⟨_, hn', rfl⟩)
  have e : liftBodyXR tp.l A hX (WFF.neg (WFF.bodyRepl
      (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
        (ShapeMap.tupC (σ := σ) A ModalSys.T rfl).obj.2) Φ)) =
      WFF.neg (liftBodyX (rclX_suffix tp.l A X) (rclXImg tp.l A X) hX (rclX_cx tp.l A X) Φ) := by
    rw [liftBodyX_born, ← liftBodyXR_tupC]
    rfl
  rw [e] at h₁
  refine hmcs.1 ⟨[_, _], fun x hx => ?_, ⟨Proof.imp_elim
    (φ := liftBodyX (rclX_suffix tp.l A X) (rclXImg tp.l A X) hX (rclX_cx tp.l A X) Φ)
    (Proof.lookup List.mem_cons_self)
    (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁
  · rw [List.mem_singleton.mp hx]; exact hΦ

/-- ⭐**The forward witness arrow at birth, with companions**. -/
theorem retChildXC_fwd :
    RetInvWB hS ModalSys.T rfl tp (retChildXC hS hy hX Ξ) tp.l Nat.succ [.VTypeBox A]
      (fun _ => y) x X (tp.l.length + 1) := by
  obtain ⟨hsub, hmcs⟩ := retChildXC_spec hS hy hX hM hΞ
  refine ⟨List.suffix_refl _, rclXImg tp.l A X, rclX_suffix tp.l A X, retBackImg tp.l A hy, hX,
    rclX_cx tp.l A X, fun Ψ hΨ => ?_⟩
  refine (congrArg (· ∈ (retChildXC hS hy hX Ξ).M) (liftBodyXR_unitBodyWC_thetaG hS tp.l A hX Ψ
    _ (VarType.compOk_compsAllB _ rfl _))).mp ?_
  have hle := ctxOf_le_of_suffix (List.suffix_refl tp.l)
  have e : WFF.unitBodyWC hS (bornComps A) (bornComps_ok A) (Term.mono hle.boxIn (tupT tp.l).2)
      (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) _
      (VarType.compOk_compsAllB _ rfl (bcT tp.l)) (thetaG A Ψ) =
      WFF.unitBodyWC hS (bornComps A) (bornComps_ok A) (tupT tp.l).2
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) _
        (VarType.compOk_compsAllB _ rfl (bcT tp.l)) (thetaG A Ψ) := by
    rw [Term.mono_refl]
  have hU : WFF.neg (WFF.retxS hS x ⟨X, hX⟩ (.nec (bornShape A)) (unarrT (σ := σ) hy).2
      (WFF.neg (WFF.unitBodyWC hS (bornComps A) (bornComps_ok A) (tupT tp.l).2
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) _
        (VarType.compOk_compsAllB _ rfl (bcT tp.l)) (thetaG A Ψ)))) ∈ tp.M := by
    refine hM.neg_mem_iff.mpr fun hr => hM.1 ⟨[WFF.retxS hS x ⟨X, hX⟩ (.nec (bornShape A))
      (unarrT (σ := σ) hy).2 (WFF.neg (WFF.unitBodyWC hS (bornComps A) (bornComps_ok A)
        (tupT tp.l).2 (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) _
        (VarType.compOk_compsAllB _ rfl (bcT tp.l)) (thetaG A Ψ))),
      liftBodyW (List.suffix_refl tp.l) (retBackImg tp.l A hy) hX Ψ], fun x hx => ?_, ⟨?_⟩⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hr
      · rw [List.mem_singleton.mp hx]; exact hΨ
    refine Proof.retxS_absurd hS ⟨X, hX⟩ _ _ _ (ctxOf_fresh (l := tp.l) le_rfl)
      (Proof.conv (by rw [e])
      (Proof.ret_unitWC hS ⟨X, hX⟩ (bornComps A) (bornComps_ok A) _ _
        (Term.mono hle.boxIn (tupT tp.l).2) (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))
        _ (VarType.compOk_compsAllB _ rfl (bcT tp.l)) _ (Proof.lookup List.mem_cons_self) ?_))
    exact Proof.conv ((holeRead_thetaG hy (Term.pair (Term.boxtm (Term.mono hle.boxIn
        (tupT tp.l).2)) (Term.eta x (.VTypeDia X) (hle.ref hX))) Ψ).trans
      (holeRead_tupImgT_pack2 (retBackImg tp.l A hy)
        (Term.pair (Term.boxtm (Term.mono hle.boxIn (tupT tp.l).2))
          (Term.eta x (.VTypeDia X) (hle.ref hX))) Ψ)).symm
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
  have h₁ := hsub (Or.inr ⟨_, hU, rfl⟩)
  exact hmcs.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact h₁,
    ⟨Proof.byContra (Proof.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.lookup List.mem_cons_self))⟩⟩

end BirthXC

end BArrow

end V12M
