import QML.QML_v12m_BRet

/-!
# QML v12m — strong B on the network: witness arrows

A witness child `k` of `p`, made for `◇_x φ`, is reached along `x`'s arrow, and its way home `k → p`
carries the returning-possibility invariant **along `x`** (`RetInvX`, docs §11.17): what `k` says
of its back-committed roots and of `x`'s content `cx` comes back to `p` as `◇_x[d ↦ t] Φ`.  It
subsumes the forward arrow's `□_x` transfer, and it is what lets a forward commitment along a
witness arrow be argued at the parent, where `x` has a name.

* `liftBodyX`, `RetInvX`: the invariant.
* `RetInvX.nil`: with nothing committed back it holds at birth, from the forward arrow's `□_x`
  transfer and `ret_new` along `x`.
-/

namespace V12M

namespace BArrow

variable [ModalSys] {σ : Signature} [ModalSys.NoFour]

/-! ## The invariant -/

/-- A witness body's context: the forward arrow's committed roots seen along `x`, with the bound
    object. -/
abbrev bodyCtxX (cls clt : List VarType) (x : VarSymb) : Ctx :=
  ((ctxOf clt).diaIn x).insert (.bnd 0) (.VTypeBox (bcT cls))

/-- ⭐A witness body read at the witness child: its items go along the forward arrow (`imgt`),
    `x`'s content to `cx`, and its bound object to the necessary object holding the
    back-committed roots' items. -/
noncomputable def liftBodyX {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf clt).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) (Φ : WFF σ (bodyCtxX cls clt x) 1) :
    WFF σ (ctxOf lv) 0 :=
  WFF.subst (Subst.setIdx (arrowXIdx imgt x cx) (.bnd 0) (liftEntry hs))
    ((arrowXS σ (ctxOf lv) imgt x cx).set (.bnd 0) (liftEntry hs))
    (Subst.ok_set (ok_arrowXS himgt hx hcx) rfl)
    (Subst.coh_set (ok_arrowXS himgt hx hcx) (coh_arrowXS himgt hx hcx)
      ((Ctx.NoSlots.slots (Γ := (ctxOf clt).diaIn x)).rootFresh (le_refl 0)) rfl)
    ((Ctx.NoSlots.slots (Γ := (ctxOf clt).diaIn x)).insert _) Ctx.NoSlots.slots Φ

/-- ⭐**The returning-possibility invariant along a witness** of a witness child `tk`'s way home to
    its parent `tp`: every body over the back-committed roots `cls` and the forward-committed roots
    `clt` seen along `x` that the child makes true is, at the parent, a returning possibility
    along `x`, valued at the tuple of the back images. -/
def RetInvX (hS : ModalSys.BStrong = true) (tk tp : NodeSt σ) (cls : List VarType)
    (imgs : ℕ → ℕ) (clt : List VarType) (imgt : ℕ → ℕ) (x : VarSymb) (X : VarType) (cx : ℕ) :
    Prop :=
  ∃ (hs : cls <:+ tk.l) (himgs : ImgOk cls (ctxOf tp.l) imgs) (ht : clt <:+ tp.l)
    (himgt : ImgOk clt (ctxOf tk.l) imgt) (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X),
    ∀ Φ : WFF σ (bodyCtxX cls clt x) 1, liftBodyX hs himgt hx hcx Φ ∈ tk.M →
      (OutLeg.pos x ⟨X, (ctxOf_le_of_suffix ht).ref hx⟩ : OutLeg (ctxOf tp.l)).ret hS
        (tupImgT cls imgs himgs).2
        (WFF.mono (((ctxOf_le_of_suffix ht).diaIn x).insert (.bnd 0) _) Φ) ∈ tp.M

/-- A non-slot variable of a witness body's context is an item, or `x`'s content. -/
theorem bodyX_item {cl clt : List VarType} {x v : VarSymb} {U : VarType}
    (hv : bodyCtxX cl clt x v = some U) (hvr : v ≠ .root (.bnd 0)) :
    (∃ u, v = .step u .box ∧ (ctxOf clt).ref u = some (.VTypeBox U)) ∨
      (v = .step x .dia ∧ (ctxOf clt).ref x = some (.VTypeDia U)) := by
  change (if v = VarSymb.root (.bnd 0) then _ else ((ctxOf clt).diaIn x) v) = _ at hv
  rw [if_neg hvr] at hv
  exact diaIn_item hv

/-- `liftBodyX` is the body sent along the forward arrow under the slot, instantiated at the
    back-committed roots' necessary object. -/
theorem liftBodyX_eq_instantiate {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf clt).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) (Φ : WFF σ (bodyCtxX cls clt x) 1) :
    liftBodyX hs himgt hx hcx Φ = WFF.instantiate Ctx.NoSlots.slots
      (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2))
      (WFF.subst (VarSymb.shiftSlot (arrowXIdx imgt x cx) 0 0)
        ((arrowXS σ (ctxOf lv) imgt x cx).under 0 0 _ (Ctx.NoSlots.slots (Γ := ctxOf lv)).root)
        (Subst.ok_under (ok_arrowXS himgt hx hcx) _ (Ctx.NoSlots.slots (Γ := ctxOf lv)).root)
        (Subst.coh_under (ok_arrowXS himgt hx hcx) (coh_arrowXS himgt hx hcx)
          Ctx.NoSlots.slots _ (Ctx.NoSlots.slots (Γ := ctxOf lv)).root)
        ((Ctx.NoSlots.slots (Γ := (ctxOf clt).diaIn x)).insert _)
        ((Ctx.NoSlots.slots (Γ := ctxOf lv)).insert _) Φ) := by
  unfold WFF.instantiate WFF.substRoot liftBodyX
  refine (WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ).symm
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    dsimp only [Subst.comp, Subst.under]
    rw [Subst.set_root, if_pos rfl]
    dsimp only [SubE.comp]
    change SubE.Sim T _ (Subst.single _ _ (.root (.bnd 0)))
    rw [show Subst.single (σ := σ) (Δ := ctxOf lv) (.bnd 0)
      (.tm (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2)))
        (.root (.bnd 0)) = _ from if_pos rfl]
    exact .refl _
  · rcases bodyX_item hv hvr with ⟨u, rfl, hu⟩ | ⟨rfl, _⟩
    · obtain ⟨r, hr, _, _⟩ := ref_rt hu
      dsimp only [Subst.comp, Subst.under]
      rw [Subst.set_ne _ _ hvr, if_neg hvr]
      change SubE.Sim T (.ren (itemImg imgt u)) ((Subst.single _ _).at (itemImg imgt u))
      rw [Subst.single_at_ne (by rw [itemAt_rt, hr]; exact fun h => by cases h)]
      exact .refl _
    · dsimp only [Subst.comp, Subst.under]
      rw [Subst.set_ne _ _ hvr, if_neg hvr]
      rw [show arrowXS σ (ctxOf lv) imgt x cx (x.step Step.dia) = .ren (.root (.free cx)) from
        if_pos rfl]
      change SubE.Sim T (.ren (.root (.free cx)))
        ((Subst.single _ _).at (.root (.free cx)))
      rw [Subst.single_at_ne (fun h => by cases h)]
      exact .refl _

/-! ## The invariant gives `□_x` transfer -/

omit [ModalSys.NoFour] in
/-- A formula as a body that does not use its bound slot. -/
def WFF.slotUp {Γ : Ctx} (hs : Γ.SlotsFrom 0) (T : VarType) (ψ : WFF σ Γ 0) :
    WFF σ (Γ.insert (.bnd 0) T) 1 :=
  WFF.subst id (Subst.idS σ (Γ.insert (.bnd 0) T)) (Subst.ok_idS_le (Ctx.le_insert hs.root T))
    (Subst.coh_idS_le (Ctx.le_insert hs.root T)) hs (hs.insert T) ψ

omit [ModalSys.NoFour] in
/-- Substituting into a body that does not use its slot substitutes into the formula. -/
theorem WFF.subst_slotUp {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom 0)
    {T : VarType} (θ : Subst σ Δ) (hθ : Subst.Ok (Γ.insert (.bnd 0) T) θ)
    (hc : Subst.Coh ι (Γ.insert (.bnd 0) T) θ) (hΔ : Δ.SlotsFrom d) (ψ : WFF σ Γ 0) :
    WFF.subst ι θ hθ hc (hs.insert T) hΔ (WFF.slotUp hs T ψ) =
      WFF.subst ι θ (hθ.restrict (Ctx.le_insert hs.root T))
        (hc.restrict (Ctx.le_insert hs.root T)) hs hΔ ψ :=
  WFF.subst_comp (Subst.idS σ _) θ θ _ _ hθ hc (hθ.restrict (Ctx.le_insert hs.root T))
    (hc.restrict (Ctx.le_insert hs.root T)) hs (hs.insert T) hΔ
    (Subst.sim_of fun v _ hlp _ => by
      change SubE.Sim _ _ (θ.at v)
      rw [Subst.at_nonproj θ hlp]
      exact .refl _) ψ

omit [ModalSys.NoFour] in
/-- Opening a binder over a weakened formula as a slot-free body is weakening. -/
theorem WFF.openFree_mono_slotUp {Γ Γ' : Ctx} {T : VarType} (h : Γ.Le Γ') (u : ℕ)
    (hu : Γ'.RootFresh (.free u)) (hs : Γ.SlotsFrom 0) (hs' : Γ'.SlotsFrom 0)
    (ψ : WFF σ Γ 0) :
    WFF.openFree u hu hs' (WFF.mono (h.insert (.bnd 0) T) (WFF.slotUp hs T ψ)) =
      WFF.weaken hu.root T (WFF.mono h ψ) := by
  unfold WFF.openFree WFF.weaken
  rw [WFF.subst_mono _ _ _ _ (hs.insert T), WFF.subst_slotUp,
    WFF.subst_ren ((h.trans (Ctx.le_insert hu.root T))) _ _ _ _ _
      (Subst.at_ren_of fun v U hlp hv => by
        have hvr : v ≠ .root (.bnd 0) := fun e => by
          subst e
          rw [hs.root] at hv
          cases hv
        rw [Subst.toFree_ne _ _ _ _ hvr]
        change ((Subst.idRen Γ') v).mono _ = _
        rw [← Subst.at_nonproj (Subst.idRen Γ') hlp, Subst.at_idRen]
        rfl) ψ, WFF.mono_mono]

/-- A witness body that does not use the bound object, read at the child: the arrow's reading. -/
theorem liftBodyX_slotUp {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf clt).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) (ψ : WFF σ ((ctxOf clt).diaIn x) 0) :
    liftBodyX hs himgt hx hcx (WFF.slotUp Ctx.NoSlots.slots _ ψ) =
      WFF.subst (arrowXIdx imgt x cx) (arrowXS σ (ctxOf lv) imgt x cx) (ok_arrowXS himgt hx hcx)
        (coh_arrowXS himgt hx hcx) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ := by
  unfold liftBodyX
  rw [WFF.subst_slotUp]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) ψ
  have hvr : v ≠ .root (.bnd 0) := fun h => by
    subst h
    rw [(Ctx.NoSlots.slots (Γ := (ctxOf clt).diaIn x)).root] at hv
    cases hv
  rw [Subst.set_ne _ _ hvr]
  exact .refl _

/-- ⭐**The invariant along `x` gives the forward arrow's `□_x` transfer.**  If `□_x ψ` held at
    the parent but `ψ` failed at the child, then `¬ψ`, a body not using the bound object, would
    be `◇_x[d ↦ t] ¬ψ` at the parent — so `◇_x ¬ψ`. -/
theorem RetInvX.transferX (hS : ModalSys.BStrong = true) {tk tp : NodeSt σ}
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cx : ℕ}
    (hk : Theory.IsMCS tk.M) (hp : Theory.IsMCS tp.M)
    (h : RetInvX hS tk tp cls imgs clt imgt x X cx) :
    ∃ (ht : clt <:+ tp.l) (himgt : ImgOk clt (ctxOf tk.l) imgt)
      (hx : (ctxOf clt).ref x = some (.VTypeDia X))
      (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X),
      TransferX tp.M clt (ctxOf_le_of_suffix ht) hx tk.M imgt himgt cx hcx := by
  obtain ⟨hs, _, ht, himgt, hx, hcx, hinv⟩ := h
  refine ⟨ht, himgt, hx, hcx, fun ψ hψ => ?_⟩
  by_contra hn
  have hle := ctxOf_le_of_suffix ht
  have hx' : ∃ Y, (ctxOf tp.l).ref x = some (.VTypeDia Y) := ⟨X, hle.ref hx⟩
  have hret := hinv (WFF.slotUp Ctx.NoSlots.slots _ (WFF.neg ψ)) (by
    rw [liftBodyX_slotUp]
    exact hk.neg_mem_iff.mpr hn)
  have hu := (ctxOf_fresh (l := tp.l) le_rfl).diaIn x
  have inner : Proof σ ((ctxOf tp.l).diaIn x)
      [WFF.ex (.VTypeBox (bcT cls)) (WFF.mono ((hle.diaIn x).insert (.bnd 0) _)
        (WFF.slotUp Ctx.NoSlots.slots _ (WFF.neg ψ)))]
      (WFF.neg (WFF.mono (hle.diaIn x) ψ)) := by
    refine Proof.ex_elim tp.l.length _ hu (φ := WFF.openFree tp.l.length hu Ctx.NoSlots.slots _)
      (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
        (Proof.lookup List.mem_cons_self)) (Proof.conv ?_ (Proof.lookup List.mem_cons_self))
    rw [WFF.openFree_mono_slotUp]
    rfl
  have hdia : WFF.dia x hx' (WFF.neg (WFF.mono (hle.diaIn x) ψ)) ∈ tp.M :=
    hp.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hret,
      ⟨Proof.imp_elim (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil)
        (Proof.imp_intro (Proof.K_dia (Δ₁ := []) (Δ₂ := []) x hx' inner)))
        (Proof.ret_dia hS (.pos x hx') _ _ (Proof.lookup List.mem_cons_self))⟩⟩
  exact hp.neg_mem_iff.mp hψ hdia

/-! ## Birth -/

/-- ⭐**Nothing committed back: the invariant along `x` at birth.**  A body true at the child is
    `◇_x ∃d. Φ` at the parent — or else `□_x ¬∃d. Φ` would transfer to the child — and `ret_new`
    along `x` names the unit return. -/
theorem RetInvX.nil (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true) {tk tp : NodeSt σ}
    {clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cx : ℕ}
    (hk : Theory.IsMCS tk.M) (hp : Theory.IsMCS tp.M) (ht : clt <:+ tp.l)
    (himgt : ImgOk clt (ctxOf tk.l) imgt) (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X)
    (htr : TransferX tp.M clt (ctxOf_le_of_suffix ht) hx tk.M imgt himgt cx hcx) :
    RetInvX hS tk tp [] imgs clt imgt x X cx := by
  have hle := ctxOf_le_of_suffix ht
  have hx' : ∃ Y, (ctxOf tp.l).ref x = some (.VTypeDia Y) := ⟨X, hle.ref hx⟩
  refine ⟨List.nil_suffix, fun r hr => absurd hr (Nat.not_lt_zero r), ht, himgt, hx, hcx,
    fun Φ hΦ => ?_⟩
  by_contra hn
  have hbox : WFF.mono hle (WFF.boxx x ⟨X, hx⟩ (WFF.neg (WFF.ex (.VTypeBox (bcT [])) Φ))) ∈
      tp.M := by
    by_contra hb
    apply hn
    by_cases hd : WFF.dia x hx' (WFF.mono (hle.diaIn x) (WFF.ex (.VTypeBox (bcT [])) Φ)) ∈ tp.M
    · refine hp.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hd, ⟨?_⟩⟩
      exact Proof.ret_new hS hB (.pos x hx') _ tp.l.length (ctxOf_fresh le_rfl)
        (Proof.lookup List.mem_cons_self) (Proof.lookup List.mem_cons_self)
    · exact absurd (hp.closed ⟨[_], fun y hy => by
        rw [List.mem_singleton.mp hy]; exact hp.neg_mem_iff.mpr hd,
        ⟨Proof.boxx_neg_of_not_dia x hx' _⟩⟩) hb
  have hneg := htr _ hbox
  refine hk.1 ⟨[_, _], fun y hy => ?_, ⟨Proof.imp_elim (Proof.lookup List.mem_cons_self)
    (Proof.ex_intro _ _ (Proof.conv (liftBodyX_eq_instantiate List.nil_suffix himgt hx hcx Φ)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))))⟩⟩
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hneg
  · rw [List.mem_singleton.mp hy]
    exact hΦ

end BArrow

end V12M
