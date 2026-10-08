import QML.QML_v12m_BPack
import QML.QML_v12m_BNet

/-!
# QML v12m — strong B on the network: the returning-possibility invariant

Under strong B an arrow `v → w` of the network carries, besides necessity transfer, the **atom
invariant** of `docs/v12-modal-extensions.md` §11.17: what `v` says of the roots committed along
the arrow comes back to `w` as a returning possibility, valued at their images.  The roots are
packed into one bound necessary object (`QML_v12m_BPack`).

* `liftBody`: a body over the committed roots, read at `v` — its `□` items sent along the
  reverse arrow, its bound object the necessary object holding the committed roots' items.
* ⭐`RetInv`: every body true at `v` when read there is a returning possibility at `w`.
* ⭐`RetInv.transfer`: the invariant gives necessity transfer, by `ret_counit` on a packed
  necessity — so under strong B the network can keep the invariant alone.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## Hole formulas -/

/-- Reading a hole formula at depth 0 is reading it at any depth. -/
theorem WFF.holeRead_eq_holeAt {Γ : Ctx} [Γ.NoSlots] {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) :
    WFF.holeRead t ψ = WFF.holeAt Ctx.NoSlots.slots t ψ :=
  WFF.subst_mono _ _ _ _ _ _ _ ψ

/-- Weakening a hole formula's reading is reading it at the weakened term. -/
theorem WFF.mono_holeAt {Γ Γ' : Ctx} (h : Γ.Le Γ') {d : ℕ} (hs : Γ.SlotsFrom d)
    (hs' : Γ'.SlotsFrom d) {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) :
    WFF.mono h (WFF.holeAt hs t ψ) = WFF.holeAt hs' (Term.mono h t) ψ := by
  unfold WFF.holeAt
  rw [WFF.mono_subst h _ _ _ _ hs hs']
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of ?_) ψ
  intro v T _ hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    change SubE.Sim T
      (SubE.mono h (Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm t) (.root (.bnd 0))))
      (Subst.single (σ := σ) (Δ := Γ') (.bnd 0) (.tm (Term.mono h t)) (.root (.bnd 0)))
    unfold Subst.single
    rw [if_pos rfl, if_pos rfl]
    exact .refl _
  · change (if v = VarSymb.root (.bnd 0) then _ else Ctx.empty v) = _ at hv
    rw [if_neg hvr] at hv
    cases hv

variable [ModalSys.NoFour]

/-- The entry of a necessary object's term, one view in: its body. -/
theorem Subst.box_at_inner_boxtm {Δ : Ctx} (θ : Subst σ Δ) {v : VarSymb} {A : VarType}
    {a : Ann A} {t : Term σ Δ.boxIn A a} (hs : θ.at v = .tm (.boxtm t)) :
    θ.box.at v.inner = .tm t := by
  rw [VarSymb.inner_box ModalSys.NoFour.keepOnly]
  change (θ.at v).unbox = _
  rw [hs]
  rfl

/-! ## The invariant -/

/-- A body's context: the reverse arrow's committed roots' `□` view, with the bound object. -/
abbrev bodyCtx (cls clt : List VarType) : Ctx :=
  (ctxOf clt).boxIn.insert (.bnd 0) (.VTypeBox (bcN cls cls.length))

/-- ⭐A body read at the far end `v`: its `□` items sent along the reverse arrow (`imgt`), its
    bound object the necessary object holding the committed roots' items. -/
def liftBody {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) (Φ : WFF σ (bodyCtx cls clt) 1) : WFF σ (ctxOf lv) 0 :=
  WFF.instantiate Ctx.NoSlots.slots
    (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupN cls cls.length le_rfl).2))
    (WFF.subst (VarSymb.shiftSlot (arrowIdx imgt) 0 0)
      ((arrowS σ (ctxOf lv) imgt).under 0 0 _ (Ctx.NoSlots.slots (Γ := ctxOf lv)).root)
      (Subst.ok_under (ok_arrowS himgt) _ (Ctx.NoSlots.slots (Γ := ctxOf lv)).root)
      (Subst.coh_under (ok_arrowS himgt) (coh_arrowS himgt) Ctx.NoSlots.slots _
        (Ctx.NoSlots.slots (Γ := ctxOf lv)).root)
      ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).insert _)
      ((Ctx.NoSlots.slots (Γ := ctxOf lv)).insert _) Φ)

/-- ⭐**The returning-possibility invariant** of an arrow `v → w` (docs §11.17): every body over
    the roots `cls` committed along it that `v` makes true when read there is a returning
    possibility at `w`, valued at the tuple of their images. -/
def RetInv (hS : ModalSys.BStrong = true) (tv tw : NodeSt σ) (cls : List VarType)
    (imgs : ℕ → ℕ) (clt : List VarType) (imgt : ℕ → ℕ) : Prop :=
  ∃ (hs : cls <:+ tv.l) (himgs : ImgOk cls (ctxOf tw.l) imgs) (ht : clt <:+ tw.l)
    (himgt : ImgOk clt (ctxOf tv.l) imgt),
    ∀ Φ : WFF σ (bodyCtx cls clt) 1, liftBody hs himgt Φ ∈ tv.M →
      WFF.ret hS (tupImg cls imgs himgs cls.length le_rfl).2
        (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Φ) ∈ tw.M

/-! ## Transfer from the invariant -/

/-- A packed necessity of the bound object, read at `v`: the packed formula, necessarily, at the
    committed roots' items. -/
theorem liftBody_box_holeAt {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (bcN cls cls.length)) 1) :
    liftBody hs himgt (WFF.box (WFF.holeAt
        ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).insert _).boxIn
        (Term.eta (VarSymb.root (.bnd 0)).inner _
          (Ctx.ref_inner (Ctx.ref_insert_root _ (.bnd 0) (.VTypeBox (bcN cls cls.length)))))
        θ)) =
      WFF.box (WFF.holeAt Ctx.NoSlots.slots
        (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupN cls cls.length le_rfl).2) θ) := by
  unfold liftBody WFF.instantiate WFF.substRoot
  simp only [WFF.subst]
  rw [WFF.subst_holeAt, WFF.subst_holeAt]
  refine congrArg WFF.box (WFF.holeAt_congr _ ?_ θ)
  have hw : ((ctxOf lv).insert (.bnd 0) (.VTypeBox (bcN cls cls.length))).boxIn.ref
      (VarSymb.root (.bnd 0)).inner = some (bcN cls cls.length) :=
    Ctx.ref_inner (Ctx.ref_insert_root _ (.bnd 0) _)
  refine (Term.subst_sigma (q := ⟨_, Term.eta _ _ hw⟩) (Term.subst_eta_renAt _ _ _ _ _ _ _ hw
    (Subst.box_at_inner_ren _ (Subst.under_at_root _ _ _)))).trans ?_
  exact Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ (by
    change Subst.single (.bnd 0) _ (.root (.bnd 0)) = _
    exact if_pos rfl))

/-- ⭐**The invariant gives necessity transfer**: a necessity about the committed roots, packed,
    is a body whose returning possibility `ret_counit` reads at the images — which is the necessity
    sent along the arrow (`holeRead_tupImg_pack`). -/
theorem RetInv.transfer {hS : ModalSys.BStrong = true} {tv tw : NodeSt σ}
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} (hM : Theory.IsMCS tw.M)
    (h : RetInv hS tv tw cls imgs clt imgt) :
    ∃ (hs : cls <:+ tv.l) (himgs : ImgOk cls (ctxOf tw.l) imgs),
      Transfer tv.M cls (ctxOf_le_of_suffix hs) tw.M imgs himgs := by
  obtain ⟨hs, himgs, ht, himgt, hinv⟩ := h
  refine ⟨hs, himgs, fun ψ hψ => ?_⟩
  have hret := hinv _ (by
    rw [liftBody_box_holeAt hs himgt (pack cls ψ),
      ← WFF.mono_holeAt _ (Ctx.NoSlots.slots (Γ := (ctxOf cls).boxIn)),
      ← WFF.holeRead_eq_holeAt, holeRead_tupN_pack]
    exact hψ)
  rw [← holeRead_tupImg_pack himgs ψ]
  refine hM.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hret, ⟨?_⟩⟩
  refine Proof.ret_counit hS _ (pack cls ψ)
    (Proof.conv (congrArg (WFF.ret hS _) ?_) (Proof.lookup List.mem_cons_self))
  change WFF.box (WFF.mono _ (WFF.holeAt _ _ (pack cls ψ))) = _
  rw [WFF.mono_holeAt _ _ (((Ctx.NoSlots.slots (Γ := (ctxOf tw.l).boxIn)).insert _).boxIn),
    Term.mono_eta]

end BArrow

end V12M
