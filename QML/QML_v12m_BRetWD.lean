import QML.QML_v12m_BRetW
import QML.QML_v12m_RetKXD

/-!
# QML v12m — strong B on the network: doubly witnessed arrows

A **doubly witnessed child** `k` of `p`, made for `◇_x[d ↦ y; e ⇝ z] Φ`, is reached along `x`'s
arrow and its way home lies in the extent of its own root `e` (docs §11.20).  Both of its arrows
carry the same invariant (`RetInvWD`), each at the fourth returning form: what the source says of
its committed roots and of its witness holds at the target as a returning possibility **along the
target's witness**, at the witnessed shape, valued at the roots' images and the source witness's
content.  The form is its own mirror, so one invariant, one realisation step and one unit
(`ret_unitWD`) serve both arrows.

* `liftBodyWD`, `RetInvWD`: the invariant.
* `RetInvWD.transferX`, `RetInvWD.transfer`: `□_e` and plain transfer back along it.
* `RetInvWD.grow_tgt`, `RetInvWD.grow_src`: growth.
* `retStepWD`, ⭐`retStepWD_ok`: realising the source's next root, by `ret_extS` and `ret_map`
  along the target's witness.
* ⭐`retStepWD_rev`: the realisation keeps the reverse arrow's invariant (`ret_unitWD`).
-/

namespace V12M

namespace BArrow

variable [ModalSys] {σ : Signature} [ModalSys.NoFour]

/-! ## The invariant -/

/-- A doubly witnessed body's context: the reverse arrow's committed roots seen along the target's
    witness `e`, with the bound object of shape `□(roots) × ◇X`. -/
abbrev bodyCtxWD (cls clt : List VarType) (e : VarSymb) (X : VarType) : Ctx :=
  ((ctxOf clt).diaIn e).insert (.bnd 0) (RShape.wit (.box (bcT cls)) X).ty

/-- ⭐A doubly witnessed body read at the source: its items go along the reverse arrow (`imgt`),
    `e`'s content to `cxv`, and its bound object to the pair of the committed roots' necessary
    object and the source's witness `x`. -/
noncomputable def liftBodyWD {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) {e : VarSymb} {E : VarType}
    (he : (ctxOf clt).ref e = some (.VTypeDia E)) {cxv : ℕ}
    (hcxv : (ctxOf lv).ref (.root (.free cxv)) = some E) (Φ : WFF σ (bodyCtxWD cls clt e X) 1) :
    WFF σ (ctxOf lv) 0 :=
  WFF.subst (Subst.setIdx (arrowXIdx imgt e cxv) (.bnd 0) (liftEntryW hs hx))
    ((arrowXS σ (ctxOf lv) imgt e cxv).set (.bnd 0) (liftEntryW hs hx))
    (Subst.ok_set (ok_arrowXS himgt he hcxv) rfl)
    (Subst.coh_set (ok_arrowXS himgt he hcxv) (coh_arrowXS himgt he hcxv)
      ((Ctx.NoSlots.slots (Γ := (ctxOf clt).diaIn e)).rootFresh (le_refl 0)) rfl)
    ((Ctx.NoSlots.slots (Γ := (ctxOf clt).diaIn e)).insert _) Ctx.NoSlots.slots Φ

/-- ⭐**The invariant of a doubly witnessed arrow** `v → w` (docs §11.20): the source's witness `x`
    (among its committed roots `cls`) has content `cxw` at the target, and the way back lies in the
    extent of the target's witness `e` (among the reverse arrow's roots `clt`), with content `cxv`
    at the source.  Every body the source makes true, read there, is at the target the fourth
    returning form `◇_e[d ↦ ā'; e' ⇝ cxw]`. -/
def RetInvWD (hS : ModalSys.BStrong = true) (tv tw : NodeSt σ) (cls : List VarType)
    (imgs : ℕ → ℕ) (clt : List VarType) (imgt : ℕ → ℕ) (x : VarSymb) (X : VarType) (cxw : ℕ)
    (e : VarSymb) (E : VarType) (cxv : ℕ) : Prop :=
  ∃ (hs : cls <:+ tv.l) (himgs : ImgOk cls (ctxOf tw.l) imgs) (ht : clt <:+ tw.l)
    (himgt : ImgOk clt (ctxOf tv.l) imgt) (hx : (ctxOf cls).ref x = some (.VTypeDia X))
    (hcxw : (ctxOf tw.l).ref (.root (.free cxw)) = some X)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf tv.l).ref (.root (.free cxv)) = some E),
    ∀ Φ : WFF σ (bodyCtxWD cls clt e X) 1, liftBodyWD hs himgt hx he hcxv Φ ∈ tv.M →
      WFF.retxS hS e ⟨E, (ctxOf_le_of_suffix ht).ref he⟩ (.wit (.box (bcT cls)) X)
        (Term.pair (tupImgT cls imgs himgs).2 (Term.eta (.root (.free cxw)) X hcxw))
        (WFF.mono (((ctxOf_le_of_suffix ht).diaIn e).insert (.bnd 0) _) Φ) ∈ tw.M

/-- A non-slot variable of a doubly witnessed body's context is an item, or `e`'s content. -/
theorem bodyWD_item {cl clt : List VarType} {e : VarSymb} {X : VarType} {v : VarSymb}
    {U : VarType} (hv : bodyCtxWD cl clt e X v = some U) (hvr : v ≠ .root (.bnd 0)) :
    (∃ u, v = .step u .box ∧ (ctxOf clt).ref u = some (.VTypeBox U)) ∨
      (v = .step e .dia ∧ (ctxOf clt).ref e = some (.VTypeDia U)) := by
  change (if v = VarSymb.root (.bnd 0) then _ else ((ctxOf clt).diaIn e) v) = _ at hv
  rw [if_neg hvr] at hv
  exact diaIn_item hv

/-- ⭐A body packed along `e`, read at the reverse arrow's images, `cxv` and the pair of the
    committed roots' necessary object and `x`: the body read at the source. -/
theorem holeRead_tupImgT_pack2WD {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) {e : VarSymb} {E : VarType}
    (he : (ctxOf clt).ref e = some (.VTypeDia E)) {cxv : ℕ}
    (hcxv : (ctxOf lv).ref (.root (.free cxv)) = some E) (Φ : WFF σ (bodyCtxWD cls clt e X) 1) :
    WFF.holeRead (Term.pair (Term.pair (tupImgT clt imgt himgt).2
        (Term.eta (.root (.free cxv)) E hcxv))
        (Term.pair (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2))
          (Term.eta x (.VTypeDia X) ((ctxOf_le_of_suffix hs).ref hx))))
      (pack2X _ he Φ) = liftBodyWD hs himgt hx he hcxv Φ :=
  holeRead_tupImgT_pack2X himgt he hcxv _ Φ

/-! ## Transfer back along the arrow -/

/-- A doubly witnessed body that does not use the bound object, read at the source: the reverse
    arrow's reading along `e`. -/
theorem liftBodyWD_slotUp {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) {e : VarSymb} {E : VarType}
    (he : (ctxOf clt).ref e = some (.VTypeDia E)) {cxv : ℕ}
    (hcxv : (ctxOf lv).ref (.root (.free cxv)) = some E) (ψ : WFF σ ((ctxOf clt).diaIn e) 0) :
    liftBodyWD hs himgt hx he hcxv (WFF.slotUp Ctx.NoSlots.slots _ ψ) =
      WFF.subst (arrowXIdx imgt e cxv) (arrowXS σ (ctxOf lv) imgt e cxv)
        (ok_arrowXS himgt he hcxv) (coh_arrowXS himgt he hcxv) Ctx.NoSlots.slots
        Ctx.NoSlots.slots ψ := by
  unfold liftBodyWD
  refine (WFF.subst_slotUp _ _ _ _ _ _).trans ?_
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) ψ
  have hvr : v ≠ .root (.bnd 0) := fun h => by
    subst h
    rw [(Ctx.NoSlots.slots (Γ := (ctxOf clt).diaIn e)).root] at hv
    cases hv
  rw [Subst.set_ne _ _ hvr]
  exact .refl _

/-- ⭐**The invariant gives `□_e` transfer back along the arrow.**  If `□_e ψ` held at the target
    but `ψ` failed at the source, then `¬ψ`, a body not using the bound object, would be
    `◇_e[…] ¬ψ` at the target — so `◇_e ¬ψ`. -/
theorem RetInvWD.transferX (hS : ModalSys.BStrong = true) {tv tw : NodeSt σ}
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cxw : ℕ}
    {e : VarSymb} {E : VarType} {cxv : ℕ} (hv : Theory.IsMCS tv.M) (hw : Theory.IsMCS tw.M)
    (h : RetInvWD hS tv tw cls imgs clt imgt x X cxw e E cxv) :
    ∃ (ht : clt <:+ tw.l) (himgt : ImgOk clt (ctxOf tv.l) imgt)
      (he : (ctxOf clt).ref e = some (.VTypeDia E))
      (hcxv : (ctxOf tv.l).ref (.root (.free cxv)) = some E),
      TransferX tw.M clt (ctxOf_le_of_suffix ht) he tv.M imgt himgt cxv hcxv := by
  obtain ⟨hs, _, ht, himgt, hx, _, he, hcxv, hinv⟩ := h
  refine ⟨ht, himgt, he, hcxv, fun ψ hψ => ?_⟩
  by_contra hn
  have hle := ctxOf_le_of_suffix ht
  have he' : ∃ Y, (ctxOf tw.l).ref e = some (.VTypeDia Y) := ⟨E, hle.ref he⟩
  have hret := hinv (WFF.slotUp Ctx.NoSlots.slots _ (WFF.neg ψ)) (by
    rw [liftBodyWD_slotUp]
    exact hv.neg_mem_iff.mpr hn)
  have hu := (ctxOf_fresh (l := tw.l) le_rfl).diaIn e
  have inner : Proof σ ((ctxOf tw.l).diaIn e)
      [WFF.ex (RShape.wit (.box (bcT cls)) X).ty (WFF.mono ((hle.diaIn e).insert (.bnd 0) _)
        (WFF.slotUp Ctx.NoSlots.slots _ (WFF.neg ψ)))]
      (WFF.neg (WFF.mono (hle.diaIn e) ψ)) := by
    refine Proof.ex_elim tw.l.length _ hu (φ := WFF.openFree tw.l.length hu Ctx.NoSlots.slots _)
      (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
        (Proof.lookup List.mem_cons_self)) (Proof.conv ?_ (Proof.lookup List.mem_cons_self))
    rw [WFF.openFree_mono_slotUp]
    rfl
  have hdia : WFF.dia e he' (WFF.neg (WFF.mono (hle.diaIn e) ψ)) ∈ tw.M :=
    hw.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hret,
      ⟨Proof.imp_elim (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil)
        (Proof.imp_intro (Proof.K_dia (Δ₁ := []) (Δ₂ := []) e he' inner)))
        (Proof.ret_diaS hS (.pos e he') _ _ (Proof.lookup List.mem_cons_self))⟩⟩
  exact hw.neg_mem_iff.mp hψ hdia

/-- A witness transfer gives plain necessity transfer: `□ψ` gives `□_x ψ` (`Proof.box_boxx`), and
    on the `□` view the witness arrow is the plain one. -/
theorem TransferX.toTransfer {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)} (hM : Theory.IsMCS M)
    {ls : List VarType} {hle : (ctxOf ls).Le Γ} {x : VarSymb} {X : VarType}
    {hx : (ctxOf ls).ref x = some (.VTypeDia X)} {Δ : Ctx} [Δ.NoSlots] {N : Set (WFF σ Δ 0)}
    {img : ℕ → ℕ} {himg : ImgOk ls Δ img} {cx : ℕ} {hcx : Δ.ref (.root (.free cx)) = some X}
    (htr : TransferX M ls hle hx N img himg cx hcx) : Transfer M ls hle N img himg := by
  intro ψ hψ
  have hb : WFF.mono hle (WFF.boxx x ⟨X, hx⟩ (WFF.mono (Ctx.le_boxIn_diaIn _ x) ψ)) ∈ M := by
    refine hM.closed ⟨[WFF.mono hle (.box ψ)], fun y hy => by
      rw [List.mem_singleton.mp hy]; exact hψ, ?_⟩
    have h := Proof.box_boxx (Γ := Γ) (x := x) ⟨X, hle.ref hx⟩ (WFF.mono hle.boxIn ψ)
    refine ⟨Proof.conv ?_ (Proof.castHyps (by simp only [WFF.mono]) h)⟩
    simp only [WFF.boxx, WFF.neg, WFF.mono, WFF.mono_mono]
  have h := htr _ hb
  rw [WFF.subst_mono _ _ _ _ Ctx.NoSlots.slots] at h
  have hsim : Subst.Sim (ctxOf ls).boxIn (arrowXS σ Δ img x cx) (arrowS σ Δ img) :=
    Subst.sim_of fun v T _ hv => by
      obtain ⟨u, rfl, _⟩ := boxIn_item hv
      exact .refl _
  rwa [WFF.subst_congr _ _ _ (ok_arrowS himg) _ (coh_arrowS himg) _ _ hsim ψ] at h

/-- The invariant gives plain necessity transfer back along the arrow. -/
theorem RetInvWD.transfer (hS : ModalSys.BStrong = true) {tv tw : NodeSt σ}
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cxw : ℕ}
    {e : VarSymb} {E : VarType} {cxv : ℕ} (hv : Theory.IsMCS tv.M) (hw : Theory.IsMCS tw.M)
    (h : RetInvWD hS tv tw cls imgs clt imgt x X cxw e E cxv) :
    ∃ (ht : clt <:+ tw.l) (himgt : ImgOk clt (ctxOf tv.l) imgt),
      Transfer tw.M clt (ctxOf_le_of_suffix ht) tv.M imgt himgt := by
  obtain ⟨ht, himgt, he, hcxv, htr⟩ := RetInvWD.transferX hS hv hw h
  have htr' : TransferX tw.M clt (ctxOf_le_of_suffix ht) he tv.M imgt himgt cxv hcxv := htr
  exact ⟨ht, himgt, TransferX.toTransfer hw htr'⟩

/-! ## Growth -/

/-- A growing target keeps the invariant. -/
theorem RetInvWD.grow_tgt {hS : ModalSys.BStrong = true} {tv tw tw' : NodeSt σ}
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cxw : ℕ}
    {e : VarSymb} {E : VarType} {cxv : ℕ}
    (h : RetInvWD hS tv tw cls imgs clt imgt x X cxw e E cxv) (hg : Grows tw tw') :
    RetInvWD hS tv tw' cls imgs clt imgt x X cxw e E cxv := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcxw, he, hcxv, hinv⟩ := h
  have hle := ctxOf_le_of_suffix hg.suf
  refine ⟨hs, himgs.mono hle, ht.trans hg.suf, himgt, hx, hle.ref hcxw, he, hcxv,
    fun Φ hΦ => ?_⟩
  have h' := hg.sub _ (hinv Φ hΦ)
  change WFF.retxS hS e _ (.wit _ _) (Term.pair (Term.mono hle _) (Term.mono hle _))
    (WFF.mono _ (WFF.mono _ Φ)) ∈ tw'.M at h'
  rw [WFF.mono_mono, WFF.retxS_congr hS e _ (.wit _ _) (sig_pair
    (tupImgT_mono hle cls imgs himgs) (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _))) rfl] at h'
  exact h'

/-- A doubly witnessed body read in a larger source is the weakening of its reading. -/
theorem liftBodyWD_mono {lv lv' cls clt : List VarType} (hs : cls <:+ lv) (hl : lv <:+ lv')
    {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) {e : VarSymb} {E : VarType}
    (he : (ctxOf clt).ref e = some (.VTypeDia E)) {cxv : ℕ}
    (hcxv : (ctxOf lv).ref (.root (.free cxv)) = some E) (Φ : WFF σ (bodyCtxWD cls clt e X) 1) :
    WFF.mono (ctxOf_le_of_suffix hl) (liftBodyWD hs himgt hx he hcxv Φ) =
      liftBodyWD (hs.trans hl) (himgt.mono (ctxOf_le_of_suffix hl)) hx he
        ((ctxOf_le_of_suffix hl).ref hcxv) Φ := by
  unfold liftBodyWD
  rw [WFF.mono_subst _ _ _ _ _ _ Ctx.NoSlots.slots]
  have heq : ((arrowXS σ (ctxOf lv) imgt e cxv).set (.bnd 0) (liftEntryW hs hx)).mono
      (ctxOf_le_of_suffix hl) =
        (arrowXS σ (ctxOf lv') imgt e cxv).set (.bnd 0) (liftEntryW (hs.trans hl) hx) := by
    funext v
    change SubE.mono _ (Subst.set _ _ _ v) = Subst.set _ _ _ v
    by_cases hv : v = .root (.bnd 0)
    · subst hv
      rw [Subst.set_root, Subst.set_root]
      change SubE.tm (Term.pair (Term.boxtm (Term.mono _ (Term.mono _ _)))
        (Term.mono _ (Term.eta _ _ _))) = _
      rw [Term.mono_mono, Term.mono_eta]
    · rw [Subst.set_ne _ _ hv, Subst.set_ne _ _ hv]
      match v with
      | .step u .box => rfl
      | .root _ => rfl
      | .step _ .fst => rfl
      | .step _ .snd => rfl
      | .step u .dia =>
          change SubE.mono _ (if u = e then _ else _) = if u = e then _ else _
          split <;> rfl
      | .step _ .here => rfl
      | .step _ .keep => rfl
  exact WFF.subst_congr _ _ _ _ _ _ _ _
    (Subst.sim_of fun v U _ _ => by rw [congrFun heq v]; exact .refl _) Φ

/-- A source growing conservatively keeps the invariant. -/
theorem RetInvWD.grow_src {hS : ModalSys.BStrong = true} {tv tv' tw : NodeSt σ}
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cxw : ℕ}
    {e : VarSymb} {E : VarType} {cxv : ℕ} (hv : Theory.IsMCS tv.M) (hv' : Theory.IsMCS tv'.M)
    (h : RetInvWD hS tv tw cls imgs clt imgt x X cxw e E cxv) (hg : Grows tv tv') :
    RetInvWD hS tv' tw cls imgs clt imgt x X cxw e E cxv := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcxw, he, hcxv, hinv⟩ := h
  have hle := ctxOf_le_of_suffix hg.suf
  refine ⟨hs.trans hg.suf, himgs, ht, himgt.mono hle, hx, hcxw, he, hle.ref hcxv,
    fun Φ hΦ => hinv Φ ?_⟩
  refine mem_of_mono_mem hle hv hv' hg.sub ?_
  rw [liftBodyWD_mono hs hg.suf himgt hx he hcxv Φ]
  exact hΦ

/-! ## The source's `∃`-introduction for a new root -/

section NewRootWD

variable {lv cls clt : List VarType} {A : VarType} {x : VarSymb} {X : VarType} {e : VarSymb}
  {E : VarType} {cxv : ℕ}

/-- The middle substitution: the reverse arrow along `e`, weakened past the `∃`'s slot, with the
    body's slot set to `midTermW`. -/
abbrev midSWD (hs : cls <:+ lv) (hx : (ctxOf cls).ref x = some (.VTypeDia X)) (A : VarType)
    (imgt : ℕ → ℕ) (e : VarSymb) (cxv : ℕ) :
    Subst σ ((ctxOf lv).insert (.bnd 0) (.VTypeBox A.bc)) :=
  ((arrowXS σ (ctxOf lv) imgt e cxv).mono
    (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf lv)).root _)).set (.bnd 0)
    (.tm (midTermW hs hx A).2)

theorem ok_midSWD (hs : cls <:+ lv) (hx : (ctxOf cls).ref x = some (.VTypeDia X)) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf lv).ref (.root (.free cxv)) = some E) :
    Subst.Ok (bodyCtxWD (A :: cls) clt e X) (midSWD (σ := σ) hs hx A imgt e cxv) :=
  Subst.ok_set (Subst.ok_mono (ok_arrowXS himgt he hcxv) _) rfl

theorem coh_midSWD (hs : cls <:+ lv) (hx : (ctxOf cls).ref x = some (.VTypeDia X))
    {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf lv).ref (.root (.free cxv)) = some E) :
    Subst.Coh (Subst.setIdx (arrowXIdx imgt e cxv) (.bnd 0) (.tm (midTermW (σ := σ) hs hx A).2))
      (bodyCtxWD (A :: cls) clt e X) (midSWD (σ := σ) hs hx A imgt e cxv) :=
  Subst.coh_set (Subst.ok_mono (ok_arrowXS himgt he hcxv) _)
    (Subst.coh_mono (coh_arrowXS himgt he hcxv) _)
    ((Ctx.NoSlots.slots (Γ := (ctxOf clt).diaIn e)).rootFresh (le_refl 0)) rfl

/-- ⭐**A new root's doubly witnessed body is an `∃`-introduction of the older roots' one**, at the
    source: `liftBodyW_ex_pairUpS_mem` along `e`. -/
theorem liftBodyWD_ex_pairUpS_mem {M : Set (WFF σ (ctxOf lv) 0)} (hM : Theory.IsMCS M)
    (hs' : (A :: cls) <:+ lv) {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt)
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf lv).ref (.root (.free cxv)) = some E)
    (Φ : WFF σ (bodyCtxWD (A :: cls) clt e X) 1)
    (h : liftBodyWD hs' himgt (ref_old_of_ref hx) he hcxv Φ ∈ M) :
    liftBodyWD ((List.suffix_cons A cls).trans hs') himgt hx he hcxv
      (WFF.ex (.VTypeBox A.bc)
        (WFF.pairUpS (.wit (.box (bcT cls)) X) A.bc (packW (bcT cls) A.bc X).2 Φ)) ∈ M := by
  have hs : cls <:+ lv := (List.suffix_cons A cls).trans hs'
  refine hM.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact h, ⟨?_⟩⟩
  refine Proof.ex_intro _ (newItem hs') (Proof.conv ?_ (Proof.lookup List.mem_cons_self))
  refine Eq.symm ?_
  unfold WFF.instantiate WFF.substRoot WFF.pairUpS liftBodyWD
  have hfr : (ctxOf lv) (.root (.bnd 0)) = none := (Ctx.NoSlots.slots (Γ := ctxOf lv)).root
  rw [WFF.subst_comp _ _ (midSWD hs hx A imgt e cxv) _ _ _ _ (ok_midSWD hs hx himgt he hcxv)
    (coh_midSWD hs hx himgt he hcxv) _ _ _ ?simA]
  case simA =>
    refine Subst.sim_of fun v U hlp hv => ?_
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      obtain rfl : U = (RShape.wit (.box (bcT (A :: cls))) X).ty := by
        change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
        rw [if_pos rfl] at hv
        exact (Option.some.inj hv).symm
      dsimp only [Subst.comp]
      rw [show midSWD (σ := σ) hs hx A imgt e cxv (.root (.bnd 0)) =
        .tm (midTermW hs hx A).2 from Subst.set_root _ _ _, Subst.set_root]
      dsimp only [SubE.comp]
      have h0 : (((arrowXS σ (ctxOf lv) imgt e cxv).set (.bnd 0) (liftEntryW hs hx)).under
          (0 + 1) 0 (.VTypeBox A.bc) hfr).at (.root (.bnd 0)) =
          .tm (Term.mono (Ctx.le_insert hfr _)
            (Term.pair (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2))
              (Term.eta x (.VTypeDia X) ((ctxOf_le_of_suffix hs).ref hx)))) := by
        rw [Subst.at_under_ne _ _ _ (fun h => by cases h)]
        change SubE.mono _ (Subst.set _ _ _ (.root (.bnd 0))) = _
        rw [Subst.set_root]
        rfl
      refine SubE.sim_tm_sigma (Eq.symm ((Term.subst_holeAt_sig _ _ _ _ _).trans ?_))
      refine Term.holeAt_congr_sig (sig_pair (sig_pair
        (Term.subst_eta_tm _ _ _ _ _ _ _ (by rw [Subst.at_proj _ _ rfl, h0]; rfl))
        (Term.subst_eta_renAt _ _ _ _ _ _ _ (Ctx.ref_insert_root _ (.bnd 0) _)
          (Subst.under_at_slot _ (0 + 1) 0 _ hfr)))
        (Term.subst_eta_tm _ _ _ _ _ _ _ (by rw [Subst.at_proj _ _ rfl, h0]; rfl))) _
    · dsimp only [Subst.comp]
      rw [show midSWD (σ := σ) hs hx A imgt e cxv v =
        SubE.mono _ (arrowXS σ (ctxOf lv) imgt e cxv v) from Subst.set_ne _ _ hvr,
        Subst.set_ne _ _ hvr]
      dsimp only [Subst.idS, SubE.comp]
      rw [Subst.at_nonproj _ hlp]
      dsimp only [Subst.under]
      have hv1 : v ≠ .root (.bnd (0 + 1)) := by
        rcases bodyWD_item hv hvr with ⟨u, rfl, _⟩ | ⟨rfl, _⟩ <;> exact fun h => by cases h
      rw [if_neg hv1, Subst.set_ne _ _ hvr]
      exact .refl _
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v U hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : U = (RShape.wit (.box (bcT (A :: cls))) X).ty := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp]
    rw [show midSWD (σ := σ) hs hx A imgt e cxv (.root (.bnd 0)) =
      .tm (midTermW hs hx A).2 from Subst.set_root _ _ _, Subst.set_root]
    dsimp only [SubE.comp, liftEntryW]
    have hsg : (Subst.single (σ := σ) (.bnd 0) (.tm (newItem hs'))).at (.root (.bnd 0)) =
        .tm (newItem hs') := by
      change Subst.single (.bnd 0) _ (.root (.bnd 0)) = _
      exact if_pos rfl
    refine SubE.sim_tm_sigma (Eq.symm ((Term.subst_holeAt_sig _ _ _ _ _).trans ?_))
    refine (Term.holeAt_congr_sig (sig_pair (sig_pair (Term.subst_single_mono_sig _ _)
      (Term.subst_eta_tm _ _ _ _ _ _ _ hsg)) (Term.subst_single_mono_sig _ _)) _).trans ?_
    refine (ShapeMap.liftObj_pack_wit _ _ _).trans ?_
    refine congrArg (Sigma.mk _) ?_
    change Term.pair (Term.boxtm (Term.pair _ _)) _ =
      Term.pair (Term.boxtm (Term.pair (Term.mono _ (Term.mono _ _)) (Term.mono _ _))) _
    rw [Term.mono_mono]
  · dsimp only [Subst.comp]
    rw [show midSWD (σ := σ) hs hx A imgt e cxv v =
      SubE.mono _ (arrowXS σ (ctxOf lv) imgt e cxv v) from Subst.set_ne _ _ hvr,
      Subst.set_ne _ _ hvr]
    rcases bodyWD_item hv hvr with ⟨u, rfl, hu⟩ | ⟨rfl, _⟩
    · obtain ⟨r, hr, _, _⟩ := ref_rt hu
      change SubE.Sim U (.ren (itemImg imgt u)) ((Subst.single _ _).at (itemImg imgt u))
      rw [Subst.single_at_ne (by rw [itemAt_rt, hr]; exact fun h => by cases h)]
      exact .refl _
    · rw [show arrowXS σ (ctxOf lv) imgt e cxv (e.step Step.dia) = .ren (.root (.free cxv)) from
        if_pos rfl]
      change SubE.Sim U (.ren (.root (.free cxv))) ((Subst.single _ _).at (.root (.free cxv)))
      rw [Subst.single_at_ne (fun h => by cases h)]
      exact .refl _

end NewRootWD

/-! ## Realising the source's next root along a doubly witnessed arrow -/

section StepWD

variable (hS : ModalSys.BStrong = true) {ts tt : NodeSt σ} {cl clt : List VarType}
  {img imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cxw : ℕ} {e : VarSymb} {E : VarType}
  {cxv : ℕ}

/-- The returning possibility along `e` a body over the source's roots with the next one becomes
    in the grown target: valued at the images, the fresh variable, and `cxw`. -/
def retAtomWD (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hcxw : (ctxOf tt.l).ref (.root (.free cxw)) = some X)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (Φ : WFF σ (bodyCtxWD (nextTy ts.l cl :: cl) clt e X) 1) :
    WFF σ (ctxOf ((nextTy ts.l cl).bc :: tt.l)) 0 :=
  WFF.retxS hS e ⟨E, (ctxOf_le_of_suffix (ht.trans (List.suffix_cons _ _))).ref he⟩
    (.wit (.box (bcT (nextTy ts.l cl :: cl))) X)
    (Term.pair
      (tupImgT (nextTy ts.l cl :: cl) (extImg img cl.length tt.l.length) (imgOk_ext himg)).2
      (Term.eta (.root (.free cxw)) X ((ctxOf_le_append [(nextTy ts.l cl).bc] tt.l).ref hcxw)))
    (WFF.mono (((ctxOf_le_of_suffix (ht.trans (List.suffix_cons _ _))).diaIn e).insert
      (.bnd 0) _) Φ)

/-- What the target gains when the source's next root is committed along a doubly witnessed
    arrow. -/
def retSetWD (hs' : (nextTy ts.l cl :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcxw : (ctxOf tt.l).ref (.root (.free cxw)) = some X)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf ts.l).ref (.root (.free cxv)) = some E) :
    Set (WFF σ (ctxOf ((nextTy ts.l cl).bc :: tt.l)) 0) :=
  {φ | ∃ Φ, liftBodyWD hs' himgt (ref_old_of_ref hx) he hcxv Φ ∈ ts.M ∧
    φ = retAtomWD hS himg ht hcxw he Φ}

/-- Finitely many of the gained atoms reduce to one, at the conjunction of their bodies. -/
theorem ret_listWD (hs' : (nextTy ts.l cl :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcxw : (ctxOf tt.l).ref (.root (.free cxw)) = some X)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf ts.l).ref (.root (.free cxv)) = some E) (hv : Theory.IsMCS ts.M)
    (S : Set (WFF σ (ctxOf ((nextTy ts.l cl).bc :: tt.l)) 0)) :
    ∀ L : List (WFF σ (ctxOf ((nextTy ts.l cl).bc :: tt.l)) 0),
      (∀ δ ∈ L, δ ∈ S ∨ δ ∈ retSetWD hS hs' himgt himg ht hx hcxw he hcxv) →
      ∃ Φ, liftBodyWD hs' himgt (ref_old_of_ref hx) he hcxv Φ ∈ ts.M ∧
        ∀ δ ∈ L, Theory.Derives (S ∪ {retAtomWD hS himg ht hcxw he Φ}) δ
  | [], _ => ⟨.top, hv.top_mem, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨Φ₀, hΦ₀, hL⟩ := ret_listWD hs' himgt himg ht hx hcxw he hcxv hv S L
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hu := ctxOf_fresh (l := (nextTy ts.l cl).bc :: tt.l) le_rfl
      rcases h δ List.mem_cons_self with hS' | ⟨Φ₁, hΦ₁, rfl⟩
      · refine ⟨Φ₀, hΦ₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact Theory.Derives.of_mem (Or.inl hS')
        · exact hL d hd
      · have hand : ∀ Φ', Proof σ _ [retAtomWD hS himg ht hcxw he (Φ₀.and Φ₁)]
              (retAtomWD hS himg ht hcxw he Φ') →
            Theory.Derives (S ∪ {retAtomWD hS himg ht hcxw he (Φ₀.and Φ₁)})
              (retAtomWD hS himg ht hcxw he Φ') :=
          fun Φ' p => ⟨[_], fun x hx => by
            rw [List.mem_singleton.mp hx]; exact Or.inr rfl, ⟨p⟩⟩
        have h₀ := hand Φ₀ (Proof.ret_monoS hS (.pos e _) _ _ _
          (Proof.lookup List.mem_cons_self) (Proof.boxx_all_and_left _ _ _ hu))
        have h₁ := hand Φ₁ (Proof.ret_monoS hS (.pos e _) _ _ _
          (Proof.lookup List.mem_cons_self) (Proof.boxx_all_and_right _ _ _ hu))
        refine ⟨Φ₀.and Φ₁, hv.closed ⟨[_, _], fun x hx => ?_,
          ⟨Proof.and_intro (Proof.lookup List.mem_cons_self)
            (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩, fun d hd => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hΦ₀
          · rw [List.mem_singleton.mp hx]; exact hΦ₁
        rcases List.mem_cons.mp hd with rfl | hd
        · exact h₁
        · refine Derives.trans (fun x hx => ?_) (hL d hd)
          rcases hx with hx | hx
          · exact Theory.Derives.of_mem (Or.inl hx)
          · rw [Set.mem_singleton_iff.mp hx]; exact h₀

/-- ⭐**The gained atoms are consistent with the target**: as `retSetW_consistent`, along `e`:
    `ret_extS` names the companion and `ret_map` along `pack` turns the result into the atom. -/
theorem retSetWD_consistent (hs' : (nextTy ts.l cl :: cl) <:+ ts.l)
    (himgt : ImgOk clt (ctxOf ts.l) imgt) (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcxw : (ctxOf tt.l).ref (.root (.free cxw)) = some X)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf ts.l).ref (.root (.free cxv)) = some E)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : ∀ Φ : WFF σ (bodyCtxWD cl clt e X) 1,
      liftBodyWD ((List.suffix_cons _ _).trans hs') himgt hx he hcxv Φ ∈ ts.M →
        WFF.retxS hS e ⟨E, (ctxOf_le_of_suffix ht).ref he⟩ (.wit (.box (bcT cl)) X)
          (Term.pair (tupImgT cl img himg).2 (Term.eta (.root (.free cxw)) X hcxw))
          (WFF.mono (((ctxOf_le_of_suffix ht).diaIn e).insert (.bnd 0) _) Φ) ∈ tt.M) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l) '' tt.M ∪
      retSetWD hS hs' himgt himg ht hx hcxw he hcxv) := by
  rintro ⟨L, hL, p⟩
  obtain ⟨Φ, hΦ, hder⟩ := ret_listWD hS hs' himgt himg ht hx hcxw he hcxv hv _ L hL
  have h₁ := hinv _ (liftBodyWD_ex_pairUpS_mem hv hs' himgt hx he hcxv Φ hΦ)
  have hu := ctxOf_fresh (l := tt.l) le_rfl
  have hle := ctxOf_le_of_suffix ht
  obtain ⟨Δ, hΔ, hq⟩ : Theory.Derives (WFF.mono (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l) ''
      tt.M ∪ {retAtomWD hS himg ht hcxw he Φ}) .bot :=
    Derives.trans (fun y hy => hder y hy) ⟨L, fun y hy => hy, p⟩
  obtain ⟨Δ₀, h₀, h₁'⟩ := exists_hyps_cons_map (P := fun y => y ∈ tt.M)
    (fun y => WFF.mono (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l) y)
    (retAtomWD hS himg ht hcxw he Φ) Δ
    (fun δ hδ => by
      rcases hΔ δ hδ with ⟨y, hy, rfl⟩ | h
      · exact Or.inr ⟨y, hy, rfl⟩
      · exact Or.inl (Set.mem_singleton_iff.mp h))
  obtain ⟨q'⟩ := Provable.mono h₁' hq
  obtain ⟨Δ₁, hΔ₁, ⟨pex⟩⟩ := Theory.Derives.of_mem (S := tt.M) h₁
  refine hw.1 ⟨Δ₁ ++ Δ₀, fun y hy => (List.mem_append.mp hy).elim (hΔ₁ y) (h₀ y), ⟨?_⟩⟩
  refine Proof.ret_extS hS (.pos e ⟨E, hle.ref he⟩) (S := .wit (.box (bcT cl)) X) _
    (WFF.mono (((hle.diaIn e).insert (.bnd 0) _).insert (.bnd 1) _)
      (WFF.pairUpS (.wit (.box (bcT cl)) X) (nextTy ts.l cl).bc
        (packW (bcT cl) (nextTy ts.l cl).bc X).2 Φ))
    tt.l.length hu (φ := .bot) (Proof.ofSubset (fun y hy => List.mem_append_left _ hy) pex) ?_
  refine Proof.imp_elim (Proof.ofSubset (fun y hy => ?_) (Proof.imp_intro q')) ?_
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_append_right _ hz))
  refine Proof.conv ?_ (Proof.ret_map hS (.pos e _)
    (S := .wit (.prod (.box (bcT cl)) (.box (nextTy ts.l cl).bc)) X)
    (.pack (bcT cl) (nextTy ts.l cl).bc) _
    (WFF.mono (((ctxOf_le_of_suffix (ht.trans (List.suffix_cons _ _))).diaIn e).insert
      (.bnd 0) _) Φ)
    (Proof.conv (OutLeg.retS_congr' hS _ _ rfl ?_) (Proof.lookup List.mem_cons_self)))
  · refine WFF.retxS_congr hS e _ _ ?_ rfl
    rw [Term.holeRead_eq_holeAt]
    refine (Term.holeAt_congr_sig (RShape.extTm_wit _ _ _) _).trans
      ((ShapeMap.liftVal_pack_wit _ _).trans
        (sig_pair (tupImgT_ext himg (imgOk_ext himg)).symm ?_))
    exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)
  · dsimp only [OutLeg.view]
    rw [WFF.bodySplit_mono_pairUpS (hle.diaIn e),
      WFF.mono_bodyRepl ((Ctx.le_insert hu.root _).diaIn e), Term.mono_mono, WFF.mono_mono]

/-- The target grown by the image of the source's next root, along a doubly witnessed arrow. -/
noncomputable def retStepWD (hs' : (nextTy ts.l cl :: cl) <:+ ts.l)
    (himgt : ImgOk clt (ctxOf ts.l) imgt) (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcxw : (ctxOf tt.l).ref (.root (.free cxw)) = some X)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf ts.l).ref (.root (.free cxv)) = some E) : NodeSt σ :=
  ⟨(nextTy ts.l cl).bc :: tt.l, complete (WFF.mono (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l) ''
    tt.M ∪ retSetWD hS hs' himgt himg ht hx hcxw he hcxv)⟩

/-- ⭐**One realisation step along a doubly witnessed arrow**: when the invariant holds, the grown
    target is maximal consistent, extends the old one, and the invariant holds for one more
    root. -/
theorem retStepWD_ok (hs' : (nextTy ts.l cl :: cl) <:+ ts.l)
    (himgt : ImgOk clt (ctxOf ts.l) imgt) (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcxw : (ctxOf tt.l).ref (.root (.free cxw)) = some X)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf ts.l).ref (.root (.free cxv)) = some E)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : RetInvWD hS ts tt cl img clt imgt x X cxw e E cxv) :
    Theory.IsMCS (retStepWD hS hs' himgt himg ht hx hcxw he hcxv).M ∧
      Grows tt (retStepWD hS hs' himgt himg ht hx hcxw he hcxv) ∧
      RetInvWD hS ts (retStepWD hS hs' himgt himg ht hx hcxw he hcxv) (nextTy ts.l cl :: cl)
        (extImg img cl.length tt.l.length) clt imgt x X cxw e E cxv := by
  obtain ⟨_, _, _, _, _, _, _, _, h⟩ := hinv
  have hcons := retSetWD_consistent hS hs' himgt himg ht hx hcxw he hcxv hv hw h
  obtain ⟨hsub, hmcs⟩ := complete_spec hcons
  refine ⟨hmcs, ⟨⟨[_], rfl⟩, fun φ hφ => hsub (Or.inl ⟨φ, hφ, rfl⟩)⟩,
    hs', imgOk_ext himg, ht.trans (List.suffix_cons _ _), himgt, ref_old_of_ref hx,
    (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l).ref hcxw, he, hcxv, fun Φ hΦ => ?_⟩
  exact hsub (Or.inr ⟨Φ, hΦ, rfl⟩)

end StepWD

/-! ## Cross-arrow preservation -/

omit [ModalSys.NoFour] in
/-- Weakening the doubly witnessed unit's conjunct weakens its terms. -/
theorem WFF.mono_unitBodyWD {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ')
    (hS : ModalSys.BStrong = true) {x : VarSymb} {C Xe A X : VarType} {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X} (u : Term σ (Γ.diaIn x) X b₀)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd C Xe) (RShape.wit (.box A) X).ty)) 1) :
    WFF.mono ((h.diaIn x).insert (.bnd 0) (RShape.wit (.box C) Xe).ty)
        (WFF.unitBodyWD hS sb u θ) =
      WFF.unitBodyWD hS (Term.mono h.boxIn sb) (Term.mono (h.diaIn x) u) θ := by
  unfold WFF.unitBodyWD
  refine WFF.retxS_congr' hS _ _ _ ?_ ?_
  · change Term.pair (Term.mono _ (Term.mono _ sb)) (Term.mono _ (Term.mono _ u)) =
      Term.pair (Term.mono _ (Term.mono _ sb)) (Term.mono _ (Term.mono _ u))
    simp only [Term.mono_mono]
  · rw [WFF.mono_holeAt _ _
      ((((Ctx.NoSlots.slots (Γ := Γ'.diaIn x)).insert _).diaIn _).insert _)]
    change WFF.holeAt _ (Term.pair (Term.pair (Term.mono _ (Term.eta _ _ _))
      (Term.mono _ (Term.eta _ _ _))) (Term.mono _ (Term.eta _ _ _))) θ = _
    rw [Term.mono_eta, Term.mono_eta, Term.mono_eta]

/-- ⭐The doubly witnessed unit's conjunct at the reverse arrow's items and `e`'s content, with a
    body packed along `x`, read at the source: the reverse arrow's returning possibility along `x`
    at the witnessed shape, valued at the reverse images and `cxv`. -/
theorem liftBodyWD_unitBodyWD {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) {e : VarSymb} {E : VarType}
    (he : (ctxOf clt).ref e = some (.VTypeDia E)) {cxv : ℕ}
    (hcxv : (ctxOf lv).ref (.root (.free cxv)) = some E) (hS : ModalSys.BStrong = true)
    (Φ : WFF σ (bodyCtxWD clt cls x E) 1) :
    liftBodyWD hs himgt hx he hcxv (WFF.unitBodyWD (Γ := ctxOf clt) hS (tupT clt).2
        (Term.eta (e.step .dia) E (Ctx.ref_diaIn_of he)) (pack2X _ hx Φ)) =
      WFF.retxS hS x ⟨X, (ctxOf_le_of_suffix hs).ref hx⟩ (.wit (.box (bcT clt)) E)
        (Term.pair (tupImgT clt imgt himgt).2 (Term.eta (.root (.free cxv)) E hcxv))
        (WFF.mono (((ctxOf_le_of_suffix hs).diaIn x).insert (.bnd 0) _) Φ) := by
  have hle := ctxOf_le_of_suffix hs
  have hu := Ctx.ref_insert_root ((ctxOf clt).diaIn e) (.bnd 0)
    (RShape.wit (.box (bcT cls)) X).ty
  have hsnd := Ctx.ref_snd_of hu
  have hθ : Subst.Ok (bodyCtxWD cls clt e X)
      ((arrowXS σ (ctxOf lv) imgt e cxv).set (.bnd 0) (liftEntryW hs hx)) :=
    Subst.ok_set (ok_arrowXS himgt he hcxv) rfl
  have hc : Subst.Coh (Subst.setIdx (arrowXIdx imgt e cxv) (.bnd 0) (liftEntryW hs hx))
      (bodyCtxWD cls clt e X) ((arrowXS σ (ctxOf lv) imgt e cxv).set (.bnd 0) (liftEntryW hs hx)) :=
    Subst.coh_set (ok_arrowXS himgt he hcxv) (coh_arrowXS himgt he hcxv)
      ((Ctx.NoSlots.slots (Γ := (ctxOf clt).diaIn e)).rootFresh (le_refl 0)) rfl
  have hw : (((arrowXS σ (ctxOf lv) imgt e cxv).set (.bnd 0) (liftEntryW hs hx)).at
      (.step (.root (.bnd 0)) .snd)).idxAlong [] = x := rfl
  have hfst : ((arrowXS σ (ctxOf lv) imgt e cxv).set (.bnd 0) (liftEntryW hs hx)).at
      (.step (.root (.bnd 0)) .fst) =
      .tm (Term.boxtm (Term.mono hle.boxIn (tupT cls).2)) := by
    rw [Subst.at_proj _ _ rfl]
    change (Subst.set _ _ _ (.root (.bnd 0))).proj .fst = _
    rw [Subst.set_root]
    rfl
  unfold liftBodyWD WFF.unitBodyWD
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ x rfl ⟨X, hle.ref hx⟩
    ((Ctx.NoSlots.slots (Γ := ctxOf lv)).diaIn x) (Subst.ok_dia hθ ⟨X, hsnd⟩ hw)
    (Subst.coh_dia hθ hc ⟨X, hsnd⟩)]
  refine WFF.retxS_congr hS _ _ _ (sig_pair ?_ ?_) ?_
  · rw [Term.subst_mono]
    refine (Term.subst_congr _ (arrowS σ (ctxOf lv) imgt) _ (ok_arrowS himgt) _
      (coh_arrowS himgt) ?_ _).trans (subst_arrow_tupT clt himgt)
    refine Subst.sim_of fun v T _ hv => ?_
    obtain ⟨u, rfl, _⟩ := boxIn_item hv
    rw [Subst.set_ne _ _ (fun h => by cases h)]
    exact .refl _
  · rw [Term.subst_mono]
    refine Term.subst_eta_renAt _ _ _ _ _ _ _ _ ?_
    rw [Subst.at_nonproj _ rfl, Subst.set_ne _ _ (fun h => by cases h)]
    exact if_pos rfl
  · rw [WFF.subst_holeAt]
    refine (WFF.holeAt_congr _ ?_ _).trans (holeAt_tupT_pack2X (hle.diaIn x) hx Φ)
    refine sig_pair (sig_pair ?_ ?_) ?_
    · refine (Term.subst_eta_tm _ _ _ _ _ _
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf lv).diaIn x)).root _)
          (Term.mono (Ctx.le_boxIn_diaIn _ x) (Term.mono hle.boxIn (tupT cls).2))) ?_).trans ?_
      · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
          Subst.dia_eq_box_mono (Δ₁ := ((ctxOf clt).diaIn e).insert (.bnd 0) _) _ _ x _ _
            (Ctx.ref_inner (Ctx.ref_fst_of hu)), Subst.box_at_inner_boxtm _ hfst]
        rfl
      · exact congrArg (Sigma.mk _) (by rw [Term.mono_mono, Term.mono_mono])
    · refine (Term.subst_eta_tm _ _ _ _ _ _
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf lv).diaIn x)).root _)
          (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of (hle.ref hx)))) ?_).trans ?_
      · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_nonproj _ rfl]
        dsimp only [Subst.dia]
        rw [if_pos rfl, Subst.at_proj _ _ rfl]
        change SubE.mono _ (SubE.diaBody x ((Subst.set _ _ _ (.root (.bnd 0))).proj .snd)) = _
        rw [Subst.set_root]
        change SubE.mono _ (SubE.diaBody x (SubE.tm (Term.diatm x _
          (Term.eta (x.step .dia) X _)))) = _
        rw [SubE.diaBody_diatm]
        rfl
      · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)
    · exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ (0 + 1) 0 _ _)

/-- ⭐**Cross-arrow preservation along a doubly witnessed arrow**: committing the source's next
    root keeps the reverse arrow's invariant, over the extended list.  Were the reverse returning
    possibility for `Φ` to fail at the source, its negation would be a forward body
    (`liftBodyWD_unitBodyWD`), so the grown target would have `◇_e[…] ¬U`; `Φ`, read there, is
    `θ(y, □sb, e)` (`holeRead_tupImgT_pack2WD`), and `ret_unitWD` gives `◇_e[…](¬U ∧ U)`, which is
    absurd (`Proof.retxS_absurd`). -/
theorem retStepWD_rev (hS : ModalSys.BStrong = true) {ts tt : NodeSt σ} {cl clt : List VarType}
    {img imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cxw : ℕ} {e : VarSymb} {E : VarType}
    {cxv : ℕ} (hs' : (nextTy ts.l cl :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcxw : (ctxOf tt.l).ref (.root (.free cxw)) = some X)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf ts.l).ref (.root (.free cxv)) = some E)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : RetInvWD hS ts tt cl img clt imgt x X cxw e E cxv) :
    RetInvWD hS (retStepWD hS hs' himgt himg ht hx hcxw he hcxv) ts clt imgt
      (nextTy ts.l cl :: cl) (extImg img cl.length tt.l.length) e E cxv x X cxw := by
  obtain ⟨_, _, _, _, _, _, _, _, h⟩ := hinv
  obtain ⟨hsub, hmcs⟩ :=
    complete_spec (retSetWD_consistent hS hs' himgt himg ht hx hcxw he hcxv hv hw h)
  have ht' : clt <:+ (nextTy ts.l cl).bc :: tt.l := ht.trans (List.suffix_cons _ _)
  have hle := ctxOf_le_of_suffix ht'
  have hx' : (ctxOf (nextTy ts.l cl :: cl)).ref x = some (.VTypeDia X) := ref_old_of_ref hx
  have hcxw' := (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l).ref hcxw
  have he'' : ∃ Y, (ctxOf ((nextTy ts.l cl).bc :: tt.l)).ref e = some (.VTypeDia Y) :=
    ⟨E, hle.ref he⟩
  refine ⟨ht', himgt, hs', imgOk_ext himg, he, hcxv, hx', hcxw', fun Φ hΦ => ?_⟩
  by_contra hn
  have hneg := hv.neg_mem_iff.mpr hn
  have hΨ : liftBodyWD hs' himgt hx' he hcxv (WFF.neg (WFF.unitBodyWD (Γ := ctxOf clt) hS
      (tupT clt).2 (Term.eta (e.step .dia) E (Ctx.ref_diaIn_of he)) (pack2X _ hx' Φ))) ∈
      ts.M := by
    change WFF.neg (liftBodyWD hs' himgt hx' he hcxv _) ∈ ts.M
    rw [liftBodyWD_unitBodyWD]
    exact hneg
  have hret := hsub (Or.inr ⟨_, hΨ, rfl⟩)
  have p₁ : Proof σ (ctxOf ((nextTy ts.l cl).bc :: tt.l))
      [retAtomWD hS himg ht hcxw he (WFF.neg (WFF.unitBodyWD (Γ := ctxOf clt) hS (tupT clt).2
        (Term.eta (e.step .dia) E (Ctx.ref_diaIn_of he)) (pack2X _ hx' Φ)))]
      (WFF.retxS hS e he'' (.wit (.box (bcT (nextTy ts.l cl :: cl))) X)
        (Term.pair (tupImgT (nextTy ts.l cl :: cl) (extImg img cl.length tt.l.length)
            (imgOk_ext himg)).2 (Term.eta (.root (.free cxw)) X hcxw'))
        (WFF.neg (WFF.unitBodyWD hS (Term.mono hle.boxIn (tupT clt).2)
          (Term.eta (e.step .dia) E (Ctx.ref_diaIn_of (hle.ref he))) (pack2X _ hx' Φ)))) := by
    refine Proof.conv ?_ (Proof.lookup List.mem_cons_self)
    unfold retAtomWD
    refine congrArg (WFF.retxS hS e _ _ _) ?_
    change WFF.imp (WFF.mono _ _) .bot = _
    rw [WFF.mono_unitBodyWD hle, Term.mono_eta]
  have p₂ : Proof σ (ctxOf ((nextTy ts.l cl).bc :: tt.l))
      [liftBodyWD ht' (imgOk_ext himg) he hx' hcxw' Φ]
      (WFF.holeRead (Term.pair (Term.pair (tupImgT (nextTy ts.l cl :: cl)
          (extImg img cl.length tt.l.length) (imgOk_ext himg)).2
          (Term.eta (.root (.free cxw)) X hcxw'))
        (Term.pair (Term.boxtm (Term.mono hle.boxIn (tupT clt).2))
          (Term.diatm e he'' (Term.eta (e.step .dia) E (Ctx.ref_diaIn_of (hle.ref he))))))
        (pack2X _ hx' Φ)) :=
    Proof.conv (holeRead_tupImgT_pack2WD ht' (imgOk_ext himg) he hx' hcxw' Φ).symm
      (Proof.lookup List.mem_cons_self)
  have p₃ : Proof σ (ctxOf ((nextTy ts.l cl).bc :: tt.l))
      [retAtomWD hS himg ht hcxw he (WFF.neg (WFF.unitBodyWD (Γ := ctxOf clt) hS (tupT clt).2
        (Term.eta (e.step .dia) E (Ctx.ref_diaIn_of he)) (pack2X _ hx' Φ))),
        liftBodyWD ht' (imgOk_ext himg) he hx' hcxw' Φ] .bot :=
    Proof.retxS_absurd hS he'' _ _ _ (ctxOf_fresh (l := (nextTy ts.l cl).bc :: tt.l) le_rfl)
      (Proof.ret_unitWD hS he'' _ _ _ _ _
        (Proof.ofSubset (fun y hy => by
          rw [List.mem_singleton.mp hy]; exact List.mem_cons_self) p₁)
        (Proof.ofSubset (fun y hy => by
          rw [List.mem_singleton.mp hy]; exact List.mem_cons_of_mem _ List.mem_cons_self) p₂))
  refine hmcs.1 ⟨_, fun y hy => ?_, ⟨p₃⟩⟩
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hret
  · rw [List.mem_singleton.mp hy]
    exact hΦ

end BArrow

end V12M
