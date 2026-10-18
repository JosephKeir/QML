import QML.QML_v12m_BPack
import QML.QML_v12m_BNetGrow
import QML.QML_v12m_BNetStep
import QML.QML_v12m_RetMono
import QML.QML_v12m_RetDerived

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

/-! ## The invariant -/

/-- A body's context: the reverse arrow's committed roots' `□` view, with the bound object. -/
abbrev bodyCtx (cls clt : List VarType) : Ctx :=
  (ctxOf clt).boxIn.insert (.bnd 0) (.VTypeBox (bcT cls))

/-- The bound object's entry: the necessary object holding the committed roots' items. -/
abbrev liftEntry {lv cls : List VarType} (hs : cls <:+ lv) : SubE σ (ctxOf lv) :=
  .tm (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2))

/-- ⭐A body read at the far end `v`, by one substitution: its `□` items go along the reverse
    arrow (`imgt`), its bound object to the necessary object holding the committed roots'
    items. -/
def liftBody {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) (Φ : WFF σ (bodyCtx cls clt) 1) : WFF σ (ctxOf lv) 0 :=
  WFF.subst (Subst.setIdx (arrowIdx imgt) (.bnd 0) (liftEntry hs))
    ((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntry hs))
    (Subst.ok_set (ok_arrowS himgt) rfl)
    (Subst.coh_set (ok_arrowS himgt) (coh_arrowS himgt)
      ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).rootFresh (le_refl 0)) rfl)
    ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).insert _) Ctx.NoSlots.slots Φ

/-- ⭐**The returning-possibility invariant** of an arrow `v → w` (docs §11.17): every body over
    the roots `cls` committed along it that `v` makes true when read there is a returning
    possibility at `w`, valued at the tuple of their images. -/
def RetInv (hS : ModalSys.BStrong = true) (tv tw : NodeSt σ) (cls : List VarType)
    (imgs : ℕ → ℕ) (clt : List VarType) (imgt : ℕ → ℕ) : Prop :=
  ∃ (hs : cls <:+ tv.l) (himgs : ImgOk cls (ctxOf tw.l) imgs) (ht : clt <:+ tw.l)
    (himgt : ImgOk clt (ctxOf tv.l) imgt),
    ∀ Φ : WFF σ (bodyCtx cls clt) 1, liftBody hs himgt Φ ∈ tv.M →
      WFF.ret hS (tupImgT cls imgs himgs).2
        (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Φ) ∈ tw.M

omit [ModalSys.NoFour] in
/-- Replacing a body's slot by its own η-expansion leaves it alone. -/
theorem WFF.bodyRepl_eta {V : Ctx} [V.NoSlots] {A : VarType} (Φ : WFF σ (V.insert (.bnd 0) A) 1) :
    WFF.bodyRepl (Term.mono ((Ctx.empty_le V).insert (.bnd 0) A)
      (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root _ _ _))) Φ = Φ := by
  unfold WFF.bodyRepl
  refine (WFF.subst_congr _ (Subst.idS σ _) _ (Subst.ok_idS_le (Ctx.Le.refl _)) _
    (Subst.coh_idS_le (Ctx.Le.refl _)) _ _ ?_ Φ).trans
    ((WFF.subst_ren (Ctx.Le.refl _) _ _ _ _ _ (fun v _ _ => Subst.at_idS v) Φ).trans
      (WFF.mono_refl _ Φ))
  refine Subst.sim_of fun v T _ hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = A := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    change SubE.Sim _ (((Subst.idS σ _).set (.bnd 0) _) (.root (.bnd 0))) (.ren _)
    rw [Subst.set_root, Term.mono_eta]
    exact .eta_ren _ _
  · change SubE.Sim T (((Subst.idS σ _).set (.bnd 0) _) v) (.ren v)
    rw [Subst.set_ne _ _ hvr]
    exact .refl _

/-! ## The invariant with the tuple's companions (T)

Under T the tuple object `□(tupT cls)` has companions, and they come back too (docs §11.21, the
commitment refactor): each companion's contents (`compVal`) sent along the arrow, as the tuple's
own value `tupImgT` is `tupT` sent along it (`subst_arrow_tupT`).  Everything takes the flag `b`
as an argument, so that at `false` it is `RetInv` definitionally. -/

/-- The tuple's value and its companions' values at the far end: `tupImgT`, then each companion's
    contents sent along the arrow. -/
def tupCompsImg {Δ : Ctx} (cls : List VarType) (img : ℕ → ℕ) (himg : ImgOk cls Δ img) :
    (cs : List (List Step)) → (bcT cls).CompOk cs →
    Σ a : Ann ((bcT cls).compsFlat cs), Term σ Δ ((bcT cls).compsFlat cs) a
  | [], _ => tupImgT cls img himg
  | p :: ps, h => ⟨_, Term.pair (tupCompsImg cls img himg ps h.tail).2
      (Term.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS himg) (coh_arrowS himg)
        (compVal (tupT cls).2 p h).2)⟩

/-- The tuple's shape: `□(bcT cls)` with all its companions (none with T off). -/
abbrev tupShape (b : Bool) (hb : ModalSys.T = b) (cls : List VarType) : NShape :=
  .boxC (bcT cls) ((bcT cls).compsAllB b) (VarType.compOk_compsAllB b hb _)

/-- ⭐**The returning-possibility invariant with companions**: `RetInv`, with the tuple bound at
    `tupShape` and its companions coming back as `tupCompsImg`.  At `b = false` this is `RetInv`
    (`retInvB_false`). -/
def RetInvB (hS : ModalSys.BStrong = true) (b : Bool) (hb : ModalSys.T = b) (tv tw : NodeSt σ)
    (cls : List VarType) (imgs : ℕ → ℕ) (clt : List VarType) (imgt : ℕ → ℕ) : Prop :=
  ∃ (hs : cls <:+ tv.l) (himgs : ImgOk cls (ctxOf tw.l) imgs) (ht : clt <:+ tw.l)
    (himgt : ImgOk clt (ctxOf tv.l) imgt),
    ∀ Φ : WFF σ (bodyCtx cls clt) 1, liftBody hs himgt Φ ∈ tv.M →
      WFF.retS hS (.nec (tupShape b hb cls))
        (tupCompsImg cls imgs himgs _ (VarType.compOk_compsAllB b hb _)).2
        (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Φ) ∈ tw.M

/-- With T off the invariant with companions is the invariant. -/
theorem retInvB_false {hS : ModalSys.BStrong = true} (hT : ModalSys.T = false)
    {tv tw : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ} :
    RetInvB hS false hT tv tw cls imgs clt imgt ↔ RetInv hS tv tw cls imgs clt imgt :=
  Iff.rfl

/-- The flag can be taken to be T itself. -/
theorem retInvB_flag {hS : ModalSys.BStrong = true} {b : Bool} (hb : ModalSys.T = b)
    {tv tw : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ} :
    RetInvB hS ModalSys.T rfl tv tw cls imgs clt imgt ↔
      RetInvB hS b hb tv tw cls imgs clt imgt := by
  cases hb
  exact Iff.rfl

/-- Reading the value with companions at a companion: that companion's contents sent along the
    arrow. -/
theorem at_compsIdx_tupCompsImg {Δ : Ctx} (cls : List VarType) (img : ℕ → ℕ)
    (himg : ImgOk cls Δ img) (θ : Subst σ Δ) :
    ∀ (cs : List (List Step)) (h : (bcT cls).CompOk cs) (u : VarSymb),
      θ.at u = .tm (tupCompsImg cls img himg cs h).2 → ∀ (q : List Step) (hq : q ∈ cs),
      θ.at (u.ext (compsIdx cs q)) = .tm (Term.subst (arrowIdx img) (arrowS σ Δ img)
        (ok_arrowS himg) (coh_arrowS himg) (compVal (tupT cls).2 q (h.single hq)).2)
  | [], _, _, _, q, hq => absurd hq List.not_mem_nil
  | p :: ps, h, u, hu, q, hq => by
      unfold compsIdx
      split_ifs with hqp
      · subst hqp
        change θ.at (.step u .snd) = _
        rw [Subst.at_proj θ u rfl, hu]
        rfl
      · change θ.at ((VarSymb.step u .fst).ext (compsIdx ps q)) = _
        refine at_compsIdx_tupCompsImg cls img himg θ ps h.tail _ ?_ q
          ((List.mem_cons.mp hq).resolve_left hqp)
        rw [Subst.at_proj θ u rfl, hu]
        rfl

/-- Reading the value with companions along the first components: the tuple's value. -/
theorem at_compsFst_tupCompsImg {Δ : Ctx} (cls : List VarType) (img : ℕ → ℕ)
    (himg : ImgOk cls Δ img) (θ : Subst σ Δ) :
    ∀ (cs : List (List Step)) (h : (bcT cls).CompOk cs) (u : VarSymb),
      θ.at u = .tm (tupCompsImg cls img himg cs h).2 →
      θ.at (u.ext (compsFst cs)) = .tm (tupImgT cls img himg).2
  | [], _, _, hu => hu
  | _ :: ps, h, u, hu => by
      change θ.at ((VarSymb.step u .fst).ext (compsFst ps)) = _
      refine at_compsFst_tupCompsImg cls img himg θ ps h.tail _ ?_
      rw [Subst.at_proj θ u rfl, hu]
      rfl

theorem holeRead_forgetC_tupCompsImg {Δ : Ctx} [Δ.NoSlots] (cls : List VarType) (img : ℕ → ℕ)
    (himg : ImgOk cls Δ img) (cs : List (List Step)) (h : (bcT cls).CompOk cs) :
    (⟨_, Term.holeRead (tupCompsImg cls img himg cs h).2
        (ShapeMap.forgetC (σ := σ) (bcT cls) cs h).val.2⟩ : Σ a, Term σ Δ (bcT cls) a) =
      tupImgT cls img himg := by
  unfold Term.holeRead
  dsimp only [ShapeMap.val]
  rw [Term.subst_mono]
  refine Term.subst_eta_tm _ _ _ _ _ _ _
    (at_compsFst_tupCompsImg cls img himg _ cs h _ ?_)
  rw [Subst.at_nonproj _ rfl, Subst.single_root]

/-- ⭐**Forgetting the companions**: the invariant with companions gives the invariant
    (`ShapeMap.forgetC`), so its T-generic consequences (`transfer`, growth) carry over. -/
theorem RetInvB.forget {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b}
    {tv tw : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ} (hM : Theory.IsMCS tw.M)
    (h : RetInvB hS b hb tv tw cls imgs clt imgt) : RetInv hS tv tw cls imgs clt imgt := by
  obtain ⟨hs, himgs, ht, himgt, hinv⟩ := h
  refine ⟨hs, himgs, ht, himgt, fun Φ hΦ => ?_⟩
  have hret := hinv Φ hΦ
  refine hM.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hret, ⟨?_⟩⟩
  refine Proof.conv (WFF.retS_congr hS _ (holeRead_forgetC_tupCompsImg cls imgs himgs _ _) rfl)
    (Proof.ret_map hS .nec (S := .nec (tupShape b hb cls))
      (ShapeMap.forgetC (bcT cls) _ (VarType.compOk_compsAllB b hb _)) _ _ ?_)
  exact Proof.conv (congrArg (WFF.retS hS _ _) (WFF.bodyRepl_eta _).symm)
    (Proof.lookup List.mem_cons_self)

/-! ## Transfer from the invariant -/

/-- A packed necessity of the bound object, read at `v`: the packed formula, necessarily, at the
    committed roots' items. -/
theorem liftBody_box_holeAt {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (bcT cls)) 1) :
    liftBody hs himgt (WFF.box (WFF.holeAt
        ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).insert _).boxIn
        (Term.eta (VarSymb.root (.bnd 0)).inner _
          (Ctx.ref_inner (Ctx.ref_insert_root _ (.bnd 0) (.VTypeBox (bcT cls)))))
        θ)) =
      WFF.box (WFF.holeAt Ctx.NoSlots.slots
        (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2) θ) := by
  unfold liftBody
  simp only [WFF.subst]
  rw [WFF.subst_holeAt]
  refine congrArg WFF.box (WFF.holeAt_congr _ ?_ θ)
  exact Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ (by
    change Subst.set _ _ _ (.root (.bnd 0)) = _
    exact Subst.set_root _ _ _))

/-- ⭐**The invariant gives necessity transfer**: a necessity about the committed roots, packed,
    is a body whose returning possibility `ret_counit` reads at the images — which is the necessity
    sent along the arrow (`holeRead_tupImgT_pack`). -/
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
      ← WFF.holeRead_eq_holeAt, holeRead_tupT_pack]
    exact hψ)
  rw [← holeRead_tupImgT_pack himgs ψ]
  refine hM.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hret, ⟨?_⟩⟩
  refine Proof.ret_counit hS .nec _ (pack cls ψ)
    (Proof.conv (congrArg (WFF.ret hS _) ?_) (Proof.lookup List.mem_cons_self))
  change WFF.box (WFF.mono _ (WFF.holeAt _ _ (pack cls ψ))) = _
  rw [WFF.mono_holeAt _ _ (((Ctx.NoSlots.slots (Γ := (ctxOf tw.l).boxIn)).insert _).boxIn),
    Term.mono_eta]
  rfl

/-! ## Growth -/

omit [ModalSys.NoFour] in
/-- Weakening the tuple of the images is the tuple of the images in the larger target. -/
theorem tupImgT_mono {Δ Δ' : Ctx} (h : Δ.Le Δ') : ∀ (l : List VarType) (img : ℕ → ℕ)
    (himg : ImgOk l Δ img),
    (⟨_, Term.mono h (tupImgT (σ := σ) l img himg).2⟩ : Σ a, Term σ Δ' (bcT l) a) =
      tupImgT (σ := σ) l img (himg.mono h)
  | [], _, _ => rfl
  | A :: l, img, himg =>
      sig_pair (tupImgT_mono h l img (ImgOk.tail himg)) (by rw [Term.mono_eta])

/-- A growing target keeps the invariant. -/
theorem RetInv.grow_tgt {hS : ModalSys.BStrong = true} {tv tw tw' : NodeSt σ}
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} (h : RetInv hS tv tw cls imgs clt imgt)
    (hg : Grows tw tw') : RetInv hS tv tw' cls imgs clt imgt := by
  obtain ⟨hs, himgs, ht, himgt, hinv⟩ := h
  have hle := ctxOf_le_of_suffix hg.suf
  refine ⟨hs, himgs.mono hle, ht.trans hg.suf, himgt, fun Φ hΦ => ?_⟩
  have h' := hg.sub _ (hinv Φ hΦ)
  change WFF.ret hS (Term.mono hle _) (WFF.mono _ (WFF.mono _ Φ)) ∈ tw'.M at h'
  rw [WFF.mono_mono, WFF.ret_congr hS (tupImgT_mono hle cls imgs himgs) rfl] at h'
  exact h'

/-- A body read in a larger source is the weakening of its reading. -/
theorem liftBody_mono {lv lv' cls clt : List VarType} (hs : cls <:+ lv) (hl : lv <:+ lv')
    {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt) (Φ : WFF σ (bodyCtx cls clt) 1) :
    WFF.mono (ctxOf_le_of_suffix hl) (liftBody hs himgt Φ) =
      liftBody (hs.trans hl) (himgt.mono (ctxOf_le_of_suffix hl)) Φ := by
  unfold liftBody
  rw [WFF.mono_subst _ _ _ _ _ _ Ctx.NoSlots.slots]
  have heq : ((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntry hs)).mono
      (ctxOf_le_of_suffix hl) =
        (arrowS σ (ctxOf lv') imgt).set (.bnd 0) (liftEntry (hs.trans hl)) := by
    funext v
    change SubE.mono _ (Subst.set _ _ _ v) = Subst.set _ _ _ v
    by_cases hv : v = .root (.bnd 0)
    · subst hv
      rw [Subst.set_root, Subst.set_root]
      change SubE.tm (Term.boxtm (Term.mono _ (Term.mono _ _))) = _
      rw [Term.mono_mono]
    · rw [Subst.set_ne _ _ hv, Subst.set_ne _ _ hv]
      match v with
      | .step u .box => rfl
      | .root _ => rfl
      | .step _ .fst => rfl
      | .step _ .snd => rfl
      | .step _ .dia => rfl
      | .step _ .here => rfl
      | .step _ .keep => rfl
  exact WFF.subst_congr _ _ _ _ _ _ _ _
    (Subst.sim_of fun v U _ _ => by rw [congrFun heq v]; exact .refl _) Φ

/-- A source growing conservatively keeps the invariant. -/
theorem RetInv.grow_src {hS : ModalSys.BStrong = true} {tv tv' tw : NodeSt σ}
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} (hv : Theory.IsMCS tv.M)
    (hv' : Theory.IsMCS tv'.M) (h : RetInv hS tv tw cls imgs clt imgt) (hg : Grows tv tv') :
    RetInv hS tv' tw cls imgs clt imgt := by
  obtain ⟨hs, himgs, ht, himgt, hinv⟩ := h
  have hle := ctxOf_le_of_suffix hg.suf
  refine ⟨hs.trans hg.suf, himgs, ht, himgt.mono hle, fun Φ hΦ => hinv Φ ?_⟩
  refine mem_of_mono_mem hle hv hv' hg.sub ?_
  rw [liftBody_mono hs hg.suf himgt Φ]
  exact hΦ

/-! ## Witnessing a returning possibility's new item -/

/-- `ret_ext`'s instance at a fresh `c`: the returning possibility with the companion item, its
    value the old value paired with `c`. -/
def retExtAtom {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) {A B : VarType} {a : Ann A}
    (t : Term σ Γ A a)
    (Φ : WFF σ ((Γ.boxIn.insert (.bnd 0) (.VTypeBox A)).insert (.bnd 1) (.VTypeBox B)) 2)
    (c : ℕ) (hc : Γ.RootFresh (.free c)) : WFF σ (Γ.insert (.free c) B) 0 :=
  WFF.ret hS
    (Term.pair (Term.weaken hc.root B t)
      (Term.eta (.root (.free c)) B (Ctx.ref_insert_root Γ (.free c) B)))
    (WFF.mono ((Ctx.le_insert hc.root B).boxIn.insert (.bnd 0) _) (WFF.bodySplit
      (Term.boxFst (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox (.VTypeProd A B))))
      (Term.boxSnd (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox (.VTypeProd A B))))
      Φ))

/-- ⭐**A returning possibility's new item is witnessed by a fresh variable** (`ret_ext`), as an
    existential's is (`henkin_consistent`). -/
theorem retExt_consistent {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)}
    (hM : Theory.Consistent M) (hS : ModalSys.BStrong = true) {A B : VarType} {a : Ann A}
    (t : Term σ Γ A a)
    (Φ : WFF σ ((Γ.boxIn.insert (.bnd 0) (.VTypeBox A)).insert (.bnd 1) (.VTypeBox B)) 2)
    (hex : Theory.Derives M (WFF.ret hS t (WFF.ex (.VTypeBox B) Φ))) {u : ℕ}
    (hu : Γ.RootFresh (.free u)) :
    Theory.Consistent (WFF.mono (Ctx.le_insert hu.root B) '' M ∪
      {retExtAtom hS t Φ u hu}) := by
  rintro ⟨Δ, hΔ, p⟩
  obtain ⟨Δ₀, h₀, h₁⟩ := exists_hyps_cons_map (P := fun x => x ∈ M)
    (fun x => WFF.mono (Ctx.le_insert hu.root B) x) (retExtAtom hS t Φ u hu) Δ
    (fun δ hδ => by
      rcases hΔ δ hδ with ⟨x, hx, rfl⟩ | h
      · exact Or.inr ⟨x, hx, rfl⟩
      · exact Or.inl (Set.mem_singleton_iff.mp h))
  obtain ⟨q⟩ := Provable.mono h₁ p
  obtain ⟨Δ₁, hΔ₁, ⟨pex⟩⟩ := hex
  refine hM ⟨Δ₁ ++ Δ₀, fun x hx => (List.mem_append.mp hx).elim (hΔ₁ x) (h₀ x), ⟨?_⟩⟩
  refine Proof.ret_ext hS .nec t Φ u hu (φ := .bot)
    (Proof.ofSubset (fun x hx => List.mem_append_left _ hx) pex)
    (Proof.ofSubset (fun x hx => ?_) q)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact List.mem_cons_self
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_append_right _ hy))

/-! ## A paired item from its components -/

section Pair

variable {V : Ctx} [V.NoSlots]

omit [ModalSys] [ModalSys.NoFour] in
/-- The view with two slots for a paired item's components. -/
theorem pair_le (X Y : VarType) :
    V.Le ((V.insert (.bnd 0) (.VTypeBox X)).insert (.bnd 1) (.VTypeBox Y)) :=
  (body_le _).trans (Ctx.le_insert (((Ctx.NoSlots.slots (Γ := V)).insert _).root) _)

/-- The paired item from its two components: `□⟨d₀.box, d₁.box⟩`. -/
def pairItem (X Y : VarType) :
    Term σ ((V.insert (.bnd 0) (.VTypeBox X)).insert (.bnd 1) (.VTypeBox Y))
      (.VTypeBox (.VTypeProd X Y))
      (.box (.prod (Ann.eta (VarSymb.root (.bnd 0)).inner X)
        (Ann.eta (VarSymb.root (.bnd 1)).inner Y))) :=
  .boxtm (.pair
    (Term.eta (VarSymb.root (.bnd 0)).inner X (Ctx.ref_inner
      ((Ctx.le_insert (((Ctx.NoSlots.slots (Γ := V)).insert _).root) _).ref
        (Ctx.ref_insert_root V (.bnd 0) (.VTypeBox X)))))
    (Term.eta (VarSymb.root (.bnd 1)).inner Y
      (Ctx.ref_inner (Ctx.ref_insert_root _ (.bnd 1) (.VTypeBox Y)))))

/-- ⭐A body about a paired item, as a body about its two components. -/
def WFF.pairUp {X Y : VarType} (Φ : WFF σ (V.insert (.bnd 0) (.VTypeBox (.VTypeProd X Y))) 1) :
    WFF σ ((V.insert (.bnd 0) (.VTypeBox X)).insert (.bnd 1) (.VTypeBox Y)) 2 :=
  WFF.subst (Subst.setIdx id (.bnd 0) (.tm (pairItem X Y)))
    ((Subst.idS σ _).set (.bnd 0) (.tm (pairItem X Y)))
    (Subst.ok_set (Subst.ok_idS_le (pair_le X Y)) rfl)
    (Subst.coh_set (Subst.ok_idS_le (pair_le X Y)) (Subst.coh_idS_le (pair_le X Y))
      ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) rfl)
    ((Ctx.NoSlots.slots (Γ := V)).insert _) (((Ctx.NoSlots.slots (Γ := V)).insert _).insert _) Φ

/-- The paired item, substituted by an entry sending its components to `w`'s components: the
    η-expansion of `w`. -/
theorem sim_pairItem {X Y : VarType} {Δ : Ctx} {ι : VarSymb → VarSymb} (θ : Subst σ Δ)
    (hθ : Subst.Ok ((V.insert (.bnd 0) (.VTypeBox X)).insert (.bnd 1) (.VTypeBox Y)) θ)
    (hc : Subst.Coh ι ((V.insert (.bnd 0) (.VTypeBox X)).insert (.bnd 1) (.VTypeBox Y)) θ)
    {w : VarSymb} (hw : Δ.ref w = some (.VTypeBox (.VTypeProd X Y)))
    (h0 : θ.at (.root (.bnd 0)) = .tm (Term.boxFst hw))
    (h1 : θ.at (.root (.bnd 1)) = .tm (Term.boxSnd hw)) :
    SubE.Sim (.VTypeBox (.VTypeProd X Y)) (.ren w)
      (.tm (Term.subst ι θ hθ hc (pairItem (σ := σ) (V := V) X Y))) := by
  have e : (⟨_, Term.subst ι θ hθ hc (pairItem (σ := σ) (V := V) X Y)⟩ :
      Σ b, Term σ Δ (.VTypeBox (.VTypeProd X Y)) b) = ⟨_, Term.eta w _ hw⟩ :=
    sig_boxtm (sig_pair
      (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ h0))
      (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ h1)))
  rw [SubE.tm_sigma e]
  exact .ren_eta _ hw

/-- ⭐Splitting the paired item into its components undoes `pairUp`: the composite sends the slot
    to its own η-expansion. -/
theorem WFF.bodySplit_pairUp {X Y : VarType}
    (Φ : WFF σ (V.insert (.bnd 0) (.VTypeBox (.VTypeProd X Y))) 1) :
    WFF.bodySplit (Term.boxFst (Ctx.ref_insert_root V (.bnd 0) (.VTypeBox (.VTypeProd X Y))))
      (Term.boxSnd (Ctx.ref_insert_root V (.bnd 0) (.VTypeBox (.VTypeProd X Y))))
      (WFF.pairUp Φ) = Φ := by
  unfold WFF.bodySplit WFF.pairUp
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ Subst.ok_idS Subst.coh_idS _ _ _ ?_ Φ).trans
    (WFF.subst_id _ _ _ Φ)
  refine Subst.sim_of fun v U hlp hv => ?_
  have hb1 : v ≠ .root (.bnd 1) → v ≠ .root (.bnd 0) →
      (((Subst.idS σ (V.insert (.bnd 0) (.VTypeBox (.VTypeProd X Y)))).set (.bnd 0)
        (.tm (Term.boxFst (Ctx.ref_insert_root V (.bnd 0) (.VTypeBox (.VTypeProd X Y)))))).set
        (.bnd 1) (.tm (Term.boxSnd (Ctx.ref_insert_root V (.bnd 0)
          (.VTypeBox (.VTypeProd X Y)))))) v = .ren v := fun h₁ h₀ => by
    rw [Subst.set_ne _ _ h₁, Subst.set_ne _ _ h₀]
    rfl
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : U = .VTypeBox (.VTypeProd X Y) := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else V _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    change SubE.Sim _ (.ren (.root (.bnd 0)))
      ((((Subst.idS σ _).set (.bnd 0) (.tm (pairItem X Y))) (.root (.bnd 0))).comp _ _ _)
    rw [Subst.set_root]
    refine sim_pairItem _ _ _ (Ctx.ref_insert_root V (.bnd 0) _) ?_ ?_
    · change (Subst.set _ _ _) (.root (.bnd 0)) = _
      rw [Subst.set_ne _ _ (fun h => by cases h), Subst.set_root]
    · change (Subst.set _ _ _) (.root (.bnd 1)) = _
      rw [Subst.set_root]
  · have hv' : V v = some U := by
      change (if v = VarSymb.root (.bnd 0) then _ else V v) = _ at hv
      rwa [if_neg hvr] at hv
    have hv1 : v ≠ .root (.bnd 1) := fun h => by
      subst h
      rw [((Ctx.NoSlots.slots (Γ := V)).rootFresh (Nat.zero_le 1)).root] at hv'
      cases hv'
    change SubE.Sim U (.ren v)
      ((((Subst.idS σ _).set (.bnd 0) (.tm (pairItem X Y))) v).comp _ _ _)
    rw [Subst.set_ne _ _ hvr]
    change SubE.Sim U (.ren v) ((Subst.set _ _ _).at v)
    rw [Subst.at_nonproj _ hlp, hb1 hv1 hvr]
    exact .refl _

end Pair

/-! ## The source's `∃`-introduction for a new root -/

section NewRoot

variable {lv cls clt : List VarType} {A : VarType}

/-- The new root's necessary object at the source: `□` of its items. -/
abbrev newItem (hs' : (A :: cls) <:+ lv) :
    Term σ (ctxOf lv) (.VTypeBox A.bc) (.box (tupAnn (.root (.free cls.length)) A)) :=
  Term.boxtm (Term.mono (ctxOf_le_of_suffix hs').boxIn
    (tup (σ := σ) (.root (.free cls.length)) A (ctxOf_ref_new A cls)))

/-- The pair of the older roots' necessary object and the new root's item slot, in the view of
    the `∃` the new item is bound by. -/
def midTerm (hs : cls <:+ lv) (A : VarType) :
    Σ a, Term σ ((ctxOf lv).insert (.bnd 0) (.VTypeBox A.bc)) (.VTypeBox (bcT (A :: cls))) a :=
  ⟨_, .boxtm (.pair
    (Term.mono ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf lv)).root _).boxIn)
      (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2))
    (Term.eta (VarSymb.root (.bnd 0)).inner A.bc
      (Ctx.ref_inner (Ctx.ref_insert_root _ (.bnd 0) _))))⟩

/-- The middle substitution: the reverse arrow, weakened past the `∃`'s slot, with the body's slot
    set to `midTerm`. -/
abbrev midS (hs : cls <:+ lv) (A : VarType) (imgt : ℕ → ℕ) :
    Subst σ ((ctxOf lv).insert (.bnd 0) (.VTypeBox A.bc)) :=
  ((arrowS σ (ctxOf lv) imgt).mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf lv)).root _)).set
    (.bnd 0) (.tm (midTerm hs A).2)

theorem ok_midS (hs : cls <:+ lv) {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt) :
    Subst.Ok (bodyCtx (A :: cls) clt) (midS (σ := σ) hs A imgt) :=
  Subst.ok_set (Subst.ok_mono (ok_arrowS himgt) _) rfl

theorem coh_midS (hs : cls <:+ lv) {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt) :
    Subst.Coh (Subst.setIdx (arrowIdx imgt) (.bnd 0) (.tm (midTerm (σ := σ) hs A).2))
      (bodyCtx (A :: cls) clt) (midS (σ := σ) hs A imgt) :=
  Subst.coh_set (Subst.ok_mono (ok_arrowS himgt) _) (Subst.coh_mono (coh_arrowS himgt) _)
    ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).rootFresh (le_refl 0)) rfl

/-- A non-slot variable of a body's context is an item of the reverse arrow's view. -/
theorem body_item {cl clt : List VarType} {v : VarSymb} {U : VarType} (_hlp : v.lastProj = false)
    (hv : bodyCtx cl clt v = some U) (hvr : v ≠ .root (.bnd 0)) :
    ∃ u, v = .step u .box ∧ (ctxOf clt).ref u = some (.VTypeBox U) := by
  change (if v = VarSymb.root (.bnd 0) then _ else (ctxOf clt).boxIn v) = _ at hv
  rw [if_neg hvr] at hv
  exact boxIn_item hv

/-- ⭐**A new root's body is an `∃`-introduction of the older roots' body.**  Read at the source,
    the split body `∃e. pairUp Φ` over the older roots, at the new root's necessary object, is the
    body `Φ` over all of them, since `tupT (A :: cls) = ⟨tupT cls, tup c⟩`. -/
theorem liftBody_ex_pairUp_mem {M : Set (WFF σ (ctxOf lv) 0)} (hM : Theory.IsMCS M)
    (hs' : (A :: cls) <:+ lv) {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt)
    (Φ : WFF σ (bodyCtx (A :: cls) clt) 1) (h : liftBody hs' himgt Φ ∈ M) :
    liftBody ((List.suffix_cons A cls).trans hs') himgt
      (WFF.ex (.VTypeBox A.bc) (WFF.pairUp Φ)) ∈ M := by
  have hs : cls <:+ lv := (List.suffix_cons A cls).trans hs'
  refine hM.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact h, ⟨?_⟩⟩
  refine Proof.ex_intro _ (newItem hs') (Proof.conv ?_ (Proof.lookup List.mem_cons_self))
  refine Eq.symm ?_
  unfold WFF.instantiate WFF.substRoot WFF.pairUp
  have hfr : (ctxOf lv) (.root (.bnd 0)) = none := (Ctx.NoSlots.slots (Γ := ctxOf lv)).root
  -- Step A: the split, then the reverse arrow under the `∃`, is the middle substitution.
  have simA : Subst.Sim (bodyCtx (A :: cls) clt) (midS (σ := σ) hs A imgt)
      (((Subst.idS σ (((ctxOf clt).boxIn.insert (.bnd 0) (.VTypeBox (bcT cls))).insert
          (.bnd 1) (.VTypeBox A.bc))).set (.bnd 0) (.tm (pairItem (bcT cls) A.bc))).comp
        (((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntry hs)).under (0 + 1) 0
          (.VTypeBox A.bc) hfr)
        (Subst.ok_under (Subst.ok_set (T := .VTypeBox (bcT cls)) (e := liftEntry hs)
          (ok_arrowS himgt) rfl) _ hfr)
        (Subst.coh_under (Subst.ok_set (T := .VTypeBox (bcT cls)) (e := liftEntry hs)
            (ok_arrowS himgt) rfl)
          (Subst.coh_set (T := .VTypeBox (bcT cls)) (e := liftEntry hs) (ok_arrowS himgt)
            (coh_arrowS himgt)
            ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).rootFresh (le_refl 0)) rfl)
          ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).insert _) _ hfr)) := by
    refine Subst.sim_of fun v U hlp hv => ?_
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      obtain rfl : U = .VTypeBox (bcT (A :: cls)) := by
        change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
        rw [if_pos rfl] at hv
        exact (Option.some.inj hv).symm
      dsimp only [Subst.comp]
      rw [show midS (σ := σ) hs A imgt (.root (.bnd 0)) = .tm (midTerm hs A).2 from
        Subst.set_root _ _ _]
      have h0 : (((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntry hs)).under (0 + 1) 0
          (.VTypeBox A.bc) hfr).at (.root (.bnd 0)) =
          .tm (Term.boxtm (Term.mono ((Ctx.le_insert hfr _).boxIn)
            (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2))) := by
        rw [Subst.at_under_ne _ _ _ (fun h => by cases h)]
        change SubE.mono _ (Subst.set _ _ _ (.root (.bnd 0))) = _
        rw [Subst.set_root]
        rfl
      dsimp only [SubE.comp]
      exact SubE.sim_tm_sigma (sig_boxtm (sig_pair
        (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ h0))
        (Term.subst_eta_renAt _ _ _ _ _ _ _ (Ctx.ref_inner (Ctx.ref_insert_root _ (.bnd 0) _))
          (Subst.box_at_inner_ren _ (Subst.under_at_slot _ (0 + 1) 0 _ hfr))))).symm
    · obtain ⟨u, rfl, hu⟩ := body_item hlp hv hvr
      dsimp only [Subst.comp]
      rw [show midS (σ := σ) hs A imgt (.step u .box) =
        SubE.mono _ (arrowS σ (ctxOf lv) imgt (.step u .box)) from Subst.set_ne _ _ hvr,
        Subst.set_ne _ _ hvr]
      dsimp only [Subst.idS, SubE.comp]
      rw [Subst.at_nonproj _ hlp]
      dsimp only [Subst.under]
      rw [if_neg (fun h => by cases h), Subst.set_ne _ _ hvr]
      exact .refl _
  rw [WFF.subst_comp _ _ (midS hs A imgt) _ _ _ _ (ok_midS hs himgt) (coh_midS hs himgt)
    _ _ _ simA]
  -- Step B: then the new root's object in the `∃`'s slot is the reading over all the roots.
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v U hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : U = .VTypeBox (bcT (A :: cls)) := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp]
    rw [show midS (σ := σ) hs A imgt (.root (.bnd 0)) = .tm (midTerm hs A).2 from
      Subst.set_root _ _ _]
    dsimp only [SubE.comp]
    have hsg : (Subst.single (σ := σ) (.bnd 0) (.tm (newItem hs'))).at (.root (.bnd 0)) =
        .tm (newItem hs') := by
      change Subst.single (.bnd 0) _ (.root (.bnd 0)) = _
      exact if_pos rfl
    have hsim : Subst.Sim (ctxOf cls).boxIn
        (Subst.single (σ := σ) (Δ := ctxOf lv) (.bnd 0) (.tm (newItem hs'))).box
        (Subst.idS σ (ctxOf lv).boxIn) := by
      refine Subst.sim_of fun v U _ hv => ?_
      obtain ⟨u, rfl, hu⟩ := boxIn_item hv
      obtain ⟨r, hr, _, _⟩ := ref_rt hu
      change SubE.Sim U ((Subst.single _ _).at u).unbox (.ren (.step u .box))
      rw [Subst.single_at_ne (by rw [hr]; exact fun h => by cases h)]
      change SubE.Sim U (.ren u.inner) _
      rw [VarSymb.inner_box ModalSys.NoFour.keepOnly]
      exact .refl _
    refine SubE.sim_tm_sigma (sig_boxtm (sig_pair ?_
      (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ hsg)))).symm
    rw [Term.mono_mono, Term.mono_mono, Term.subst_mono]
    exact (Term.subst_congr _ _ _ (Subst.ok_idS_le (ctxOf_le_of_suffix hs).boxIn) _
      (Subst.coh_idS_le (ctxOf_le_of_suffix hs).boxIn) hsim _).trans
      (Term.subst_idS_mono (ctxOf_le_of_suffix hs).boxIn _ _ _)
  · obtain ⟨u, rfl, hu⟩ := body_item hlp hv hvr
    obtain ⟨r, hr, _, _⟩ := ref_rt hu
    dsimp only [Subst.comp]
    rw [show midS (σ := σ) hs A imgt (.step u .box) =
      SubE.mono _ (arrowS σ (ctxOf lv) imgt (.step u .box)) from Subst.set_ne _ _ hvr,
      Subst.set_ne _ _ hvr]
    change SubE.Sim U (.ren (itemImg imgt u)) ((Subst.single _ _).at (itemImg imgt u))
    rw [Subst.single_at_ne (by rw [itemAt_rt, hr]; exact fun h => by cases h)]
    exact .refl _

end NewRoot

/-! ## Splitting a returning possibility over a conjunction -/

omit [ModalSys.NoFour] in
/-- `□∀d.(Φ ∧ Ψ → Φ)`, by necessitation of a tautology. -/
def Proof.box_all_and_left {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} {A : VarType}
    (Φ Ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) {u : ℕ} (hu : Γ.RootFresh (.free u)) :
    Proof σ Γ Δ (WFF.box (WFF.all A (WFF.imp (WFF.and Φ Ψ) Φ))) := by
  have q : Proof σ Γ.boxIn [] (WFF.all A (WFF.imp (WFF.and Φ Ψ) Φ)) := by
    have := Proof.all_intro (Δ := []) u A hu.boxIn
      (φ := WFF.openFree u hu.boxIn Ctx.NoSlots.slots (WFF.imp (WFF.and Φ Ψ) Φ))
      (Proof.imp_intro (Proof.and_elim_l (Proof.lookup List.mem_cons_self)))
    rwa [WFF.bindFree_openFree] at this
  exact Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.K_box (Δ := []) q)

omit [ModalSys.NoFour] in
/-- `□∀d.(Φ ∧ Ψ → Ψ)`. -/
def Proof.box_all_and_right {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} {A : VarType}
    (Φ Ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) {u : ℕ} (hu : Γ.RootFresh (.free u)) :
    Proof σ Γ Δ (WFF.box (WFF.all A (WFF.imp (WFF.and Φ Ψ) Ψ))) := by
  have q : Proof σ Γ.boxIn [] (WFF.all A (WFF.imp (WFF.and Φ Ψ) Ψ)) := by
    have := Proof.all_intro (Δ := []) u A hu.boxIn
      (φ := WFF.openFree u hu.boxIn Ctx.NoSlots.slots (WFF.imp (WFF.and Φ Ψ) Ψ))
      (Proof.imp_intro (Proof.and_elim_r (Proof.lookup List.mem_cons_self)))
    rwa [WFF.bindFree_openFree] at this
  exact Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.K_box (Δ := []) q)

/-! ## The images under an extended index map -/

omit [ModalSys.NoFour] in
/-- An η-expansion of a root depends only on the root's index. -/
theorem eta_root_congr {Δ : Ctx} {T : VarType} {x y : ℕ} (h : x = y)
    (hx : Δ.ref (.root (.free x)) = some T) (hy : Δ.ref (.root (.free y)) = some T) :
    (⟨_, Term.eta (σ := σ) (.root (.free x)) T hx⟩ : Σ a, Term σ Δ T a) =
      ⟨_, Term.eta (.root (.free y)) T hy⟩ := by
  subst h
  rfl

omit [ModalSys.NoFour] in
/-- The tuple of the images depends only on the images of the list's roots. -/
theorem tupImgT_congr {Δ : Ctx} : ∀ (l : List VarType) {img img' : ℕ → ℕ}
    (himg : ImgOk l Δ img) (himg' : ImgOk l Δ img'), (∀ r, r < l.length → img r = img' r) →
    tupImgT (σ := σ) l img himg = tupImgT l img' himg'
  | [], _, _, _, _, _ => rfl
  | _ :: l, _, _, himg, himg', h =>
      sig_pair (tupImgT_congr l (ImgOk.tail himg) (ImgOk.tail himg')
          (fun r hr => h r (Nat.lt_succ_of_lt hr)))
        (eta_root_congr (h l.length (Nat.lt_succ_self _)) _ _)

omit [ModalSys.NoFour] in
/-- ⭐The images' tuple after committing one more root: the old tuple, weakened, paired with the
    fresh variable — the value `ret_ext` gives. -/
theorem tupImgT_ext {A : VarType} {cl lt : List VarType} {img : ℕ → ℕ}
    (himg : ImgOk cl (ctxOf lt) img)
    (himg' : ImgOk (A :: cl) (ctxOf (A.bc :: lt)) (extImg img cl.length lt.length)) :
    tupImgT (σ := σ) (A :: cl) (extImg img cl.length lt.length) himg' =
      ⟨_, Term.pair (Term.weaken (ctxOf_fresh (l := lt) le_rfl).root A.bc (tupImgT cl img himg).2)
        (Term.eta (.root (.free lt.length)) A.bc
          (Ctx.ref_insert_root (ctxOf lt) (.free lt.length) A.bc))⟩ := by
  refine sig_pair ?_ (eta_root_congr (by simp [extImg]) _ _)
  refine (tupImgT_congr cl _ (himg.mono (ctxOf_le_append [A.bc] lt)) (fun r hr => ?_)).trans
    (tupImgT_mono (ctxOf_le_append [A.bc] lt) cl img himg).symm
  simp [extImg, Nat.ne_of_lt hr]

/-! ## Splitting a weakened paired body -/

/-- `bodySplit_pairUp` through a weakening of the view: splitting the weakened split body is the
    weakened body. -/
theorem WFF.bodySplit_mono_pairUp {V V' : Ctx} [V.NoSlots] [V'.NoSlots] (h : V.Le V')
    {X Y : VarType} (Φ : WFF σ (V.insert (.bnd 0) (.VTypeBox (.VTypeProd X Y))) 1) :
    WFF.bodySplit (Term.boxFst (Ctx.ref_insert_root V' (.bnd 0) (.VTypeBox (.VTypeProd X Y))))
      (Term.boxSnd (Ctx.ref_insert_root V' (.bnd 0) (.VTypeBox (.VTypeProd X Y))))
      (WFF.mono ((h.insert (.bnd 0) _).insert (.bnd 1) _) (WFF.pairUp Φ)) =
      WFF.mono (h.insert (.bnd 0) _) Φ := by
  unfold WFF.bodySplit WFF.pairUp
  rw [WFF.mono_subst _ _ _ _ _ _ (((Ctx.NoSlots.slots (Γ := V')).insert _).insert _)]
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ (Subst.ok_idS_le (h.insert (.bnd 0) _))
    (Subst.coh_idS_le (h.insert (.bnd 0) _)) _ _ _ ?_ Φ).trans
    (WFF.subst_ren (h.insert (.bnd 0) _) _ _ _ _ _ (fun v _ _ => Subst.at_idS v) Φ)
  refine Subst.sim_of fun v U hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : U = .VTypeBox (.VTypeProd X Y) := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else V _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp, Subst.mono]
    rw [Subst.set_root]
    dsimp only [SubE.mono, SubE.comp]
    rw [Term.subst_mono]
    refine sim_pairItem _ _ _ (Ctx.ref_insert_root V' (.bnd 0) _) ?_ ?_
    · change (Subst.set _ _ _) (.root (.bnd 0)) = _
      rw [Subst.set_ne _ _ (fun h => by cases h), Subst.set_root]
    · change (Subst.set _ _ _) (.root (.bnd 1)) = _
      rw [Subst.set_root]
  · have hv' : V v = some U := by
      change (if v = VarSymb.root (.bnd 0) then _ else V v) = _ at hv
      rwa [if_neg hvr] at hv
    have hv1 : v ≠ .root (.bnd 1) := fun h => by
      subst h
      rw [((Ctx.NoSlots.slots (Γ := V)).rootFresh (Nat.zero_le 1)).root] at hv'
      cases hv'
    dsimp only [Subst.comp, Subst.mono]
    rw [Subst.set_ne _ _ hvr]
    dsimp only [Subst.idS, SubE.mono, SubE.comp]
    rw [Subst.at_nonproj _ hlp, Subst.set_ne _ _ hv1, Subst.set_ne _ _ hvr]
    exact .refl _

/-! ## Realising the source's next root -/

section Step

variable (hS : ModalSys.BStrong = true) {ts tt : NodeSt σ} {cl clt : List VarType}
  {img imgt : ℕ → ℕ}

/-- The returning possibility a body over the roots committed so far, with the next one, becomes
    in the grown target: valued at the images and the fresh variable. -/
def retAtom (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (Φ : WFF σ (bodyCtx (nextTy ts.l cl :: cl) clt) 1) :
    WFF σ (ctxOf ((nextTy ts.l cl).bc :: tt.l)) 0 :=
  WFF.ret hS (tupImgT (nextTy ts.l cl :: cl) (extImg img cl.length tt.l.length)
      (imgOk_ext himg)).2
    (WFF.mono ((ctxOf_le_of_suffix (ht.trans (List.suffix_cons _ _))).boxIn.insert (.bnd 0) _) Φ)

/-- What the target gains when the source's next root is committed. -/
def retSet (hs' : (nextTy ts.l cl :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l) :
    Set (WFF σ (ctxOf ((nextTy ts.l cl).bc :: tt.l)) 0) :=
  {φ | ∃ Φ, liftBody hs' himgt Φ ∈ ts.M ∧ φ = retAtom hS himg ht Φ}

/-- Finitely many of the gained atoms reduce to one, at the conjunction of their bodies. -/
theorem ret_list (hs' : (nextTy ts.l cl :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l) (hv : Theory.IsMCS ts.M)
    (S : Set (WFF σ (ctxOf ((nextTy ts.l cl).bc :: tt.l)) 0)) :
    ∀ L : List (WFF σ (ctxOf ((nextTy ts.l cl).bc :: tt.l)) 0),
      (∀ δ ∈ L, δ ∈ S ∨ δ ∈ retSet hS hs' himgt himg ht) →
      ∃ Φ, liftBody hs' himgt Φ ∈ ts.M ∧
        ∀ δ ∈ L, Theory.Derives (S ∪ {retAtom hS himg ht Φ}) δ
  | [], _ => ⟨.top, hv.top_mem, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨Φ₀, hΦ₀, hL⟩ := ret_list hs' himgt himg ht hv S L
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hu := ctxOf_fresh (l := (nextTy ts.l cl).bc :: tt.l) le_rfl
      rcases h δ List.mem_cons_self with hS' | ⟨Φ₁, hΦ₁, rfl⟩
      · refine ⟨Φ₀, hΦ₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact Theory.Derives.of_mem (Or.inl hS')
        · exact hL d hd
      · have hand : ∀ Φ', Proof σ _ [retAtom hS himg ht (Φ₀.and Φ₁)] (retAtom hS himg ht Φ') →
            Theory.Derives (S ∪ {retAtom hS himg ht (Φ₀.and Φ₁)}) (retAtom hS himg ht Φ') :=
          fun Φ' p => ⟨[_], fun x hx => by
            rw [List.mem_singleton.mp hx]; exact Or.inr rfl, ⟨p⟩⟩
        have h₀ := hand Φ₀ (Proof.ret_mono hS .nec _ _ _ (Proof.lookup List.mem_cons_self)
          (Proof.box_all_and_left _ _ hu))
        have h₁ := hand Φ₁ (Proof.ret_mono hS .nec _ _ _ (Proof.lookup List.mem_cons_self)
          (Proof.box_all_and_right _ _ hu))
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

/-- ⭐**The gained atoms are consistent with the target**: finitely many reduce to one body `Φ`
    (`ret_list`); the source has `∃e. pairUp Φ` at the older roots (`liftBody_ex_pairUp_mem`), so
    by the invariant the target has `◇[d ↦ t] ∃e. pairUp Φ`; `ret_ext` witnesses `e` by the fresh
    variable (`retExt_consistent`), and splitting undoes `pairUp` (`bodySplit_mono_pairUp`). -/
theorem retSet_consistent (hs' : (nextTy ts.l cl :: cl) <:+ ts.l)
    (himgt : ImgOk clt (ctxOf ts.l) imgt) (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : ∀ Φ : WFF σ (bodyCtx cl clt) 1,
      liftBody ((List.suffix_cons _ _).trans hs') himgt Φ ∈ ts.M →
        WFF.ret hS (tupImgT cl img himg).2
          (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Φ) ∈ tt.M) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l) '' tt.M ∪
      retSet hS hs' himgt himg ht) := by
  rintro ⟨L, hL, p⟩
  obtain ⟨Φ, hΦ, hder⟩ := ret_list hS hs' himgt himg ht hv _ L hL
  have h₁ := hinv _ (liftBody_ex_pairUp_mem hv hs' himgt Φ hΦ)
  have hc := retExt_consistent hw.1 hS _ _ (Theory.Derives.of_mem h₁)
    (ctxOf_fresh (l := tt.l) le_rfl)
  have heq : retExtAtom hS (tupImgT cl img himg).2
      (WFF.mono (((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _).insert (.bnd 1) _)
        (WFF.pairUp Φ)) tt.l.length (ctxOf_fresh le_rfl) = retAtom hS himg ht Φ := by
    unfold retExtAtom retAtom
    refine WFF.ret_congr hS (tupImgT_ext himg (imgOk_ext himg)).symm ?_
    rw [WFF.bodySplit_mono_pairUp (ctxOf_le_of_suffix ht).boxIn, WFF.mono_mono]
  rw [heq] at hc
  exact hc (Derives.trans (fun x hx => hder x hx) ⟨L, fun x hx => hx, p⟩)

/-- The target grown by the image of the source's next root, under strong B: every body true at
    the source over the roots with the next one becomes a returning possibility valued at the
    images and the fresh variable. -/
noncomputable def retStep (hs' : (nextTy ts.l cl :: cl) <:+ ts.l)
    (himgt : ImgOk clt (ctxOf ts.l) imgt) (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l) :
    NodeSt σ :=
  ⟨(nextTy ts.l cl).bc :: tt.l, complete (WFF.mono (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l) ''
    tt.M ∪ retSet hS hs' himgt himg ht)⟩

/-- ⭐**One realisation step under strong B**: when the arrow's invariant holds, the grown target
    is maximal consistent, extends the old one, and the invariant holds for one more root — and
    with it necessity transfer (`RetInv.transfer`). -/
theorem retStep_ok (hs' : (nextTy ts.l cl :: cl) <:+ ts.l)
    (himgt : ImgOk clt (ctxOf ts.l) imgt) (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M) (hinv : RetInv hS ts tt cl img clt imgt) :
    Theory.IsMCS (retStep hS hs' himgt himg ht).M ∧ Grows tt (retStep hS hs' himgt himg ht) ∧
      RetInv hS ts (retStep hS hs' himgt himg ht) (nextTy ts.l cl :: cl)
        (extImg img cl.length tt.l.length) clt imgt := by
  obtain ⟨_, _, _, _, h⟩ := hinv
  have hcons := retSet_consistent hS hs' himgt himg ht hv hw h
  obtain ⟨hsub, hmcs⟩ := complete_spec hcons
  refine ⟨hmcs, ⟨⟨[_], rfl⟩, fun φ hφ => hsub (Or.inl ⟨φ, hφ, rfl⟩)⟩,
    hs', imgOk_ext himg, ht.trans (List.suffix_cons _ _), himgt, fun Φ hΦ => ?_⟩
  exact hsub (Or.inr ⟨Φ, hΦ, rfl⟩)

end Step

/-! ## The reverse arrow: cross-arrow preservation -/

omit [ModalSys.NoFour] in
/-- A returning possibility whose body refutes itself is absurd: it is a possibility (`ret_dia`)
    of an existential that nothing satisfies. -/
def Proof.ret_absurd {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
    {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    (U : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1) {u : ℕ} (hu : Γ.RootFresh (.free u))
    (p : Proof σ Γ Δ (WFF.ret hS t (WFF.and (WFF.neg U) U))) : Proof σ Γ Δ .bot := by
  have hd := Proof.ret_dia hS .nec t _ p
  have q : Proof σ Γ.boxIn [] (WFF.neg (WFF.ex (.VTypeBox A) (WFF.and (WFF.neg U) U))) := by
    refine Proof.imp_intro (Proof.ex_elim u (.VTypeBox A) hu.boxIn
      (φ := WFF.openFree u hu.boxIn Ctx.NoSlots.slots (WFF.and (WFF.neg U) U)) (ψ := .bot)
      (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
        (Proof.lookup List.mem_cons_self)) ?_)
    exact Proof.imp_elim (Proof.and_elim_l (Proof.lookup List.mem_cons_self))
      (Proof.and_elim_r (Proof.lookup List.mem_cons_self))
  exact Proof.imp_elim hd
    (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.K_box (Δ := []) q))

omit [ModalSys.NoFour] in
/-- Weakening `ret_unit`'s conjunct weakens its object. -/
theorem WFF.mono_unitBody {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ')
    (hS : ModalSys.BStrong = true) {C A : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF.mono (h.boxIn.insert (.bnd 0) (.VTypeBox C)) (WFF.unitBody hS sb θ) =
      WFF.unitBody hS (Term.mono h.boxIn sb) θ := by
  unfold WFF.unitBody
  refine WFF.ret_congr' hS ?_ ?_
  · change Term.mono _ (Term.mono _ sb) = Term.mono _ (Term.mono _ sb)
    rw [Term.mono_mono, Term.mono_mono]
  · rw [WFF.mono_holeAt _ _ ((((Ctx.NoSlots.slots (Γ := Γ'.boxIn)).insert _).boxIn).insert _)]
    change WFF.holeAt _ (Term.pair (Term.mono _ (Term.eta _ _ _)) (Term.mono _ (Term.eta _ _ _)))
      θ = _
    rw [Term.mono_eta, Term.mono_eta]

/-- ⭐`ret_unit`'s conjunct at the reverse arrow's items, read at the forward arrow's source, is the
    reverse arrow's returning possibility: its object is the reverse images' tuple
    (`subst_arrow_tupT`), and its body is `Φ` (`holeAt_tupT_pack2`). -/
theorem liftBody_unitBody {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) (hS : ModalSys.BStrong = true)
    (Φ : WFF σ ((ctxOf cls).boxIn.insert (.bnd 0) (.VTypeBox (bcT clt))) 1) :
    liftBody hs himgt (WFF.unitBody (Γ := ctxOf clt) hS (tupT clt).2
        (pack2 cls (.VTypeBox (bcT clt)) Φ)) =
      WFF.ret hS (tupImgT clt imgt himgt).2
        (WFF.mono ((ctxOf_le_of_suffix hs).boxIn.insert (.bnd 0) _) Φ) := by
  unfold liftBody WFF.unitBody
  refine WFF.ret_congr hS ?_ ?_
  · rw [Term.subst_mono]
    refine (Term.subst_congr _ (arrowS σ (ctxOf lv) imgt) _ (ok_arrowS himgt) _
      (coh_arrowS himgt) ?_ _).trans (subst_arrow_tupT clt himgt)
    refine Subst.sim_of fun v T _ hv => ?_
    obtain ⟨u, rfl, _⟩ := boxIn_item hv
    rw [Subst.set_ne _ _ (fun h => by cases h)]
    exact .refl _
  · rw [WFF.subst_holeAt]
    refine (WFF.holeAt_congr _ ?_ _).trans (holeAt_tupT_pack2 (ctxOf_le_of_suffix hs).boxIn Φ)
    refine sig_pair ?_ ?_
    · refine (Term.subst_eta_tm _ _ _ _ _ _
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf lv).boxIn)).root _)
          (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2)) ?_).trans ?_
      · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
          Subst.box_at_inner_boxtm _ (by
            change Subst.set _ _ _ (.root (.bnd 0)) = _
            exact Subst.set_root _ _ _)]
        rfl
      · rw [Term.mono_mono]
    · exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ _ _ _ _)

/-- ⭐**Cross-arrow preservation**: committing the source's next root along the forward arrow keeps
    the reverse arrow's invariant, over the extended list.  Were the reverse arrow's returning
    possibility for `Φ` to fail at the source, its negation would be a body over the forward
    arrow's roots (`liftBody_unitBody`), so the grown target would have `◇[d ↦ y] ¬U`; `Φ`, read
    there, is `θ(y, □sb)` (`holeRead_tupImgT_pack2`), and `ret_unit` gives `◇[d ↦ y](¬U ∧ U)`,
    which is absurd (`Proof.ret_absurd`). -/
theorem retStep_rev (hS : ModalSys.BStrong = true) {ts tt : NodeSt σ} {cl clt : List VarType}
    {img imgt : ℕ → ℕ} (hs' : (nextTy ts.l cl :: cl) <:+ ts.l)
    (himgt : ImgOk clt (ctxOf ts.l) imgt) (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M) (hinv : RetInv hS ts tt cl img clt imgt) :
    RetInv hS (retStep hS hs' himgt himg ht) ts clt imgt (nextTy ts.l cl :: cl)
      (extImg img cl.length tt.l.length) := by
  obtain ⟨_, _, _, _, h⟩ := hinv
  obtain ⟨hsub, hmcs⟩ := complete_spec (retSet_consistent hS hs' himgt himg ht hv hw h)
  have ht' : clt <:+ (nextTy ts.l cl).bc :: tt.l := ht.trans (List.suffix_cons _ _)
  refine ⟨ht', himgt, hs', imgOk_ext himg, fun Φ hΦ => ?_⟩
  by_contra hn
  have hneg := hv.neg_mem_iff.mpr hn
  have hΨ : liftBody hs' himgt (WFF.neg (WFF.unitBody (Γ := ctxOf clt) hS (tupT clt).2
      (pack2 (nextTy ts.l cl :: cl) (.VTypeBox (bcT clt)) Φ))) ∈ ts.M := by
    change WFF.neg (liftBody hs' himgt _) ∈ ts.M
    rw [liftBody_unitBody]
    exact hneg
  have hret := hsub (Or.inr ⟨_, hΨ, rfl⟩)
  have p₁ : Proof σ (ctxOf ((nextTy ts.l cl).bc :: tt.l))
      [retAtom hS himg ht (WFF.neg (WFF.unitBody (Γ := ctxOf clt) hS (tupT clt).2
        (pack2 (nextTy ts.l cl :: cl) (.VTypeBox (bcT clt)) Φ)))]
      (WFF.ret hS (tupImgT (nextTy ts.l cl :: cl) (extImg img cl.length tt.l.length)
          (imgOk_ext himg)).2
        (WFF.neg (WFF.unitBody hS (Term.mono (ctxOf_le_of_suffix ht').boxIn (tupT clt).2)
          (pack2 (nextTy ts.l cl :: cl) (.VTypeBox (bcT clt)) Φ)))) := by
    refine Proof.conv ?_ (Proof.lookup List.mem_cons_self)
    unfold retAtom
    refine congrArg (WFF.ret hS _) ?_
    change WFF.imp (WFF.mono _ _) .bot = _
    rw [WFF.mono_unitBody (ctxOf_le_of_suffix ht')]
  have p₂ : Proof σ (ctxOf ((nextTy ts.l cl).bc :: tt.l))
      [liftBody ht' (imgOk_ext himg) Φ]
      (WFF.holeRead (Term.pair (tupImgT (nextTy ts.l cl :: cl)
          (extImg img cl.length tt.l.length) (imgOk_ext himg)).2
        (Term.boxtm (Term.mono (ctxOf_le_of_suffix ht').boxIn (tupT clt).2)))
        (pack2 (nextTy ts.l cl :: cl) (.VTypeBox (bcT clt)) Φ)) :=
    Proof.conv (holeRead_tupImgT_pack2 (imgOk_ext himg) _ Φ).symm
      (Proof.lookup List.mem_cons_self)
  have p₃ : Proof σ (ctxOf ((nextTy ts.l cl).bc :: tt.l))
      [retAtom hS himg ht (WFF.neg (WFF.unitBody (Γ := ctxOf clt) hS (tupT clt).2
        (pack2 (nextTy ts.l cl :: cl) (.VTypeBox (bcT clt)) Φ))),
        liftBody ht' (imgOk_ext himg) Φ] .bot :=
    Proof.ret_absurd hS _ _ (ctxOf_fresh (l := (nextTy ts.l cl).bc :: tt.l) le_rfl)
    (Proof.ret_unit hS .nec _ _ _ _
      (Proof.ofSubset (fun x hx => by
        rw [List.mem_singleton.mp hx]; exact List.mem_cons_self) p₁)
      (Proof.ofSubset (fun x hx => by
        rw [List.mem_singleton.mp hx]; exact List.mem_cons_of_mem _ List.mem_cons_self) p₂))
  refine hmcs.1 ⟨_, fun x hx => ?_, ⟨p₃⟩⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hret
  · rw [List.mem_singleton.mp hx]
    exact hΦ

/-! ## Birth: an arrow with nothing committed -/

/-- `liftBody` is the body sent along the reverse arrow under the slot, instantiated at the
    committed roots' necessary object. -/
theorem liftBody_eq_instantiate {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) (Φ : WFF σ (bodyCtx cls clt) 1) :
    liftBody hs himgt Φ = WFF.instantiate Ctx.NoSlots.slots
      (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2))
      (WFF.subst (VarSymb.shiftSlot (arrowIdx imgt) 0 0)
        ((arrowS σ (ctxOf lv) imgt).under 0 0 _ (Ctx.NoSlots.slots (Γ := ctxOf lv)).root)
        (Subst.ok_under (ok_arrowS himgt) _ (Ctx.NoSlots.slots (Γ := ctxOf lv)).root)
        (Subst.coh_under (ok_arrowS himgt) (coh_arrowS himgt) Ctx.NoSlots.slots _
          (Ctx.NoSlots.slots (Γ := ctxOf lv)).root)
        ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).insert _)
        ((Ctx.NoSlots.slots (Γ := ctxOf lv)).insert _) Φ) := by
  unfold WFF.instantiate WFF.substRoot liftBody
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
  · obtain ⟨u, rfl, hu⟩ := body_item hlp hv hvr
    obtain ⟨r, hr, _, _⟩ := ref_rt hu
    dsimp only [Subst.comp, Subst.under]
    rw [Subst.set_ne _ _ hvr, if_neg hvr]
    change SubE.Sim T (.ren (itemImg imgt u)) ((Subst.single _ _).at (itemImg imgt u))
    rw [Subst.single_at_ne (by rw [itemAt_rt, hr]; exact fun h => by cases h)]
    exact .refl _

/-- ⭐**An arrow with nothing committed has the invariant**, given the reverse arrow's transfer:
    a body true at `v`, its item a unit, is `◇∃d. Φ` at `w` — or else `□¬∃d. Φ` at `w` would
    transfer to `¬∃d. Φ` at `v` — and `ret_new` names the unit return. -/
theorem RetInv.nil (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true) {tv tw : NodeSt σ}
    {clt : List VarType} {imgs imgt : ℕ → ℕ} (hv : Theory.IsMCS tv.M) (hw : Theory.IsMCS tw.M)
    (ht : clt <:+ tw.l) (himgt : ImgOk clt (ctxOf tv.l) imgt)
    (htr : Transfer tw.M clt (ctxOf_le_of_suffix ht) tv.M imgt himgt) :
    RetInv hS tv tw [] imgs clt imgt := by
  refine ⟨List.nil_suffix, fun r hr => absurd hr (Nat.not_lt_zero r), ht, himgt,
    fun Φ hΦ => ?_⟩
  by_contra hn
  have hbox : WFF.mono (ctxOf_le_of_suffix ht)
      (.box (WFF.neg (WFF.ex (.VTypeBox (bcT [])) Φ))) ∈ tw.M := by
    by_contra hb
    have hd := hw.neg_mem_iff.mpr hb
    apply hn
    refine hw.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hd, ⟨?_⟩⟩
    exact Proof.ret_new hS hB .nec _ tw.l.length (ctxOf_fresh le_rfl)
      (Proof.lookup List.mem_cons_self) (Proof.lookup List.mem_cons_self)
  have hneg := htr _ hbox
  refine hv.1 ⟨[_, _], fun x hx => ?_, ⟨Proof.imp_elim (Proof.lookup List.mem_cons_self)
    (Proof.ex_intro _ _ (Proof.conv (liftBody_eq_instantiate List.nil_suffix himgt Φ)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))))⟩⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hneg
  · rw [List.mem_singleton.mp hx]
    exact hΦ

/-! ## `ret_unit`'s base form -/

omit [ModalSys.NoFour] in
theorem pairHole_snd_ref {C A : VarType} :
    (Ctx.empty.insert (.bnd 0) (.VTypeProd C A)).ref (.step (.root (.bnd 0)) .snd) = some A := by
  simp only [Ctx.ref, Step.isProj, if_true]
  rfl

omit [ModalSys.NoFour] in
/-- A hole formula read at the second component of a pair hole. -/
def WFF.holeSnd {C A : VarType} (θ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C A)) 1 :=
  WFF.holeAt (Ctx.slotsFrom_empty.insert _)
    (Term.eta (.step (.root (.bnd 0)) .snd) A pairHole_snd_ref) θ

omit [ModalSys.NoFour] in
/-- `holeSnd θ` read at a pair is `θ` read at its second component. -/
theorem WFF.holeAt_pair_holeSnd {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {C A : VarType}
    {c : Ann C} {a : Ann A} (s : Term σ Γ C c) (t : Term σ Γ A a)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) :
    WFF.holeAt hs (Term.pair s t) (WFF.holeSnd (C := C) θ) = WFF.holeAt hs t θ := by
  unfold WFF.holeSnd
  change WFF.subst _ _ _ _ _ hs (WFF.holeAt (Ctx.slotsFrom_empty.insert _) _ θ) = _
  rw [WFF.subst_holeAt]
  refine WFF.holeAt_congr _ ?_ θ
  refine Term.subst_eta_tm _ _ _ _ _ _ t ?_
  rw [Subst.at_proj _ _ rfl]
  change SubE.proj (Subst.single (.bnd 0) _ (.root (.bnd 0))) .snd = _
  rw [show Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm (Term.pair s t)) (.root (.bnd 0)) =
    .tm (Term.pair s t) from if_pos rfl]
  rfl

omit [ModalSys.NoFour] in
/-- Instantiating the unused slot of `unitBody hS sb (holeSnd θ)` gives `◇[d ↦ sb] θ(d)`. -/
theorem WFF.instantiate_unitBody_holeSnd {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    {C A : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeBox A)) 1) {c : Ann (.VTypeBox C)}
    (t : Term σ Γ.boxIn (.VTypeBox C) c) :
    WFF.instantiate Ctx.NoSlots.slots t (WFF.unitBody hS sb (WFF.holeSnd (C := C) θ)) =
      WFF.ret hS sb (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).insert _)
        (Term.eta (.root (.bnd 0)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd 0) _)) θ) := by
  unfold WFF.unitBody
  rw [WFF.holeAt_pair_holeSnd]
  unfold WFF.instantiate WFF.substRoot
  refine WFF.ret_congr hS ?_ ?_
  · rw [Term.subst_mono]
    refine (Term.subst_congr _ (Subst.idS σ _) _ (Subst.ok_idS_le (Ctx.Le.refl _)) _
      (Subst.coh_idS_le (Ctx.Le.refl _)) ?_ sb).trans
      ((Term.subst_idS_mono (Ctx.Le.refl _) _ _ sb).trans (by rw [Term.mono_refl]))
    refine Subst.sim_of fun v T _ hv => ?_
    have hvr : v ≠ .root (.bnd 0) := fun h => by
      subst h
      rw [(Ctx.NoSlots.slots (Γ := Γ.boxIn)).root] at hv
      cases hv
    change SubE.Sim T (if v = .root (.bnd 0) then _ else _) _
    rw [if_neg hvr]
    exact .refl _
  · rw [WFF.subst_holeAt]
    refine WFF.holeAt_congr _ ?_ θ
    exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ _ _ _ _)

omit [ModalSys.NoFour] in
/-- ⭐**`ret_unit`'s base form**: what holds of `□sb` holds, necessarily, of `sb`'s returns
    (`◇[d ↦ sb] θ(d)` at every successor). Otherwise some successor has a unit `d₁` refuting the
    unit conjunct at `holeSnd θ` (J3); `ret_new` names that unit's return `c`, and `ret_unit` at
    `c` asserts the very conjunct its body refutes. -/
def Proof.ret_unit_base {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)}
    (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true) {A : VarType} {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeBox A)) 1)
    (p : Proof σ Γ Δ (WFF.holeRead (Term.boxtm sb) θ)) :
    Proof σ Γ Δ (WFF.box (WFF.ret hS sb
      (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).insert _)
        (Term.eta (.root (.bnd 0)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd 0) _)) θ))) := by
  refine Proof.byContra ?_
  have q : Proof σ Γ.boxIn
      [WFF.neg (WFF.ex (.VTypeBox .VTypeOne)
        (WFF.neg (WFF.unitBody hS sb (WFF.holeSnd (C := .VTypeOne) θ))))]
      (WFF.ret hS sb (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).insert _)
        (Term.eta (.root (.bnd 0)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd 0) _)) θ)) := by
    refine Proof.byContra (Proof.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.ex_intro _ (Term.boxtm Term.unit) (Proof.conv ?_ (Proof.lookup List.mem_cons_self))))
    exact congrArg WFF.neg
      (WFF.instantiate_unitBody_holeSnd hS sb θ (Term.boxtm Term.unit)).symm
  have hd : Proof σ Γ (_ :: Δ) ((OutLeg.nec : OutLeg Γ).dia (WFF.ex (.VTypeBox .VTypeOne)
      (WFF.neg (WFF.unitBody hS sb (WFF.holeSnd (C := .VTypeOne) θ))))) :=
    Proof.imp_intro (Proof.imp_elim
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.ofSubset (fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_self)
        (Proof.K_box q)))
  refine Proof.ret_new hS hB .nec _ _ (Ctx.Presented.fresh_bound _ le_rfl) hd ?_
  have hle := Ctx.le_insert (Ctx.Presented.fresh_bound (Γ := Γ) _ le_rfl).root .VTypeOne
  have r₁ : Proof σ (Γ.insert (.free (Ctx.Presented.bound Γ)) .VTypeOne)
      [WFF.ret hS (Term.eta (.root (.free (Ctx.Presented.bound Γ))) _ (Ctx.ref_insert_root _ _ _))
        (WFF.mono (hle.boxIn.insert (.bnd 0) _)
          (WFF.neg (WFF.unitBody hS sb (WFF.holeSnd (C := .VTypeOne) θ))))]
      (WFF.ret hS (Term.eta (.root (.free (Ctx.Presented.bound Γ))) _ (Ctx.ref_insert_root _ _ _))
        (WFF.neg (WFF.unitBody hS (Term.mono hle.boxIn sb) (WFF.holeSnd (C := .VTypeOne) θ)))) := by
    refine Proof.conv ?_ (Proof.lookup List.mem_cons_self)
    refine congrArg (WFF.ret hS _) ?_
    change WFF.imp (WFF.mono _ _) .bot = _
    rw [WFF.mono_unitBody hle]
  have r₂ : Proof σ (Γ.insert (.free (Ctx.Presented.bound Γ)) .VTypeOne) (Δ.map (WFF.mono hle))
      (WFF.holeRead (Term.pair
          (Term.eta (.root (.free (Ctx.Presented.bound Γ))) _ (Ctx.ref_insert_root _ _ _))
        (Term.boxtm (Term.mono hle.boxIn sb))) (WFF.holeSnd (C := .VTypeOne) θ)) := by
    refine Proof.conv ?_ (Proof.mono hle p)
    rw [WFF.holeRead_eq_holeAt, WFF.holeRead_eq_holeAt, WFF.mono_holeAt _ _ Ctx.NoSlots.slots,
      WFF.holeAt_pair_holeSnd]
    rfl
  exact Proof.ret_absurd hS _ _ (Ctx.Presented.fresh_bound _ le_rfl) (Proof.ret_unit hS .nec _ _ _ _
    (Proof.ofSubset (fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_self) r₁)
    (Proof.ofSubset (fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)) r₂))

omit [ModalSys.NoFour] in
/-- Reading a hole formula built at `⟨(), d⟩` at `t` reads the original at `⟨(), t⟩`. -/
theorem WFF.holeAt_holeAt_pairUnit {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {U : VarType}
    {a : Ann U} (t : Term σ Γ U a)
    (P : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd .VTypeOne U)) 1) :
    WFF.holeAt hs t (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Ctx.empty)).insert U)
      (Term.pair Term.unit (Term.eta (.root (.bnd 0)) U (Ctx.ref_insert_root _ (.bnd 0) U))) P) =
      WFF.holeAt hs (Term.pair Term.unit t) P := by
  change WFF.subst _ _ _ _ _ hs (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Ctx.empty)).insert U) _ P) = _
  rw [WFF.subst_holeAt]
  refine WFF.holeAt_congr _ (sig_pair rfl ?_) P
  exact Term.subst_eta_tm _ _ _ _ _ _ t (by
    change Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm t) (.root (.bnd 0)) = _
    exact if_pos rfl)

/-- ⭐**The forward arrow at birth has the invariant**: with nothing committed back, a body true
    at the parent of the committed roots' necessary object is, by `ret_unit_base`, necessarily a
    returning possibility from their tuple — which the arrow's transfer sends to the child. -/
theorem RetInv.birth (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true) {tv tw : NodeSt σ}
    {cls : List VarType} {imgs imgt : ℕ → ℕ} (hv : Theory.IsMCS tv.M) (hs : cls <:+ tv.l)
    (himgs : ImgOk cls (ctxOf tw.l) imgs)
    (htr : Transfer tv.M cls (ctxOf_le_of_suffix hs) tw.M imgs himgs) :
    RetInv hS tv tw cls imgs [] imgt := by
  have himgt : ImgOk [] (ctxOf tv.l) imgt := fun r hr => absurd hr (Nat.not_lt_zero r)
  refine ⟨hs, himgs, List.nil_suffix, himgt, fun Φ hΦ => ?_⟩
  have hle := ctxOf_le_of_suffix hs
  have hread : WFF.holeRead (Term.boxtm (Term.mono hle.boxIn (tupT cls).2))
      (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Ctx.empty)).insert _)
        (Term.pair Term.unit (Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)))
        (pack2 [] (.VTypeBox (bcT cls)) Φ)) = liftBody hs himgt Φ := by
    rw [WFF.holeRead_eq_holeAt, WFF.holeAt_holeAt_pairUnit, ← WFF.holeRead_eq_holeAt]
    exact holeRead_tupImgT_pack2 himgt _ Φ
  have hbox := hv.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hΦ,
    ⟨Proof.ret_unit_base hS hB _ _ (Proof.conv hread.symm (Proof.lookup List.mem_cons_self))⟩⟩
  have hbox' : WFF.mono hle (.box (WFF.ret hS (tupT cls).2
      (WFF.holeAt ((Ctx.NoSlots.slots (Γ := (ctxOf cls).boxIn.boxIn)).insert _)
        (Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _))
        (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Ctx.empty)).insert _)
          (Term.pair Term.unit (Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)))
          (pack2 [] (.VTypeBox (bcT cls)) Φ))))) ∈ tv.M := by
    refine (congrArg (· ∈ tv.M) ?_).mpr hbox
    change WFF.box (WFF.ret hS (Term.mono _ _) (WFF.mono _ (WFF.holeAt _ _ _))) = _
    rw [WFF.mono_holeAt _ _ ((Ctx.NoSlots.slots (Γ := (ctxOf tv.l).boxIn.boxIn)).insert _),
      Term.mono_eta]
  refine (congrArg (· ∈ tw.M) ?_).mp (htr _ hbox')
  refine WFF.ret_congr hS (subst_arrow_tupT cls himgs) ?_
  rw [WFF.subst_holeAt]
  refine (WFF.holeAt_congr _ (Term.subst_eta_renAt _ _ _ _ _ _ _
    (Ctx.ref_insert_root _ (.bnd 0) _) (Subst.under_at_slot _ _ _ _ _)) _).trans ?_
  dsimp only [RShape.ty, NShape.ty]
  rw [WFF.holeAt_holeAt_pairUnit]
  exact holeAt_tupT_pack2 (ctxOf_le_of_suffix (List.nil_suffix (l := tw.l))).boxIn Φ

end BArrow

end V12M
