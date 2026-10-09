import QML.QML_v12m_BRetW
import QML.QML_v12m_BNetMono

/-!
# QML v12m — strong B on the network: the invariants and the operations

Under strong B every child's two arrows carry the returning-possibility invariants (docs §11.17):
`RetInv` both ways for a plain child; `RetInvW` forward and `RetInvX` home for a witness child
(`RetData`).  Necessity transfer, and so weak B's `Good`, follows from them (`GoodS.good`).

* `RetData.grow_src`, `RetData.grow_tgt`, ⭐`GoodS.setSt`: growing a node keeps the invariants.
* `realFS`, `realBS`: the realisation steps under strong B grow the target with returning
  possibilities (`retStep`; `retStepW` forward and `retStepX` home for a witness child);
  ⭐`GoodS.realFS`, `GoodS.realBS` by the realisation steps and cross-arrow preservation.
* `GoodS.henk`, ⭐`GoodS.mkChild`: Henkin steps and children are weak B's; a child is born with
  the invariants (`RetData.birth`).
* `netS`, ⭐`goodS_netS`, `ext_netS`: the chain under strong B.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## The way home's necessity transfer along a back witness -/

omit [ModalSys.NoFour] in
/-- A hole formula reading only the first component, read at a pair. -/
theorem WFF.holeAt_holeAt_fst {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {U V : VarType}
    {a : Ann U} {b : Ann V} (s : Term σ Γ U a) (t : Term σ Γ V b)
    (P : WFF σ (Ctx.empty.insert (.bnd 0) U) 1) :
    WFF.holeAt hs (Term.pair s t) (WFF.holeAt
      ((Ctx.NoSlots.slots (Γ := Ctx.empty)).insert (.VTypeProd U V))
      (Term.eta (.step (.root (.bnd 0)) .fst) U (Ctx.ref_fst_of (Ctx.ref_insert_root _ (.bnd 0) _)))
      P) = WFF.holeAt hs s P := by
  change WFF.subst _ _ _ _ _ hs (WFF.holeAt _ _ P) = _
  rw [WFF.subst_holeAt]
  refine WFF.holeAt_congr _ ?_ P
  exact Term.subst_eta_tm _ _ _ _ _ _ s (by
    rw [Subst.at_proj _ _ rfl]
    change (Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm (Term.pair s t)) (.root (.bnd 0))).proj
      .fst = _
    rw [show Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm (Term.pair s t)) (.root (.bnd 0)) =
      .tm (Term.pair s t) from if_pos rfl]
    rfl)

omit [ModalSys.NoFour] in
/-- Weakening the counit's body of a possible part leaves it alone. -/
theorem WFF.mono_counitBodyD {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ') {C X : VarType}
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C X)) 1) :
    WFF.mono (h.boxIn.insert (.bnd 0) (RShape.wit (.box C) X).ty) (WFF.counitBodyD (Γ := Γ) ψ) =
      WFF.counitBodyD (Γ := Γ') ψ := by
  unfold WFF.counitBodyD WFF.boxx
  change WFF.imp (WFF.dia _ _ (WFF.imp (WFF.mono _ (WFF.holeAt _ _ ψ)) WFF.bot)) WFF.bot = _
  rw [WFF.mono_holeAt _ _ (((Ctx.NoSlots.slots (Γ := Γ'.boxIn)).insert _).diaIn _)]
  change WFF.imp (WFF.dia _ _ (WFF.imp (WFF.holeAt _ (Term.pair (Term.mono _ (Term.eta _ _ _))
    (Term.mono _ (Term.eta _ _ _))) ψ) WFF.bot)) WFF.bot = _
  rw [Term.mono_eta, Term.mono_eta]

/-- The counit's body of the possible part, read at the source of a witness arrow: `□_x` of the
    hole formula at the committed roots' items and `x`'s content. -/
theorem liftBodyW_counitBodyD {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X))
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (bcT cls) X)) 1) :
    liftBodyW hs himgt hx (WFF.counitBodyD (Γ := ctxOf clt) ψ) =
      WFF.boxx x ⟨X, (ctxOf_le_of_suffix hs).ref hx⟩ (WFF.holeAt Ctx.NoSlots.slots
        (Term.pair (Term.mono (Ctx.le_boxIn_diaIn _ x)
            (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2))
          (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of ((ctxOf_le_of_suffix hs).ref hx)))) ψ) := by
  have hle := ctxOf_le_of_suffix hs
  have hu := Ctx.ref_insert_root (ctxOf clt).boxIn (.bnd 0)
    (RShape.wit (.box (bcT cls)) X).ty
  have hsnd := Ctx.ref_snd_of hu
  have hθ : Subst.Ok (bodyCtxW cls clt X)
      ((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntryW hs hx)) :=
    Subst.ok_set (ok_arrowS himgt) rfl
  have hc : Subst.Coh (Subst.setIdx (arrowIdx imgt) (.bnd 0) (liftEntryW hs hx))
      (bodyCtxW cls clt X) ((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntryW hs hx)) :=
    Subst.coh_set (ok_arrowS himgt) (coh_arrowS himgt)
      ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).rootFresh (le_refl 0)) rfl
  have hw : (((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntryW hs hx)).at
      (.step (.root (.bnd 0)) .snd)).idxAlong [] = x := rfl
  have hfst : ((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntryW hs hx)).at
      (.step (.root (.bnd 0)) .fst) =
      .tm (Term.boxtm (Term.mono hle.boxIn (tupT cls).2)) := by
    rw [Subst.at_proj _ _ rfl]
    change (Subst.set _ _ _ (.root (.bnd 0))).proj .fst = _
    rw [Subst.set_root]
    rfl
  unfold liftBodyW WFF.counitBodyD WFF.boxx
  change WFF.imp (WFF.subst _ _ _ _ _ _ (WFF.dia _ _ _)) WFF.bot = _
  rw [WFF.subst_dia_at _ _ _ _ _ _ _ _ x rfl ⟨X, hle.ref hx⟩
    ((Ctx.NoSlots.slots (Γ := ctxOf lv)).diaIn x) (Subst.ok_dia hθ ⟨X, hsnd⟩ hw)
    (Subst.coh_dia hθ hc ⟨X, hsnd⟩)]
  refine congrArg (fun φ => WFF.imp (WFF.dia x _ (WFF.imp φ WFF.bot)) WFF.bot) ?_
  rw [WFF.subst_holeAt]
  refine WFF.holeAt_congr _ (sig_pair ?_ ?_) ψ
  · refine Term.subst_eta_tm _ _ _ _ _ _ _ ?_
    rw [Subst.dia_eq_box_mono (Δ₁ := (ctxOf clt).boxIn.insert (.bnd 0) _) _ _ x _ _
        (Ctx.ref_inner (Ctx.ref_fst_of hu)), Subst.box_at_inner_boxtm _ hfst]
    rfl
  · refine Term.subst_eta_tm _ _ _ _ _ _ _ ?_
    rw [Subst.at_nonproj _ rfl]
    dsimp only [Subst.dia]
    rw [if_pos rfl, Subst.at_proj _ _ rfl]
    change SubE.diaBody x ((Subst.set _ _ _ (.root (.bnd 0))).proj .snd) = _
    rw [Subst.set_root]
    change SubE.diaBody x (SubE.tm (Term.diatm x _ (Term.eta (x.step .dia) X _))) = _
    rw [SubE.diaBody_diatm]

/-- ⭐**The witnessed invariant gives necessity transfer**: a necessity about the committed roots,
    packed into the necessary part of a body that ignores the witness, is `□_x`-necessary
    (`box_boxx`), so the counit of the possible part (`ret_counitD`) reads it at the images. -/
theorem RetInvW.transfer {hS : ModalSys.BStrong = true} {tv tw : NodeSt σ}
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cx : ℕ}
    (hv : Theory.IsMCS tv.M) (hw : Theory.IsMCS tw.M)
    (h : RetInvW hS tv tw cls imgs clt imgt x X cx) :
    ∃ (hs : cls <:+ tv.l) (himgs : ImgOk cls (ctxOf tw.l) imgs),
      Transfer tv.M cls (ctxOf_le_of_suffix hs) tw.M imgs himgs := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
  refine ⟨hs, himgs, fun ψ hψ => ?_⟩
  have hle := ctxOf_le_of_suffix hs
  have hret := hinv (WFF.counitBodyD (WFF.holeAt
      ((Ctx.NoSlots.slots (Γ := Ctx.empty)).insert (.VTypeProd (bcT cls) X))
      (Term.eta (.step (.root (.bnd 0)) .fst) (bcT cls)
        (Ctx.ref_fst_of (Ctx.ref_insert_root _ (.bnd 0) _))) (pack cls ψ))) (by
    rw [liftBodyW_counitBodyD, WFF.holeAt_holeAt_fst,
      ← WFF.mono_holeAt _ (Ctx.NoSlots.slots (Γ := (ctxOf tv.l).boxIn)),
      ← WFF.mono_holeAt _ (Ctx.NoSlots.slots (Γ := (ctxOf cls).boxIn)),
      ← WFF.holeRead_eq_holeAt, holeRead_tupT_pack]
    exact hv.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hψ,
      ⟨Proof.box_boxx _ _⟩⟩)
  rw [WFF.mono_counitBodyD (ctxOf_le_of_suffix ht)] at hret
  rw [← holeRead_tupImgT_pack himgs ψ]
  refine hw.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hret, ⟨?_⟩⟩
  refine Proof.conv ?_ (Proof.ret_counitD hS _ _ (Proof.lookup List.mem_cons_self))
  rw [WFF.holeRead_eq_holeAt]
  exact (WFF.holeAt_holeAt_fst _ _ _ _).trans (WFF.holeRead_eq_holeAt _ _).symm

/-- ⭐The returning-possibility invariants of a child's arrows `p → k` and `k → p`: `RetInv` both
    ways for a plain child; `RetInvW` out along `x` and `RetInvX` home for a witness child; and for
    a back-witness child (`bkd = (e, X)`, its way home in `e`'s extent), the mirror: `RetInvX` out,
    along `e` read at the child, and `RetInvW` home. -/
def RetData (hS : ModalSys.BStrong = true) (tp tk : NodeSt σ)
    (kind bkd : Option (VarSymb × VarType)) (cx : ℕ) (fcl : List VarType) (fimg : ℕ → ℕ)
    (bcl : List VarType) (bimg : ℕ → ℕ) : Prop :=
  match kind, bkd with
  | some (x, X), _ =>
      RetInvW hS tp tk fcl fimg bcl bimg x X cx ∧ RetInvX hS tk tp bcl bimg fcl fimg x X cx
  | none, none => RetInv hS tp tk fcl fimg bcl bimg ∧ RetInv hS tk tp bcl bimg fcl fimg
  | none, some (e, X) =>
      RetInvX hS tp tk fcl fimg bcl bimg e X cx ∧ RetInvW hS tk tp bcl bimg fcl fimg e X cx

namespace RetData

variable {hS : ModalSys.BStrong = true} {tp tk : NodeSt σ} {kind bkd : Option (VarSymb × VarType)}
  {cx : ℕ} {fcl : List VarType} {fimg : ℕ → ℕ} {bcl : List VarType} {bimg : ℕ → ℕ}

/-- The forward arrow's transfer. -/
theorem fwd (hp : Theory.IsMCS tp.M) (hk : Theory.IsMCS tk.M)
    (h : RetData hS tp tk kind bkd cx fcl fimg bcl bimg) : FwdData tp tk kind cx fcl fimg := by
  cases kind with
  | none =>
      cases bkd with
      | none =>
          obtain ⟨hs, himgs, htr⟩ := RetInv.transfer hk h.1
          exact ⟨hs, himgs, htr⟩
      | some eX =>
          obtain ⟨e, X⟩ := eX
          obtain ⟨hs, himgs, htr⟩ := RetInvX.transfer hk h.1
          exact ⟨hs, himgs, htr⟩
  | some xX =>
      obtain ⟨x, X⟩ := xX
      obtain ⟨ht, himgt, hx, hcx, htr⟩ := RetInvX.transferX hS hk hp h.2
      exact ⟨ht, himgt, hx, hcx, htr⟩

/-- The back arrow's transfer. -/
theorem back (hp : Theory.IsMCS tp.M) (hk : Theory.IsMCS tk.M)
    (h : RetData hS tp tk kind bkd cx fcl fimg bcl bimg) : BackData tk tp bcl bimg := by
  cases kind with
  | none =>
      cases bkd with
      | none =>
          obtain ⟨hs, himgs, htr⟩ := RetInv.transfer hp h.2
          exact ⟨hs, himgs, htr⟩
      | some eX =>
          obtain ⟨e, X⟩ := eX
          obtain ⟨hs, himgs, htr⟩ := RetInvW.transfer hk hp h.2
          exact ⟨hs, himgs, htr⟩
  | some xX =>
      obtain ⟨x, X⟩ := xX
      obtain ⟨hs, himgs, htr⟩ := RetInvX.transfer hp h.2
      exact ⟨hs, himgs, htr⟩

/-- A growing child keeps the invariants. -/
theorem grow_tgt (hk : Theory.IsMCS tk.M) {tk' : NodeSt σ} (hk' : Theory.IsMCS tk'.M)
    (h : RetData hS tp tk kind bkd cx fcl fimg bcl bimg) (hg : Grows tk tk') :
    RetData hS tp tk' kind bkd cx fcl fimg bcl bimg := by
  cases kind with
  | none =>
      cases bkd with
      | none => exact ⟨h.1.grow_tgt hg, h.2.grow_src hk hk' hg⟩
      | some eX =>
          obtain ⟨e, X⟩ := eX
          exact ⟨h.1.grow_tgt hg, h.2.grow_src hk hk' hg⟩
  | some xX =>
      obtain ⟨x, X⟩ := xX
      exact ⟨h.1.grow_tgt hg, h.2.grow_src hk hk' hg⟩

/-- A growing parent keeps the invariants. -/
theorem grow_src (hp : Theory.IsMCS tp.M) {tp' : NodeSt σ} (hp' : Theory.IsMCS tp'.M)
    (h : RetData hS tp tk kind bkd cx fcl fimg bcl bimg) (hg : Grows tp tp') :
    RetData hS tp' tk kind bkd cx fcl fimg bcl bimg := by
  cases kind with
  | none =>
      cases bkd with
      | none => exact ⟨h.1.grow_src hp hp' hg, h.2.grow_tgt hg⟩
      | some eX =>
          obtain ⟨e, X⟩ := eX
          exact ⟨h.1.grow_src hp hp' hg, h.2.grow_tgt hg⟩
  | some xX =>
      obtain ⟨x, X⟩ := xX
      exact ⟨h.1.grow_src hp hp' hg, h.2.grow_tgt hg⟩

end RetData

namespace NetSt

/-- The invariants of the child `k`'s arrows, to and from its parent `p`. -/
def RetOk (hS : ModalSys.BStrong = true) (N : NetSt σ) (k p : Node) : Prop :=
  RetData hS (N.st p) (N.st k) (N.kind k) (N.bkind k) (N.cx k) (N.fcl k) (N.fimg k) (N.bcl k)
    (N.bimg k)

/-- ⭐The invariants of a network under strong B. -/
structure GoodS (hS : ModalSys.BStrong = true) (N : NetSt σ) : Prop where
  mcs : ∀ s, N.Live s → Theory.IsMCS (N.st s).M
  ret : ∀ c p, N.Live (c :: p) → N.RetOk hS (c :: p) p

/-- ⭐Strong B's invariants give weak B's. -/
theorem GoodS.good {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) : N.Good :=
  ⟨hN.mcs, fun c p hk => (hN.ret c p hk).fwd (hN.mcs p hk.1) (hN.mcs _ hk),
    fun c p hk => (hN.ret c p hk).back (hN.mcs p hk.1) (hN.mcs _ hk)⟩

/-- ⭐Growing one live node conservatively keeps the invariants. -/
theorem GoodS.setSt {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {s : Node}
    {t : NodeSt σ} (hs : N.Live s) (hg : Grows (N.st s) t) (ht : Theory.IsMCS t.M) :
    (N.setSt s t).GoodS hS := by
  refine ⟨(hN.good.setSt hs hg ht).mcs, fun c p hk => ?_⟩
  rw [live_setSt] at hk
  have hr := hN.ret c p hk
  unfold RetOk at hr ⊢
  change RetData hS ((N.setSt s t).st p) ((N.setSt s t).st (c :: p)) _ _ _ _ _ _ _
  by_cases hkp : (c :: p : Node) = s
  · subst hkp
    rw [setSt_ne _ _ (fun h => ne_parent c p h.symm), setSt_self]
    exact hr.grow_tgt (hN.mcs _ hk) ht hg
  · rw [setSt_ne _ _ hkp]
    by_cases hps : p = s
    · subst hps
      rw [setSt_self]
      exact hr.grow_src (hN.mcs p hk.1) ht hg
    · rw [setSt_ne _ _ hps]
      exact hr

/-! ## Realising forward -/

open Classical in
/-- The child grown by the image of its parent's next variable, under strong B: the target gains
    returning possibilities (`retStep`, or `retStepW` for a witness child). -/
noncomputable def fwdStepS (hS : ModalSys.BStrong = true) (N : NetSt σ) (k p : Node) :
    NodeSt σ :=
  if h : (N.fcl k).length < (N.st p).l.length ∧ N.fcl k <:+ (N.st p).l ∧
      ImgOk (N.bcl k) (ctxOf (N.st p).l) (N.bimg k) ∧
      ImgOk (N.fcl k) (ctxOf (N.st k).l) (N.fimg k) ∧ N.bcl k <:+ (N.st k).l then
    match N.kind k, N.bkind k with
    | some (x, X), _ =>
        if hX : (ctxOf (N.fcl k)).ref x = some (.VTypeDia X) ∧
            (ctxOf (N.st k).l).ref (.root (.free (N.cx k))) = some X then
          retStepW hS (suffix_next h.2.1 h.1) h.2.2.1 h.2.2.2.1 h.2.2.2.2 hX.1 hX.2
        else N.st k
    | none, none => retStep hS (suffix_next h.2.1 h.1) h.2.2.1 h.2.2.2.1 h.2.2.2.2
    | none, some (e, X) =>
        if hX : (ctxOf (N.bcl k)).ref e = some (.VTypeDia X) ∧
            (ctxOf (N.st p).l).ref (.root (.free (N.cx k))) = some X then
          retStepX hS (suffix_next h.2.1 h.1) h.2.2.1 hX.1 hX.2 h.2.2.2.1 h.2.2.2.2
        else N.st k
  else N.st k

/-- ⭐Give the parent's next variable an image in the child `k`, under strong B. -/
noncomputable def realFS (hS : ModalSys.BStrong = true) (N : NetSt σ) : Node → NetSt σ
  | [] => N
  | c :: p =>
      if (N.fcl (c :: p)).length < (N.st p).l.length then
        (N.setSt (c :: p) (N.fwdStepS hS (c :: p) p)).setFwd (c :: p)
          (nextTy (N.st p).l (N.fcl (c :: p)) :: N.fcl (c :: p))
          (extImg (N.fimg (c :: p)) (N.fcl (c :: p)).length (N.st (c :: p)).l.length)
      else N

theorem fwdStepS_ok {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {c : ℕ}
    {p : Node} (hk : N.Live (c :: p)) (hlt : (N.fcl (c :: p)).length < (N.st p).l.length) :
    Theory.IsMCS (N.fwdStepS hS (c :: p) p).M ∧ Grows (N.st (c :: p)) (N.fwdStepS hS (c :: p) p) ∧
      RetData hS (N.st p) (N.fwdStepS hS (c :: p) p) (N.kind (c :: p)) (N.bkind (c :: p))
        (N.cx (c :: p))
        (nextTy (N.st p).l (N.fcl (c :: p)) :: N.fcl (c :: p))
        (extImg (N.fimg (c :: p)) (N.fcl (c :: p)).length (N.st (c :: p)).l.length)
        (N.bcl (c :: p)) (N.bimg (c :: p)) := by
  have hr := hN.ret c p hk
  have hp := hN.mcs p hk.1
  have hkM := hN.mcs _ hk
  unfold RetOk at hr
  unfold fwdStepS
  generalize N.kind (c :: p) = kd at hr ⊢
  generalize N.bkind (c :: p) = bkd at hr ⊢
  cases kd with
  | none =>
      cases bkd with
      | none =>
          obtain ⟨hF, -⟩ := hr
          obtain ⟨hs, himgs, ht, himgt, -⟩ := id hF
          rw [dif_pos ⟨hlt, hs, himgt, himgs, ht⟩]
          obtain ⟨h₁, h₂, h₃⟩ := retStep_ok hS (suffix_next hs hlt) himgt himgs ht hp hkM hF
          exact ⟨h₁, h₂, h₃, retStep_rev hS (suffix_next hs hlt) himgt himgs ht hp hkM hF⟩
      | some eX =>
          obtain ⟨e, X⟩ := eX
          obtain ⟨hF, -⟩ := hr
          obtain ⟨hs, himgs, ht, himgt, hx, hcx, -⟩ := id hF
          rw [dif_pos ⟨hlt, hs, himgt, himgs, ht⟩]
          dsimp only
          rw [dif_pos ⟨hx, hcx⟩]
          obtain ⟨h₁, h₂, h₃⟩ :=
            retStepX_ok hS (suffix_next hs hlt) himgt hx hcx himgs ht hp hkM hF
          exact ⟨h₁, h₂, h₃,
            retStepX_rev hS (suffix_next hs hlt) himgt hx hcx himgs ht hp hkM hF⟩
  | some xX =>
      obtain ⟨x, X⟩ := xX
      obtain ⟨hW, -⟩ := hr
      obtain ⟨hs, himgs, ht, himgt, hx, hcx, -⟩ := id hW
      rw [dif_pos ⟨hlt, hs, himgt, himgs, ht⟩]
      dsimp only
      rw [dif_pos ⟨hx, hcx⟩]
      obtain ⟨h₁, h₂, h₃⟩ :=
        retStepW_ok hS (suffix_next hs hlt) himgt himgs ht hx hcx hp hkM hW
      exact ⟨h₁, h₂, h₃,
        retStepW_rev hS (suffix_next hs hlt) himgt himgs ht hx hcx hp hkM hW⟩

/-- ⭐Realising forward under strong B preserves the invariants. -/
theorem GoodS.realFS {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {k : Node}
    (hk : N.Live k) : (N.realFS hS k).GoodS hS := by
  match k with
  | [] => exact hN
  | c :: p =>
      simp only [NetSt.realFS]
      split_ifs with hlt
      · obtain ⟨hmcs, hg, hrd⟩ := fwdStepS_ok hN hk hlt
        have hN₁ := hN.setSt hk hg hmcs
        refine ⟨fun s hs => hN₁.mcs s ((live_setFwd _ _ _ _ s).mp hs), fun c' p' hk' => ?_⟩
        rw [live_setFwd] at hk'
        by_cases he : (c' :: p' : Node) = c :: p
        · obtain ⟨rfl, rfl⟩ := List.cons.inj he.symm
          unfold RetOk
          simp only [setFwd, Function.update_self]
          rw [setSt_ne _ _ (fun h => ne_parent c p h.symm), setSt_self]
          exact hrd
        · have := hN₁.ret c' p' hk'
          unfold RetOk at this ⊢
          simp only [setFwd, Function.update_of_ne he]
          exact this
      · exact hN

/-! ## Realising back -/

open Classical in
/-- The parent grown by the image of the child `k`'s next variable, under strong B (`retStep`, or
    `retStepX` along the witness for a witness child). -/
noncomputable def backStepS (hS : ModalSys.BStrong = true) (N : NetSt σ) (k p : Node) :
    NodeSt σ :=
  if h : (N.bcl k).length < (N.st k).l.length ∧ N.bcl k <:+ (N.st k).l ∧
      ImgOk (N.fcl k) (ctxOf (N.st k).l) (N.fimg k) ∧
      ImgOk (N.bcl k) (ctxOf (N.st p).l) (N.bimg k) ∧ N.fcl k <:+ (N.st p).l then
    match N.kind k, N.bkind k with
    | some (x, X), _ =>
        if hX : (ctxOf (N.fcl k)).ref x = some (.VTypeDia X) ∧
            (ctxOf (N.st k).l).ref (.root (.free (N.cx k))) = some X then
          retStepX hS (suffix_next h.2.1 h.1) h.2.2.1 hX.1 hX.2 h.2.2.2.1 h.2.2.2.2
        else N.st p
    | none, none => retStep hS (suffix_next h.2.1 h.1) h.2.2.1 h.2.2.2.1 h.2.2.2.2
    | none, some (e, X) =>
        if hX : (ctxOf (N.bcl k)).ref e = some (.VTypeDia X) ∧
            (ctxOf (N.st p).l).ref (.root (.free (N.cx k))) = some X then
          retStepW hS (suffix_next h.2.1 h.1) h.2.2.1 h.2.2.2.1 h.2.2.2.2 hX.1 hX.2
        else N.st p
  else N.st p

/-- ⭐Give the child `k`'s next variable an image in its parent, under strong B. -/
noncomputable def realBS (hS : ModalSys.BStrong = true) (N : NetSt σ) : Node → NetSt σ
  | [] => N
  | c :: p =>
      if (N.bcl (c :: p)).length < (N.st (c :: p)).l.length then
        (N.setSt p (N.backStepS hS (c :: p) p)).setBack (c :: p)
          (nextTy (N.st (c :: p)).l (N.bcl (c :: p)) :: N.bcl (c :: p))
          (extImg (N.bimg (c :: p)) (N.bcl (c :: p)).length (N.st p).l.length)
      else N

theorem backStepS_ok {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {c : ℕ}
    {p : Node} (hk : N.Live (c :: p))
    (hlt : (N.bcl (c :: p)).length < (N.st (c :: p)).l.length) :
    Theory.IsMCS (N.backStepS hS (c :: p) p).M ∧ Grows (N.st p) (N.backStepS hS (c :: p) p) ∧
      RetData hS (N.backStepS hS (c :: p) p) (N.st (c :: p)) (N.kind (c :: p))
        (N.bkind (c :: p)) (N.cx (c :: p))
        (N.fcl (c :: p)) (N.fimg (c :: p))
        (nextTy (N.st (c :: p)).l (N.bcl (c :: p)) :: N.bcl (c :: p))
        (extImg (N.bimg (c :: p)) (N.bcl (c :: p)).length (N.st p).l.length) := by
  have hr := hN.ret c p hk
  have hp := hN.mcs p hk.1
  have hkM := hN.mcs _ hk
  unfold RetOk at hr
  unfold backStepS
  generalize N.kind (c :: p) = kd at hr ⊢
  generalize N.bkind (c :: p) = bkd at hr ⊢
  cases kd with
  | none =>
      cases bkd with
      | none =>
          obtain ⟨-, hB⟩ := hr
          obtain ⟨hs, himgs, ht, himgt, -⟩ := id hB
          rw [dif_pos ⟨hlt, hs, himgt, himgs, ht⟩]
          obtain ⟨h₁, h₂, h₃⟩ := retStep_ok hS (suffix_next hs hlt) himgt himgs ht hkM hp hB
          exact ⟨h₁, h₂, retStep_rev hS (suffix_next hs hlt) himgt himgs ht hkM hp hB, h₃⟩
      | some eX =>
          obtain ⟨e, X⟩ := eX
          obtain ⟨-, hW⟩ := hr
          obtain ⟨hs, himgs, ht, himgt, hx, hcx, -⟩ := id hW
          rw [dif_pos ⟨hlt, hs, himgt, himgs, ht⟩]
          dsimp only
          rw [dif_pos ⟨hx, hcx⟩]
          obtain ⟨h₁, h₂, h₃⟩ :=
            retStepW_ok hS (suffix_next hs hlt) himgt himgs ht hx hcx hkM hp hW
          exact ⟨h₁, h₂,
            retStepW_rev hS (suffix_next hs hlt) himgt himgs ht hx hcx hkM hp hW, h₃⟩
  | some xX =>
      obtain ⟨x, X⟩ := xX
      obtain ⟨-, hX⟩ := hr
      obtain ⟨hs, himgs, ht, himgt, hx, hcx, -⟩ := id hX
      rw [dif_pos ⟨hlt, hs, himgt, himgs, ht⟩]
      dsimp only
      rw [dif_pos ⟨hx, hcx⟩]
      obtain ⟨h₁, h₂, h₃⟩ :=
        retStepX_ok hS (suffix_next hs hlt) himgt hx hcx himgs ht hkM hp hX
      exact ⟨h₁, h₂,
        retStepX_rev hS (suffix_next hs hlt) himgt hx hcx himgs ht hkM hp hX, h₃⟩

/-- ⭐Realising back under strong B preserves the invariants. -/
theorem GoodS.realBS {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {k : Node}
    (hk : N.Live k) : (N.realBS hS k).GoodS hS := by
  match k with
  | [] => exact hN
  | c :: p =>
      simp only [NetSt.realBS]
      split_ifs with hlt
      · obtain ⟨hmcs, hg, hrd⟩ := backStepS_ok hN hk hlt
        have hN₁ := hN.setSt hk.1 hg hmcs
        refine ⟨fun s hs => hN₁.mcs s ((live_setBack _ _ _ _ s).mp hs), fun c' p' hk' => ?_⟩
        rw [live_setBack] at hk'
        by_cases he : (c' :: p' : Node) = c :: p
        · obtain ⟨rfl, rfl⟩ := List.cons.inj he.symm
          unfold RetOk
          simp only [setBack, Function.update_self]
          rw [setSt_ne _ _ (ne_parent c p), setSt_self]
          exact hrd
        · have := hN₁.ret c' p' hk'
          unfold RetOk at this ⊢
          simp only [setBack, Function.update_of_ne he]
          exact this
      · exact hN

/-! ## Henkin witnesses -/

/-- A Henkin step leaves the network or grows the node. -/
theorem henk_cases {N : NetSt σ} {s : Node} (hM : Theory.IsMCS (N.st s).M) (P : NetSt σ → Prop)
    (hP : P N)
    (hset : ∀ t, Grows (N.st s) t → Theory.IsMCS t.M → P (N.setSt s t))
    (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : P (N.henk s o) := by
  obtain ⟨l, φ⟩ := o
  simp only [NetSt.henk]
  split_ifs with h
  · split
    · split_ifs with hmem
      · obtain ⟨h₁, h₂⟩ := henk_grow hM (Theory.Derives.of_mem hmem)
        exact hset _ h₂ h₁
      · exact hP
    · rename_i A ψ
      split_ifs with hmem
      · have hex : Theory.Derives (N.st s).M
            (.ex A (WFF.mono ((ctxOf_le_of_suffix h).insert _ A) ψ).neg) :=
          ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hmem,
            ⟨Proof.exNeg_of_negAll _⟩⟩
        obtain ⟨h₁, h₂⟩ := henk_grow hM hex
        exact hset _ h₂ h₁
      · exact hP
    · exact hP
  · exact hP

/-- ⭐Henkin witnesses preserve the invariants under strong B. -/
theorem GoodS.henk {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {s : Node}
    (hs : N.Live s) (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : (N.henk s o).GoodS hS :=
  henk_cases (hN.mcs s hs) (·.GoodS hS) hN (fun _ hg ht => hN.setSt hs hg ht) o

/-! ## Children -/

/-- ⭐**Birth**: a new child's arrows, with all the parent's variables committed forward and none
    back, carry the invariants — from the seed's transfer (`RetInv.birth`, `RetInv.nil`;
    `RetInvW.birth`, `RetInvX.nil`). -/
theorem RetData.birth (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true) {tp tk : NodeSt σ}
    {kd : Option (VarSymb × VarType)} {cx : ℕ} (hp : Theory.IsMCS tp.M)
    (hk : Theory.IsMCS tk.M) (hf : FwdData tp tk kd cx tp.l id) :
    RetData hS tp tk kd none cx tp.l id [] id := by
  cases kd with
  | none =>
      obtain ⟨hsuf, himg, htr⟩ := hf
      exact ⟨RetInv.birth hS hB hp hsuf himg htr, RetInv.nil hS hB hk hp hsuf himg htr⟩
  | some xX =>
      obtain ⟨x, X⟩ := xX
      obtain ⟨hsuf, himg, hx, hcx, htr⟩ := hf
      exact ⟨RetInvW.birth hS hB hp hsuf himg hx hcx htr,
        RetInvX.nil hS hB hk hp hsuf himg hx hcx htr⟩

/-- A new child whose arrows carry the invariants keeps them. -/
theorem GoodS.newChild {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {s : Node}
    (hs : N.Live s) {kd : Option (VarSymb × VarType)} {cx : ℕ} {t : NodeSt σ}
    {fimg₀ : ℕ → ℕ} {bcl₀ : List VarType} {bimg₀ : ℕ → ℕ} {bkd₀ : Option (VarSymb × VarType)}
    (ht : Theory.IsMCS t.M) (hr : RetData hS (N.st s) t kd bkd₀ cx (N.st s).l fimg₀ bcl₀ bimg₀) :
    (N.newChild s kd cx t fimg₀ bcl₀ bimg₀ bkd₀).GoodS hS := by
  have hks : (N.nch s :: s : Node) ≠ s := ne_parent _ s
  have hold : ∀ k, N.Live k → k ≠ N.nch s :: s := fun k hk h => not_live_new s (h ▸ hk)
  refine ⟨fun k hk => ?_, fun c p hk => ?_⟩
  · rcases (live_newChild hs kd cx t k).mp hk with hk | rfl
    · change Theory.IsMCS (Function.update N.st _ t k).M
      rw [Function.update_of_ne (hold k hk)]
      exact hN.mcs k hk
    · change Theory.IsMCS (Function.update N.st _ t _).M
      rw [Function.update_self]
      exact ht
  · rcases (live_newChild hs kd cx t _).mp hk with hk | he
    · have hne := hold _ hk
      have hpne := hold p hk.1
      have := hN.ret c p hk
      unfold RetOk at this ⊢
      change RetData hS (Function.update N.st _ t p) (Function.update N.st _ t (c :: p))
        (Function.update N.kind _ kd (c :: p)) (Function.update N.bkind _ bkd₀ (c :: p))
        (Function.update N.cx _ cx (c :: p))
        (Function.update N.fcl _ (N.st s).l (c :: p)) (Function.update N.fimg _ fimg₀ (c :: p))
        (Function.update N.bcl _ bcl₀ (c :: p)) (Function.update N.bimg _ bimg₀ (c :: p))
      simp only [Function.update_of_ne hne, Function.update_of_ne hpne]
      exact this
    · obtain ⟨rfl, rfl⟩ := List.cons.inj he
      unfold RetOk
      change RetData hS (Function.update N.st _ t p) (Function.update N.st _ t (N.nch p :: p))
        (Function.update N.kind _ kd _) (Function.update N.bkind _ bkd₀ _)
        (Function.update N.cx _ cx _)
        (Function.update N.fcl _ (N.st p).l _) (Function.update N.fimg _ fimg₀ _)
        (Function.update N.bcl _ bcl₀ _) (Function.update N.bimg _ bimg₀ _)
      simp only [Function.update_self, Function.update_of_ne hks.symm]
      exact hr

/-- Creating a child leaves the network or adds a child with a good seed. -/
theorem mkChild_cases {N : NetSt σ} {s : Node} (hM : Theory.IsMCS (N.st s).M)
    (P : NetSt σ → Prop) (hP : P N)
    (hnew : ∀ kd cx t, Theory.IsMCS t.M → FwdData (N.st s) t kd cx (N.st s).l id →
      P (N.newChild s kd cx t))
    (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : P (N.mkChild s o) := by
  obtain ⟨l, φ⟩ := o
  simp only [NetSt.mkChild]
  split_ifs with h
  · split
    · rename_i ψ
      split_ifs with hmem
      · exact hP
      · obtain ⟨hS, ht⟩ := complete_spec (child_consistent hM
          (φ := WFF.mono (ctxOf_le_of_suffix h).boxIn ψ) hmem)
        exact hnew none 0 _ ht ⟨List.suffix_refl _, childImg _,
          fun ψ' hψ' => hS (Or.inr ⟨ψ', hψ', rfl⟩)⟩
    · rename_i x hx ψ
      split_ifs with hmem
      · split
        · rename_i X hX
          obtain ⟨hS, ht⟩ := complete_spec (childX_consistent hM hX
            (φ := WFF.mono ((ctxOf_le_of_suffix h).diaIn x) ψ) hmem)
          exact hnew (some (x, X)) (N.st s).l.length _ ht
            ⟨List.suffix_refl _, childXImg _ X, hX, childX_cx _ X,
              fun ψ' hψ' => hS (Or.inr ⟨ψ', hψ', rfl⟩)⟩
        · exact hP
      · exact hP
    · exact hP
  · exact hP

/-- ⭐Creating a child preserves the invariants under strong B: its arrows are born with them. -/
theorem GoodS.mkChild {hS : ModalSys.BStrong = true} (hB : ModalSys.B = true) {N : NetSt σ}
    (hN : N.GoodS hS) {s : Node} (hs : N.Live s) (o : Σ l : List VarType, WFF σ (ctxOf l) 0) :
    (N.mkChild s o).GoodS hS :=
  mkChild_cases (hN.mcs s hs) (·.GoodS hS) hN
    (fun _ _ _ ht hf => hN.newChild hs ht (RetData.birth hS hB (hN.mcs s hs) ht hf)) o

/-! ## The chain under strong B -/

open Classical in
/-- Perform one operation under strong B, at a live node only. -/
noncomputable def applyOpS (hS : ModalSys.BStrong = true) (N : NetSt σ) : Op σ → NetSt σ
  | .inl (s, o) => if N.Live s then N.henk s o else N
  | .inr (.inl (s, o)) => if N.Live s then N.mkChild s o else N
  | .inr (.inr (.inl k)) => if N.Live k then N.realFS hS k else N
  | .inr (.inr (.inr k)) => if N.Live k then N.realBS hS k else N

theorem GoodS.applyOpS {hS : ModalSys.BStrong = true} (hB : ModalSys.B = true) {N : NetSt σ}
    (hN : N.GoodS hS) (o : Op σ) : (N.applyOpS hS o).GoodS hS := by
  rcases o with ⟨s, o⟩ | ⟨s, o⟩ | k | k
  · simp only [NetSt.applyOpS]
    split_ifs with h
    · exact hN.henk h o
    · exact hN
  · simp only [NetSt.applyOpS]
    split_ifs with h
    · exact hN.mkChild hB h o
    · exact hN
  · simp only [NetSt.applyOpS]
    split_ifs with h
    · exact hN.realFS h
    · exact hN
  · simp only [NetSt.applyOpS]
    split_ifs with h
    · exact hN.realBS h
    · exact hN

theorem Ext.realFS {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {k : Node}
    (hk : N.Live k) : Ext N (N.realFS hS k) := by
  match k with
  | [] => exact Ext.refl N
  | c :: p =>
      simp only [NetSt.realFS]
      split_ifs with hlt
      · obtain ⟨_, hg, _⟩ := fwdStepS_ok hN hk hlt
        exact (Ext.setSt hg).trans (Ext.setFwd _)
      · exact Ext.refl N

theorem Ext.realBS {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {k : Node}
    (hk : N.Live k) : Ext N (N.realBS hS k) := by
  match k with
  | [] => exact Ext.refl N
  | c :: p =>
      simp only [NetSt.realBS]
      split_ifs with hlt
      · obtain ⟨_, hg, _⟩ := backStepS_ok hN hk hlt
        exact (Ext.setSt hg).trans (Ext.setBack _)
      · exact Ext.refl N

theorem Ext.applyOpS {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) (o : Op σ) :
    Ext N (N.applyOpS hS o) := by
  rcases o with ⟨s, o⟩ | ⟨s, o⟩ | k | k
  · simp only [NetSt.applyOpS]
    split_ifs with h
    · exact Ext.henk hN.good h o
    · exact Ext.refl N
  · simp only [NetSt.applyOpS]
    split_ifs with h
    · exact Ext.mkChild h o
    · exact Ext.refl N
  · simp only [NetSt.applyOpS]
    split_ifs with h
    · exact Ext.realFS hN h
    · exact Ext.refl N
  · simp only [NetSt.applyOpS]
    split_ifs with h
    · exact Ext.realBS hN h
    · exact Ext.refl N

theorem GoodS.init (hS : ModalSys.BStrong = true) {l₀ : List VarType}
    {M₀ : Set (WFF σ (ctxOf l₀) 0)} (h : Theory.IsMCS M₀) : (init M₀).GoodS hS :=
  ⟨fun _ _ => h, fun _ _ hk => absurd (init_live hk) (by simp)⟩

end NetSt

section ChainS

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- ⭐The chain of networks from a root theory `M₀`, under strong B. -/
noncomputable def netS (hS : ModalSys.BStrong = true) {l₀ : List VarType}
    (M₀ : Set (WFF σ (ctxOf l₀) 0)) : ℕ → NetSt σ
  | 0 => NetSt.init M₀
  | n + 1 => (netS hS M₀ n).applyOpS hS (sched n)

/-- ⭐Every network of the strong chain is good under strong B. -/
theorem goodS_netS (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true) {l₀ : List VarType}
    {M₀ : Set (WFF σ (ctxOf l₀) 0)} (h : Theory.IsMCS M₀) : ∀ n, (netS hS M₀ n).GoodS hS
  | 0 => NetSt.GoodS.init hS h
  | n + 1 => (goodS_netS hS hB h n).applyOpS hB (sched n)

/-- ⭐Along the strong chain, later networks extend earlier ones. -/
theorem ext_netS (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true) {l₀ : List VarType}
    {M₀ : Set (WFF σ (ctxOf l₀) 0)} (h : Theory.IsMCS M₀) {n m : ℕ} (hnm : n ≤ m) :
    NetSt.Ext (netS hS M₀ n) (netS hS M₀ m) := by
  induction hnm with
  | refl => exact NetSt.Ext.refl _
  | step _ ih => exact ih.trans (NetSt.Ext.applyOpS (goodS_netS hS hB h _) _)

end ChainS

end BArrow

end V12M
