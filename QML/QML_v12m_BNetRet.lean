import QML.QML_v12m_BRetWD
import QML.QML_v12m_BNetMono

/-!
# QML v12m — strong B on the network: the invariants

Under strong B every child's two arrows carry the returning-possibility invariants (docs §11.17):
`RetInv` both ways for a plain child; `RetInvW` forward and `RetInvX` home for a witness child
(`RetData`).  Necessity transfer, and so weak B's `Good`, follows from them (`RetData.fwd`,
`RetData.back`).  The network carries them with the tuple's companions (`RetDataB`, in
`QML_v12m_BNetRetC`, with the operations); these are what forgetting the companions gives
(`NetSt.RetOk`).
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
    ways for a plain child; `RetInvW` out along `x` and `RetInvX` home for a witness child; for a
    back-witness child (`bkd = (e, X)`, its way home in `e`'s extent, content `bcx` at the parent),
    the mirror: `RetInvX` out, along `e` read at the child, and `RetInvW` home; and for a doubly
    witnessed child, `RetInvWD` both ways (docs §11.20). -/
def RetData (hS : ModalSys.BStrong = true) (tp tk : NodeSt σ)
    (kind bkd : Option (VarSymb × VarType)) (cx bcx : ℕ) (fcl : List VarType) (fimg : ℕ → ℕ)
    (bcl : List VarType) (bimg : ℕ → ℕ) : Prop :=
  match kind, bkd with
  | some (x, X), none =>
      RetInvW hS tp tk fcl fimg bcl bimg x X cx ∧ RetInvX hS tk tp bcl bimg fcl fimg x X cx
  | some (x, X), some (e, E) =>
      RetInvWD hS tp tk fcl fimg bcl bimg x X cx e E bcx ∧
        RetInvWD hS tk tp bcl bimg fcl fimg e E bcx x X cx
  | none, none => RetInv hS tp tk fcl fimg bcl bimg ∧ RetInv hS tk tp bcl bimg fcl fimg
  | none, some (e, X) =>
      RetInvX hS tp tk fcl fimg bcl bimg e X bcx ∧ RetInvW hS tk tp bcl bimg fcl fimg e X bcx

namespace RetData

variable {hS : ModalSys.BStrong = true} {tp tk : NodeSt σ} {kind bkd : Option (VarSymb × VarType)}
  {cx bcx : ℕ} {fcl : List VarType} {fimg : ℕ → ℕ} {bcl : List VarType} {bimg : ℕ → ℕ}

/-- The forward arrow's transfer. -/
theorem fwd (hp : Theory.IsMCS tp.M) (hk : Theory.IsMCS tk.M)
    (h : RetData hS tp tk kind bkd cx bcx fcl fimg bcl bimg) : FwdData tp tk kind cx fcl fimg := by
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
      cases bkd with
      | none =>
          obtain ⟨ht, himgt, hx, hcx, htr⟩ := RetInvX.transferX hS hk hp h.2
          exact ⟨ht, himgt, hx, hcx, htr⟩
      | some eE =>
          obtain ⟨e, E⟩ := eE
          obtain ⟨ht, himgt, hx, hcx, htr⟩ := RetInvWD.transferX hS hk hp h.2
          exact ⟨ht, himgt, hx, hcx, htr⟩

/-- The back arrow's transfer. -/
theorem back (hp : Theory.IsMCS tp.M) (hk : Theory.IsMCS tk.M)
    (h : RetData hS tp tk kind bkd cx bcx fcl fimg bcl bimg) : BackData tk tp bcl bimg := by
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
      cases bkd with
      | none =>
          obtain ⟨hs, himgs, htr⟩ := RetInvX.transfer hp h.2
          exact ⟨hs, himgs, htr⟩
      | some eE =>
          obtain ⟨e, E⟩ := eE
          obtain ⟨hs, himgs, htr⟩ := RetInvWD.transfer hS hp hk h.1
          exact ⟨hs, himgs, htr⟩

end RetData

namespace NetSt

/-- The invariants of the child `k`'s arrows, to and from its parent `p`. -/
def RetOk (hS : ModalSys.BStrong = true) (N : NetSt σ) (k p : Node) : Prop :=
  RetData hS (N.st p) (N.st k) (N.kind k) (N.bkind k) (N.cx k) (N.bcx k) (N.fcl k) (N.fimg k)
    (N.bcl k)
    (N.bimg k)

end NetSt

end BArrow

end V12M
