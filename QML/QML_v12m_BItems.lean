import QML.QML_v12m_BodyAbs

/-!
# QML v12m — B's canonical model: the items of a necessary shape, and unpacking

The objects of a necessary shape, for every T (docs §11.21, step 8):

* ⭐`NItems`: an item at each `□`, whatever its companions (they are definable from the object,
  `compVal`), with the object they make (`obj`), the value with companions they send along a
  substitution (`subst`), and every term of the shape's type their object (`exists_obj`).
* The own arrow (item 5): the items packed into one `□` (`NItems.pack`, of type `N.packTy`), and
  ⭐`unpackAt`, the map from that one object with all its companions back to the shape, `holeC`
  at each `□`.  At the packed object it gives the items' object (`holeAt_unpackAt_obj`); at the
  packed object's readings, the readings of its object (`holeVal_unpackAt_compsRead`).
-/

namespace V12M

variable [ModalSys]

/-- The contents of a necessary shape's items packed into one `□`: their types, paired as the
    shape pairs them. -/
def NShape.packTy : NShape → VarType
  | .boxC A _ _ => A
  | .prod R S => .VTypeProd R.packTy S.packTy

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## Items of a necessary shape, for every T -/

/-- ⭐The **items of a necessary shape** over a `□` view: one term for each `□`, whatever its
    companions (they are definable from the object, `compVal`). -/
def NItems (σ : Signature) (V : Ctx) : NShape → Type
  | .boxC A _ _ => Σ b, Term σ V A b
  | .prod R S => NItems σ V R × NItems σ V S

namespace NItems

/-- Weakening the items. -/
def mono {Γ Γ' : Ctx} (h : Γ.Le Γ') : {N : NShape} → NItems σ Γ.boxIn N → NItems σ Γ'.boxIn N
  | .boxC _ _ _, ⟨_, u⟩ => ⟨_, Term.mono h.boxIn u⟩
  | .prod _ _, (n₁, n₂) => (mono h n₁, mono h n₂)

/-- ⭐The necessary object they make: `□u` for each item, paired. -/
def obj {Γ : Ctx} : {N : NShape} → NItems σ Γ.boxIn N → Σ c, Term σ Γ N.ty c
  | .boxC _ _ _, ⟨_, u⟩ => ⟨_, Term.boxtm u⟩
  | .prod _ _, (n₁, n₂) => ⟨_, Term.pair (obj n₁).2 (obj n₂).2⟩

/-- ⭐The value they make along a substitution of the `□` view (the way home): each item with its
    companions (`compsVal`) sent along it, paired. -/
def subst {Γ : Ctx} (ι : VarSymb → VarSymb) {Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ.boxIn θ) (hc : Subst.Coh ι Γ.boxIn θ) :
    {N : NShape} → NItems σ Γ.boxIn N → Σ c, Term σ Δ N.flat c
  | .boxC _ cs h, ⟨_, u⟩ => ⟨_, Term.subst ι θ hθ hc (compsVal u cs h).2⟩
  | .prod _ _, (n₁, n₂) => ⟨_, Term.pair (subst ι θ hθ hc n₁).2 (subst ι θ hθ hc n₂).2⟩

omit [ModalSys.NoFour] in
/-- ⭐Every term of a necessary shape's type is the object of its items. -/
theorem exists_obj {Γ : Ctx} : (N : NShape) → {c : Ann N.ty} → (g : Term σ Γ N.ty c) →
    ∃ n : NItems σ Γ.boxIn N, n.obj = ⟨c, g⟩
  | .boxC _ _ _, _, .boxtm u => ⟨⟨_, u⟩, rfl⟩
  | .prod R S, _, .pair g₁ g₂ => by
      obtain ⟨n₁, h₁⟩ := exists_obj R g₁
      obtain ⟨n₂, h₂⟩ := exists_obj S g₂
      exact ⟨(n₁, n₂), sig_pair h₁ h₂⟩

omit [ModalSys.NoFour] in
theorem obj_mono {Γ Γ' : Ctx} (h : Γ.Le Γ') : {N : NShape} → (n : NItems σ Γ.boxIn N) →
    (n.mono h).obj = ⟨_, Term.mono h n.obj.2⟩
  | .boxC _ _ _, ⟨_, _⟩ => rfl
  | .prod _ _, (n₁, n₂) => sig_pair (obj_mono h n₁) (obj_mono h n₂)

omit [ModalSys.NoFour] in
theorem mono_mono {Γ Γ' Γ'' : Ctx} (h : Γ.Le Γ') (h' : Γ'.Le Γ'') : {N : NShape} →
    (n : NItems σ Γ.boxIn N) → (n.mono h).mono h' = n.mono (h.trans h')
  | .boxC _ _ _, ⟨_, u⟩ => by
      change (⟨_, Term.mono h'.boxIn (Term.mono h.boxIn u)⟩ : Σ b, Term σ Γ''.boxIn _ b) = ⟨_, _⟩
      rw [Term.mono_mono]
  | .prod _ _, (n₁, n₂) => Prod.ext (mono_mono h h' n₁) (mono_mono h h' n₂)

omit [ModalSys.NoFour] in
theorem subst_mono {Γ Γ' : Ctx} {ι : VarSymb → VarSymb} {Δ : Ctx} (h : Γ.Le Γ') (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ'.boxIn θ) (hc : Subst.Coh ι Γ'.boxIn θ) : {N : NShape} →
    (n : NItems σ Γ.boxIn N) →
    (n.mono h).subst ι θ hθ hc = n.subst ι θ (hθ.restrict h.boxIn) (hc.restrict h.boxIn)
  | .boxC _ cs hcs, ⟨_, u⟩ => by
      change (⟨_, Term.subst ι θ hθ hc (compsVal (Term.mono h.boxIn u) cs hcs).2⟩ :
        Σ b, Term σ Δ _ b) = ⟨_, _⟩
      rw [mono_compsVal h u cs hcs]
      exact congrArg (Sigma.mk _) (Term.subst_mono _ _ _ _ _)
  | .prod _ _, (n₁, n₂) => sig_pair (subst_mono h θ hθ hc n₁) (subst_mono h θ hθ hc n₂)

omit [ModalSys.NoFour] in
theorem subst_congr {Γ : Ctx} {ι ι' : VarSymb → VarSymb} {Δ : Ctx} (θ θ' : Subst σ Δ)
    (hθ : Subst.Ok Γ.boxIn θ) (hθ' : Subst.Ok Γ.boxIn θ') (hc : Subst.Coh ι Γ.boxIn θ)
    (hc' : Subst.Coh ι' Γ.boxIn θ') (hs : Subst.Sim Γ.boxIn θ θ') : {N : NShape} →
    (n : NItems σ Γ.boxIn N) → n.subst ι θ hθ hc = n.subst ι' θ' hθ' hc'
  | .boxC _ cs hcs, ⟨_, u⟩ => Term.subst_congr θ θ' hθ hθ' hc hc' hs (compsVal u cs hcs).2
  | .prod _ _, (n₁, n₂) =>
      sig_pair (subst_congr θ θ' hθ hθ' hc hc' hs n₁) (subst_congr θ θ' hθ hθ' hc hc' hs n₂)

end NItems

/-- The items packed into one term: their contents, paired. -/
def NItems.pack {V : Ctx} : {N : NShape} → NItems σ V N → Σ b, Term σ V N.packTy b
  | .boxC _ _ _, ⟨_, u⟩ => ⟨_, u⟩
  | .prod _ _, (n₁, n₂) => ⟨_, Term.pair (NItems.pack n₁).2 (NItems.pack n₂).2⟩

/-! ## The unpacking map (T) -/

/-- ⭐**The unpacking map** (T): from one necessary object `□P` with **all** its companions to the
    shape `N`, the items read off its contents by `q` — `holeC` at each `□`, so each item's
    companions are read off the source's (no side condition). -/
def unpackAt (hT : ModalSys.T = true) {P : VarType} : (N : NShape) → {c : Ann N.packTy} →
    Term σ (Ctx.empty.insert (.bnd 0) P) N.packTy c →
    ShapeMap σ (.boxC P (P.compsAllB true) (VarType.compOk_compsAllB true hT P)) N
  | .boxC _ cs h, _, q => .holeC q true hT ModalSys.NoFour.noFour cs h
  | .prod R S, _, q => .pair
      (unpackAt hT R (Term.holeAt q (Term.eta (.step (.root (.bnd 0)) .fst) R.packTy
        (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))))
      (unpackAt hT S (Term.holeAt q (Term.eta (.step (.root (.bnd 0)) .snd) S.packTy
        (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)))))

/-- ⭐**The unpacking map's object at a packed object**: when `q` reads the items off the packed
    contents, the object the items make. -/
theorem holeAt_unpackAt_obj (hT : ModalSys.T = true) {Γ : Ctx} {P : VarType} {a : Ann P}
    (sb : Term σ Γ.boxIn P a) : ∀ (N : NShape) {c : Ann N.packTy}
    (q : Term σ (Ctx.empty.insert (.bnd 0) P) N.packTy c) (n : NItems σ Γ.boxIn N),
    (⟨_, Term.holeAt sb q⟩ : Σ e, Term σ Γ.boxIn N.packTy e) = n.pack →
    (⟨_, Term.holeAt (Term.boxtm sb) (unpackAt hT N q).obj.2⟩ : Σ e, Term σ Γ N.ty e) = n.obj
  | .boxC _ _ _, _, q, ⟨_, u⟩, hq => by
      change (⟨_, Term.boxtm (Term.subst _ _ _ _ (Term.holeAt _ q))⟩ :
        Σ e, Term σ Γ (.VTypeBox _) e) = _
      refine sig_boxtm ?_
      refine (Term.subst_holeAt_sig _ _ _ _ _).trans ?_
      refine (sig_holeAt (Term.subst_eta_tm _ _ _ _ _ _ _
        (Subst.box_at_inner_boxtm _ ?_)) _).trans hq
      change Subst.single _ _ (.root (.bnd 0)) = _
      exact if_pos rfl
  | .prod R S, _, q, (n₁, n₂), hq =>
      sig_pair
        (holeAt_unpackAt_obj hT sb R _ n₁ ((Term.holeAt_holeAt_sig _ _ _).trans
          ((Term.holeAt_congr_sig hq _).trans (Term.holeAt_pair_fst _ _))))
        (holeAt_unpackAt_obj hT sb S _ n₂ ((Term.holeAt_holeAt_sig _ _ _).trans
          ((Term.holeAt_congr_sig hq _).trans (Term.holeAt_pair_snd _ _))))

/-- ⭐**The unpacking map's value at a packed object's readings**: the readings of its object
    (`holeC_compsRead` at each `□`). -/
theorem holeVal_unpackAt_compsRead (hT : ModalSys.T = true) {M : Model σ} {P : VarType}
    {v w : M.frame.W} (e : M.frame.Dom (.VTypeBox P) v) (r : M.frame.R v w) :
    ∀ (N : NShape) {c : Ann N.packTy} (q : Term σ (Ctx.empty.insert (.bnd 0) P) N.packTy c),
      M.holeVal (unpackAt hT N q).val.2
          (M.compsRead P (P.compsAllB true) (VarType.compOk_compsAllB true hT P) e r) =
        M.NRead N (M.holeVal (unpackAt hT N q).obj.2 e) r
  | .boxC _ cs h, _, q => Model.holeC_compsRead q true hT ModalSys.NoFour.noFour cs h e r
  | .prod R S, _, _ => Prod.ext (holeVal_unpackAt_compsRead hT e r R _)
      (holeVal_unpackAt_compsRead hT e r S _)

end BArrow

end V12M
