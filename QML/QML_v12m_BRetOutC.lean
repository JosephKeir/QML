import QML.QML_v12m_BRetOut
import QML.QML_v12m_BCompNamed

/-!
# QML v12m — B's canonical model: `ret` membership ⇒ truth at companion shapes (strong B, any T)

Under T a returning possibility's necessary object comes back with its companions, so the
returning successors are stated at companion shapes (docs §11.21, item 6):

* `Model.compBack_of_ind`, `BData.compsBack_of_ind`: readings `Ind` to a value come back as it;
* ⭐`BData.RetOutC` and ⭐`BData.sat_retC_of_mem`: a returning successor, with the readings home of
  the object's value with companions `Ind` to the value, makes the atom true;
* every necessary shape packs into one `□` with companions (`packG`, by `packCC`) and unpacks
  (`unpackG`, by `fstC`/`sndC`), the identity on objects and on values
  (`holeAt_packG_unpackG`, `holeAt_packG_unpackG_val`); canonical `Ind` is a congruence before the
  truth lemma (`BData.indCongr`), so ⭐`BData.sat_retS_nec_of_memC` maps the truth back
  (`sat_ret_map` along `unpackG`);
* ⭐`bdataS_retOutC`: the limit has the returning successors — name the missing companions
  (`ret_comps_named`), alias the value's tuple, move it to the alias's arrangement and take the
  obligation's child (`lretC`).
-/

namespace V12M

variable [ModalSys]

namespace Model

variable {σ : Signature} {M : Model σ}

/-- A companion whose reading is `Ind` to `o` comes back as `o` (the converse of
    `ind_compRead`). -/
theorem compBack_of_ind (hT : ModalSys.T = true) : ∀ (A : VarType) (p : List Step)
    {v w : M.frame.W} (x : M.frame.Dom A v) (r : M.frame.R v w)
    (o : M.frame.Dom ((A.compAt p).getD .VTypeOne) w), (A.compAt p).isSome = true →
    M.Ind (M.compRead hT A p x r) o → M.compBack A p x r o := by
  intro A p
  induction p generalizing A with
  | nil =>
      intro v w x r o hs hb
      cases A <;> simp only [VarType.compAt, Option.isSome_none, Bool.false_eq_true] at hs
      exact hb
  | cons s p ih =>
      intro v w x r o hs hb
      cases A <;> cases s <;>
        simp only [VarType.compAt, Option.isSome_none, Bool.false_eq_true] at hs
      · exact ih _ x.1 r o hs hb
      · exact ih _ x.2 r o hs hb
      · exact (iff_of_eq (dif_pos hT)).mpr (ih _ _ r o hs hb)

end Model

/-- The companions of a necessary shape's items packed into one `□` (`NShape.packTy`): each item's
    own, under the steps to it. -/
def NShape.packComps : NShape → List (List Step)
  | .boxC _ cs _ => cs
  | .prod R S => pairComps R.packComps S.packComps

theorem NShape.packOk : (N : NShape) → N.packTy.CompOk N.packComps
  | .boxC _ _ h => h
  | .prod R S => VarType.compOk_pairComps R.packOk S.packOk

/-- A necessary shape packed into one `□` with companions. -/
abbrev NShape.packed (N : NShape) : NShape := .boxC N.packTy N.packComps N.packOk

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## Packing with companions -/

/-- ⭐The **packing map with companions**: a necessary shape's items into one necessary object,
    their companions under the steps to them (`packCC`). -/
def packG : (N : NShape) → ShapeMap σ N N.packed
  | .boxC A cs h => .id (.boxC A cs h)
  | .prod R S => .comp (.pair (.comp (.fst R S) (packG R)) (.comp (.snd R S) (packG S)))
      (.packCC R.packTy S.packTy R.packComps S.packComps R.packOk S.packOk)

/-- ⭐The **unpacking map with companions**: each half with its companions (`fstC`, `sndC`). -/
def unpackG : (N : NShape) → ShapeMap σ N.packed N
  | .boxC A cs h => .id (.boxC A cs h)
  | .prod R S => .pair
      (.comp (.fstC R.packTy S.packTy R.packComps S.packComps R.packOk S.packOk) (unpackG R))
      (.comp (.sndC R.packTy S.packTy R.packComps S.packComps R.packOk S.packOk) (unpackG S))

omit [ModalSys.NoFour] in
/-- ⭐**Packing then unpacking is the identity** on objects of a necessary shape (any T). -/
theorem holeAt_packG_unpackG : (N : NShape) → {Γ : Ctx} → {c : Ann N.ty} →
    (x : Term σ Γ N.ty c) →
    (⟨_, Term.holeAt (Term.holeAt x (packG (σ := σ) N).obj.2) (unpackG (σ := σ) N).obj.2⟩ :
      Σ e, Term σ Γ N.ty e) = ⟨c, x⟩
  | .boxC _ _ _, _, _, x =>
      (Term.holeAt_congr_sig (Term.holeAt_eta_root x) _).trans (Term.holeAt_eta_root x)
  | .prod R S, Γ, _, .pair x₁ x₂ => by
      obtain ⟨_, s₁, h₁⟩ := exists_boxtm (Term.holeAt x₁ (packG (σ := σ) R).obj.2)
      obtain ⟨_, s₂, h₂⟩ := exists_boxtm (Term.holeAt x₂ (packG (σ := σ) S).obj.2)
      have hP : (⟨_, Term.holeAt (Term.pair x₁ x₂) (packG (σ := σ) (.prod R S)).obj.2⟩ :
          Σ e, Term σ Γ (NShape.packed (.prod R S)).ty e) =
          ⟨_, Term.boxtm (Term.pair s₁ s₂)⟩ := by
        change (⟨_, Term.holeAt (Term.pair x₁ x₂) (Term.holeAt (Term.pair
          (Term.holeAt _ (packG (σ := σ) R).obj.2) (Term.holeAt _ (packG (σ := σ) S).obj.2))
          (ShapeMap.pack (σ := σ) R.packTy S.packTy).obj.2)⟩ : Σ e, Term σ Γ _ e) = _
        refine (Term.holeAt_holeAt_sig _ _ _).trans ?_
        refine (Term.holeAt_congr_sig (sig_pair
          ((Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
            (Term.holeAt_pair_fst x₁ x₂) _).trans h₁))
          ((Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
            (Term.holeAt_pair_snd x₁ x₂) _).trans h₂))) _).trans ?_
        exact Term.holeAt_pack s₁ s₂
      refine (Term.holeAt_congr_sig hP _).trans ?_
      change (⟨_, Term.pair (Term.holeAt _ (Term.holeAt _ (unpackG (σ := σ) R).obj.2))
        (Term.holeAt _ (Term.holeAt _ (unpackG (σ := σ) S).obj.2))⟩ : Σ e, Term σ Γ _ e) = _
      refine sig_pair ?_ ?_
      · refine (Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
          ((holeAt_box_fst s₁ s₂ _).trans h₁.symm) _).trans ?_)
        exact holeAt_packG_unpackG R x₁
      · refine (Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
          ((holeAt_box_snd s₁ s₂ _).trans h₂.symm) _).trans ?_)
        exact holeAt_packG_unpackG S x₂

omit [ModalSys.NoFour] in
/-- Packing then unpacking, on the slot. -/
theorem holeAt_packG_unpackG_slot (N : NShape) :
    (⟨_, Term.holeAt (packG (σ := σ) N).obj.2 (unpackG (σ := σ) N).obj.2⟩ :
      Σ e, Term σ (Ctx.empty.insert (.bnd 0) N.ty) N.ty e) =
      ⟨_, Term.eta (.root (.bnd 0)) N.ty (Ctx.ref_insert_root _ _ _)⟩ := by
  have h := holeAt_packG_unpackG N (σ := σ)
    (Term.eta (.root (.bnd 0)) N.ty (Ctx.ref_insert_root Ctx.empty (.bnd 0) N.ty))
  rw [Term.holeAt_congr_sig (Term.holeAt_eta_slot (V := Ctx.empty) _) _, Term.mono_refl] at h
  exact h

omit [ModalSys.NoFour] in
/-- `fstC` after `packCC` is the first half. -/
theorem packCC_fstC_val {Γ : Ctx} (X Y : VarType) (csX csY : List (List Step))
    (hX : X.CompOk csX) (hY : Y.CompOk csY) {a₁ : Ann (X.compsFlat csX)}
    {a₂ : Ann (Y.compsFlat csY)} (u₁ : Term σ Γ (X.compsFlat csX) a₁)
    (u₂ : Term σ Γ (Y.compsFlat csY) a₂) :
    (⟨_, Term.holeAt (Term.holeAt (Term.pair u₁ u₂)
        (ShapeMap.packCC (σ := σ) X Y csX csY hX hY).val.2)
      (ShapeMap.fstC (σ := σ) X Y csX csY hX hY).val.2⟩ :
      Σ c, Term σ Γ (X.compsFlat csX) c) = ⟨a₁, u₁⟩ := by
  refine compsFlat_ext X csX hX.nodup _ u₁ ?_ (fun q hq => ?_)
  · have e₁ := fstC_read_main X Y csX csY hX hY (Term.holeAt (Term.pair u₁ u₂)
      (ShapeMap.packCC (σ := σ) X Y csX csY hX hY).val.2) []
    have e₂ := packCC_read_fst X Y csX csY hX hY (Term.pair u₁ u₂) []
    rw [List.append_nil] at e₁
    rw [e₁, e₂, List.append_nil, getP_pair_fst]
  · rw [fstC_read_idx' X Y csX csY hX hY _ q hq, packCC_read_idx_fst' X Y csX csY hX hY _ q hq,
      getP_pair_fst]

omit [ModalSys.NoFour] in
/-- `sndC` after `packCC` is the second half. -/
theorem packCC_sndC_val {Γ : Ctx} (X Y : VarType) (csX csY : List (List Step))
    (hX : X.CompOk csX) (hY : Y.CompOk csY) {a₁ : Ann (X.compsFlat csX)}
    {a₂ : Ann (Y.compsFlat csY)} (u₁ : Term σ Γ (X.compsFlat csX) a₁)
    (u₂ : Term σ Γ (Y.compsFlat csY) a₂) :
    (⟨_, Term.holeAt (Term.holeAt (Term.pair u₁ u₂)
        (ShapeMap.packCC (σ := σ) X Y csX csY hX hY).val.2)
      (ShapeMap.sndC (σ := σ) X Y csX csY hX hY).val.2⟩ :
      Σ c, Term σ Γ (Y.compsFlat csY) c) = ⟨a₂, u₂⟩ := by
  refine compsFlat_ext Y csY hY.nodup _ u₂ ?_ (fun q hq => ?_)
  · have e₁ := sndC_read_main X Y csX csY hX hY (Term.holeAt (Term.pair u₁ u₂)
      (ShapeMap.packCC (σ := σ) X Y csX csY hX hY).val.2) []
    have e₂ := packCC_read_snd X Y csX csY hX hY (Term.pair u₁ u₂) []
    rw [List.append_nil] at e₁
    rw [e₁, e₂, List.append_nil, getP_pair_snd]
  · rw [sndC_read_idx' X Y csX csY hX hY _ q hq, packCC_read_idx_snd' X Y csX csY hX hY _ q hq,
      getP_pair_snd]

omit [ModalSys.NoFour] in
/-- ⭐**Unpacking packed values is the identity** (any T). -/
theorem holeAt_packG_unpackG_val : (N : NShape) → {Γ : Ctx} → {c : Ann N.flat} →
    (w : Term σ Γ N.flat c) →
    (⟨_, Term.holeAt (Term.holeAt w (packG (σ := σ) N).val.2) (unpackG (σ := σ) N).val.2⟩ :
      Σ e, Term σ Γ N.flat e) = ⟨c, w⟩
  | .boxC _ _ _, _, _, w =>
      (Term.holeAt_congr_sig (Term.holeAt_eta_root w) _).trans (Term.holeAt_eta_root w)
  | .prod R S, Γ, _, .pair w₁ w₂ => by
      have hP : (⟨_, Term.holeAt (Term.pair w₁ w₂) (packG (σ := σ) (.prod R S)).val.2⟩ :
          Σ e, Term σ Γ (NShape.packed (.prod R S)).flat e) =
          ⟨_, Term.holeAt (Term.pair (Term.holeAt w₁ (packG (σ := σ) R).val.2)
            (Term.holeAt w₂ (packG (σ := σ) S).val.2))
            (ShapeMap.packCC (σ := σ) R.packTy S.packTy R.packComps S.packComps R.packOk
              S.packOk).val.2⟩ := by
        change (⟨_, Term.holeAt (Term.pair w₁ w₂) (Term.holeAt (Term.pair
          (Term.holeAt _ (packG (σ := σ) R).val.2) (Term.holeAt _ (packG (σ := σ) S).val.2))
          (ShapeMap.packCC (σ := σ) R.packTy S.packTy R.packComps S.packComps R.packOk
            S.packOk).val.2)⟩ : Σ e, Term σ Γ _ e) = _
        exact (Term.holeAt_holeAt_sig _ _ _).trans (Term.holeAt_congr_sig (sig_pair
          ((Term.holeAt_holeAt_sig _ _ _).trans
            (Term.holeAt_congr_sig (Term.holeAt_pair_fst w₁ w₂) _))
          ((Term.holeAt_holeAt_sig _ _ _).trans
            (Term.holeAt_congr_sig (Term.holeAt_pair_snd w₁ w₂) _))) _)
      refine (Term.holeAt_congr_sig hP _).trans ?_
      change (⟨_, Term.pair (Term.holeAt _ (Term.holeAt _ (unpackG (σ := σ) R).val.2))
        (Term.holeAt _ (Term.holeAt _ (unpackG (σ := σ) S).val.2))⟩ : Σ e, Term σ Γ _ e) = _
      refine sig_pair ?_ ?_
      · refine (Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
          (packCC_fstC_val _ _ _ _ _ _ _ _) _).trans ?_)
        exact holeAt_packG_unpackG_val R w₁
      · refine (Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
          (packCC_sndC_val _ _ _ _ _ _ _ _) _).trans ?_)
        exact holeAt_packG_unpackG_val S w₂

/-- ⭐**A returning possibility at a necessary shape is one at its packed shape**: `ret_map` along
    `packG`, the body read back through `unpackG`. -/
def retS_packG (hS : ModalSys.BStrong = true) {Γ : Ctx} [Γ.NoSlots] (O : OutLeg Γ)
    {Δ : List (WFF σ Γ 0)} {N : NShape} {a : Ann N.flat} (t : Term σ Γ N.flat a)
    (Φ : WFF σ (O.view.insert (.bnd 0) N.ty) 1)
    (p : Proof σ Γ Δ (O.retS hS (.nec N) t Φ)) :
    Proof σ Γ Δ (O.retS hS (.nec N.packed) (Term.holeRead t (packG N).val.2)
      (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (unpackG N).obj.2) Φ)) := by
  refine Proof.ret_map hS O (S := .nec N) (packG N) t _ (Proof.conv ?_ p)
  change O.retS hS (.nec N) t Φ = O.retS hS (.nec N) t (WFF.bodyRepl _ (WFF.bodyRepl _ Φ))
  rw [WFF.bodyRepl_bodyRepl]
  dsimp only [ShapeMap.liftObj]
  rw [WFF.bodyRepl_congr (sig_mono _ (holeAt_packG_unpackG_slot N))]
  exact congrArg (O.retS hS (.nec N) t) (WFF.bodyRepl_eta Φ).symm

namespace BData

variable {B : BData σ}

/-- Canonical `Ind` at a pair gives it at each component. -/
theorem ind_fst {s : B.W} {X Y : VarType} {a a' : B.frame.Dom (.VTypeProd X Y) s}
    (h : B.Ind a a') : B.Ind a.1 a'.1 := by
  have h₁ := ind_map (Term.eta (σ := σ) (.step (.root (.bnd 0)) .fst) X
    (Ctx.ref_fst_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeProd X Y)))) h
  unfold Model.holeVal at h₁
  rw [Model.interp_eta_slot_fst] at h₁
  erw [Model.interp_eta_slot_fst] at h₁
  exact h₁

theorem ind_snd {s : B.W} {X Y : VarType} {a a' : B.frame.Dom (.VTypeProd X Y) s}
    (h : B.Ind a a') : B.Ind a.2 a'.2 := by
  have h₂ := ind_map (Term.eta (σ := σ) (.step (.root (.bnd 0)) .snd) Y
    (Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeProd X Y)))) h
  unfold Model.holeVal at h₂
  rw [Model.interp_eta_slot_snd] at h₂
  erw [Model.interp_eta_slot_snd] at h₂
  exact h₂

/-- ⭐A necessary object whose readings with companions are `Ind` to `o` comes back as `o`. -/
theorem compsBack_of_ind (A : VarType) {s k : B.W} (e : B.frame.Dom (.VTypeBox A) k)
    (r : B.frame.R k s) : ∀ (cs : List (List Step)) (h : A.CompOk cs)
    (o : B.frame.Dom (A.compsFlat cs) s),
    B.Ind (B.model.compsRead A cs h e r) o → B.model.compsBack A cs e r o
  | [], _, _, hI => hI
  | p :: ps, h, o, hI => by
      obtain ⟨hT, hall, -⟩ := h.resolve_left (List.cons_ne_nil _ _)
      refine ⟨compsBack_of_ind A e r ps h.tail o.1 (ind_fst hI), ?_⟩
      rw [dif_pos hT]
      exact Model.compBack_of_ind (M := B.model) hT (.VTypeBox A) (.here :: p) e r o.2
        (hall p List.mem_cons_self) (by exact ind_snd hI)

/-- ⭐**Returning successors at companion shapes** (plain leg): a returning possibility at a
    necessary object with companions `cs` in a world's theory has an arrow `s → k` and a term `g` of
    `k`'s `□` view with `Φ(□g)` at `k` (read along the arrow), whose value with companions read home
    is `Ind` to the value.  The limit of a strong chain has it (`bdataS_retOutC`). -/
def RetOutC (B : BData σ) (hS : ModalSys.BStrong = true) : Prop :=
  ∀ {s : B.W} {i : ℕ} {A : VarType} {cs : List (List Step)} {h : A.CompOk cs}
    {a : Ann (A.compsFlat cs)} (V : Term σ ((B.w s).ctx i) (A.compsFlat cs) a)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) (.VTypeBox A)) 1),
    WFF.retS hS (.nec (.boxC A cs h)) V Φ ∈ (B.w s).M i →
      ∃ (k : B.W) (hR : B.R s k) (j : ℕ) (hj : B.stg s k i ≤ j) (b : Ann A)
        (g : Term σ ((B.w k).ctx j).boxIn A b),
        readArrow ((B.imgOk hR i).mono ((B.w k).le hj)) (Term.boxtm g) Φ ∈ (B.w k).M j ∧
        B.Ind (B.toDom (A.compsFlat cs) s (B.rden s (B.stg k s j) (Ctx.Le.refl _)
            (Term.subst (arrowIdx (B.img k s)) (arrowS σ _ (B.img k s))
              (ok_arrowS (B.imgOk (B.symm hR) j)) (coh_arrowS (B.imgOk (B.symm hR) j))
              (compsVal g cs h).2)) (definable_rden _ _))
          (B.toDom (A.compsFlat cs) s (B.rden s i (Ctx.Le.refl _) V) (definable_rden _ _))

/-- ⭐⭐**`ret` at a companion shape, membership ⇒ truth** (plain leg): the returning successor's
    object `□g` has `Φ` by the induction hypothesis, and its readings home with companions are the
    value with companions sent home (`interp_compsVal`, `boxPush_canon_at`), `Ind` to the value; so
    it comes back as it (`compsBack_of_ind`). -/
theorem sat_retC_of_mem (hS : ModalSys.BStrong = true) (hRO : B.RetOutC hS) {s : B.W} {i : ℕ}
    {A : VarType} {cs : List (List Step)} {h : A.CompOk cs} {a : Ann (A.compsFlat cs)}
    (V : Term σ ((B.w s).ctx i) (A.compsFlat cs) a)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0), φ.size < Φ.size + 1 →
      (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (hm : (WFF.retS hS (.nec (.boxC A cs h)) V Φ : WFF σ _ 0) ∈ (B.w s).M i) :
    B.model.sat (B.canonEnv s i) (WFF.retS hS (.nec (.boxC A cs h)) V Φ : WFF σ _ 0) := by
  obtain ⟨k, hR, j, hj, b, g, hmem, hInd⟩ := hRO V Φ hm
  have hsat := (IH k j _ (by unfold readArrow; rw [WFF.size_subst]; omega)).mpr hmem
  rw [sat_readArrow, ← boxPush_canon_at s i ⟨k, ⟨Or.inl hR⟩⟩ hR hj] at hsat
  refine ⟨⟨k, ⟨Or.inl hR⟩⟩, _, hsat, Or.inl (B.symm hR), ?_⟩
  change B.model.compsBack A cs (Model.interp (B.canonEnv k j) (Term.boxtm g)) _ _
  refine compsBack_of_ind A _ _ cs h _ ?_
  rw [← interp_canon _ (Model.Env.Agree.refl' _), ← interp_canon V (Model.Env.Agree.refl' _),
    Model.interp_subst _ _ _ (Ctx.noProjLast_boxIn _),
    ← boxPush_canon_at k _ ⟨s, ⟨Or.inl (B.symm hR)⟩⟩ (B.symm hR) le_rfl,
    Model.interp_compsVal] at hInd
  exact hInd

/-- ⭐**Canonical `Ind` is a congruence**, before the truth lemma (`ind_map`, `ind_pair`). -/
theorem indCongr : B.model.IndCongr where
  map := by
    intro _ _ _ s _ _ _ h
    exact ind_map s h
  pair := by
    intro _ _ _ _ _ _ _ h₁ h₂
    exact ind_pair h₁ h₂

/-- ⭐⭐**`ret`, membership ⇒ truth at every necessary shape** (plain leg; any T): pack the shape
    into one object with companions (`retS_packG`), take the truth there (`sat_retC_of_mem`), and
    map it back (`sat_ret_map` along `unpackG`, canonical `Ind` being a congruence, `indCongr`):
    unpacking packed values is the identity (`holeAt_packG_unpackG_val`). -/
theorem sat_retS_nec_of_memC (hS : ModalSys.BStrong = true) (hRO : B.RetOutC hS) {s : B.W}
    {i : ℕ} {N : NShape} {a : Ann N.flat} (t : Term σ ((B.w s).ctx i) N.flat a)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) N.ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < (WFF.retS hS (.nec N) t Φ : WFF σ _ 0).size →
        (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (h : (WFF.retS hS (.nec N) t Φ : WFF σ _ 0) ∈ (B.w s).M i) :
    B.model.sat (B.canonEnv s i) (WFF.retS hS (.nec N) t Φ : WFF σ _ 0) := by
  have hsz : (WFF.retS hS (.nec N) t Φ : WFF σ _ 0).size = Φ.size + N.flat.eqRecSize + 1 := rfl
  have hp := BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by
    rw [List.mem_singleton.mp hψ]; exact h)
    ⟨retS_packG hS .nec t Φ (Proof.lookup List.mem_cons_self)⟩
  have hsat := sat_retC_of_mem hS hRO _ _ (fun s' K φ hφ => IH s' K φ (by
    unfold WFF.bodyRepl at hφ
    rw [WFF.size_subst] at hφ
    omega)) hp
  have hb := Model.sat_ret_map (B.canonEnv s i) (noProjLast s i) indCongr hS .nec
    (S := .nec N.packed) (unpackG N) _ Φ hsat
  refine (congrArg (B.model.sat _) (OutLeg.retS_congr hS .nec (.nec N) ?_ rfl)).mp hb
  rw [Term.holeRead_eq_holeAt, Term.holeRead_eq_holeAt]
  exact holeAt_packG_unpackG_val N t

/-- ⭐**Returning successors along a witness at companion shapes**: as `RetOutC`, along an arrow
    of `y`'s extent.  The limit of a strong chain has it (`bdataS_retOutXC`). -/
def RetOutXC (B : BData σ) (hS : ModalSys.BStrong = true) : Prop :=
  ∀ {s : B.W} {i : ℕ} {y : VarSymb} {Y : VarType}
    (hy : ((B.w s).ctx i).ref y = some (.VTypeDia Y)) {A : VarType} {cs : List (List Step)}
    {h : A.CompOk cs} {a : Ann (A.compsFlat cs)} (V : Term σ ((B.w s).ctx i) (A.compsFlat cs) a)
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) (.VTypeBox A)) 1),
    (OutLeg.pos y ⟨Y, hy⟩ : OutLeg ((B.w s).ctx i)).retS hS (.nec (.boxC A cs h)) V Φ ∈
        (B.w s).M i →
      ∃ (k : B.W) (hk : B.kd s k = some (y, Y)) (j : ℕ) (hj : B.stg s k i ≤ j) (b : Ann A)
        (g : Term σ ((B.w k).ctx j).boxIn A b),
        readArrowX ((B.imgOk (B.kdR hk) i).mono ((B.w k).le hj)) hy
            (((B.w k).le hj).ref (B.hcx hk i)) (Term.boxtm g) Φ ∈ (B.w k).M j ∧
        B.Ind (B.toDom (A.compsFlat cs) s (B.rden s (B.stg k s j) (Ctx.Le.refl _)
            (Term.subst (arrowIdx (B.img k s)) (arrowS σ _ (B.img k s))
              (ok_arrowS (B.imgOk (B.symm (B.kdR hk)) j))
              (coh_arrowS (B.imgOk (B.symm (B.kdR hk)) j)) (compsVal g cs h).2))
            (definable_rden _ _))
          (B.toDom (A.compsFlat cs) s (B.rden s i (Ctx.Le.refl _) V) (definable_rden _ _))

/-- ⭐⭐**`ret` along a witness at a companion shape, membership ⇒ truth**: as
    `sat_retC_of_mem`, along an arrow of `y`'s extent (`diaPush_canon_at`). -/
theorem sat_retxC_of_mem (hS : ModalSys.BStrong = true) (hRX : B.RetOutXC hS) {s : B.W}
    {i : ℕ} {y : VarSymb} {Y : VarType} (hY : ((B.w s).ctx i).ref y = some (.VTypeDia Y))
    {A : VarType} {cs : List (List Step)} {h : A.CompOk cs} {a : Ann (A.compsFlat cs)}
    (V : Term σ ((B.w s).ctx i) (A.compsFlat cs) a)
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) (.VTypeBox A)) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0), φ.size < Φ.size + 1 →
      (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (hm : ((OutLeg.pos y ⟨Y, hY⟩ : OutLeg ((B.w s).ctx i)).retS hS (.nec (.boxC A cs h)) V Φ :
      WFF σ _ 0) ∈ (B.w s).M i) :
    B.model.sat (B.canonEnv s i)
      ((OutLeg.pos y ⟨Y, hY⟩ : OutLeg ((B.w s).ctx i)).retS hS (.nec (.boxC A cs h)) V Φ :
        WFF σ _ 0) := by
  obtain ⟨k, hk, j, hj, b, g, hmem, hInd⟩ := hRX hY V Φ hm
  have hR := B.kdR hk
  have hsat := (IH k j _ (by unfold readArrowX; rw [WFF.size_subst]; omega)).mpr hmem
  have ha : (⟨k, ⟨Or.inl hR⟩⟩ : B.Acc s) ∈
      (B.model.posEval ((B.canonEnv s i).ref y hY)).1 := by
    rw [canonEnv_extent s i hY]
    exact Or.inl ⟨Y, B.kd_lb hk⟩
  rw [sat_readArrowX, ← diaPush_canon_at s i hY ⟨⟨k, ⟨Or.inl hR⟩⟩, ha⟩ (B.kd_lb hk) hj]
    at hsat
  refine ⟨Y, hY, ⟨⟨k, ⟨Or.inl hR⟩⟩, ha⟩, _, hsat, Or.inl (B.symm hR), ?_⟩
  change B.model.compsBack A cs (Model.interp (B.canonEnv k j) (Term.boxtm g)) _ _
  refine compsBack_of_ind A _ _ cs h _ ?_
  rw [← interp_canon _ (Model.Env.Agree.refl' _), ← interp_canon V (Model.Env.Agree.refl' _),
    Model.interp_subst _ _ _ (Ctx.noProjLast_boxIn _),
    ← boxPush_canon_at k _ ⟨s, ⟨Or.inl (B.symm hR)⟩⟩ (B.symm hR) le_rfl,
    Model.interp_compsVal] at hInd
  exact hInd

/-- ⭐⭐**`ret` along a witness, membership ⇒ truth at every necessary shape** (any T): as
    `sat_retS_nec_of_memC`, along `y` (`RetOutXC`). -/
theorem sat_retxS_nec_of_memC (hS : ModalSys.BStrong = true) (hRX : B.RetOutXC hS) {s : B.W}
    {i : ℕ} {y : VarSymb} (hy : ∃ Y, ((B.w s).ctx i).ref y = some (.VTypeDia Y)) {N : NShape}
    {a : Ann N.flat} (t : Term σ ((B.w s).ctx i) N.flat a)
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) N.ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.nec N) t Φ :
        WFF σ _ 0).size → (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (h : ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.nec N) t Φ : WFF σ _ 0) ∈
      (B.w s).M i) :
    B.model.sat (B.canonEnv s i)
      ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.nec N) t Φ : WFF σ _ 0) := by
  have hsz : ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.nec N) t Φ :
      WFF σ _ 0).size = Φ.size + N.flat.eqRecSize + 1 := rfl
  obtain ⟨Y, hY⟩ := hy
  have hp := BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by
    rw [List.mem_singleton.mp hψ]; exact h)
    ⟨retS_packG hS (.pos y ⟨Y, hY⟩) t Φ (Proof.lookup List.mem_cons_self)⟩
  have hsat := sat_retxC_of_mem hS hRX hY _ _ (fun s' K φ hφ => IH s' K φ (by
    unfold WFF.bodyRepl at hφ
    rw [WFF.size_subst] at hφ
    omega)) hp
  have hb := Model.sat_ret_map (B.canonEnv s i) (noProjLast s i) indCongr hS (.pos y ⟨Y, hY⟩)
    (S := .nec N.packed) (unpackG N) _ Φ hsat
  refine (congrArg (B.model.sat _) (OutLeg.retS_congr hS (.pos y ⟨Y, hY⟩) (.nec N) ?_ rfl)).mp hb
  rw [Term.holeRead_eq_holeAt, Term.holeRead_eq_holeAt]
  exact holeAt_packG_unpackG_val N t

end BData

/-! ## The limit -/

section LimitOutC

variable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} {hS : ModalSys.BStrong = true}
  (C : StrongChain hS M₀) (E : LimitEx C.toFairChain)

/-- ⭐⭐**The limit has returning successors at companion shapes** (plain leg; any T).  Name the
    missing companions (`ret_comps_named`), reorder to the born order (`ret_map` along `subC`),
    alias the value's tuple (`lalias`, `arrB`), move the value to the alias's arrangement
    (`alias_interch` at `unarr`'s slot formula, `unarrAt_arrB`, `unarrAt_eta`), and take the
    obligation's child (`lretC`).  The born root's readings home are `unarrT y` with `cs` selected
    (`subst_arrow_compsSlot_born`), `Ind` to `V` through the alias (`lalias_ind`, `ind_map`) and
    selecting back (`holeAt_subC_sel`). -/
theorem bdataS_retOutC (hW : ModalSys.BStrongW = false) : (bdataS C E).RetOutC hS := by
  classical
  intro s i A cs h a V Φ hm
  -- name the missing companions, and reorder to the born order
  obtain ⟨j₁, hij₁, a₁, V₁, hV₁, hm₁⟩ := BWorld.ret_comps_named ((bdataS C E).w s) hS
    (missComps A cs) (missComps_ok h) .nec V Φ hm
  set R := ShapeMap.subC (σ := σ) A (missComps A cs ++ cs) (bornComps A) (missComps_ok h)
    (bornComps_ok A) (missComps_sub A cs)
  set Φ₁ := WFF.mono ((((bdataS C E).w s).le hij₁).boxIn.insert (.bnd 0) (.VTypeBox A)) Φ
  have hm₂ : WFF.retS hS (.nec (bornShape A)) (Term.holeRead V₁ R.val.2) Φ₁ ∈
      ((bdataS C E).w s).M j₁ :=
    BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hm₁)
      ⟨Proof.ret_map hS .nec (S := .nec (.boxC A (missComps A cs ++ cs) (missComps_ok h)))
        R V₁ Φ₁ (Proof.conv (congrArg _ (WFF.bodyRepl_eta Φ₁).symm)
          (Proof.lookup List.mem_cons_self))⟩
  -- alias the value's tuple
  set W := Term.holeRead V₁ R.val.2
  set t := Term.holeAt W (arrB (σ := σ) A).2
  obtain ⟨i₂, hj₁i₂, l, hl, hal⟩ := lalias C s j₁ t
  obtain ⟨hsuf₂, hal₂⟩ := hal i₂ le_rfl
  have hM₂ := (C.good _).mcs s.1 (live_birth C.toFairChain s.2 (Nat.le_add_right _ i₂))
  have hy₂ : (ctxOf (lat s i₂)).ref (.root (.free l.length)) = some (VarType.VTypeBox A).bc :=
    (ctxOf_le_of_suffix hsuf₂).ref (ctxOf_ref_new _ l)
  have hii₂ : i ≤ i₂ := hij₁.trans hj₁i₂
  set Φ₂ : WFF σ ((ctxOf (lat s i₂)).boxIn.insert (.bnd 0) (.VTypeBox A)) 1 :=
    WFF.mono ((((bdataS C E).w s).le hii₂).boxIn.insert (.bnd 0) (.VTypeBox A)) Φ
  have hm₃ : WFF.retS hS (.nec (bornShape A))
      (Term.mono (((bdataS C E).w s).le hj₁i₂) W :
        Term σ (((bdataS C E).w s).ctx i₂) (RShape.nec (bornShape A)).flat _) Φ₂ ∈
      ((C.net (birth C.toFairChain s.2 + i₂)).st s.1).M := by
    have := (BWorld.mem_lift (w := (bdataS C E).w s) hj₁i₂).mp hm₂
    change WFF.retS hS (.nec (bornShape A)) (Term.mono _ W) (WFF.mono _ (WFF.mono _ Φ)) ∈ _
      at this
    rw [WFF.mono_mono] at this
    exact this
  -- move the value to the alias's arrangement
  have hi := alias_interch hsuf₂ hM₂ (Term.mono (ctxOf_le_of_suffix hl) t) hal₂
    (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (unarrHole (σ := σ) A).2)
      (WFF.retSlot hS (.nec (bornShape A)) Φ₂))
  have e₁ := WFF.instantiate_compSlot hS (.nec (bornShape A))
    (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (unarrHole (σ := σ) A).2) Φ₂
    (Term.mono (ctxOf_le_of_suffix hsuf₂) (Term.eta (.root (.free l.length)) _ (ctxOf_ref_new _ l)))
  have e₂ := WFF.instantiate_compSlot hS (.nec (bornShape A))
    (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (unarrHole (σ := σ) A).2) Φ₂
    (Term.mono (ctxOf_le_of_suffix hsuf₂) (Term.mono (aliasLe _ l)
      (Term.mono (ctxOf_le_of_suffix hl) t)))
  have e_y : (⟨_, Term.holeRead (Term.mono (ctxOf_le_of_suffix hsuf₂)
      (Term.eta (.root (.free l.length)) _ (ctxOf_ref_new _ l))) (unarrHole (σ := σ) A).2⟩ :
      Σ c, Term σ (ctxOf (lat s i₂)) _ c) = unarrT hy₂ := by
    rw [Term.holeRead_eq_holeAt]
    refine (holeAt_unarrHole A _).trans ?_
    rw [Term.mono_eta]
    exact unarrAt_eta hy₂
  have e_t : (⟨_, Term.holeRead (Term.mono (ctxOf_le_of_suffix hsuf₂)
      (Term.mono (aliasLe _ l) (Term.mono (ctxOf_le_of_suffix hl) t))) (unarrHole (σ := σ) A).2⟩ :
      Σ c, Term σ (ctxOf (lat s i₂)) _ c) =
      ⟨_, Term.mono (((bdataS C E).w s).le hj₁i₂) W⟩ := by
    rw [Term.holeRead_eq_holeAt]
    refine (holeAt_unarrHole A _).trans ?_
    rw [Term.mono_mono, Term.mono_mono]
    refine (unarrAt_sig A (Term.mono_holeAt_sig _ W _)).trans ?_
    exact unarrAt_arrB A _
  have hobl : WFF.retS hS (.nec (bornShape A)) (unarrT hy₂).2 Φ₂ ∈
      ((C.net (birth C.toFairChain s.2 + i₂)).st s.1).M :=
    (congrArg (· ∈ _) (e₁.trans (OutLeg.retS_congr hS .nec _ e_y rfl))).mp
      (hi.mpr ((congrArg (· ∈ _) (e₂.trans (OutLeg.retS_congr hS .nec _ e_t rfl))).mpr hm₃))
  -- the obligation's child
  obtain ⟨k, hsk, hcl, hback, hmk⟩ := lretC C hW s i₂ hy₂ Φ₂ hobl
  have hj : lstg C.toFairChain s k i ≤ lstg C.toFairChain s k i₂ := lstg_mono C hsk hii₂
  have hcK : (ctxOf (lat k (lstg C.toFairChain s k i₂))).ref (.root (.free 0)) =
      some (.VTypeBox A) := (ctxOf_le_of_suffix hcl).ref (born_ref A)
  refine ⟨k, hsk, lstg C.toFairChain s k i₂, hj, _,
    Term.eta (VarSymb.root (.free 0)).inner A (Ctx.ref_inner hcK), ?_, ?_⟩
  · have e := readArrow_mono_congr (C.lang_suffix (by omega)
      (live_birth C.toFairChain s.2 (Nat.le_add_right _ i))) (Ctx.Le.refl _)
      ((limgOk C.toFairChain hsk i).mono (((bdataS C E).w k).le hj))
      (limgOk C.toFairChain hsk i₂) (fun _ _ => rfl)
      (Term.boxtm (Term.eta (VarSymb.root (.free 0)).inner A (Ctx.ref_inner hcK))) Φ
    rw [Term.mono_refl, WFF.mono_refl] at e
    exact (congrArg (· ∈ _) e).mpr hmk
  -- the born root's readings home, `Ind` to `V`
  set K := lstg C.toFairChain k s (lstg C.toFairChain s k i₂)
  have hiK : i₂ ≤ K := by
    have h₁ := (lstg_spec C.toFairChain hsk i₂).1
    have h₂ := (lstg_spec C.toFairChain hsk.symm (lstg C.toFairChain s k i₂)).1
    omega
  have hyK := (((bdataS C E).w s).le hiK).ref hy₂
  set Sel := ShapeMap.subC (σ := σ) A (bornComps A) cs (bornComps_ok A) h (compOk_sub_born h)
  have eR : (⟨_, Term.subst (arrowIdx (limg C.toFairChain k s))
      (arrowS σ (ctxOf (lat s K)) (limg C.toFairChain k s))
      (ok_arrowS (limgOk C.toFairChain hsk.symm (lstg C.toFairChain s k i₂)))
      (coh_arrowS (limgOk C.toFairChain hsk.symm (lstg C.toFairChain s k i₂)))
      (compsVal (Term.eta (VarSymb.root (.free 0)).inner A (Ctx.ref_inner hcK)) cs h).2⟩ :
      Σ c, Term σ (ctxOf (lat s K)) (A.compsFlat cs) c) =
      ⟨_, Term.holeAt (unarrT (σ := σ) hyK).2 Sel.val.2⟩ := by
    rw [compsVal_eta hcK cs h]
    exact subst_arrow_compsSlot_born hcK (limgOk C.toFairChain hsk.symm _) hyK hback cs h
      (compOk_sub_born h)
  -- the alias, mapped
  have hA := lalias_ind C E s t hl hal hy₂
  rw [← BData.interp_canon _ (Model.Env.Agree.refl' _),
    ← BData.interp_canon t (Model.Env.Agree.refl' _)] at hA
  have hM := BData.ind_map (Term.holeAt (unarrHole (σ := σ) A).2 Sel.val.2) hA
  rw [← Model.interp_holeAt, ← Model.interp_holeAt] at hM
  have eL := congrArg (fun x : Σ c, Term σ (ctxOf (lat s i₂)) (A.compsFlat cs) c =>
    Model.interp ((bdataS C E).canonEnv s i₂) x.2)
    ((Term.holeAt_holeAt_sig _ _ _).trans (Term.holeAt_congr_sig
      ((holeAt_unarrHole A _).trans (unarrAt_eta hy₂)) Sel.val.2))
  have eRt := congrArg (fun x : Σ c, Term σ (ctxOf (lat s j₁)) (A.compsFlat cs) c =>
    Model.interp ((bdataS C E).canonEnv s j₁) x.2)
    ((Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
      ((holeAt_unarrHole A t).trans (unarrAt_arrB A W)) Sel.val.2).trans
      ((Term.holeAt_congr_sig (congrArg (Sigma.mk _) (Term.holeRead_eq_holeAt V₁ R.val.2))
        Sel.val.2).trans (holeAt_subC_sel h _ V₁ hV₁))))
  dsimp only at eL eRt
  rw [eL, eRt, Model.interp_mono (BData.canonEnv_le (B := bdataS C E) s hij₁) V] at hM
  have eK : Model.interp ((bdataS C E).canonEnv s K) (Term.holeAt (unarrT hyK).2 Sel.val.2) =
      Model.interp ((bdataS C E).canonEnv s i₂) (Term.holeAt (unarrT hy₂).2 Sel.val.2) := by
    have e := congrArg (fun x : Σ c, Term σ (ctxOf (lat s K)) (A.compsFlat cs) c =>
      Model.interp ((bdataS C E).canonEnv s K) x.2)
      ((Term.holeAt_congr_sig (mono_unarrT (((bdataS C E).w s).suf hiK) hy₂).symm
        Sel.val.2).trans (Term.mono_holeAt_sig _ _ _).symm)
    exact e.trans (Model.interp_mono (BData.canonEnv_le (B := bdataS C E) s hiK) _)
  rw [← BData.interp_canon _ (Model.Env.Agree.refl' _),
    ← BData.interp_canon V (Model.Env.Agree.refl' _)]
  refine (congrArg (fun o => (bdataS C E).Ind o _)
    ((congrArg (fun x : Σ c, Term σ (ctxOf (lat s K)) (A.compsFlat cs) c =>
      Model.interp ((bdataS C E).canonEnv s K) x.2) eR).trans eK)).mpr hM


/-- ⭐⭐**The limit has returning successors along a witness at companion shapes** (any T): as
    `bdataS_retOutC`, along `y` (`ret_comps_named` along the leg, `OutLeg.instantiate_compSlot`,
    the witness child `lretXC`). -/
theorem bdataS_retOutXC (hW : ModalSys.BStrongW = false) : (bdataS C E).RetOutXC hS := by
  classical
  intro s i y Y hy A cs h a V Φ hm
  -- name the missing companions, and reorder to the born order
  obtain ⟨j₁, hij₁, a₁, V₁, hV₁, hm₁⟩ := BWorld.ret_comps_named ((bdataS C E).w s) hS
    (missComps A cs) (missComps_ok h) (.pos y ⟨Y, hy⟩) V Φ hm
  have hy₁ := (((bdataS C E).w s).le hij₁).ref hy
  set R := ShapeMap.subC (σ := σ) A (missComps A cs ++ cs) (bornComps A) (missComps_ok h)
    (bornComps_ok A) (missComps_sub A cs)
  set Φ₁ := WFF.mono (((((bdataS C E).w s).le hij₁).diaIn y).insert (.bnd 0) (.VTypeBox A)) Φ
  have hm₂ : (OutLeg.pos y ⟨Y, hy₁⟩ : OutLeg (((bdataS C E).w s).ctx j₁)).retS hS
      (.nec (bornShape A)) (Term.holeRead V₁ R.val.2) Φ₁ ∈ ((bdataS C E).w s).M j₁ :=
    BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hm₁)
      ⟨Proof.ret_map hS (.pos y ⟨Y, hy₁⟩)
        (S := .nec (.boxC A (missComps A cs ++ cs) (missComps_ok h)))
        R V₁ Φ₁ (Proof.conv (congrArg _ (WFF.bodyRepl_eta Φ₁).symm)
          (Proof.lookup List.mem_cons_self))⟩
  -- alias the value's tuple
  set W := Term.holeRead V₁ R.val.2
  set t := Term.holeAt W (arrB (σ := σ) A).2
  obtain ⟨i₂, hj₁i₂, l, hl, hal⟩ := lalias C s j₁ t
  obtain ⟨hsuf₂, hal₂⟩ := hal i₂ le_rfl
  have hM₂ := (C.good _).mcs s.1 (live_birth C.toFairChain s.2 (Nat.le_add_right _ i₂))
  have hy₂ : (ctxOf (lat s i₂)).ref (.root (.free l.length)) = some (VarType.VTypeBox A).bc :=
    (ctxOf_le_of_suffix hsuf₂).ref (ctxOf_ref_new _ l)
  have hii₂ : i ≤ i₂ := hij₁.trans hj₁i₂
  have hyi₂ := (((bdataS C E).w s).le hii₂).ref hy
  set Φ₂ : WFF σ (((ctxOf (lat s i₂)).diaIn y).insert (.bnd 0) (.VTypeBox A)) 1 :=
    WFF.mono (((((bdataS C E).w s).le hii₂).diaIn y).insert (.bnd 0) (.VTypeBox A)) Φ
  have hm₃ : (OutLeg.pos y ⟨Y, hyi₂⟩ : OutLeg (((bdataS C E).w s).ctx i₂)).retS hS
      (.nec (bornShape A))
      (Term.mono (((bdataS C E).w s).le hj₁i₂) W :
        Term σ (((bdataS C E).w s).ctx i₂) (RShape.nec (bornShape A)).flat _) Φ₂ ∈
      ((C.net (birth C.toFairChain s.2 + i₂)).st s.1).M := by
    have := (BWorld.mem_lift (w := (bdataS C E).w s) hj₁i₂).mp hm₂
    change (OutLeg.pos y ⟨Y, hyi₂⟩ : OutLeg (((bdataS C E).w s).ctx i₂)).retS hS
      (.nec (bornShape A)) (Term.mono _ W) (WFF.mono _ (WFF.mono _ Φ)) ∈ _ at this
    rw [WFF.mono_mono] at this
    exact this
  -- move the value to the alias's arrangement
  have hi := alias_interch hsuf₂ hM₂ (Term.mono (ctxOf_le_of_suffix hl) t) hal₂
    (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (unarrHole (σ := σ) A).2)
      ((OutLeg.pos y ⟨Y, hyi₂⟩ : OutLeg (ctxOf (lat s i₂))).retSlot hS (.nec (bornShape A)) Φ₂))
  have e₁ := OutLeg.instantiate_compSlot hS (.pos y ⟨Y, hyi₂⟩) (.nec (bornShape A))
    (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (unarrHole (σ := σ) A).2) Φ₂
    (Term.mono (ctxOf_le_of_suffix hsuf₂) (Term.eta (.root (.free l.length)) _ (ctxOf_ref_new _ l)))
  have e₂ := OutLeg.instantiate_compSlot hS (.pos y ⟨Y, hyi₂⟩) (.nec (bornShape A))
    (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (unarrHole (σ := σ) A).2) Φ₂
    (Term.mono (ctxOf_le_of_suffix hsuf₂) (Term.mono (aliasLe _ l)
      (Term.mono (ctxOf_le_of_suffix hl) t)))
  have e_y : (⟨_, Term.holeRead (Term.mono (ctxOf_le_of_suffix hsuf₂)
      (Term.eta (.root (.free l.length)) _ (ctxOf_ref_new _ l))) (unarrHole (σ := σ) A).2⟩ :
      Σ c, Term σ (ctxOf (lat s i₂)) _ c) = unarrT hy₂ := by
    rw [Term.holeRead_eq_holeAt]
    refine (holeAt_unarrHole A _).trans ?_
    rw [Term.mono_eta]
    exact unarrAt_eta hy₂
  have e_t : (⟨_, Term.holeRead (Term.mono (ctxOf_le_of_suffix hsuf₂)
      (Term.mono (aliasLe _ l) (Term.mono (ctxOf_le_of_suffix hl) t))) (unarrHole (σ := σ) A).2⟩ :
      Σ c, Term σ (ctxOf (lat s i₂)) _ c) =
      ⟨_, Term.mono (((bdataS C E).w s).le hj₁i₂) W⟩ := by
    rw [Term.holeRead_eq_holeAt]
    refine (holeAt_unarrHole A _).trans ?_
    rw [Term.mono_mono, Term.mono_mono]
    refine (unarrAt_sig A (Term.mono_holeAt_sig _ W _)).trans ?_
    exact unarrAt_arrB A _
  have hobl : WFF.retxS hS y ⟨Y, hyi₂⟩ (.nec (bornShape A)) (unarrT hy₂).2 Φ₂ ∈
      ((C.net (birth C.toFairChain s.2 + i₂)).st s.1).M :=
    (congrArg (· ∈ _) (e₁.trans (OutLeg.retS_congr hS (.pos y ⟨Y, hyi₂⟩) _ e_y rfl))).mp
      (hi.mpr ((congrArg (· ∈ _)
        (e₂.trans (OutLeg.retS_congr hS (.pos y ⟨Y, hyi₂⟩) _ e_t rfl))).mpr hm₃))
  -- the obligation's witness child
  obtain ⟨k, hk, hcl, hback, hmk⟩ := lretXC C hW s i₂ hy₂ hyi₂ Φ₂ hobl
  have hsk := lkdR hk
  have hj : lstg C.toFairChain s k i ≤ lstg C.toFairChain s k i₂ := lstg_mono C hsk hii₂
  have hcK : (ctxOf (lat k (lstg C.toFairChain s k i₂))).ref (.root (.free 0)) =
      some (.VTypeBox A) := (ctxOf_le_of_suffix hcl).ref (born_ref A)
  refine ⟨k, hk, lstg C.toFairChain s k i₂, hj, _,
    Term.eta (VarSymb.root (.free 0)).inner A (Ctx.ref_inner hcK), ?_, ?_⟩
  · have e := readArrowX_mono_congr (C.lang_suffix (by omega)
      (live_birth C.toFairChain s.2 (Nat.le_add_right _ i))) (Ctx.Le.refl _)
      ((limgOk C.toFairChain hsk i).mono (((bdataS C E).w k).le hj))
      (limgOk C.toFairChain hsk i₂) (fun _ _ => rfl) hy hyi₂
      ((((bdataS C E).w k).le hj).ref ((bdataS C E).hcx hk i)) (lhcx C.toFairChain hk i₂)
      (Term.boxtm (Term.eta (VarSymb.root (.free 0)).inner A (Ctx.ref_inner hcK))) Φ
    rw [Term.mono_refl, WFF.mono_refl] at e
    exact (congrArg (· ∈ _) e).mpr hmk
  -- the born root's readings home, `Ind` to `V`
  set K := lstg C.toFairChain k s (lstg C.toFairChain s k i₂)
  have hiK : i₂ ≤ K := by
    have h₁ := (lstg_spec C.toFairChain hsk i₂).1
    have h₂ := (lstg_spec C.toFairChain hsk.symm (lstg C.toFairChain s k i₂)).1
    omega
  have hyK := (((bdataS C E).w s).le hiK).ref hy₂
  set Sel := ShapeMap.subC (σ := σ) A (bornComps A) cs (bornComps_ok A) h (compOk_sub_born h)
  have eR : (⟨_, Term.subst (arrowIdx (limg C.toFairChain k s))
      (arrowS σ (ctxOf (lat s K)) (limg C.toFairChain k s))
      (ok_arrowS (limgOk C.toFairChain hsk.symm (lstg C.toFairChain s k i₂)))
      (coh_arrowS (limgOk C.toFairChain hsk.symm (lstg C.toFairChain s k i₂)))
      (compsVal (Term.eta (VarSymb.root (.free 0)).inner A (Ctx.ref_inner hcK)) cs h).2⟩ :
      Σ c, Term σ (ctxOf (lat s K)) (A.compsFlat cs) c) =
      ⟨_, Term.holeAt (unarrT (σ := σ) hyK).2 Sel.val.2⟩ := by
    rw [compsVal_eta hcK cs h]
    exact subst_arrow_compsSlot_born hcK (limgOk C.toFairChain hsk.symm _) hyK hback cs h
      (compOk_sub_born h)
  -- the alias, mapped
  have hA := lalias_ind C E s t hl hal hy₂
  rw [← BData.interp_canon _ (Model.Env.Agree.refl' _),
    ← BData.interp_canon t (Model.Env.Agree.refl' _)] at hA
  have hM := BData.ind_map (Term.holeAt (unarrHole (σ := σ) A).2 Sel.val.2) hA
  rw [← Model.interp_holeAt, ← Model.interp_holeAt] at hM
  have eL := congrArg (fun x : Σ c, Term σ (ctxOf (lat s i₂)) (A.compsFlat cs) c =>
    Model.interp ((bdataS C E).canonEnv s i₂) x.2)
    ((Term.holeAt_holeAt_sig _ _ _).trans (Term.holeAt_congr_sig
      ((holeAt_unarrHole A _).trans (unarrAt_eta hy₂)) Sel.val.2))
  have eRt := congrArg (fun x : Σ c, Term σ (ctxOf (lat s j₁)) (A.compsFlat cs) c =>
    Model.interp ((bdataS C E).canonEnv s j₁) x.2)
    ((Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
      ((holeAt_unarrHole A t).trans (unarrAt_arrB A W)) Sel.val.2).trans
      ((Term.holeAt_congr_sig (congrArg (Sigma.mk _) (Term.holeRead_eq_holeAt V₁ R.val.2))
        Sel.val.2).trans (holeAt_subC_sel h _ V₁ hV₁))))
  dsimp only at eL eRt
  rw [eL, eRt, Model.interp_mono (BData.canonEnv_le (B := bdataS C E) s hij₁) V] at hM
  have eK : Model.interp ((bdataS C E).canonEnv s K) (Term.holeAt (unarrT hyK).2 Sel.val.2) =
      Model.interp ((bdataS C E).canonEnv s i₂) (Term.holeAt (unarrT hy₂).2 Sel.val.2) := by
    have e := congrArg (fun x : Σ c, Term σ (ctxOf (lat s K)) (A.compsFlat cs) c =>
      Model.interp ((bdataS C E).canonEnv s K) x.2)
      ((Term.holeAt_congr_sig (mono_unarrT (((bdataS C E).w s).suf hiK) hy₂).symm
        Sel.val.2).trans (Term.mono_holeAt_sig _ _ _).symm)
    exact e.trans (Model.interp_mono (BData.canonEnv_le (B := bdataS C E) s hiK) _)
  rw [← BData.interp_canon _ (Model.Env.Agree.refl' _),
    ← BData.interp_canon V (Model.Env.Agree.refl' _)]
  refine (congrArg (fun o => (bdataS C E).Ind o _)
    ((congrArg (fun x : Σ c, Term σ (ctxOf (lat s K)) (A.compsFlat cs) c =>
      Model.interp ((bdataS C E).canonEnv s K) x.2) eR).trans eK)).mpr hM

end LimitOutC

end BArrow

end V12M
