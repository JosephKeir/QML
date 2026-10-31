import QML.QML_v12m_RetLift
import QML.QML_v12m_RetK
import QML.QML_v12m_BRetChildC
import QML.QML_v12m_BRetOutC

/-!
# QML v12m — strong B on S5: lifting at every necessary shape

`Proof.ret_lift` lifts a returning possibility of one necessary object, because `ret_counit` and the
unit live at that shape.  At a necessary shape `N`, pairs and companions included, pack everything
into one object `p : □N.flat` (`NShape.packMap`, `ret_map`) and lift that.

The object itself can be read back off `p` (`NShape.unpack`), but its companions cannot: `p` knows
the companions' contents, not that they are the companions of what it holds.  So the body also
carries one **tie** per companion, `□ Back (Y.keep.dup) x`, for `Y` the companion and `x` its
contents in `p` (`WFF.nTies`), which is `back_keep` at the packed object (`Proof.nTies_intro`).
-/

namespace V12M

universe u v

variable [ModalSys] {σ : Signature}

open BArrow

/-! ## Packing -/

/-- ⭐**Packing a necessary shape** into one necessary object. -/
def NShape.packMap {σ : Signature} : (N : NShape) → ShapeMap σ N (.box N.flat)
  | .boxC A cs h => .packC A cs h
  | .prod R S => .comp
      (.pair (.comp (.fst R S) (NShape.packMap R)) (.comp (.snd R S) (NShape.packMap S)))
      (.pack R.flat S.flat)

/-- A shape's contents, read off an address of it. -/
def NShape.contents {Δ₀ Δ' : Ctx} (hle : Δ₀.boxIn.Le Δ') : (N : NShape) → (u : VarSymb) →
    Δ₀.ref u = some N.ty → Σ b, Term σ Δ' N.flat b
  | .boxC _ cs h, _, hu => compsSlot hu hle cs h
  | .prod R S, _, hu => ⟨_, Term.pair (NShape.contents hle R _ (Ctx.ref_fst_of hu)).2
      (NShape.contents hle S _ (Ctx.ref_snd_of hu)).2⟩

/-- The shape read back off its contents, at an address of a `□` view. -/
def NShape.unpack {Γ : Ctx} : (N : NShape) → (z : VarSymb) → Γ.boxIn.ref z = some N.flat →
    Σ b, Term σ Γ N.ty b
  | .boxC A cs _, z, hz => ⟨_, Term.boxtm (Term.eta (z.ext (compsFst cs)) A
      (Ctx.ref_compsFst cs hz))⟩
  | .prod R S, _, hz => ⟨_, Term.pair (NShape.unpack R _ (Ctx.ref_fst_of hz)).2
      (NShape.unpack S _ (Ctx.ref_snd_of hz)).2⟩

omit [ModalSys] in
/-- A companion's type, as the option it is read from. -/
theorem compAt_getD {A : VarType} {p : List Step} (h : (A.compAt p).isSome = true) :
    A.compAt p = some ((A.compAt p).getD .VTypeOne) := by
  obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp h
  rw [hC]
  rfl

/-- The object's contents with its companions, filled at an address. -/
theorem Term.subst_compsBody {ι : VarSymb → VarSymb} {Γ : Ctx} {A : VarType} {u : VarSymb}
    (hu : Γ.ref u = some (.VTypeBox A)) (θ : Subst σ Γ)
    (hθ : Subst.Ok (Ctx.empty.insert (.bnd 0) (.VTypeBox A)) θ)
    (hc : Subst.Coh ι (Ctx.empty.insert (.bnd 0) (.VTypeBox A)) θ)
    (hat : θ.at (.root (.bnd 0)) = .tm (Term.eta u (.VTypeBox A) hu)) :
    ∀ (cs : List (List Step)) (h : A.CompOk cs),
      (⟨_, Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) (compsBody A cs h).2⟩ :
        Σ a, Term σ Γ.boxIn (A.compsFlat cs) a) = compsSlot hu (Ctx.Le.refl _) cs h
  | [], _ => Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ hat)
  | p :: ps, h => by
      obtain ⟨hT, hall, -⟩ := h.resolve_left (List.cons_ne_nil _ _)
      exact sig_pair (Term.subst_compsBody hu θ hθ hc hat ps h.tail)
        (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _
          (Subst.at_ext_eta hT θ (.here :: p) hu (compAt_getD (hall p List.mem_cons_self))
            (h.ref_head hu) hat)))

/-- ⭐The packed object at an address. -/
theorem NShape.holeAt_packObj {Γ : Ctx} : ∀ (N : NShape) (u : VarSymb) (hu : Γ.ref u = some N.ty),
    (⟨_, Term.holeAt (Term.eta (σ := σ) u N.ty hu) (NShape.packMap (σ := σ) N).obj.2⟩ :
      Σ b, Term σ Γ (.VTypeBox N.flat) b) =
      ⟨_, Term.boxtm (NShape.contents (σ := σ) (Ctx.Le.refl _) N u hu).2⟩
  | .boxC A cs h, u, hu =>
      have hu' : Γ.ref u = some (.VTypeBox A) := hu
      sig_boxtm (Term.subst_compsBody hu' (Subst.single (.bnd 0) (.tm (Term.eta u _ hu')))
        (Subst.ok_single (Ctx.empty_le Γ) rfl)
        (Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le Γ) rfl)
        (Subst.at_single_root _ _) cs h)
  | .prod R S, u, hu => by
      have hR := NShape.holeAt_packObj R _ (Ctx.ref_fst_of hu)
      have hS := NShape.holeAt_packObj S _ (Ctx.ref_snd_of hu)
      let t := Term.eta (σ := σ) u (NShape.prod R S).ty hu
      let X₁ := Term.holeAt (Term.eta (σ := σ) (.step (.root (.bnd 0)) .fst) R.ty
        (Ctx.ref_fst_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (NShape.prod R S).ty)))
        (NShape.packMap (σ := σ) R).obj.2
      let X₂ := Term.holeAt (Term.eta (σ := σ) (.step (.root (.bnd 0)) .snd) S.ty
        (Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (NShape.prod R S).ty)))
        (NShape.packMap (σ := σ) S).obj.2
      have e₁ : (⟨_, Term.holeAt t X₁⟩ : Σ b, Term σ Γ (.VTypeBox R.flat) b) =
          ⟨_, Term.boxtm (NShape.contents (σ := σ) (Ctx.Le.refl _) R _ (Ctx.ref_fst_of hu)).2⟩ :=
        (Term.holeAt_holeAt_sig t _ _).trans ((Term.holeAt_congr_sig
          (Term.holeAt_pair_fst _ _) _).trans hR)
      have e₂ : (⟨_, Term.holeAt t X₂⟩ : Σ b, Term σ Γ (.VTypeBox S.flat) b) =
          ⟨_, Term.boxtm (NShape.contents (σ := σ) (Ctx.Le.refl _) S _ (Ctx.ref_snd_of hu)).2⟩ :=
        (Term.holeAt_holeAt_sig t _ _).trans ((Term.holeAt_congr_sig
          (Term.holeAt_pair_snd _ _) _).trans hS)
      refine (Term.holeAt_holeAt_sig t (Term.pair X₁ X₂) _).trans
        ((Term.holeAt_congr_sig (sig_pair e₁ e₂) _).trans (sig_boxtm (sig_pair ?_ ?_)))
      · refine Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ ?_)
        rw [Subst.at_proj _ _ rfl, Subst.at_single_root]
        rfl
      · refine Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ ?_)
        rw [Subst.at_proj _ _ rfl, Subst.at_single_root]
        rfl

/-- ⭐The value comes back unchanged by packing. -/
theorem NShape.holeAt_packVal {Γ : Ctx} : ∀ (N : NShape) {a : Ann N.flat} (t : Term σ Γ N.flat a),
    (⟨_, Term.holeAt t (NShape.packMap (σ := σ) N).val.2⟩ : Σ b, Term σ Γ N.flat b) = ⟨_, t⟩
  | .boxC _ _ _, _, t => Term.subst_eta_tm _ _ _ _ _ _ t (Subst.at_single_root _ _)
  | .prod R S, _, .pair t₁ t₂ => by
      let X := Term.pair
        (Term.holeAt (Term.eta (σ := σ) (.step (.root (.bnd 0)) .fst) R.flat
          (Ctx.ref_fst_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (NShape.prod R S).flat)))
          (NShape.packMap (σ := σ) R).val.2)
        (Term.holeAt (Term.eta (σ := σ) (.step (.root (.bnd 0)) .snd) S.flat
          (Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (NShape.prod R S).flat)))
          (NShape.packMap (σ := σ) S).val.2)
      refine (Term.holeAt_holeAt_sig (Term.pair t₁ t₂) X _).trans ?_
      refine (Term.subst_eta_tm _ _ _ (.VTypeProd R.flat S.flat) (.root (.bnd 0))
        (Ctx.ref_insert_root Ctx.empty (.bnd 0) _) (Term.holeAt (Term.pair t₁ t₂) X)
        (Subst.at_single_root _ _)).trans (sig_pair ?_ ?_)
      · exact (Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
          (Term.holeAt_pair_fst _ _) _).trans (NShape.holeAt_packVal R t₁))
      · exact (Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
          (Term.holeAt_pair_snd _ _) _).trans (NShape.holeAt_packVal S t₂))

/-- ⭐Reading the shape back off its contents gives the address. -/
theorem NShape.subst_unpack {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) : ∀ (N : NShape) (z : VarSymb)
    (hz : Γ.boxIn.ref z = some N.flat) (u : VarSymb) (hu : Δ.ref u = some N.ty),
    θ.box.at z = .tm (NShape.contents (Ctx.Le.refl _) N u hu).2 →
    (⟨_, Term.subst ι θ hθ hc (NShape.unpack (σ := σ) N z hz).2⟩ : Σ b, Term σ Δ N.ty b) =
      ⟨_, Term.eta u N.ty hu⟩
  | .boxC _ cs h, z, _, _, hu, hat => sig_boxtm (Term.subst_eta_tm _ _ _ _ _ _ _
      (at_compsFst_compsSlot _ hu (Ctx.Le.refl _) cs h z hat))
  | .prod R S, z, hz, u, hu, hat => by
      refine sig_pair (NShape.subst_unpack θ hθ hc R _ (Ctx.ref_fst_of hz) _ (Ctx.ref_fst_of hu) ?_)
        (NShape.subst_unpack θ hθ hc S _ (Ctx.ref_snd_of hz) _ (Ctx.ref_snd_of hu) ?_)
      · rw [Subst.at_proj _ _ rfl, hat]
        rfl
      · rw [Subst.at_proj _ _ rfl, hat]
        rfl

/-! ## The ties of the companions -/

section Ties

/-- One tie per companion of `e : □A`, its contents being at `z` one view in, under `snd`s and
    `fst`s: `□ Back (Y.keep.dup) x`, `Y` the companion, `x` its contents. -/
def WFF.cTies (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) {Ω : Ctx} {d : ℕ}
    (hs : Ω.SlotsFrom d) {A : VarType} (e : VarSymb) (he : Ω.ref e = some (.VTypeBox A)) :
    (cs : List (List Step)) → A.CompOk cs → (z : VarSymb) →
    Ω.boxIn.ref z = some (A.compsFlat cs) → WFF σ Ω d
  | [], _, _, _ => .top
  | q :: ps, h, z, hz => WFF.and
      (WFF.box (WFF.holeAt hs.boxIn
        (Term.pair (Term.eta (.step z .snd) ((A.compAt q).getD .VTypeOne) (Ctx.ref_snd_of hz))
          (Term.eta (.step ((VarSymb.step e .here).ext q) .keep)
            (.VTypeBox ((A.compAt q).getD .VTypeOne))
            (Ctx.ref_keep_of' hF (h.ref_head he) rfl)))
        (WFF.backDup hS hF _)))
      (WFF.cTies hS hF hs e he ps h.tail (.step z .fst) (Ctx.ref_fst_of hz))

/-- ⭐**The ties of a necessary shape.** -/
def WFF.nTies (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) {Ω : Ctx} {d : ℕ}
    (hs : Ω.SlotsFrom d) : (N : NShape) → (e : VarSymb) → Ω.ref e = some N.ty → (z : VarSymb) →
    Ω.boxIn.ref z = some N.flat → WFF σ Ω d
  | .boxC _ cs h, e, he, z, hz => WFF.cTies hS hF hs e he cs h z hz
  | .prod R S, _, he, _, hz => WFF.and
      (WFF.nTies hS hF hs R _ (Ctx.ref_fst_of he) _ (Ctx.ref_fst_of hz))
      (WFF.nTies hS hF hs S _ (Ctx.ref_snd_of he) _ (Ctx.ref_snd_of hz))

variable {Γ Ω : Ctx} [Γ.NoSlots] {d : ℕ} {ι : VarSymb → VarSymb} (θ : Subst σ Γ)
  (hθ : Subst.Ok Ω θ) (hc : Subst.Coh ι Ω θ) (hs : Ω.SlotsFrom d) (hs' : Γ.SlotsFrom 0)

/-- Each companion's tie is `back_keep`. -/
def Proof.cTies_intro (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} {A : VarType} (e : VarSymb)
    (he : Ω.ref e = some (.VTypeBox A)) (u : VarSymb) (hu : Γ.ref u = some (.VTypeBox A))
    (hat : θ.at e = .tm (Term.eta u (.VTypeBox A) hu)) :
    (cs : List (List Step)) → (h : A.CompOk cs) → (z : VarSymb) →
    (hz : Ω.boxIn.ref z = some (A.compsFlat cs)) →
    θ.box.at z = .tm (compsSlot hu (Ctx.Le.refl _) cs h).2 →
    Proof σ Γ Δ (WFF.subst ι θ hθ hc hs hs' (WFF.cTies hS hF hs e he cs h z hz))
  | [], _, _, _, _ => Proof.top_intro
  | q :: ps, h, z, hz, hzat => by
      obtain ⟨-, hall, -⟩ := h.resolve_left (List.cons_ne_nil _ _)
      refine Proof.and_intro ?_ (Proof.cTies_intro hS hT hF e he u hu hat ps h.tail _
        (Ctx.ref_fst_of hz) (by rw [Subst.at_proj _ _ rfl, hzat]; rfl))
      have hq := compAt_getD (hall q List.mem_cons_self)
      have hY := Subst.at_ext_eta hT θ (.here :: q) hu hq (h.ref_head hu) hat
      let C := (A.compAt q).getD .VTypeOne
      have hY' : Γ.ref ((VarSymb.step u .here).ext q) = some (.VTypeBox C) := h.ref_head hu
      let x := Term.eta (σ := σ) ((VarSymb.step u .here).ext q).inner C (Ctx.ref_inner hY')
      have hY : θ.at ((VarSymb.step e .here).ext q) =
          .tm (Term.eta ((VarSymb.step u .here).ext q) (.VTypeBox C) hY') :=
        Subst.at_ext_eta hT θ (.here :: q) hu hq hY' hat
      have ha : θ.box.at (.step z .snd) = .tm x := by
        rw [Subst.at_proj _ _ rfl, hzat]
        rfl
      have hb : θ.box.at (.step ((VarSymb.step e .here).ext q) .keep) =
          .tm (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) x)) := by
        rw [Subst.box_at_keep, hY]
        exact SubE.keepE_tm x hF
      refine Proof.conv (congrArg WFF.box ((WFF.subst_holeAt θ.box (Subst.ok_box hθ)
        (Subst.coh_box hθ hc) hs.boxIn hs'.boxIn
        (Term.pair (Term.eta (.step z .snd) C (Ctx.ref_snd_of hz))
          (Term.eta (.step ((VarSymb.step e .here).ext q) .keep) (.VTypeBox C)
            (Ctx.ref_keep_of' hF (h.ref_head he) rfl))) (WFF.backDup hS hF C)).trans
        (WFF.holeAt_congr _ (sig_pair (Term.subst_eta_tm _ _ _ _ _ _ x ha)
          (Term.subst_eta_tm _ _ _ _ _ _ _ hb)) _))).symm ?_
      exact Proof.nec (Proof.conv (WFF.holeAt_backDup hS hF _ _ _).symm
        (Proof.back_shift hS hT hF x))

/-- ⭐**The ties of a shape** are `back_keep`, at the object's own contents. -/
def Proof.nTies_intro (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} :
    (N : NShape) → (e : VarSymb) → (he : Ω.ref e = some N.ty) → (u : VarSymb) →
    (hu : Γ.ref u = some N.ty) → θ.at e = .tm (Term.eta u N.ty hu) → (z : VarSymb) →
    (hz : Ω.boxIn.ref z = some N.flat) →
    θ.box.at z = .tm (NShape.contents (Ctx.Le.refl _) N u hu).2 →
    Proof σ Γ Δ (WFF.subst ι θ hθ hc hs hs' (WFF.nTies hS hF hs N e he z hz))
  | .boxC _ cs h, e, he, u, hu, hat, z, hz, hzat =>
      Proof.cTies_intro θ hθ hc hs hs' hS hT hF e he u hu hat cs h z hz hzat
  | .prod R S, e, he, u, hu, hat, z, hz, hzat => Proof.and_intro
      (Proof.nTies_intro hS hT hF R _ (Ctx.ref_fst_of he) _ (Ctx.ref_fst_of hu)
        (by rw [Subst.at_proj _ _ rfl, hat]; rfl) _ (Ctx.ref_fst_of hz)
        (by rw [Subst.at_proj _ _ rfl, hzat]; rfl))
      (Proof.nTies_intro hS hT hF S _ (Ctx.ref_snd_of he) _ (Ctx.ref_snd_of hu)
        (by rw [Subst.at_proj _ _ rfl, hat]; rfl) _ (Ctx.ref_snd_of hz)
        (by rw [Subst.at_proj _ _ rfl, hzat]; rfl))

end Ties

/-! ## The packed body -/

section Packed

/-- The hole of a shape's ties: the object, and the object packed. -/
abbrev packHoleTy (N : NShape) : VarType := .VTypeProd N.ty (.VTypeBox N.flat)

/-- The ties, on the hole `⟨e, p⟩`. -/
def WFF.packTies (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) (N : NShape) :
    WFF σ (Ctx.empty.insert (.bnd 0) (packHoleTy N)) 1 :=
  WFF.nTies hS hF (Ctx.slotsFrom_empty.insert _) N (.step (.root (.bnd 0)) .fst)
    (Ctx.ref_fst_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (packHoleTy N)))
    (VarSymb.step (.root (.bnd 0)) .snd).inner
    (Ctx.ref_inner (Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (packHoleTy N))))

/-- ⭐The ties hold of an object and its own packing. -/
def Proof.packTies_intro (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (N : NShape)
    (u : VarSymb) (hu : Γ.ref u = some N.ty) :
    Proof σ Γ Δ (WFF.holeAt Ctx.NoSlots.slots (Term.pair (Term.eta u N.ty hu)
      (Term.boxtm (NShape.contents (Ctx.Le.refl _) N u hu).2)) (WFF.packTies hS hF N)) := by
  have hr := Subst.at_single_root (σ := σ) (Δ := Γ) (.bnd 0) (.tm (Term.pair (Term.eta u N.ty hu)
    (Term.boxtm (NShape.contents (Ctx.Le.refl _) N u hu).2)))
  exact Proof.nTies_intro _ _ _ _ _ hS hT hF N _ _ u hu
    (by rw [Subst.at_proj _ _ rfl, hr]; rfl) _ _
    (Subst.box_at_inner_boxtm _ (by rw [Subst.at_proj _ _ rfl, hr]; rfl))

/-- The object read back off the packed object at the hole. -/
abbrev NShape.unpack₀ (N : NShape) :
    Σ b, Term σ (Ctx.empty.insert (.bnd 0) (.VTypeBox N.flat)) N.ty b :=
  NShape.unpack N (VarSymb.root (.bnd 0)).inner
    (Ctx.ref_inner (Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox N.flat)))

variable {V : Ctx} [V.NoSlots] {N : NShape}

/-- ⭐**The packed body**: `Φ` of the object read back, with its ties. -/
def WFF.packedBody (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true)
    (Φ : WFF σ (V.insert (.bnd 0) N.ty) 1) : WFF σ (V.insert (.bnd 0) (.VTypeBox N.flat)) 1 :=
  WFF.and (WFF.bodyRepl (Term.mono ((Ctx.empty_le V).insert (.bnd 0) _) (NShape.unpack₀ N).2) Φ)
    (WFF.holeAt ((Ctx.NoSlots.slots (Γ := V)).insert _)
      (Term.mono ((Ctx.empty_le V).insert (.bnd 0) _) (Term.pair (NShape.unpack₀ N).2
        (Term.eta (.root (.bnd 0)) (.VTypeBox N.flat)
          (Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox N.flat)))))
      (WFF.packTies hS hF N))

/-- The packed body under a weakening of the view. -/
theorem WFF.mono_packedBody {V' : Ctx} [V'.NoSlots] (h : V.Le V') (hS : ModalSys.BStrong = true)
    (hF : ModalSys.Four = true) (Φ : WFF σ (V.insert (.bnd 0) N.ty) 1) :
    WFF.mono (h.insert (.bnd 0) _) (WFF.packedBody hS hF Φ) =
      WFF.packedBody hS hF (WFF.mono (h.insert (.bnd 0) _) Φ) := by
  refine congrArg₂ WFF.and ?_ ?_
  · rw [WFF.mono_bodyRepl h, Term.mono_mono]
  · rw [WFF.mono_holeAt _ _ ((Ctx.NoSlots.slots (Γ := V')).insert _), Term.mono_mono]

/-- ⭐The packed body at an object's own packing. -/
theorem WFF.instantiate_packedBody (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true)
    (Φ : WFF σ (V.insert (.bnd 0) N.ty) 1) (u : VarSymb) (hu : V.ref u = some N.ty) :
    WFF.instantiate Ctx.NoSlots.slots (Term.boxtm (NShape.contents (Ctx.Le.refl _) N u hu).2)
        (WFF.packedBody hS hF Φ) =
      WFF.and (WFF.instantiate Ctx.NoSlots.slots (Term.eta u N.ty hu) Φ)
        (WFF.holeAt Ctx.NoSlots.slots (Term.pair (Term.eta u N.ty hu)
          (Term.boxtm (NShape.contents (Ctx.Le.refl _) N u hu).2)) (WFF.packTies hS hF N)) := by
  have hat := Subst.at_single_root (σ := σ) (Δ := V) (.bnd 0)
    (.tm (Term.boxtm (NShape.contents (Ctx.Le.refl _) N u hu).2))
  have hU : (⟨_, Term.subst (Subst.singleIdx (.bnd 0)
      (.tm (Term.boxtm (NShape.contents (Ctx.Le.refl _) N u hu).2)))
      (Subst.single (.bnd 0) (.tm (Term.boxtm (NShape.contents (Ctx.Le.refl _) N u hu).2)))
      (Subst.ok_single (Ctx.empty_le V) rfl)
      (Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le V) rfl) (NShape.unpack₀ N).2⟩ :
      Σ b, Term σ V N.ty b) = ⟨_, Term.eta u N.ty hu⟩ :=
    NShape.subst_unpack _ _ _ N _ _ u hu (Subst.box_at_inner_boxtm _ hat)
  refine congrArg₂ WFF.and ((WFF.instantiate_bodyRepl _ _ _).trans
    (WFF.instantiate_congr_sig _ ?_ Φ)) ?_
  · rw [Term.subst_mono]
    exact hU
  · change WFF.subst _ _ _ _ _ _ (WFF.holeAt _ _ _) = _
    rw [WFF.subst_holeAt]
    refine WFF.holeAt_congr _ ?_ _
    rw [Term.subst_mono]
    exact sig_pair hU (Term.subst_eta_tm _ _ _ _ _ _ _ hat)

end Packed

/-! ## Lifting at a necessary shape -/

section Main

variable {Γ : Ctx} [Γ.NoSlots]

/-- ⭐**Packing a returning possibility**: at a necessary shape it is a returning possibility of
    one necessary object, with the same value, whose body reads the object back with its ties. -/
def Proof.retN_packed (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ) (N : NShape)
    {a : Ann N.flat} (t : Term σ Γ N.flat a) (Φ : WFF σ (O.view.insert (.bnd 0) N.ty) 1) (u : ℕ)
    (hu : O.view.RootFresh (.free u)) (H : Proof σ Γ Δ (O.retS hS (.nec N) t Φ)) :
    Proof σ Γ Δ (O.ret hS t (WFF.packedBody hS hF Φ)) := by
  have h₁ : Proof σ Γ Δ (O.retS hS (.nec N) t (WFF.bodyRepl
      (Term.mono ((Ctx.empty_le O.view).insert (.bnd 0) _) (NShape.packMap (σ := σ) N).obj.2)
      (WFF.packedBody hS hF Φ))) := by
    refine Proof.ret_monoS (S := .nec N) hS O t Φ _ H (Proof.leg_all O _ _ u hu ?_)
    have hV := Ctx.le_insert hu.root N.ty
    have h₀ := Ctx.ref_insert_root O.view (.free u) N.ty
    have hP := NShape.holeAt_packObj (σ := σ) N _ h₀
    rw [← WFF.instantiate_eta_openFree u hu Ctx.NoSlots.slots Ctx.NoSlots.slots
      (WFF.bodyRepl _ _), WFF.mono_bodyRepl hV, WFF.instantiate_bodyRepl, Term.mono_mono,
      Term.subst_mono]
    refine Proof.conv (WFF.instantiate_congr_sig _ hP _).symm ?_
    rw [WFF.mono_packedBody hV, WFF.instantiate_packedBody]
    exact Proof.and_intro (Proof.conv (WFF.instantiate_eta_openFree u hu Ctx.NoSlots.slots
      Ctx.NoSlots.slots Φ).symm (Proof.lookup List.mem_cons_self))
      (Proof.packTies_intro hS hT hF N _ h₀)
  refine Proof.conv (OutLeg.retS_congr hS O (.box N.flat) ?_ rfl)
    (Proof.ret_map hS O (S := .nec N) (T := .box N.flat) (NShape.packMap N) t _ h₁)
  rw [Term.holeRead_eq_holeAt]
  exact NShape.holeAt_packVal N t

/-- ⭐⭐**Lifting at every necessary shape** (T + 4, strong B): `Proof.ret_lift` at the packed
    object. -/
def Proof.retN_lift (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (O : OutLeg Γ) (N : NShape)
    {a : Ann N.flat} (t : Term σ Γ N.flat a) (Φ : WFF σ (O.view.insert (.bnd 0) N.ty) 1)
    (c : ℕ) (hc : Γ.RootFresh (.free c)) (hc₁ : Γ.RootFresh (.free (c + 1)))
    (hc₂ : Γ.RootFresh (.free (c + 2))) (p : Proof σ Γ Δ (O.retS hS (.nec N) t Φ))
    (q : Proof σ (Γ.insert (.free c) (.VTypeBox N.flat))
      (WFF.lifted hS hF O t (WFF.packedBody hS hF Φ) c hc :: Δ.map (WFF.weaken hc.root _))
      (φ.weaken hc.root _)) :
    Proof σ Γ Δ φ :=
  Proof.ret_lift hS hT hF O t _ c hc hc₁ hc₂
    (Proof.retN_packed hS hT hF O N t Φ (c + 1) (OutLeg.rootFresh hc₁ O) p) q

end Main

/-! ## What the ties say in a model -/

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

/-- ⭐**A tie, read**: the companion read along the way home is `Ind` to whatever its contents are.
    `Ind` need not compose, so the value is moved inside the `Back` atom first (`hM.inv`), and the
    own arrow reads the atom (`RoundTrip.own`). -/
theorem ind_of_tie (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) (hM : M.IndInvariant) {Ω : Ctx} {d : ℕ}
    (hs : Ω.SlotsFrom d) {v w : M.frame.W} (env : M.Env Ω v) {C : VarType} {Y z : VarSymb}
    (hY : Ω.ref Y = some (.VTypeBox C)) (hz : Ω.boxIn.ref z = some C)
    (hsat : M.sat env (WFF.box (WFF.holeAt hs.boxIn
      (Term.pair (Term.eta z C hz) (Term.eta (.step Y .keep) (.VTypeBox C)
        (Ctx.ref_keep_of' hF hY rfl))) (WFF.backDup hS hF C))))
    (r : M.frame.R v w) (o : M.frame.Dom C w)
    (hi : M.Ind ((env.boxPush ⟨w, ⟨r⟩⟩).ref z hz) o) :
    M.Ind (M.necEval (env.ref Y hY : M.frame.Nec C v) ⟨w, ⟨r⟩⟩) o := by
  let a : M.frame.Acc v := ⟨w, ⟨r⟩⟩
  have h₁ := (sat_holeAt _ (env.boxPush a) _ _).mp (hsat a)
  let c := interp (env.boxPush a) (Term.eta (σ := σ) (.step Y .keep) (.VTypeBox C)
    (Ctx.ref_keep_of' hF hY rfl))
  have hI : M.Ind (A := .VTypeProd C (.VTypeBox C)) (w := w)
      (interp (env.boxPush a) (Term.eta (σ := σ) z C hz), c) (o, c) :=
    hM.pair (by rw [interp_eta]; exact hi) (M.Ind_refl _)
  have hnp : Ctx.empty.NoProjLast := fun _ _ h => by simp [Ctx.empty] at h
  have h₂ := (hM.inv (Ctx.Presented.tame _) hnp (Env.empty w) _ _ _ hI).mp h₁
  let oc : M.frame.Dom (.VTypeProd C (.VTypeBox C)) w := (o, c)
  let env₀ := (Env.empty w).extend (.bnd 0) oc
  have hsnd : (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox C))).ref
      (.step (.root (.bnd 0)) .snd) = some (.VTypeBox C) :=
    Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)
  have hown := (OutLeg.sat_back_rt hS env₀ .nec
    (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (Term.eta (σ := σ)
      (VarSymb.step (.root (.bnd 0)) .snd).inner C (Ctx.ref_inner hsnd)))
    (Term.eta (.step (.root (.bnd 0)) .fst) C (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))
    h₂).own hT hS
  have hown' : M.Ind (interp ((env₀.boxPush (M.frame.reflAcc hT w)).boxPush
      (M.frame.reflAcc hT w)) (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (Term.eta (σ := σ)
        (VarSymb.step (.root (.bnd 0)) .snd).inner C (Ctx.ref_inner hsnd))))
      (interp env₀ (Term.eta (σ := σ) (.step (.root (.bnd 0)) .fst) C
        (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))) := hown
  have e₂ : env₀.ref (.step (.root (.bnd 0)) .snd) hsnd = c := by
    have := interp_eta_slot_snd (σ := σ) (Env.empty w) oc hsnd
    rwa [interp_eta] at this
  have hc : c = M.necEval (M.ops.necDup hF (env.ref Y hY)) a := by
    change interp (env.boxPush a) (Term.eta (σ := σ) _ _ _) = _
    rw [interp_eta, Env.ref, dif_neg (by decide : ¬ Step.keep.isProj = true)]
    rfl
  rw [interp_eta_slot_fst, interp_shift (Env.shiftAgree_twoBox hF env₀ _ _), interp_eta,
    Env.ref_inner _ _ hsnd, e₂, hc, M.necDup_eval] at hown'
  exact (congrArg (fun x : M.frame.R v w =>
    M.Ind (M.necEval (env.ref Y hY : M.frame.Nec C v) ⟨w, ⟨x⟩⟩) o)
    (@Subsingleton.elim _ (M.frame.homeUnique hS) (M.frame.trans hF r
      (M.frame.trans hF (M.frame.refl hT w) (M.frame.refl hT w))) r)).mp hown'

/-- `Ind` passes to first components. -/
theorem ind_fst (hM : M.IndInvariant) {A B : VarType} {w : M.frame.W}
    {x y : M.frame.Dom (.VTypeProd A B) w} (h : M.Ind x y) : M.Ind x.1 y.1 := by
  have := hM.map (Term.eta (σ := σ) (.step (.root (.bnd 0)) .fst) A
    (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))) h
  simpa only [holeVal, interp_eta_slot_fst] using this

/-- `Ind` passes to second components. -/
theorem ind_snd (hM : M.IndInvariant) {A B : VarType} {w : M.frame.W}
    {x y : M.frame.Dom (.VTypeProd A B) w} (h : M.Ind x y) : M.Ind x.2 y.2 := by
  have := hM.map (Term.eta (σ := σ) (.step (.root (.bnd 0)) .snd) B
    (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))) h
  simpa only [holeVal, interp_eta_slot_snd] using this

/-- The object's own value inside a value with companions. -/
def compsHead (A : VarType) : (cs : List (List Step)) → {w : M.frame.W} →
    M.frame.Dom (A.compsFlat cs) w → M.frame.Dom A w
  | [], _, z => z
  | _ :: ps, _, z => compsHead A ps z.1

/-- The object out there is what its packed contents say, read along the way home. -/
def NReads : (N : NShape) → {v w : M.frame.W} → M.frame.Dom N.ty v → M.frame.R v w →
    M.frame.Dom N.flat w → Prop
  | .boxC A cs _, _, w, e, r, z =>
      M.necEval (e : M.frame.Nec A _) ⟨w, ⟨r⟩⟩ = compsHead (M := M) A cs z
  | .prod R S, _, _, e, r, z => NReads R e.1 r z.1 ∧ NReads S e.2 r z.2

/-- ⭐The companions' ties give the object's return. -/
theorem compsBack_of_ties (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) (hM : M.IndInvariant) {Ω : Ctx} {d : ℕ}
    (hs : Ω.SlotsFrom d) {v : M.frame.W} (env : M.Env Ω v) {A : VarType} (e : VarSymb)
    (he : Ω.ref e = some (.VTypeBox A)) : ∀ (cs : List (List Step)) (h : A.CompOk cs)
    (z : VarSymb) (hz : Ω.boxIn.ref z = some (A.compsFlat cs)),
    M.sat env (WFF.cTies hS hF hs e he cs h z hz) → ∀ {w : M.frame.W} (r : M.frame.R v w)
    (o : M.frame.Dom (A.compsFlat cs) w),
    M.necEval (env.ref e he : M.frame.Nec A v) ⟨w, ⟨r⟩⟩ =
      compsHead (M := M) A cs ((env.boxPush ⟨w, ⟨r⟩⟩).ref z hz) →
    M.Ind ((env.boxPush ⟨w, ⟨r⟩⟩).ref z hz) o → M.compsBack A cs (env.ref e he) r o
  | [], _, _, _, _, _, r, o, hread, hi => by
      change M.Ind _ o
      rw [hread]
      exact hi
  | q :: ps, h, z, hz, hsat, w, r, o, hread, hi => by
      obtain ⟨-, hall, -⟩ := h.resolve_left (List.cons_ne_nil _ _)
      have hfst : (env.boxPush ⟨w, ⟨r⟩⟩).ref (.step z .fst) (Ctx.ref_fst_of hz) =
          ((env.boxPush ⟨w, ⟨r⟩⟩).ref z hz).1 := Env.ref_fst _ hz _
      have hsnd : (env.boxPush ⟨w, ⟨r⟩⟩).ref (.step z .snd) (Ctx.ref_snd_of hz) =
          ((env.boxPush ⟨w, ⟨r⟩⟩).ref z hz).2 := Env.ref_snd _ hz _
      refine ⟨compsBack_of_ties hS hT hF hM hs env e he ps h.tail _ _ hsat.2 r o.1
        (by rw [hfst]; exact hread) (by rw [hfst]; exact ind_fst hM hi), ?_⟩
      refine (iff_of_eq (dif_pos hT)).mpr (compBack_of_ind hT (.VTypeBox A) (.here :: q) _ r o.2
        (hall q List.mem_cons_self) ?_)
      rw [← necEval_ref_compRead hT env r (.here :: q) he (h.ref_head he)
        (hall q List.mem_cons_self)]
      exact ind_of_tie hS hT hF hM hs env (h.ref_head he) _ hsat.1 r o.2
        (by rw [hsnd]; exact ind_snd hM hi)

/-- ⭐**The ties give the return at every necessary shape**: if the packed object's reading along
    the way home is `Ind` to `o`, then the object comes back as `o`. -/
theorem nComesBack_of_ties (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) (hM : M.IndInvariant) {Ω : Ctx} {d : ℕ}
    (hs : Ω.SlotsFrom d) {v : M.frame.W} (env : M.Env Ω v) : ∀ (N : NShape) (e : VarSymb)
    (he : Ω.ref e = some N.ty) (z : VarSymb) (hz : Ω.boxIn.ref z = some N.flat),
    M.sat env (WFF.nTies hS hF hs N e he z hz) → ∀ {w : M.frame.W} (r : M.frame.R v w)
    (o : M.frame.Dom N.flat w), NReads N (env.ref e he) r ((env.boxPush ⟨w, ⟨r⟩⟩).ref z hz) →
    M.Ind ((env.boxPush ⟨w, ⟨r⟩⟩).ref z hz) o → M.NComesBack N (env.ref e he) r o
  | .boxC _ cs h, e, he, z, hz, hsat, _, r, o, hread, hi =>
      compsBack_of_ties hS hT hF hM hs env e he cs h z hz hsat r o hread hi
  | .prod R S, _, he, _, hz, hsat, _, r, o, hread, hi => by
      have hf₁ := Env.ref_fst env he (Ctx.ref_fst_of he)
      have hf₂ := Env.ref_snd env he (Ctx.ref_snd_of he)
      have hz₁ := Env.ref_fst (env.boxPush ⟨_, ⟨r⟩⟩) hz (Ctx.ref_fst_of hz)
      have hz₂ := Env.ref_snd (env.boxPush ⟨_, ⟨r⟩⟩) hz (Ctx.ref_snd_of hz)
      refine ⟨?_, ?_⟩
      · rw [← hf₁]
        exact nComesBack_of_ties hS hT hF hM hs env R _ _ _ _ hsat.1 r o.1
          (by rw [hf₁, hz₁]; exact hread.1) (by rw [hz₁]; exact ind_fst hM hi)
      · rw [← hf₂]
        exact nComesBack_of_ties hS hT hF hM hs env S _ _ _ _ hsat.2 r o.2
          (by rw [hf₂, hz₂]; exact hread.2) (by rw [hz₂]; exact ind_snd hM hi)

end Model

end V12M
