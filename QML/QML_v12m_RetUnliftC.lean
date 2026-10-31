import QML.QML_v12m_RetUnlift

/-!
# QML v12m — strong B on S5: unlifting with companions

The converse of `Proof.retN_lift`.  A companion's way home is only said by a companion shape, so
its value has to be named (`ret_compS`) and then identified with the given one.  `ret_counitC`
reads `.box` atoms and no shape map projects a companion's object, so it reads the packed object
instead (`ret_map` at `packC`), whose contents hold the companion's: that gives `Back (k.dup) z`,
for `k` the home term carrying the given value, and `z` and the value interchange at the value
slot.  Pairs need nothing more: a shape and its packed shape say the same (`BArrow.retS_packG`,
and `ret_map` along `unpackG` back), so `Proof.retN_unlift` is `Proof.retC_unlift` at the packed
shape.  A possible part is then `ret_keep`.
-/

namespace V12M

variable [ModalSys] {σ : Signature}

open BArrow

/-! ## Weakening along a leg -/

section Leg

theorem OutLeg.mono_box {Γ Γ' : Ctx} (h : Γ.Le Γ') (O : OutLeg Γ) (φ : WFF σ O.view 0) :
    WFF.mono h (O.box φ) = (O.mono h).box (WFF.mono (OutLeg.le_view_mono h O) φ) := by
  cases O <;> rfl

theorem OutLeg.mono_back {Γ Γ' : Ctx} (h : Γ.Le Γ') (hS : ModalSys.BStrong = true) (O : OutLeg Γ)
    {A : VarType} {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A} (t : Term σ Γ A a) :
    WFF.mono h (O.back hS bd t : WFF σ Γ 0) =
      (O.mono h).back hS (Term.mono (OutLeg.le_view_mono h O).boxIn bd) (Term.mono h t) := by
  cases O <;> rfl

end Leg

/-! ## Reading a companion through the packed object -/

section Tie

/-- A companion's type. -/
abbrev compTy (A : VarType) (q : List Step) : VarType := (A.compAt q).getD .VTypeOne

/-- `Back (c.dup) z` on a hole `⟨⟨v, z⟩, c⟩`: the new companion's value, and a carrier. -/
def WFF.backSnd (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) (F C : VarType) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd F C) (.VTypeBox C))) 1 :=
  WFF.backG hS (.comp (.dup hF) .snd) (.comp .snd .fst)

theorem WFF.holeAt_backSnd (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) {Ω : Ctx}
    {d : ℕ} (hs : Ω.SlotsFrom d) {F C : VarType} {a₁ : Ann F} {a₂ : Ann C} {c₀ : Ann C}
    (v : Term σ Ω F a₁) (z : Term σ Ω C a₂) (c : Term σ Ω.boxIn C c₀) :
    WFF.holeAt hs (Term.pair (Term.pair v z) (Term.boxtm c)) (WFF.backSnd hS hF F C) =
      WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Ω) c))) z :=
  WFF.holeAt_backG hS hs _ _ _

/-- The carrier of a home term `k`: `□k`, kept, read along the leg. -/
def compBd {Γ : Ctx} (hF : ModalSys.Four = true) (O : OutLeg Γ) {C : VarType} {k₀ : Ann C}
    (k : Term σ Γ.boxIn C k₀) : Σ b, Term σ O.view.boxIn (.VTypeBox C) b :=
  ⟨_, Term.mono O.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ)
    (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) k)))⟩

theorem compBd_mono {Γ Γ' : Ctx} (h : Γ.Le Γ') (hF : ModalSys.Four = true) (O : OutLeg Γ)
    {C : VarType} {k₀ : Ann C} (k : Term σ Γ.boxIn C k₀) :
    (⟨_, Term.mono (OutLeg.le_view_mono h O).boxIn (compBd hF O k).2⟩ :
        Σ b, Term σ (O.mono h).view.boxIn (.VTypeBox C) b) =
      compBd hF (O.mono h) (Term.mono h.boxIn k) := by
  unfold compBd
  dsimp only
  have e₁ := Term.shift_mono (σ := σ) (Ctx.shifts_boxIn_boxIn hF Γ)
    (Ctx.shifts_boxIn_boxIn hF Γ') h.boxIn h.boxIn.boxIn k
  have e₂ := Term.shift_mono (σ := σ) (Ctx.shifts_boxIn_boxIn hF Γ)
    (Ctx.shifts_boxIn_boxIn hF Γ') h.boxIn h.boxIn.boxIn
    (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) k))
  rw [e₁]
  refine Eq.trans ?_ (congrArg (fun t => (⟨_, Term.mono (O.mono h).le_view.boxIn t⟩ :
    Σ b, Term σ (O.mono h).view.boxIn (.VTypeBox C) b)) e₂.symm)
  dsimp only
  rw [Term.mono_mono, Term.mono_mono]

variable {V V' : Ctx} [V.NoSlots] [V'.NoSlots]

/-- Weakening `ret_counitC`'s body weakens its carrier. -/
theorem mono_counitBodyC (h : V.Le V') {A C : VarType} {c₀ : Ann C} (bd : Term σ V.boxIn C c₀)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A C)) 1) :
    WFF.mono (h.insert (.bnd 0) (.VTypeBox A)) (counitBodyC bd ψ) =
      counitBodyC (Term.mono h.boxIn bd) ψ := by
  unfold counitBodyC
  refine congrArg WFF.box ((WFF.mono_holeAt _ _
    ((Ctx.NoSlots.slots (Γ := V')).insert _).boxIn _ ψ).trans
    (WFF.holeAt_congr _ (sig_pair (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)) ?_) ψ))
  rw [Term.mono_mono, Term.mono_mono]

/-- ⭐What the object must say for the value of its companion `q` to be identified: necessarily, the
    carrier comes back as the packed object's last part, which is the companion's contents. -/
def WFF.compTie (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) {A : VarType}
    (q : List Step) (cs : List (List Step)) (h' : A.CompOk (q :: cs))
    {b : Ann (.VTypeBox (compTy A q))} (bd : Term σ V.boxIn (.VTypeBox (compTy A q)) b) :
    WFF σ (V.insert (.bnd 0) (.VTypeBox A)) 1 :=
  WFF.bodyRepl (Term.mono ((Ctx.empty_le V).insert (.bnd 0) _)
      (NShape.packMap (σ := σ) (.boxC A (q :: cs) h')).obj.2)
    (counitBodyC (A := A.compsFlat (q :: cs)) bd
      (WFF.backSnd hS hF (A.compsFlat cs) (compTy A q)))

theorem WFF.compTie_congr (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) {A : VarType}
    (q : List Step) (cs : List (List Step)) (h' : A.CompOk (q :: cs))
    {b b' : Ann (.VTypeBox (compTy A q))} {bd : Term σ V.boxIn (.VTypeBox (compTy A q)) b}
    {bd' : Term σ V.boxIn (.VTypeBox (compTy A q)) b'}
    (e : (⟨_, bd⟩ : Σ c, Term σ V.boxIn (.VTypeBox (compTy A q)) c) = ⟨_, bd'⟩) :
    WFF.compTie hS hF q cs h' bd = WFF.compTie hS hF q cs h' bd' := by
  cases e
  rfl

theorem WFF.mono_compTie (h : V.Le V') (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true)
    {A : VarType} (q : List Step) (cs : List (List Step)) (h' : A.CompOk (q :: cs))
    {b : Ann (.VTypeBox (compTy A q))} (bd : Term σ V.boxIn (.VTypeBox (compTy A q)) b) :
    WFF.mono (h.insert (.bnd 0) (.VTypeBox A)) (WFF.compTie hS hF q cs h' bd) =
      WFF.compTie hS hF q cs h' (Term.mono h.boxIn bd) := by
  unfold WFF.compTie
  rw [WFF.mono_bodyRepl h, Term.mono_mono, mono_counitBodyC h]

end Tie

/-! ## One companion -/

section Step

variable {Γ : Ctx} [Γ.NoSlots] {A : VarType} {cs : List (List Step)}

/-- The companion's slot formula, filled. -/
theorem instantiate_compSlot_self (hS : ModalSys.BStrong = true) (q : List Step)
    (h' : A.CompOk (q :: cs)) (O : OutLeg Γ) {a : Ann (A.compsFlat cs)}
    (V : Term σ Γ (A.compsFlat cs) a) (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1)
    {c : Ann (compTy A q)} (z : Term σ Γ (compTy A q) c) :
    WFF.instantiate Ctx.NoSlots.slots z (compSlot hS q h' O V Φ) =
      O.retS hS (.nec (.boxC A (q :: cs) h')) (Term.pair V z) Φ := by
  unfold compSlot
  refine (OutLeg.instantiate_compSlot hS O (.nec (.boxC A (q :: cs) h')) _ _ z).trans ?_
  exact OutLeg.retS_congr hS O _ (sig_pair (Term.subst_single_mono_sig z V)
    (Term.subst_eta_tm _ _ _ _ _ _ z (Subst.at_single_root _ _))) rfl

/-- ⭐**Swapping a companion's value**: if the object says `compTie` of the carrier of `k`, the
    named value `z` is `k`'s value, and so is `u`. -/
def Proof.ret_comp_swap (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ) (q : List Step)
    (h' : A.CompOk (q :: cs)) {v₀ : Ann (A.compsFlat cs)} (V : Term σ Γ (A.compsFlat cs) v₀)
    {z₀ : Ann (compTy A q)} (z : Term σ Γ (compTy A q) z₀) {k₀ : Ann (compTy A q)}
    (k : Term σ Γ.boxIn (compTy A q) k₀) {u₀ : Ann (compTy A q)} (u : Term σ Γ (compTy A q) u₀)
    (Ψ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1)
    (H : Proof σ Γ Δ (O.retS hS (.nec (.boxC A (q :: cs) h')) (Term.pair V z) Ψ))
    (ht : Proof σ Γ Δ (O.box (WFF.all (.VTypeBox A)
      (WFF.imp Ψ (WFF.compTie hS hF q cs h' (compBd hF O k).2)))))
    (B : Proof σ Γ Δ (O.back hS (compBd hF O k).2 (Term.boxtm k)))
    (hb : Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift
      (Ctx.shifts_boxIn_boxIn hF Γ) k))) u)) :
    Proof σ Γ Δ (O.retS hS (.nec (.boxC A (q :: cs) h')) (Term.pair V u) Ψ) := by
  have H₁ := Proof.ret_monoS (S := .nec (.boxC A (q :: cs) h')) hS O (Term.pair V z) Ψ _ H ht
  have H₂ := Proof.ret_map hS O (S := .nec (.boxC A (q :: cs) h'))
    (T := .box (NShape.boxC A (q :: cs) h').flat) (NShape.packMap _) _ _ H₁
  have H₃ : Proof σ Γ Δ (O.ret hS (Term.pair V z) (counitBodyC (A := A.compsFlat (q :: cs))
      (compBd hF O k).2 (WFF.backSnd hS hF (A.compsFlat cs) (compTy A q)))) := by
    refine Proof.conv (OutLeg.retS_congr hS O (.box (A.compsFlat (q :: cs))) ?_ rfl) H₂
    rw [Term.holeRead_eq_holeAt]
    exact NShape.holeAt_packVal (.boxC A (q :: cs) h') (Term.pair V z)
  have H₄ := Proof.ret_counitC hS O (Term.pair V z) (compBd hF O k).2 (Term.boxtm k)
    (WFF.backSnd hS hF (A.compsFlat cs) (compTy A q)) H₃ B
  have H₅ : Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift
      (Ctx.shifts_boxIn_boxIn hF Γ) k))) z) :=
    Proof.conv ((WFF.holeRead_eq_holeAt _ _).trans (WFF.holeAt_backSnd hS hF _ V z k)) H₄
  have R₁ := Proof.back_here hS hT (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) k) z
    (compSlot hS q h' O V Ψ) H₅ (Proof.conv (instantiate_compSlot_self hS q h' O V Ψ z).symm H)
  refine Proof.conv (instantiate_compSlot_self hS q h' O V Ψ u)
    (Proof.back_value hS hT hF k u _ hb (Proof.conv ?_ R₁))
  exact WFF.instantiate_congr_sig _ (congrArg (fun p =>
    (⟨_, Term.collapse (Ctx.collapses_boxIn_self hT Γ) p.2⟩ : Σ e, Term σ Γ _ e))
    (Term.collapse_shift_boxIn hT hF k)) _

/-- ⭐⭐**One more companion, with its value given** (T + 4, strong B): `ret_compS` names the value,
    and `Proof.ret_comp_swap` identifies it. -/
def Proof.ret_comp_value (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ) {h : A.CompOk cs}
    (q : List Step) (h' : A.CompOk (q :: cs)) {v₀ : Ann (A.compsFlat cs)}
    (V : Term σ Γ (A.compsFlat cs) v₀) {k₀ : Ann (compTy A q)}
    (k : Term σ Γ.boxIn (compTy A q) k₀) {u₀ : Ann (compTy A q)} (u : Term σ Γ (compTy A q) u₀)
    (Ψ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1) (c : ℕ) (hc : Γ.RootFresh (.free c))
    (p : Proof σ Γ Δ (O.retS hS (.nec (.boxC A cs h)) V Ψ))
    (ht : Proof σ Γ Δ (O.box (WFF.all (.VTypeBox A)
      (WFF.imp Ψ (WFF.compTie hS hF q cs h' (compBd hF O k).2)))))
    (hb : Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift
      (Ctx.shifts_boxIn_boxIn hF Γ) k))) u)) :
    Proof σ Γ Δ (O.retS hS (.nec (.boxC A (q :: cs) h')) (Term.pair V u) Ψ) := by
  have hne : Proof σ Γ Δ (O.dia .top) :=
    Proof.leg_dia O Proof.top_intro (Proof.ret_diaS hS O _ _ p)
  have B₀ : Proof σ Γ Δ (O.back hS (compBd hF O k).2 (Term.boxtm k)) :=
    Proof.conv (OutLeg.back_congr hS O rfl (Term.collapse_boxtm_shift hT hF k))
      (Proof.back_keep hS hT hF O (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) k)) hne)
  have hL := Ctx.le_insert hc.root (compTy A q)
  refine Proof.ret_compS hS O (.nec (.boxC A cs h)) q h' V Ψ c hc p ?_
  have wk : ∀ {H : WFF σ (Γ.insert (.free c) (compTy A q)) 0} {φ : WFF σ Γ 0}, Proof σ Γ Δ φ →
      Proof σ (Γ.insert (.free c) (compTy A q))
        (H :: Δ.map (WFF.weaken hc.root (compTy A q))) (φ.weaken hc.root (compTy A q)) :=
    fun p => Proof.ofSubset (fun _ hx => List.mem_cons_of_mem _ hx) (Proof.weak_ctx c _ hc p)
  refine Proof.conv (OutLeg.mono_retS hL hS O (.nec (.boxC A (q :: cs) h')) (Term.pair V u) Ψ).symm
    (Proof.ret_comp_swap hS hT hF (O.mono hL) q h' (Term.mono hL V)
      (Term.eta (.root (.free c)) (compTy A q) (Ctx.ref_insert_root Γ (.free c) (compTy A q)))
      (Term.mono hL.boxIn k) (Term.mono hL u) _ ?_ ?_ ?_ ?_)
  · refine Proof.conv ?_ (Proof.lookup List.mem_cons_self)
    exact congrArg (fun φ => (O.mono hL).retS hS (.nec (.boxC A (q :: cs) h'))
      (Term.pair (Term.mono hL V) (Term.eta (.root (.free c)) (compTy A q)
        (Ctx.ref_insert_root Γ (.free c) (compTy A q))))
      (WFF.mono ((OutLeg.le_view_mono hL O).insert (.bnd 0) _) φ)) (WFF.bodyRepl_eta' Ψ)
  · refine Proof.conv ?_ (wk ht)
    refine (OutLeg.mono_box hL O _).trans (congrArg (O.mono hL).box ?_)
    change WFF.all _ (WFF.imp _ (WFF.mono _ _)) = _
    rw [WFF.mono_compTie (OutLeg.le_view_mono hL O)]
    exact congrArg (fun φ => WFF.all _ (WFF.imp _ φ))
      (WFF.compTie_congr hS hF q cs h' (compBd_mono hL hF O k))
  · refine Proof.conv ?_ (wk B₀)
    exact (OutLeg.mono_back hL hS O _ _).trans
      (OutLeg.back_congr hS _ (compBd_mono hL hF O k) rfl)
  · refine Proof.conv ?_ (wk hb)
    change WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.mono hL.boxIn.boxIn _))) _ = _
    rw [← Term.shift_mono (Ctx.shifts_boxIn_boxIn hF Γ) (Ctx.shifts_boxIn_boxIn hF _) hL.boxIn
      hL.boxIn.boxIn k]

end Step

/-! ## Turning a tie round -/

section Flip

/-- `Back (c.dup) v` on a hole `⟨c, v⟩`. -/
def WFF.backDupL (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) (C : VarType) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeBox C) C)) 1 :=
  WFF.backG hS (.comp (.dup hF) .fst) .snd

variable {Ω : Ctx} [Ω.NoSlots] {C : VarType}

/-- ⭐**A tie, turned round**: `□ Back (Y.keep.dup) x` says `Y` read at each arrow is `x`, so `Y`'s
    contents come back from the carrier of `x`. -/
def Proof.tie_flip (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Ω 0)} {Y : VarSymb}
    (hY : Ω.ref Y = some (.VTypeBox C)) {x₀ : Ann C} (x : Term σ Ω.boxIn C x₀)
    (H : Proof σ Ω Δ (WFF.box (WFF.holeAt Ctx.NoSlots.slots
      (Term.pair x (Term.eta (.step Y .keep) (.VTypeBox C) (Ctx.ref_keep_of' hF hY rfl)))
      (WFF.backDup hS hF C)))) :
    Proof σ Ω Δ (WFF.box (WFF.back hS .nec (Term.boxtm (Term.boxtm
      (Term.shift (Ctx.shifts_boxIn_boxIn hF Ω.boxIn)
        (Term.shift (Ctx.shifts_boxIn_boxIn hF Ω) x))))
      (Term.eta Y.inner C (Ctx.ref_inner hY)))) := by
  refine Proof.leg_K (.nec : OutLeg Ω) ?_ H
  have hk := Ctx.ref_inner (Ctx.ref_keep_of' hF hY rfl)
  have h₁ := Proof.conv (WFF.holeAt_backDup hS hF Ctx.NoSlots.slots x (Term.eta _ C hk))
    (Proof.lookup (Δ := [_]) List.mem_cons_self)
  let φ := WFF.holeAt ((Ctx.NoSlots.slots (Γ := Ω.boxIn)).insert C)
    (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Ω.boxIn)).root C)
        (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Ω) x)))
      (Term.eta (.root (.bnd 0)) C (Ctx.ref_insert_root Ω.boxIn (.bnd 0) C)))
    (WFF.backDupL (σ := σ) hS hF C)
  have eφ : ∀ {a : Ann C} (v : Term σ Ω.boxIn C a), WFF.instantiate Ctx.NoSlots.slots v φ =
      WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Ω.boxIn)
        (Term.shift (Ctx.shifts_boxIn_boxIn hF Ω) x)))) v := fun v =>
    (WFF.instantiate_holeAt_pair _ _ v).trans (WFF.holeAt_backG hS _ _ _ _)
  have R := Proof.back_here hS hT (Term.shift (Ctx.shifts_boxIn_boxIn hF Ω.boxIn)
    (Term.eta _ C hk)) x φ h₁ (Proof.conv (eφ x).symm (Proof.back_shift hS hT hF x))
  refine Proof.conv (eφ _) (Proof.conv (WFF.instantiate_congr_sig _ ?_ φ) R)
  have e₁ : (⟨_, Term.eta (σ := σ) (VarSymb.step Y .keep).inner C hk⟩ :
      Σ b, Term σ Ω.boxIn.boxIn C b) =
      ⟨_, Term.shift (Ctx.shifts_boxIn_boxIn hF Ω) (Term.eta Y.inner C (Ctx.ref_inner hY))⟩ :=
    (Term.eta_congr (VarSymb.inner_shift_zero Y).symm C _ _).trans
      (Term.shift_eta _ _ C _).symm
  refine (congrArg (fun p => (⟨_, Term.collapse (Ctx.collapses_boxIn_self hT Ω.boxIn) p.2⟩ :
    Σ e, Term σ Ω.boxIn C e)) (Term.collapse_shift_boxIn hT hF (Term.eta _ C hk))).trans ?_
  refine (congrArg (fun p => (⟨_, Term.collapse (Ctx.collapses_boxIn_self hT Ω.boxIn) p.2⟩ :
    Σ e, Term σ Ω.boxIn C e)) e₁).trans ?_
  exact Term.collapse_shift_boxIn hT hF _

end Flip

/-! ## The ties, read -/

section Read

/-- The base of a value with companions: its first component, once per companion. -/
def compsBase {Δ : Ctx} {A : VarType} : (cs : List (List Step)) → {b : Ann (A.compsFlat cs)} →
    Term σ Δ (A.compsFlat cs) b → Σ c, Term σ Δ A c
  | [], _, t => ⟨_, t⟩
  | _ :: ps, _, .pair t _ => compsBase ps t

theorem at_compsBase {Δ : Ctx} {A : VarType} (θ : Subst σ Δ) :
    ∀ (cs : List (List Step)) {b : Ann (A.compsFlat cs)} (s : Term σ Δ (A.compsFlat cs) b)
      (v : VarSymb), θ.at v = .tm s → θ.at (v.ext (compsFst cs)) = .tm (compsBase cs s).2
  | [], _, _, _, hv => hv
  | _ :: ps, _, .pair s _, v, hv => by
      change θ.at ((VarSymb.step v .fst).ext (compsFst ps)) = _
      exact at_compsBase θ ps s _ (by rw [Subst.at_proj θ v rfl, hv]; rfl)

/-- The ties of a companion list at an address `e`, with the contents at a term. -/
def WFF.cTiesAt (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) {Ω : Ctx} {d : ℕ}
    (hs : Ω.SlotsFrom d) {A : VarType} (e : VarSymb) (he : Ω.ref e = some (.VTypeBox A)) :
    (cs : List (List Step)) → A.CompOk cs → {b : Ann (A.compsFlat cs)} →
    Term σ Ω.boxIn (A.compsFlat cs) b → WFF σ Ω d
  | [], _, _, _ => .top
  | q :: ps, h, _, .pair s x => WFF.and
      (WFF.box (WFF.holeAt hs.boxIn
        (Term.pair x (Term.eta (.step ((VarSymb.step e .here).ext q) .keep) (.VTypeBox (compTy A q))
          (Ctx.ref_keep_of' hF (h.ref_head he) rfl)))
        (WFF.backDup hS hF _)))
      (WFF.cTiesAt hS hF hs e he ps h.tail s)

variable {Γ Ω : Ctx} [Γ.NoSlots] {d : ℕ} {ι : VarSymb → VarSymb} (θ : Subst σ Γ)
  (hθ : Subst.Ok Ω θ) (hc : Subst.Coh ι Ω θ) (hs : Ω.SlotsFrom d) (hs' : Γ.SlotsFrom 0)

omit [Γ.NoSlots] in
/-- ⭐Substituting the ties. -/
theorem WFF.subst_cTies (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {A : VarType} (e : VarSymb)
    (he : Ω.ref e = some (.VTypeBox A)) (u : VarSymb) (hu : Γ.ref u = some (.VTypeBox A))
    (hat : θ.at e = .tm (Term.eta u (.VTypeBox A) hu)) :
    ∀ (cs : List (List Step)) (h : A.CompOk cs) (z : VarSymb)
      (hz : Ω.boxIn.ref z = some (A.compsFlat cs)) {b : Ann (A.compsFlat cs)}
      (s : Term σ Γ.boxIn (A.compsFlat cs) b), θ.box.at z = .tm s →
      WFF.subst ι θ hθ hc hs hs' (WFF.cTies hS hF hs e he cs h z hz) =
        WFF.cTiesAt hS hF hs' u hu cs h s
  | [], _, _, _, _, _, _ => rfl
  | q :: ps, h, z, hz, _, .pair s x, hzat => by
      obtain ⟨-, hall, -⟩ := h.resolve_left (List.cons_ne_nil _ _)
      have hq := compAt_getD (hall q List.mem_cons_self)
      have hY' : Γ.ref ((VarSymb.step u .here).ext q) = some (.VTypeBox (compTy A q)) :=
        h.ref_head hu
      have hY : θ.at ((VarSymb.step e .here).ext q) =
          .tm (Term.eta ((VarSymb.step u .here).ext q) (.VTypeBox (compTy A q)) hY') :=
        Subst.at_ext_eta hT θ (.here :: q) hu hq hY' hat
      have ha : θ.box.at (.step z .snd) = .tm x := by
        rw [Subst.at_proj _ _ rfl, hzat]
        rfl
      have hb : θ.box.at (.step ((VarSymb.step e .here).ext q) .keep) =
          .tm (Term.eta (.step ((VarSymb.step u .here).ext q) .keep) (.VTypeBox (compTy A q))
            (Ctx.ref_keep_of' hF hY' rfl)) := by
        rw [Subst.box_at_keep, hY]
        exact SubE.keepE_eta hF hY'
      refine congrArg₂ WFF.and (congrArg WFF.box ((WFF.subst_holeAt θ.box (Subst.ok_box hθ)
        (Subst.coh_box hθ hc) hs.boxIn hs'.boxIn _ (WFF.backDup hS hF (compTy A q))).trans
        (WFF.holeAt_congr _ (sig_pair (Term.subst_eta_tm _ _ _ _ _ _ x ha)
          (Term.subst_eta_tm _ _ _ _ _ _ _ hb)) _)))
        (WFF.subst_cTies hS hT hF e he u hu hat ps h.tail _ (Ctx.ref_fst_of hz) s
          (by rw [Subst.at_proj _ _ rfl, hzat]; rfl))

end Read

section Ties

variable {V : Ctx} [V.NoSlots]

/-- ⭐The ties of a `.boxC` shape, read at an address and a packed object. -/
theorem WFF.holeAt_packTies_boxC (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {A : VarType} {cs : List (List Step)} (h : A.CompOk cs)
    (u : VarSymb) (hu : V.ref u = some (.VTypeBox A)) {b : Ann (A.compsFlat cs)}
    (s : Term σ V.boxIn (A.compsFlat cs) b) :
    WFF.holeAt Ctx.NoSlots.slots (Term.pair (Term.eta u (.VTypeBox A) hu) (Term.boxtm s))
        (WFF.packTies hS hF (.boxC A cs h)) =
      WFF.cTiesAt hS hF Ctx.NoSlots.slots u hu cs h s := by
  have hr := Subst.at_single_root (σ := σ) (Δ := V) (.bnd 0)
    (.tm (Term.pair (Term.eta u (.VTypeBox A) hu) (Term.boxtm s)))
  exact WFF.subst_cTies _ _ _ _ _ hS hT hF _ _ u hu (by rw [Subst.at_proj _ _ rfl, hr]; rfl) cs h
    _ _ s (Subst.box_at_inner_boxtm _ (by rw [Subst.at_proj _ _ rfl, hr]; rfl))

/-- The ties of a shape's slot against a packed object of the view. -/
def WFF.tieHole (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) (N : NShape)
    {p₀ : Ann (.VTypeBox N.flat)} (P : Term σ V (.VTypeBox N.flat) p₀) :
    WFF σ (V.insert (.bnd 0) N.ty) 1 :=
  WFF.holeAt ((Ctx.NoSlots.slots (Γ := V)).insert _)
    (Term.pair (Term.eta (.root (.bnd 0)) N.ty (Ctx.ref_insert_root V (.bnd 0) N.ty))
      (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root N.ty) P))
    (WFF.packTies hS hF N)

theorem WFF.instantiate_tieHole (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true)
    (N : NShape) {p₀ : Ann (.VTypeBox N.flat)} (P : Term σ V (.VTypeBox N.flat) p₀)
    {e₀ : Ann N.ty} (E : Term σ V N.ty e₀) :
    WFF.instantiate Ctx.NoSlots.slots E (WFF.tieHole hS hF N P) =
      WFF.holeAt Ctx.NoSlots.slots (Term.pair E P) (WFF.packTies hS hF N) := by
  unfold WFF.tieHole WFF.instantiate WFF.substRoot
  rw [WFF.subst_holeAt]
  refine WFF.holeAt_congr _ (sig_pair (Term.subst_eta_tm _ _ _ _ _ _ E
    (Subst.at_single_root _ _)) ?_) _
  exact (Term.subst_single_mono (Ctx.Le.refl _) _ _ _ _
    ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) P).trans
    (congrArg (Sigma.mk _) (Term.mono_refl _ P))

theorem WFF.mono_tieHole {V' : Ctx} [V'.NoSlots] (h : V.Le V') (hS : ModalSys.BStrong = true)
    (hF : ModalSys.Four = true) (N : NShape) {p₀ : Ann (.VTypeBox N.flat)}
    (P : Term σ V (.VTypeBox N.flat) p₀) :
    WFF.mono (h.insert (.bnd 0) N.ty) (WFF.tieHole hS hF N P) =
      WFF.tieHole hS hF N (Term.mono h P) := by
  unfold WFF.tieHole
  rw [WFF.mono_holeAt _ _ ((Ctx.NoSlots.slots (Γ := V')).insert _)]
  refine WFF.holeAt_congr _ (sig_pair (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)) ?_) _
  rw [Term.mono_mono, Term.mono_mono]

/-- `ret_counitC`'s body at a boxed object. -/
theorem instantiate_counitBodyC {A C : VarType} {s₀ : Ann A} (s : Term σ V.boxIn A s₀)
    {c₀ : Ann C} (bd : Term σ V.boxIn C c₀)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A C)) 1) :
    WFF.instantiate Ctx.NoSlots.slots (Term.boxtm s) (counitBodyC bd ψ) =
      WFF.box (WFF.holeAt Ctx.NoSlots.slots (Term.pair s bd) ψ) := by
  have hat := Subst.at_single_root (σ := σ) (Δ := V) (.bnd 0) (.tm (Term.boxtm s))
  unfold counitBodyC WFF.instantiate WFF.substRoot
  refine congrArg WFF.box ((WFF.subst_holeAt _ _ _ _ _ _ ψ).trans (WFF.holeAt_congr _
    (sig_pair (Term.subst_eta_tm _ _ _ _ _ _ s (Subst.box_at_inner_boxtm _ hat)) ?_) ψ))
  exact Eq.trans (Term.subst_single_box_mono (Ctx.Le.refl V)
    (Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root (.VTypeBox A)) (.tm (Term.boxtm s))
    (Subst.ok_single (Ctx.Le.refl V) rfl)
    (Subst.coh_single ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) (Ctx.Le.refl V) rfl)
    ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) bd)
    (congrArg (Sigma.mk _) (Term.mono_refl _ bd))

end Ties

/-! ## Unlifting a companion shape -/

section Comps

variable {Γ : Ctx} [Γ.NoSlots] {A : VarType}

omit [Γ.NoSlots] in
/-- The view with a fresh object, as the `□` view extends into it. -/
theorem le_freeView (O : OutLeg Γ) {u : ℕ} (hu : O.view.RootFresh (.free u)) (T : VarType) :
    Γ.boxIn.Le (O.view.insert (.free u) T) :=
  O.le_view.trans (Ctx.le_insert hu.root T)

/-- ⭐The object's tie at one companion gives `compTie`, at the fresh object of `Ctx.insert`. -/
def Proof.compTie_of (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) (O : OutLeg Γ) {cs : List (List Step)} (q : List Step)
    (h' : A.CompOk (q :: cs)) {k₀ : Ann (compTy A q)} (k : Term σ Γ.boxIn (compTy A q) k₀)
    (u : ℕ) (hu : O.view.RootFresh (.free u))
    {Δ : List (WFF σ (O.view.insert (.free u) (.VTypeBox A)) 0)}
    (H : Proof σ (O.view.insert (.free u) (.VTypeBox A)) Δ (WFF.box (WFF.holeAt Ctx.NoSlots.slots
      (Term.pair (Term.mono (le_freeView O hu _).boxIn
          (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) k))
        (Term.eta (.step ((VarSymb.step (.root (.free u)) .here).ext q) .keep)
          (.VTypeBox (compTy A q))
          (Ctx.ref_keep_of' hF (h'.ref_head (Ctx.ref_insert_root O.view (.free u) (.VTypeBox A)))
            rfl))) (WFF.backDup hS hF _)))) :
    Proof σ (O.view.insert (.free u) (.VTypeBox A)) Δ (WFF.openFree u hu Ctx.NoSlots.slots
      (WFF.compTie hS hF q cs h' (compBd hF O k).2)) := by
  have hV := Ctx.le_insert hu.root (.VTypeBox A)
  have h₀ := Ctx.ref_insert_root O.view (.free u) (.VTypeBox A)
  let x := Term.mono (le_freeView O hu (.VTypeBox A)).boxIn
    (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) k)
  have hP := NShape.holeAt_packObj (σ := σ) (.boxC A (q :: cs) h') _ h₀
  have e₁ : (⟨_, Term.mono hV.boxIn (compBd hF O k).2⟩ :
      Σ b, Term σ (O.view.insert (.free u) (.VTypeBox A)).boxIn (.VTypeBox (compTy A q)) b) =
      ⟨_, Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) x)⟩ := by
    unfold compBd
    dsimp only [x]
    rw [Term.mono_mono, Term.shift_mono (Ctx.shifts_boxIn_boxIn hF Γ.boxIn)
      (Ctx.shifts_boxIn_boxIn hF _) (le_freeView O hu _).boxIn (le_freeView O hu _).boxIn.boxIn]
    exact sig_boxtm (sig_mono _ (Term.shift_shift_same _ _ _ k).symm)
  rw [← WFF.instantiate_eta_openFree u hu Ctx.NoSlots.slots Ctx.NoSlots.slots, WFF.compTie,
    WFF.mono_bodyRepl hV, WFF.instantiate_bodyRepl, Term.mono_mono, Term.subst_mono]
  refine Proof.conv (WFF.instantiate_congr_sig _ hP _).symm ?_
  rw [mono_counitBodyC hV, instantiate_counitBodyC]
  refine Proof.conv (congrArg WFF.box ((WFF.holeAt_congr _ (sig_pair rfl e₁) _).trans
    (WFF.holeAt_backSnd hS hF _ _ _ _))).symm ?_
  exact Proof.tie_flip hS hT hF (h'.ref_head h₀) x H

/-- `Back` of a pair, at its first component. -/
def Proof.back_fst (hS : ModalSys.BStrong = true) {Δ : List (WFF σ Γ 0)} {F C : VarType}
    {a₁ : Ann F} {a₂ : Ann C} {b₁ : Ann F} {b₂ : Ann C} (s₁ : Term σ Γ.boxIn.boxIn F a₁)
    (s₂ : Term σ Γ.boxIn.boxIn C a₂) (t₁ : Term σ Γ F b₁) (t₂ : Term σ Γ C b₂)
    (h : Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.pair s₁ s₂)))
      (Term.pair t₁ t₂))) :
    Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm s₁)) t₁) := by
  refine Proof.conv (OutLeg.back_congr hS .nec ?_ ?_) (Proof.back_beta hS .nec (Term.pair s₁ s₂)
    (Term.pair t₁ t₂) (Term.eta (.step (.root (.bnd 0)) .fst) F
      (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))) h)
  · rw [Term.holeRead_eq_holeAt]
    exact Term.holeAt_pair_fst _ _
  · rw [Term.holeRead_eq_holeAt]
    exact Term.holeAt_pair_fst _ _

/-- `Back` of a pair, at its second component. -/
def Proof.back_snd (hS : ModalSys.BStrong = true) {Δ : List (WFF σ Γ 0)} {F C : VarType}
    {a₁ : Ann F} {a₂ : Ann C} {b₁ : Ann F} {b₂ : Ann C} (s₁ : Term σ Γ.boxIn.boxIn F a₁)
    (s₂ : Term σ Γ.boxIn.boxIn C a₂) (t₁ : Term σ Γ F b₁) (t₂ : Term σ Γ C b₂)
    (h : Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.pair s₁ s₂)))
      (Term.pair t₁ t₂))) :
    Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm s₂)) t₂) := by
  refine Proof.conv (OutLeg.back_congr hS .nec ?_ ?_) (Proof.back_beta hS .nec (Term.pair s₁ s₂)
    (Term.pair t₁ t₂) (Term.eta (.step (.root (.bnd 0)) .snd) C
      (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))) h)
  · rw [Term.holeRead_eq_holeAt]
    exact Term.holeAt_pair_snd _ _
  · rw [Term.holeRead_eq_holeAt]
    exact Term.holeAt_pair_snd _ _

/-- ⭐**The companions, one by one**: from the base object's returning possibility, add each
    companion with the value given by the carrier's component, its tie from the body. -/
def Proof.retC_aux (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ)
    (Ψ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1) (c : ℕ) (hc : Γ.RootFresh (.free c))
    (u : ℕ) (hu : O.view.RootFresh (.free u)) :
    (cs : List (List Step)) → (h : A.CompOk cs) → {b₀ : Ann (A.compsFlat cs)} →
    (b : Term σ Γ.boxIn (A.compsFlat cs) b₀) → {a : Ann (A.compsFlat cs)} →
    (t : Term σ Γ (A.compsFlat cs) a) →
    Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm
      (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b))) t) →
    Proof σ Γ Δ (O.dia (WFF.instantiate Ctx.NoSlots.slots (Term.boxtm (compsBase cs
      (Term.mono O.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b))).2) Ψ)) →
    Proof σ (O.view.insert (.free u) (.VTypeBox A)) [WFF.openFree u hu Ctx.NoSlots.slots Ψ]
      (WFF.cTiesAt hS hF Ctx.NoSlots.slots (.root (.free u))
        (Ctx.ref_insert_root O.view (.free u) (.VTypeBox A)) cs h
        (Term.mono (le_freeView O hu _).boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b))) →
    Proof σ Γ Δ (O.retS hS (.nec (.boxC A cs h)) t Ψ)
  | [], _, _, b, _, t, hb, hd, _ => Proof.ret_unlift hS hT hF O b t Ψ hb hd
  | q :: ps, h, _, .pair b₁ k, _, .pair t₁ w, hb, hd, ht =>
      Proof.ret_comp_value hS hT hF O (h := h.tail) q h t₁ k w Ψ c hc
        (Proof.retC_aux hS hT hF O Ψ c hc u hu ps h.tail b₁ t₁ (Proof.back_fst hS _ _ _ _ hb) hd
          (Proof.and_elim_r ht))
        (Proof.leg_all O _ _ u hu (Proof.compTie_of hS hT hF O q h k u hu (Proof.and_elim_l ht)))
        (Proof.back_snd hS _ _ _ _ hb)

/-- ⭐The packed body at a boxed object: `Φ` of the base, with the ties. -/
theorem WFF.instantiate_packedBody_boxC (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true)
    {V : Ctx} [V.NoSlots] {cs : List (List Step)} (h : A.CompOk cs)
    (Φ : WFF σ (V.insert (.bnd 0) (.VTypeBox A)) 1) {b : Ann (A.compsFlat cs)}
    (s : Term σ V.boxIn (A.compsFlat cs) b) :
    WFF.instantiate Ctx.NoSlots.slots (Term.boxtm s)
        (WFF.packedBody (N := .boxC A cs h) hS hF Φ) =
      WFF.and (WFF.instantiate Ctx.NoSlots.slots (Term.boxtm (compsBase cs s).2) Φ)
        (WFF.holeAt Ctx.NoSlots.slots (Term.pair (Term.boxtm (compsBase cs s).2) (Term.boxtm s))
          (WFF.packTies hS hF (.boxC A cs h))) := by
  have hat := Subst.at_single_root (σ := σ) (Δ := V) (.bnd 0) (.tm (Term.boxtm s))
  have hU : (⟨_, Term.subst (Subst.singleIdx (.bnd 0) (.tm (Term.boxtm s)))
      (Subst.single (.bnd 0) (.tm (Term.boxtm s))) (Subst.ok_single (Ctx.empty_le V) rfl)
      (Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le V) rfl)
      (NShape.unpack₀ (.boxC A cs h)).2⟩ : Σ b, Term σ V (.VTypeBox A) b) =
      ⟨_, Term.boxtm (compsBase cs s).2⟩ :=
    sig_boxtm (Term.subst_eta_tm _ _ _ _ _ _ _
      (at_compsBase _ cs s _ (Subst.box_at_inner_boxtm _ hat)))
  refine congrArg₂ WFF.and ((WFF.instantiate_bodyRepl _ _ _).trans
    (WFF.instantiate_congr_sig _ ?_ Φ)) ?_
  · rw [Term.subst_mono]
    exact hU
  · change WFF.subst _ _ _ _ _ _ (WFF.holeAt _ _ _) = _
    rw [WFF.subst_holeAt]
    refine WFF.holeAt_congr _ ?_ _
    rw [Term.subst_mono]
    exact sig_pair hU (Term.subst_eta_tm _ _ _ _ _ _ _ hat)

/-- ⭐⭐**Unlifting at a companion shape** (T + 4, strong B), the converse of `Proof.retN_lift` at
    `.boxC`, along either leg. -/
def Proof.retC_unlift (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ) {cs : List (List Step)}
    (h : A.CompOk cs) {b₀ : Ann (A.compsFlat cs)} (b : Term σ Γ.boxIn (A.compsFlat cs) b₀)
    {a : Ann (A.compsFlat cs)} (t : Term σ Γ (A.compsFlat cs) a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1) (c : ℕ) (hc : Γ.RootFresh (.free c))
    (u : ℕ) (hu : O.view.RootFresh (.free u))
    (hb : Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm
      (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b))) t))
    (hd : Proof σ Γ Δ (O.dia (WFF.instantiate Ctx.NoSlots.slots
      (Term.boxtm (Term.mono O.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b)))
      (WFF.packedBody (N := .boxC A cs h) hS hF Φ)))) :
    Proof σ Γ Δ (O.retS hS (.nec (.boxC A cs h)) t Φ) := by
  let s := Term.mono O.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b)
  let Ψ := WFF.and Φ (WFF.tieHole (V := O.view) hS hF (.boxC A cs h) (Term.boxtm s))
  have hd' : Proof σ Γ Δ (O.dia (WFF.instantiate Ctx.NoSlots.slots
      (Term.boxtm (compsBase cs s).2) Ψ)) := by
    refine Proof.conv (congrArg O.dia ?_) hd
    refine (WFF.instantiate_packedBody_boxC hS hF h Φ s).trans ?_
    exact congrArg (WFF.and _) (WFF.instantiate_tieHole hS hF (.boxC A cs h) _ _).symm
  have hV := Ctx.le_insert hu.root (.VTypeBox A)
  have ht : Proof σ (O.view.insert (.free u) (.VTypeBox A)) [WFF.openFree u hu Ctx.NoSlots.slots Ψ]
      (WFF.cTiesAt hS hF Ctx.NoSlots.slots (.root (.free u))
        (Ctx.ref_insert_root O.view (.free u) (.VTypeBox A)) cs h
        (Term.mono (le_freeView O hu _).boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b))) := by
    have e : WFF.openFree u hu Ctx.NoSlots.slots
        (WFF.tieHole hS hF (.boxC A cs h) (Term.boxtm s)) =
        WFF.cTiesAt hS hF Ctx.NoSlots.slots (.root (.free u))
          (Ctx.ref_insert_root O.view (.free u) (.VTypeBox A)) cs h
          (Term.mono (le_freeView O hu _).boxIn
            (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b)) := by
      rw [← WFF.instantiate_eta_openFree u hu Ctx.NoSlots.slots Ctx.NoSlots.slots,
        WFF.mono_tieHole hV, WFF.instantiate_tieHole]
      refine Eq.trans ?_ (WFF.holeAt_packTies_boxC hS hT hF h _ _ _)
      exact WFF.holeAt_congr _ (sig_pair rfl (sig_boxtm (congrArg (Sigma.mk _)
        (Term.mono_mono _ _ _)))) _
    exact Proof.conv e (Proof.and_elim_r (Proof.lookup
      (x := WFF.openFree u hu Ctx.NoSlots.slots Ψ) List.mem_cons_self))
  refine Proof.ret_monoS (S := .nec (.boxC A cs h)) hS O t Ψ Φ
    (Proof.retC_aux hS hT hF O Ψ c hc u hu cs h b t hb hd' ht)
    (Proof.leg_all O _ _ u hu (Proof.and_elim_l (Proof.lookup
      (x := WFF.openFree u hu Ctx.NoSlots.slots Ψ) List.mem_cons_self)))

end Comps

/-! ## Every shape -/

section Shapes

variable {Γ : Ctx} [Γ.NoSlots]

/-- ⭐⭐**Unlifting at every necessary shape** (T + 4, strong B): `Proof.retC_unlift` at the packed
    shape, then `ret_map` along `unpackG`.  The value is the packed value unpacked. -/
def Proof.retN_unlift (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ) (N : NShape)
    {b₀ : Ann N.packed.flat} (b : Term σ Γ.boxIn N.packed.flat b₀) {a : Ann N.packed.flat}
    (t : Term σ Γ N.packed.flat a) (Φ : WFF σ (O.view.insert (.bnd 0) N.ty) 1) (c : ℕ)
    (hc : Γ.RootFresh (.free c)) (u : ℕ) (hu : O.view.RootFresh (.free u))
    (hb : Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm
      (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b))) t))
    (hd : Proof σ Γ Δ (O.dia (WFF.instantiate Ctx.NoSlots.slots
      (Term.boxtm (Term.mono O.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b)))
      (WFF.packedBody (N := N.packed) hS hF (WFF.bodyRepl (Term.mono
        ((Ctx.empty_le O.view).insert (.bnd 0) _) (unpackG (σ := σ) N).obj.2) Φ))))) :
    Proof σ Γ Δ (O.retS hS (.nec N) (Term.holeRead t (unpackG (σ := σ) N).val.2) Φ) :=
  Proof.ret_map hS O (S := .nec N.packed) (T := N) (unpackG N) t Φ
    (Proof.retC_unlift hS hT hF O N.packOk b t _ c hc u hu hb hd)

/-- ⭐⭐**Unlifting at every witnessed shape** (T + 4, strong B): `ret_keep` on top of
    `Proof.retN_unlift`. -/
def Proof.retWN_unlift (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ) (N : NShape) {X : VarType}
    {b₀ : Ann N.packed.flat} (b : Term σ Γ.boxIn N.packed.flat b₀) {a : Ann N.packed.flat}
    (t : Term σ Γ N.packed.flat a) (x : VarSymb) (hx : ∃ Y, Γ.ref x = some (.VTypeDia Y))
    {x₀ : Ann X} (bd : Term σ (Γ.diaIn x) X x₀) {c₀ : Ann X} (w : Term σ Γ X c₀)
    (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit N X).ty) 1) (c : ℕ)
    (hc : Γ.RootFresh (.free c)) (u : ℕ) (hu : O.view.RootFresh (.free u))
    (hb : Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm
      (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b))) t))
    (hh : Proof σ Γ Δ (WFF.here hT (Term.diatm x hx bd) w))
    (hd : Proof σ Γ Δ (O.dia (WFF.instantiate Ctx.NoSlots.slots
      (Term.boxtm (Term.mono O.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b)))
      (WFF.packedBody (N := N.packed) hS hF (WFF.bodyRepl (Term.mono
        ((Ctx.empty_le O.view).insert (.bnd 0) _) (unpackG (σ := σ) N).obj.2)
        (WFF.bodyRepl (RShape.keepL hF O N hx bd).2 Φ)))))) :
    Proof σ Γ Δ (O.retS hS (.wit N X)
      (Term.pair (Term.holeRead t (unpackG (σ := σ) N).val.2) w) Φ) :=
  Proof.ret_keep hS hT hF O N x hx bd w _ Φ hh
    (Proof.retN_unlift hS hT hF O N b t _ c hc u hu hb hd)

end Shapes

/-! ## From a leg to a kept carrier -/

section Leg

variable {Γ : Ctx} [Γ.NoSlots] {A : VarType}

omit [Γ.NoSlots] in
/-- The carrier of a home term, as the box of its image shifted once more. -/
theorem compBd_eq (hF : ModalSys.Four = true) (O : OutLeg Γ) {k₀ : Ann A}
    (k : Term σ Γ.boxIn A k₀) :
    compBd hF O k = ⟨_, Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF O.view)
      (Term.mono O.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) k)))⟩ := by
  unfold compBd
  rw [Term.shift_mono (Ctx.shifts_boxIn_boxIn hF Γ.boxIn) (Ctx.shifts_boxIn_boxIn hF O.view)
    O.le_view.boxIn O.le_view.boxIn.boxIn]
  exact sig_boxtm (sig_mono _ (Term.shift_shift_same _ _ _ k).symm)

/-- ⭐⭐**What comes back along a leg comes back as a kept carrier** (T + 4, strong B): if a leg's
    carrier agrees at some arrow with the home term `b`, kept, then `b` kept comes back as the
    value.  So one arrow's reading of the carrier is interchangeable with the value (`back_here`,
    with any parameters).  This is what makes the round trip: `ret_bridge` with the agreement in
    the body, then `ret_counitC` at `b`'s own carrier. -/
def Proof.back_of_leg (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ) {b₀ : Ann A}
    (b : Term σ Γ.boxIn A b₀) (bd : Term σ O.view.boxIn A (Ann.shift 0 b₀)) {a : Ann A}
    (t : Term σ Γ A a) (hb : Proof σ Γ Δ (O.back hS bd t))
    (he : Proof σ Γ Δ (O.dia (WFF.box (eqRec A
      (Term.mono O.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b)) bd)))) :
    Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm
      (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b))) t) := by
  have hne : Proof σ Γ Δ (O.dia .top) := Proof.leg_dia O Proof.top_intro he
  have B₀ : Proof σ Γ Δ (O.back hS (compBd hF O b).2 (Term.boxtm b)) :=
    Proof.conv (OutLeg.back_congr hS O rfl (Term.collapse_boxtm_shift hT hF b))
      (Proof.back_keep hS hT hF O (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b)) hne)
  let x := Term.mono O.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b)
  have hq : Proof σ O.view [WFF.box (eqRec A x bd)]
      (WFF.box (WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift
        (Ctx.shifts_boxIn_boxIn hF O.view.boxIn)
        (Term.shift (Ctx.shifts_boxIn_boxIn hF O.view) x)))) bd)) :=
    Proof.leg_K (.nec : OutLeg O.view) (Proof.back_eq hS .nec _ x bd
      (Proof.back_shift hS hT hF x) (Proof.lookup List.mem_cons_self))
      (Proof.lookup List.mem_cons_self)
  have hd : Proof σ Γ Δ (O.dia (O.bodyRead (Term.boxtm bd)
      (counitBodyC (compBd hF O b).2 (WFF.backDup hS hF A)))) := by
    refine Proof.leg_dia O (Proof.conv ?_ hq) he
    unfold OutLeg.bodyRead
    rw [instantiate_counitBodyC]
    refine congrArg WFF.box (Eq.trans ?_ (WFF.holeAt_congr _
      (sig_pair rfl (compBd_eq hF O b).symm) _))
    exact (WFF.holeAt_backDup hS hF _ bd _).symm
  have H := Proof.ret_counitC hS O t (compBd hF O b).2 (Term.boxtm b) (WFF.backDup hS hF A)
    (Proof.ret_bridge hS O bd t _ hb hd) B₀
  exact Proof.conv ((WFF.holeRead_eq_holeAt _ _).trans (WFF.holeAt_backDup hS hF _ t b)) H

end Leg

end V12M
