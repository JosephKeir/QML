import QML.QML_v12m_BRet
import QML.QML_v12m_BDia
import QML.QML_v12m_CanonFunc
import QML.QML_v12m_CanonInterch

/-!
# QML v12m — strong B on S5: lifting a returning possibility

Under T and 4 (5's cluster) the object a returning possibility finds at the far end is a kept
necessary object of this world: `◇[d ↦ t] Φ(d)` gives some `n : □A` here that comes back as `t`
along an arrow out (`n.dup`) and with `◇Φ(n.keep)`.  So the canonical cluster needs no new world
for it: an ordinary child of `◇Φ(n.keep)` will do.

The derivation (docs §3 5, "Strong B on S5").  Inside the body, name `b := d.dup`.  What `b` is, is
said by three **ties**, one hole formula (`WFF.ties`) on the pair `⟨d, b⟩`:
* `□ Back (b.inner.dup) d.inner`, for `ret_counit`: `b`'s value `n` comes back as `t`;
* `□□ Back (dd b.keep.inner) b.inner.keep`: `b` is of kept form;
* `Back (b.dup) d`: `b.here` and `d` are interchangeable.
All are `back_keep` at `b = d.dup` (`Proof.ties_dup`).  The unit then carries `n.dup` to the far
end, and `ret_counitC` brings it back as `b.here`.
-/

namespace V12M

variable [ModalSys] {σ : Signature}

open BArrow

/-! ## Hole formulas of `Back` -/

/-- A `Back` atom on a hole, its carrier and value definable maps of the hole: reading it applies
    the maps (`WFF.holeAt_backG`). -/
def WFF.backG (hS : ModalSys.BStrong = true) {H X : VarType}
    (g : GFunc σ H (.VTypeBox (.VTypeBox X))) (f : GFunc σ H X) :
    WFF σ (Ctx.empty.insert (.bnd 0) H) 1 :=
  WFF.back hS .nec
    (Canon.applyG g (Term.eta (.root (.bnd 0)) H (Ctx.ref_insert_root Ctx.empty (.bnd 0) H))).2
    (Canon.applyG f (Term.eta (.root (.bnd 0)) H (Ctx.ref_insert_root Ctx.empty (.bnd 0) H))).2

theorem Canon.applyG_sig {A B : VarType} (g : GFunc σ A B) {Γ : Ctx} {a a' : Ann A}
    {t : Term σ Γ A a} {t' : Term σ Γ A a'}
    (h : (⟨a, t⟩ : Σ c, Term σ Γ A c) = ⟨a', t'⟩) : Canon.applyG g t = Canon.applyG g t' := by
  cases h
  rfl

/-- ⭐Reading a `Back` hole applies its maps. -/
theorem WFF.holeAt_backG (hS : ModalSys.BStrong = true) {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d)
    {H X : VarType} (g : GFunc σ H (.VTypeBox (.VTypeBox X))) (f : GFunc σ H X) {a : Ann H}
    (s : Term σ Γ H a) :
    WFF.holeAt hs s (WFF.backG hS g f) =
      WFF.back hS .nec (Canon.applyG g s).2 (Canon.applyG f s).2 := by
  have hη := Term.subst_eta_tm (Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm s))
    (Subst.ok_single (Ctx.empty_le Γ) rfl)
    (Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le Γ) rfl) H (.root (.bnd 0))
    (Ctx.ref_insert_root Ctx.empty (.bnd 0) H) s (Subst.at_single_root _ _)
  refine WFF.back_congr hS .nec ?_ ?_
  · exact (Canon.applyG_subst g _ _ _ _).symm.trans (Canon.applyG_sig g hη)
  · exact (Canon.applyG_subst f _ _ _ _).symm.trans (Canon.applyG_sig f hη)

/-- `Back (y.dup) x` on a hole `⟨x, y⟩`. -/
def WFF.backDup (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) (X : VarType) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd X (.VTypeBox X))) 1 :=
  WFF.backG hS (.comp (.dup hF) .snd) .fst

/-- `Back (x.dup.dup) y` on a hole `⟨x, y⟩`: `x` read at its own level is `y`
    (`Proof.back_dd_read`). -/
def WFF.backDD (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) (A : VarType) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeBox A) (.VTypeBox A))) 1 :=
  WFF.backG hS (.comp (.dup hF) (.comp (.dup hF) .fst)) .snd

theorem WFF.holeAt_backDup (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) {Γ : Ctx}
    {d : ℕ} (hs : Γ.SlotsFrom d) {X : VarType} {a : Ann X} (x : Term σ Γ X a) {c₀ : Ann X}
    (c : Term σ Γ.boxIn X c₀) :
    WFF.holeAt hs (Term.pair x (Term.boxtm c)) (WFF.backDup hS hF X) =
      WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) c))) x :=
  WFF.holeAt_backG hS hs _ _ _

theorem WFF.holeAt_backDD (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) {Γ : Ctx}
    {d : ℕ} (hs : Γ.SlotsFrom d) {A : VarType} {c₀ : Ann A} (c : Term σ Γ.boxIn A c₀)
    {a : Ann (.VTypeBox A)} (y : Term σ Γ (.VTypeBox A) a) :
    WFF.holeAt hs (Term.pair (Term.boxtm c) y) (WFF.backDD hS hF A) =
      WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ)
        (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) c))))) y :=
  WFF.holeAt_backG hS hs _ _ _

/-! ## The ties -/

/-- The hole of the ties: the object `d` and its companion `b`. -/
abbrev tieTy (A : VarType) : VarType := .VTypeProd (.VTypeBox A) (.VTypeBox (.VTypeBox A))

section Ties

variable (A : VarType)

/-- The hole's own context. -/
abbrev tieCtx : Ctx := Ctx.empty.insert (.bnd 0) (tieTy A)

omit [ModalSys] in
theorem tieCtx_slots : (tieCtx A).SlotsFrom 1 := Ctx.slotsFrom_empty.insert _

theorem tie_fst : (tieCtx A).ref (.step (.root (.bnd 0)) .fst) = some (.VTypeBox A) :=
  Ctx.ref_fst_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (tieTy A))

theorem tie_snd : (tieCtx A).ref (.step (.root (.bnd 0)) .snd) = some (.VTypeBox (.VTypeBox A)) :=
  Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (tieTy A))

/-- `□ Back (b.inner.dup) d.inner`. -/
def WFF.tieOne (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) :
    WFF σ (tieCtx A) 1 :=
  WFF.box (WFF.holeAt (tieCtx_slots A).boxIn
    (Term.pair
      (Term.eta (VarSymb.step (.root (.bnd 0)) .fst).inner A (Ctx.ref_inner (tie_fst A)))
      (Term.eta (VarSymb.step (.root (.bnd 0)) .snd).inner (.VTypeBox A)
        (Ctx.ref_inner (tie_snd A))))
    (WFF.backDup hS hF A))

/-- `□□ Back (dd b.keep.inner) b.inner.keep`: the two ways of reading `b` two views in agree. -/
def WFF.tieTwo (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) :
    WFF σ (tieCtx A) 1 :=
  WFF.box (WFF.box (WFF.holeAt (tieCtx_slots A).boxIn.boxIn
    (Term.pair
      (Term.eta (VarSymb.step (.step (.root (.bnd 0)) .snd) .keep).inner (.VTypeBox A)
        (Ctx.ref_inner (Ctx.ref_keep_of' hF (tie_snd A) rfl)))
      (Term.eta (.step (VarSymb.step (.root (.bnd 0)) .snd).inner .keep) (.VTypeBox A)
        (Ctx.ref_keep_of' hF (Ctx.ref_inner (tie_snd A)) rfl)))
    (WFF.backDD hS hF A)))

/-- ⭐**The ties** on `⟨d, b⟩`. -/
def WFF.ties (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) : WFF σ (tieCtx A) 1 :=
  WFF.and (WFF.tieOne A hS hF) (WFF.and (WFF.tieTwo A hS hF) (WFF.backDup hS hF (.VTypeBox A)))

end Ties

section Read

variable {Γ : Ctx} {A : VarType} {a₀ : Ann A} {c₀ : Ann A}

/-- An entry of a kept address, one view in. -/
theorem Subst.box_at_keep {Δ : Ctx} (θ : Subst σ Δ) (v : VarSymb) :
    θ.box.at (.step v .keep) = (θ.at v).keepE := by
  rw [Subst.at_nonproj _ rfl]
  rfl

/-- The entries of the ties' hole. -/
theorem tie_at_fst (a : Term σ Γ.boxIn A a₀) (c : Term σ Γ.boxIn.boxIn A c₀) :
    (Subst.single (σ := σ) (Δ := Γ) (.bnd 0)
      (.tm (Term.pair (Term.boxtm a) (Term.boxtm (Term.boxtm c))))).at
        (.step (.root (.bnd 0)) .fst) = .tm (Term.boxtm a) := by
  rw [Subst.at_proj _ _ rfl, Subst.at_single_root]
  rfl

theorem tie_at_snd (a : Term σ Γ.boxIn A a₀) (c : Term σ Γ.boxIn.boxIn A c₀) :
    (Subst.single (σ := σ) (Δ := Γ) (.bnd 0)
      (.tm (Term.pair (Term.boxtm a) (Term.boxtm (Term.boxtm c))))).at
        (.step (.root (.bnd 0)) .snd) = .tm (Term.boxtm (Term.boxtm c)) := by
  rw [Subst.at_proj _ _ rfl, Subst.at_single_root]
  rfl

/-- ⭐**The ties, read** at a necessary pair `⟨□a, □□c⟩`. -/
theorem WFF.holeAt_ties (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) {d : ℕ}
    (hs : Γ.SlotsFrom d) (a : Term σ Γ.boxIn A a₀) (c : Term σ Γ.boxIn.boxIn A c₀) :
    WFF.holeAt hs (Term.pair (Term.boxtm a) (Term.boxtm (Term.boxtm c))) (WFF.ties A hS hF) =
      WFF.and (WFF.box (WFF.holeAt hs.boxIn (Term.pair a (Term.boxtm c)) (WFF.backDup hS hF A)))
        (WFF.and
          (WFF.box (WFF.box (WFF.holeAt hs.boxIn.boxIn
            (Term.pair (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) (Term.boxtm c))
              (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ.boxIn) c)))
            (WFF.backDD hS hF A))))
          (WFF.holeAt hs (Term.pair (Term.boxtm a) (Term.boxtm (Term.boxtm c)))
            (WFF.backDup hS hF (.VTypeBox A)))) := by
  have hb := Subst.box_at_inner_boxtm _ (tie_at_snd a c)
  have hk : (Subst.single (σ := σ) (Δ := Γ) (.bnd 0)
      (.tm (Term.pair (Term.boxtm a) (Term.boxtm (Term.boxtm c))))).box.at
        (.step (.step (.root (.bnd 0)) .snd) .keep) =
      .tm (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) (Term.boxtm c))) := by
    rw [Subst.box_at_keep, tie_at_snd, SubE.keepE_tm _ hF]
  have e₁ : WFF.holeAt hs (Term.pair (Term.boxtm a) (Term.boxtm (Term.boxtm c)))
      (WFF.tieOne A hS hF) =
      WFF.box (WFF.holeAt hs.boxIn (Term.pair a (Term.boxtm c)) (WFF.backDup hS hF A)) := by
    refine congrArg WFF.box ((WFF.subst_holeAt _ _ _ _ _ _ _).trans (WFF.holeAt_congr _ ?_ _))
    exact sig_pair (Term.subst_eta_tm _ _ _ _ _ _ a (Subst.box_at_inner_boxtm _ (tie_at_fst a c)))
      (Term.subst_eta_tm _ _ _ _ _ _ _ hb)
  have e₂ : WFF.holeAt hs (Term.pair (Term.boxtm a) (Term.boxtm (Term.boxtm c)))
      (WFF.tieTwo A hS hF) =
      WFF.box (WFF.box (WFF.holeAt hs.boxIn.boxIn
        (Term.pair (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) (Term.boxtm c))
          (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ.boxIn) c)))
        (WFF.backDD hS hF A))) := by
    refine congrArg WFF.box (congrArg WFF.box
      ((WFF.subst_holeAt _ _ _ _ _ _ _).trans (WFF.holeAt_congr _ ?_ _)))
    refine sig_pair (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ hk))
      (Term.subst_eta_tm _ _ _ _ _ _ _ ?_)
    rw [Subst.box_at_keep, hb, SubE.keepE_tm _ hF]
  exact congrArg₂ WFF.and e₁ (congrArg₂ WFF.and e₂ rfl)

end Read

/-! ## `back_keep`, read -/

section Keep

variable {A : VarType} {a₀ c₀ : Ann A} {Γ : Ctx}

theorem keepOnly_of (hT : ModalSys.T = true) (hF : ModalSys.Four = true) :
    ModalSys.keepOnly = true := by
  simp [ModalSys.keepOnly, hT, hF]

/-- `□(shift c)` read here is `□c`. -/
theorem Term.collapse_boxtm_shift (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    (c : Term σ Γ.boxIn A c₀) :
    (⟨_, Term.collapse (Ctx.collapses_boxIn_self hT Γ)
        (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) c))⟩ :
      Σ e, Term σ Γ (.VTypeBox A) e) = ⟨_, Term.boxtm c⟩ :=
  sig_boxtm ((Term.collapse_shift_self (m := 0) (Ctx.shifts_boxIn_boxIn hF Γ)
    (Ctx.collapses_boxIn_self hT Γ).boxIn (Ctx.Le.refl _) c).trans
      (congrArg (Sigma.mk _) (Term.mono_refl _ c)))

/-- Shifting then collapsing in a `□` view undoes itself. -/
theorem Term.collapse_shift_boxIn (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    {T : VarType} {b : Ann T} (t : Term σ Γ.boxIn T b) :
    (⟨_, Term.collapse (Ctx.collapses_boxIn_self hT Γ.boxIn)
        (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) t)⟩ : Σ e, Term σ Γ.boxIn T e) = ⟨_, t⟩ :=
  (Term.collapse_shift_same (Ctx.shifts_boxIn_boxIn hF Γ) (Ctx.collapses_boxIn_self hT Γ.boxIn)
    (Ctx.Le.refl _) (Ctx.shiftCollapseId_keepOnly (keepOnly_of hT hF) Γ) t).trans
      (congrArg (Sigma.mk _) (Term.mono_refl _ t))

/-- Two views in, the two ways of shifting a kept address agree. -/
theorem Term.shift_boxtm_shift_eta (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    (r : VarSymb) (hr : Γ.ref r = some (.VTypeBox A)) :
    (⟨_, Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) (Term.boxtm (Term.shift
        (Ctx.shifts_boxIn_boxIn hF Γ) (Term.eta (σ := σ) r.inner A (Ctx.ref_inner hr))))⟩ :
      Σ e, Term σ Γ.boxIn.boxIn (.VTypeBox A) e) =
      ⟨_, Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ.boxIn) (Term.shift
        (Ctx.shifts_boxIn_boxIn hF Γ) (Term.eta (σ := σ) r.inner A (Ctx.ref_inner hr))))⟩ := by
  have hs := Ctx.shifts_boxIn_boxIn hF Γ
  have e := Term.shift_eta (σ := σ) hs r.inner A (Ctx.ref_inner hr)
  have hA : (r.inner.shift 0).shift 1 = (r.inner.shift 0).shift 0 := by
    rw [VarSymb.inner_keepOnly (keepOnly_of hT hF), VarSymb.shift_proj (s := .here) rfl,
      VarSymb.shift_level_zero (s := .keep) rfl, VarSymb.shift_proj (s := .here) rfl,
      VarSymb.shift_proj (s := .here) rfl, VarSymb.shift_level_succ (s := .keep) rfl,
      VarSymb.shift_level_zero (s := .keep) rfl, VarSymb.shift_level_zero (s := .keep) rfl]
  refine sig_boxtm ((congrArg (fun p => (⟨_, Term.shift hs.boxIn p.2⟩ :
    Σ e, Term σ Γ.boxIn.boxIn.boxIn A e)) e).trans ?_)
  have hr' := hs _ A (Ctx.ref_inner hr)
  refine (Term.shift_eta hs.boxIn _ A hr').trans ((Term.eta_congr hA A _
    (Ctx.shifts_boxIn_boxIn hF Γ.boxIn _ A hr')).trans ?_)
  exact (Term.shift_eta (Ctx.shifts_boxIn_boxIn hF Γ.boxIn) _ A hr').symm.trans
    (congrArg (fun p => (⟨_, Term.shift (Ctx.shifts_boxIn_boxIn hF Γ.boxIn) p.2⟩ :
      Σ e, Term σ Γ.boxIn.boxIn.boxIn A e)) e.symm)

variable [Γ.NoSlots]

/-- Under T some arrow leaves every world. -/
def Proof.dia_top (hT : ModalSys.T = true) {Δ : List (WFF σ Γ 0)} :
    Proof σ Γ Δ ((OutLeg.nec : OutLeg Γ).dia .top) :=
  Proof.imp_intro (Proof.imp_elim (Proof.T_box hT (Proof.lookup List.mem_cons_self))
    Proof.top_intro)

/-- ⭐A carrier kept twice comes back as itself. -/
def Proof.back_dd (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (c : Term σ Γ.boxIn A c₀) :
    Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift
      (Ctx.shifts_boxIn_boxIn hF Γ) (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) c)))))
      (Term.boxtm c)) :=
  Proof.conv (OutLeg.back_congr hS .nec (congrArg (Sigma.mk _) (Term.mono_refl _ _))
      (Term.collapse_boxtm_shift hT hF c))
    (Proof.back_keep hS hT hF .nec (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) c))
      (Proof.dia_top hT))

/-- A term of a `□` view, shifted twice, comes back as itself. -/
def Proof.back_shift (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ.boxIn 0)} (t : Term σ Γ.boxIn A a₀) :
    Proof σ Γ.boxIn Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift
      (Ctx.shifts_boxIn_boxIn hF Γ.boxIn) (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) t)))) t) :=
  Proof.conv (OutLeg.back_congr hS .nec (congrArg (Sigma.mk _) (Term.mono_refl _ _))
      (Term.collapse_shift_boxIn hT hF t))
    (Proof.back_keep hS hT hF .nec (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) t)
      (Proof.dia_top hT))

/-- ⭐**Interchange**: what a kept carrier comes back as is interchangeable with it. -/
def Proof.back_dd_read (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (c : Term σ Γ.boxIn A c₀)
    {b : Ann (.VTypeBox A)} (t : Term σ Γ (.VTypeBox A) b)
    (φ : WFF σ (Γ.insert (.bnd 0) (.VTypeBox A)) 1)
    (h : Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift
      (Ctx.shifts_boxIn_boxIn hF Γ) (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) c)))))
      t))
    (p : Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ)) :
    Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots (Term.boxtm c) φ) :=
  Proof.conv (WFF.instantiate_congr_sig _ ((congrArg (fun p =>
      (⟨_, Term.collapse (Ctx.collapses_boxIn_self hT Γ) p.2⟩ : Σ e, Term σ Γ (.VTypeBox A) e))
      (Term.collapse_shift_boxIn hT hF
        (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) c)))).trans
      (Term.collapse_boxtm_shift hT hF c)) φ)
    (Proof.back_here hS hT _ t φ h p)

/-- Necessitation. -/
def Proof.nec {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ.boxIn 0} (p : Proof σ Γ.boxIn [] φ) :
    Proof σ Γ Δ (WFF.box φ) :=
  Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.K_box (Δ := []) p)

/-- ⭐**The ties hold of `⟨d, d.dup⟩`**: each is `back_keep`. -/
def Proof.ties_dup (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (r : VarSymb)
    (hr : Γ.ref r = some (.VTypeBox A)) :
    Proof σ Γ Δ (WFF.holeAt Ctx.NoSlots.slots
      (Term.pair (Term.boxtm (Term.eta r.inner A (Ctx.ref_inner hr)))
        (Term.boxtm (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ)
          (Term.eta r.inner A (Ctx.ref_inner hr))))))
      (WFF.ties A hS hF)) := by
  refine Proof.conv (WFF.holeAt_ties hS hF _ _ _).symm (Proof.and_intro ?_ (Proof.and_intro ?_ ?_))
  · exact Proof.nec (Proof.conv (WFF.holeAt_backDup hS hF _ _ _).symm
      (Proof.back_shift hS hT hF _))
  · refine Proof.nec (Proof.nec (Proof.conv ((WFF.holeAt_backDD hS hF _ _ _).symm.trans
      (WFF.holeAt_congr _ (sig_pair (Term.shift_boxtm_shift_eta hT hF r hr).symm rfl) _))
      (Proof.back_dd hS hT hF _)))
  · exact Proof.conv (WFF.holeAt_backDup hS hF _ _ _).symm (Proof.back_dd hS hT hF _)

end Keep

/-! ## The legs -/

section Legs

variable {Γ : Ctx} [Γ.NoSlots]

/-- Necessitation along a leg. -/
def Proof.leg_nec {Δ : List (WFF σ Γ 0)} : (O : OutLeg Γ) → {φ : WFF σ O.view 0} →
    Proof σ O.view [] φ → Proof σ Γ Δ (O.box φ)
  | .nec, _, p => Proof.nec p
  | .pos _ hy, _, p => Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.boxxK hy p)

/-- A universally quantified implication along a leg, from its opened form. -/
def Proof.leg_all {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ) {T : VarType}
    (P Q : WFF σ (O.view.insert (.bnd 0) T) 1) (u : ℕ) (hu : O.view.RootFresh (.free u))
    (p : Proof σ (O.view.insert (.free u) T) [WFF.openFree u hu Ctx.NoSlots.slots P]
      (WFF.openFree u hu Ctx.NoSlots.slots Q)) :
    Proof σ Γ Δ (O.box (WFF.all T (WFF.imp P Q))) := by
  have h := Proof.all_intro (Δ := []) u T hu
    (φ := WFF.openFree u hu Ctx.NoSlots.slots (WFF.imp P Q)) (Proof.imp_intro p)
  rw [WFF.bindFree_openFree] at h
  exact Proof.leg_nec O h

/-- Possibility along a leg is monotone. -/
def Proof.leg_dia {Δ : List (WFF σ Γ 0)} : (O : OutLeg Γ) → {φ χ : WFF σ O.view 0} →
    Proof σ O.view [φ] χ → Proof σ Γ Δ (O.dia φ) → Proof σ Γ Δ (O.dia χ)
  | .nec, φ, χ, h, p => by
      refine Proof.imp_intro (Proof.imp_elim (Proof.ofSubset (fun _ hx =>
        List.mem_cons_of_mem _ hx) p) ?_)
      have q : Proof σ Γ.boxIn [χ.neg] φ.neg := Proof.imp_intro (Proof.imp_elim
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
        (Proof.ofSubset (fun _ hx => by
          rw [List.mem_singleton.mp hx]
          exact List.mem_cons_self) h))
      exact Proof.ofSubset (fun _ hx => by
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx
        subst hx
        exact List.mem_cons_self) (Proof.K_box q)
  | .pos y hy, φ, χ, h, p =>
      Proof.imp_elim (Proof.imp_intro (Proof.ofSubset (fun _ hx => by
          simp only [List.map_nil, List.append_nil, List.mem_singleton] at hx
          subst hx
          exact List.mem_cons_self)
        (Proof.K_dia (Δ₁ := []) (Δ₂ := []) y hy (ψ := φ) (φ := χ)
          (Proof.ofSubset (fun _ hx => by simpa using hx) h)))) p

end Legs

/-! ## The tied body -/

section Body

variable {V : Ctx} [V.NoSlots] {A : VarType} {a₀ c₀ : Ann A}

/-- The value of a lifted object, with the companion's. -/
abbrev liftTy (A : VarType) : VarType := .VTypeProd A (.VTypeBox A)

/-- The ties' hole, read in a body about the paired object `p`. -/
def tieTerm (V : Ctx) [V.NoSlots] (A : VarType) :
    Σ b, Term σ (V.insert (.bnd 0) (.VTypeBox (liftTy A))) (tieTy A) b :=
  ⟨_, Term.pair (Term.boxFst (Ctx.ref_insert_root V (.bnd 0) (.VTypeBox (liftTy A))))
    (Term.boxSnd (Ctx.ref_insert_root V (.bnd 0) (.VTypeBox (liftTy A))))⟩

/-- ⭐**The tied body**: `Φ` of the object, with the ties on it and its companion. -/
def WFF.tiedBody (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true)
    (Φ : WFF σ (V.insert (.bnd 0) (.VTypeBox A)) 1) :
    WFF σ (V.insert (.bnd 0) (.VTypeBox (liftTy A))) 1 :=
  WFF.and (WFF.bodyRepl (Term.boxFst (Ctx.ref_insert_root V (.bnd 0) (.VTypeBox (liftTy A)))) Φ)
    (WFF.holeAt ((Ctx.NoSlots.slots (Γ := V)).insert _) (tieTerm V A).2 (WFF.ties A hS hF))

/-- ⭐The tied body at a necessary pair. -/
theorem WFF.instantiate_tiedBody (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true)
    (Φ : WFF σ (V.insert (.bnd 0) (.VTypeBox A)) 1) (a : Term σ V.boxIn A a₀)
    (c : Term σ V.boxIn.boxIn A c₀) :
    WFF.instantiate Ctx.NoSlots.slots (Term.boxtm (Term.pair a (Term.boxtm c)))
        (WFF.tiedBody hS hF Φ) =
      WFF.and (WFF.instantiate Ctx.NoSlots.slots (Term.boxtm a) Φ)
        (WFF.holeAt Ctx.NoSlots.slots (Term.pair (Term.boxtm a) (Term.boxtm (Term.boxtm c)))
          (WFF.ties A hS hF)) := by
  have hat := Subst.at_single_root (σ := σ) (Δ := V) (.bnd 0)
    (.tm (Term.boxtm (Term.pair a (Term.boxtm c))))
  have h₁ := Subst.box_at_inner_boxtm _ hat
  have ha : (Subst.single (σ := σ) (Δ := V) (.bnd 0)
      (.tm (Term.boxtm (Term.pair a (Term.boxtm c))))).box.at
        (.step (VarSymb.root (.bnd 0)).inner .fst) = .tm a := by
    rw [Subst.at_proj _ _ rfl, h₁]
    rfl
  have hc : (Subst.single (σ := σ) (Δ := V) (.bnd 0)
      (.tm (Term.boxtm (Term.pair a (Term.boxtm c))))).box.at
        (.step (VarSymb.root (.bnd 0)).inner .snd) = .tm (Term.boxtm c) := by
    rw [Subst.at_proj _ _ rfl, h₁]
    rfl
  refine congrArg₂ WFF.and ((WFF.instantiate_bodyRepl _ _ _).trans
    (WFF.instantiate_congr_sig _ (sig_boxtm (Term.subst_eta_tm _ _ _ _ _ _ a ha)) Φ)) ?_
  change WFF.subst _ _ _ _ _ _ (WFF.holeAt _ _ _) = _
  rw [WFF.subst_holeAt]
  exact WFF.holeAt_congr _ (sig_pair (sig_boxtm (Term.subst_eta_tm _ _ _ _ _ _ a ha))
    (sig_boxtm (Term.subst_eta_tm _ _ _ _ _ _ _ hc))) _

/-- The tied body under a weakening of the view. -/
theorem WFF.mono_tiedBody {V' : Ctx} [V'.NoSlots] (h : V.Le V') (hS : ModalSys.BStrong = true)
    (hF : ModalSys.Four = true) (Φ : WFF σ (V.insert (.bnd 0) (.VTypeBox A)) 1) :
    WFF.mono (h.insert (.bnd 0) _) (WFF.tiedBody hS hF Φ) =
      WFF.tiedBody hS hF (WFF.mono (h.insert (.bnd 0) _) Φ) := by
  have e : ∀ {T : VarType} {v : VarSymb} (hv : (V.insert (.bnd 0) (.VTypeBox (liftTy A))).boxIn.ref
      v = some T) (hv' : (V'.insert (.bnd 0) (.VTypeBox (liftTy A))).boxIn.ref v = some T),
      Term.mono (h.insert (.bnd 0) _).boxIn (Term.eta (σ := σ) v T hv) = Term.eta v T hv' :=
    fun _ _ => Term.mono_eta _ _ _ _
  refine congrArg₂ WFF.and ?_ ?_
  · rw [WFF.mono_bodyRepl h]
    exact congrArg (fun X => WFF.bodyRepl X (WFF.mono (h.insert (.bnd 0) _) Φ))
      (congrArg Term.boxtm (e _ _))
  · rw [WFF.mono_holeAt _ _ ((Ctx.NoSlots.slots (Γ := V')).insert _)]
    exact WFF.holeAt_congr _ (sig_pair (sig_boxtm (congrArg (Sigma.mk _) (e _ _)))
      (sig_boxtm (congrArg (Sigma.mk _) (e _ _)))) _

end Body

/-! ## The unit's hole -/

section Unit

variable (A : VarType)

/-- The hole of the unit: the value with the companion's, and the object going home. -/
abbrev unitTy : VarType := .VTypeProd (liftTy A) (.VTypeBox (.VTypeBox A))

/-- The hole's own context. -/
abbrev unitCtx : Ctx := Ctx.empty.insert (.bnd 0) (unitTy A)

theorem unit_snd : (unitCtx A).ref (.step (.root (.bnd 0)) .snd) =
    some (.VTypeBox (.VTypeBox A)) :=
  Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (unitTy A))

theorem unit_z : (unitCtx A).ref (.step (.step (.root (.bnd 0)) .fst) .snd) =
    some (.VTypeBox A) :=
  Ctx.ref_snd_of (Ctx.ref_fst_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (unitTy A)))

/-- `□ Back (dd e.inner) z.keep` on a hole `⟨⟨_, z⟩, e⟩`: what the unit carries to the far end,
    where `e` is `z.dup`. -/
def WFF.tieUnit (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) :
    WFF σ (unitCtx A) 1 :=
  WFF.box (WFF.holeAt (Ctx.slotsFrom_empty.insert _).boxIn
    (Term.pair
      (Term.eta (VarSymb.step (.root (.bnd 0)) .snd).inner (.VTypeBox A)
        (Ctx.ref_inner (unit_snd A)))
      (Term.eta (.step (.step (.step (.root (.bnd 0)) .fst) .snd) .keep) (.VTypeBox A)
        (Ctx.ref_keep_of' hF (unit_z A) rfl)))
    (WFF.backDD hS hF A))

variable {A}

/-- ⭐`WFF.tieUnit`, read. -/
theorem WFF.holeAt_tieUnit (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) {Ω : Ctx}
    {d : ℕ} (hs : Ω.SlotsFrom d) {a₀ c₀ : Ann A} {e₀ : Ann (.VTypeBox A)} (x : Term σ Ω A a₀)
    (c : Term σ Ω.boxIn A c₀) (e : Term σ Ω.boxIn (.VTypeBox A) e₀) :
    WFF.holeAt hs (Term.pair (Term.pair x (Term.boxtm c)) (Term.boxtm e)) (WFF.tieUnit A hS hF) =
      WFF.box (WFF.holeAt hs.boxIn
        (Term.pair e (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Ω) c)))
        (WFF.backDD hS hF A)) := by
  have hat := Subst.at_single_root (σ := σ) (Δ := Ω) (.bnd 0)
    (.tm (Term.pair (Term.pair x (Term.boxtm c)) (Term.boxtm e)))
  have he : (Subst.single (σ := σ) (Δ := Ω) (.bnd 0)
      (.tm (Term.pair (Term.pair x (Term.boxtm c)) (Term.boxtm e)))).at
        (.step (.root (.bnd 0)) .snd) = .tm (Term.boxtm e) := by
    rw [Subst.at_proj _ _ rfl, hat]
    rfl
  have hz : (Subst.single (σ := σ) (Δ := Ω) (.bnd 0)
      (.tm (Term.pair (Term.pair x (Term.boxtm c)) (Term.boxtm e)))).at
        (.step (.step (.root (.bnd 0)) .fst) .snd) = .tm (Term.boxtm c) := by
    rw [Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, hat]
    rfl
  refine congrArg WFF.box ((WFF.subst_holeAt _ _ _ _ _ _ _).trans (WFF.holeAt_congr _ ?_ _))
  refine sig_pair (Term.subst_eta_tm _ _ _ _ _ _ e (Subst.box_at_inner_boxtm _ he))
    (Term.subst_eta_tm _ _ _ _ _ _ _ ?_)
  rw [Subst.box_at_keep, hz, SubE.keepE_tm _ hF]

theorem sig_unbox {Γ : Ctx} {T : VarType} {a a' : Ann T} {s : Term σ Γ.boxIn T a}
    {s' : Term σ Γ.boxIn T a'}
    (h : (⟨_, Term.boxtm s⟩ : Σ c, Term σ Γ (.VTypeBox T) c) = ⟨_, Term.boxtm s'⟩) :
    (⟨_, s⟩ : Σ c, Term σ Γ.boxIn T c) = ⟨_, s'⟩ := by
  cases h
  rfl

/-- Filling a slot leaves a term without it alone. -/
theorem Term.subst_single_mono {Ω₀ Ω : Ctx} [Ω.NoSlots] (h : Ω₀.Le Ω) {B : VarType}
    (l : Ω₀.Le (Ω.insert (.bnd 0) B)) (e : SubE σ Ω) (hθ : Subst.Ok (Ω.insert (.bnd 0) B)
      (Subst.single (.bnd 0) e)) {ι : VarSymb → VarSymb}
    (hc : Subst.Coh ι (Ω.insert (.bnd 0) B) (Subst.single (.bnd 0) e))
    (hfr : Ω₀.RootFresh (.bnd 0)) {T : VarType} {b : Ann T} (t : Term σ Ω₀ T b) :
    (⟨_, Term.subst ι (Subst.single (.bnd 0) e) hθ hc (Term.mono l t)⟩ : Σ c, Term σ Ω T c) =
      ⟨_, Term.mono h t⟩ := by
  rw [Term.subst_mono]
  exact Term.subst_ren h _ _ _ (fun v _ hv => Subst.single_at_ne (Ctx.ref_rt_ne hfr hv)) t

/-- The same one view in. -/
theorem Term.subst_single_box_mono {Ω₀ Ω : Ctx} [Ω.NoSlots] (h : Ω₀.Le Ω) {B : VarType}
    (l : Ω₀.Le (Ω.insert (.bnd 0) B)) (e : SubE σ Ω) (hθ : Subst.Ok (Ω.insert (.bnd 0) B)
      (Subst.single (.bnd 0) e)) {ι : VarSymb → VarSymb}
    (hc : Subst.Coh ι (Ω.insert (.bnd 0) B) (Subst.single (.bnd 0) e))
    (hfr : Ω₀.RootFresh (.bnd 0)) {T : VarType} {b : Ann T} (t : Term σ Ω₀.boxIn T b) :
    (⟨_, Term.subst ι (Subst.single (.bnd 0) e).box (Subst.ok_box hθ) (Subst.coh_box hθ hc)
        (Term.mono l.boxIn t)⟩ : Σ c, Term σ Ω.boxIn T c) = ⟨_, Term.mono h.boxIn t⟩ :=
  sig_unbox (Term.subst_single_mono (σ := σ) h l e hθ hc hfr (Term.boxtm t))

/-- ⭐Filling the slot of a pair hole. -/
theorem WFF.instantiate_holeAt_pair {Ω : Ctx} [Ω.NoSlots] {X Y : VarType} {x₀ : Ann X}
    (E : Term σ Ω X x₀) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd X Y)) 1) {y₀ : Ann Y}
    (t : Term σ Ω Y y₀) :
    WFF.instantiate Ctx.NoSlots.slots t (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Ω)).insert Y)
      (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Ω)).root Y) E)
        (Term.eta (.root (.bnd 0)) Y (Ctx.ref_insert_root Ω (.bnd 0) Y))) ψ) =
      WFF.holeAt Ctx.NoSlots.slots (Term.pair E t) ψ := by
  unfold WFF.instantiate WFF.substRoot
  rw [WFF.subst_holeAt]
  refine WFF.holeAt_congr _ (sig_pair ?_ (Term.subst_eta_tm _ _ _ _ _ _ t
    (Subst.at_single_root _ _))) ψ
  exact (Term.subst_single_mono (Ctx.Le.refl _) _ _ _ _
    ((Ctx.NoSlots.slots (Γ := Ω)).rootFresh (le_refl 0)) E).trans
    (congrArg (Sigma.mk _) (Term.mono_refl _ E))

end Unit

/-! ## The nested step -/

section Swap

variable {W : Ctx} [W.NoSlots] {A : VarType}

/-- `□ Back (dd e.inner) x`, the body `ret_counitC` asks of the nested returning possibility. -/
def WFF.counitBody (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true)
    {b : Ann (.VTypeBox A)} (x : Term σ W.boxIn.boxIn (.VTypeBox A) b) :
    WFF σ (W.boxIn.insert (.bnd 0) (.VTypeBox (.VTypeBox A))) 1 :=
  WFF.box (WFF.holeAt ((Ctx.NoSlots.slots (Γ := W.boxIn)).insert (.VTypeBox (.VTypeBox A))).boxIn
    (Term.pair
      (Term.eta (VarSymb.root (.bnd 0)).inner (.VTypeBox A)
        (Ctx.ref_inner (Ctx.ref_insert_root W.boxIn (.bnd 0) (.VTypeBox (.VTypeBox A)))))
      (Term.mono ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := W.boxIn)).root
        (.VTypeBox (.VTypeBox A))).boxIn) x))
    (WFF.backDD hS hF A))

/-- `WFF.counitBody`, opened at a fresh root. -/
theorem WFF.openFree_counitBody (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true)
    (e : ℕ) (he : W.boxIn.RootFresh (.free e)) {b : Ann (.VTypeBox A)}
    (x : Term σ W.boxIn.boxIn (.VTypeBox A) b) :
    WFF.openFree e he Ctx.NoSlots.slots (WFF.counitBody hS hF x) =
      WFF.box (WFF.holeAt Ctx.NoSlots.slots
        (Term.pair
          (Term.eta (VarSymb.root (.free e)).inner (.VTypeBox A)
            (Ctx.ref_inner (Ctx.ref_insert_root W.boxIn (.free e) (.VTypeBox (.VTypeBox A)))))
          (Term.mono (Ctx.le_insert he.root (.VTypeBox (.VTypeBox A))).boxIn x))
        (WFF.backDD hS hF A)) := by
  have hl := Ctx.le_insert he.root (.VTypeBox (.VTypeBox A))
  rw [← WFF.instantiate_eta_openFree e he Ctx.NoSlots.slots Ctx.NoSlots.slots]
  unfold WFF.counitBody WFF.instantiate WFF.substRoot
  change WFF.box (WFF.subst _ _ _ _ _ _ (WFF.mono _ (WFF.holeAt _ _ _))) = _
  rw [WFF.mono_holeAt _ _
    ((Ctx.NoSlots.slots (Γ := W.boxIn.insert (.free e) (.VTypeBox (.VTypeBox A)))).insert _).boxIn,
    WFF.subst_holeAt]
  refine congrArg WFF.box (WFF.holeAt_congr _ (sig_pair ?_ ?_) _)
  · rw [Term.mono_eta]
    exact Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ (Subst.at_single_root _ _))
  · rw [Term.mono_mono]
    exact Term.subst_single_box_mono hl
      (hl.trans (Ctx.le_insert (Ctx.NoSlots.slots
        (Γ := W.boxIn.insert (.free e) (.VTypeBox (.VTypeBox A)))).root _))
      (.tm (Term.eta (.root (.free e)) (.VTypeBox (.VTypeBox A)) (Ctx.ref_insert_root _ _ _)))
      (Subst.ok_single (Ctx.Le.refl _) rfl)
      (Subst.coh_single ((Ctx.NoSlots.slots
        (Γ := W.boxIn.insert (.free e) (.VTypeBox (.VTypeBox A)))).rootFresh (le_refl 0))
        (Ctx.Le.refl _) rfl)
      ((Ctx.NoSlots.slots (Γ := W.boxIn)).rootFresh (le_refl 0)) x

/-- ⭐**Swapping the value** under the nested returning possibility: what comes back as `k` under
    the arrow, the tie `Back (dd y) k` makes come back as `y`. -/
def Proof.ret_swap (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ W 0)} (e : ℕ)
    (he : W.boxIn.RootFresh (.free e)) {m₀ : Ann (.VTypeBox A)}
    (m : Term σ W (.VTypeBox A) m₀) {y₀ : Ann A} (yb : Term σ W.boxIn.boxIn.boxIn A y₀)
    {k₀ : Ann (.VTypeBox A)} (k : Term σ W.boxIn.boxIn (.VTypeBox A) k₀)
    (hN : Proof σ W Δ (WFF.ret hS m (WFF.counitBody hS hF k)))
    (h₂ : Proof σ W Δ (WFF.box (WFF.box (WFF.holeAt Ctx.NoSlots.slots
      (Term.pair (Term.boxtm yb) k) (WFF.backDD hS hF A))))) :
    Proof σ W Δ (WFF.ret hS m (WFF.counitBody hS hF (Term.boxtm yb))) := by
  have hl := Ctx.le_insert he.root (.VTypeBox (.VTypeBox A))
  let E := Term.eta (σ := σ) (VarSymb.root (.free e)).inner (.VTypeBox A)
    (Ctx.ref_inner (Ctx.ref_insert_root W.boxIn (.free e) (.VTypeBox (.VTypeBox A))))
  let T := WFF.holeAt Ctx.NoSlots.slots (Term.pair (Term.boxtm yb) k) (WFF.backDD hS hF A)
  let H := WFF.holeAt Ctx.NoSlots.slots (Term.pair E (Term.mono hl.boxIn k)) (WFF.backDD hS hF A)
  have e₁ : WFF.mono hl.boxIn T = WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift
      (Ctx.shifts_boxIn_boxIn hF _) (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _)
        (Term.mono hl.boxIn.boxIn yb)))))) (Term.mono hl.boxIn k) :=
    (WFF.mono_holeAt hl.boxIn Ctx.NoSlots.slots Ctx.NoSlots.slots _ _).trans
      (WFF.holeAt_backDD hS hF _ _ _)
  have q₂ : Proof σ (W.boxIn.insert (.free e) (.VTypeBox (.VTypeBox A))).boxIn
      [H, WFF.mono hl.boxIn T]
      (WFF.holeAt Ctx.NoSlots.slots (Term.pair E (Term.mono hl.boxIn (Term.boxtm yb)))
        (WFF.backDD hS hF A)) :=
    Proof.conv (WFF.instantiate_holeAt_pair E _ _) (Proof.back_dd_read hS hT hF _
      (Term.mono hl.boxIn k) _
      (Proof.conv e₁ (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))
      (Proof.conv (WFF.instantiate_holeAt_pair E _ _).symm (Proof.lookup List.mem_cons_self)))
  have h₀ := Proof.all_intro (Δ := [WFF.box T]) e (.VTypeBox (.VTypeBox A)) he
    (φ := WFF.openFree e he Ctx.NoSlots.slots
      (WFF.imp (WFF.counitBody hS hF k) (WFF.counitBody hS hF (Term.boxtm yb))))
    (Proof.conv (congrArg₂ WFF.imp (WFF.openFree_counitBody hS hF e he k)
      (WFF.openFree_counitBody hS hF e he (Term.boxtm yb))).symm
      (Proof.imp_intro (Proof.K_box (Δ := [H, WFF.mono hl.boxIn T]) q₂)))
  rw [WFF.bindFree_openFree] at h₀
  refine Proof.ret_mono hS .nec m _ _ hN (Proof.imp_elim (Proof.imp_intro (Proof.ofSubset ?_
    (Proof.K_box (Δ := [WFF.box T]) h₀))) h₂)
  intro _ hx
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx
  subst hx
  exact List.mem_cons_self

/-- ⭐**The far end of the unit.**  Inside the body: `Φ` of the object, the ties, and the nested
    returning possibility, whose value `□mb` is `n.keep`, give `Φ(□mb)`. -/
def Proof.lift_inner (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ W 0)} (e : ℕ)
    (he : W.boxIn.RootFresh (.free e)) {a₀ c₀ m₀ : Ann A} (a : Term σ W.boxIn A a₀)
    (c : Term σ W.boxIn.boxIn A c₀) (mb : Term σ W.boxIn A m₀)
    (φ : WFF σ (W.insert (.bnd 0) (.VTypeBox A)) 1)
    (hΦ : Proof σ W Δ (WFF.instantiate Ctx.NoSlots.slots (Term.boxtm a) φ))
    (hK : Proof σ W Δ (WFF.holeAt Ctx.NoSlots.slots
      (Term.pair (Term.boxtm a) (Term.boxtm (Term.boxtm c))) (WFF.ties A hS hF)))
    (hN : Proof σ W Δ (WFF.ret hS (Term.boxtm mb) (WFF.counitBody hS hF
      (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF W.boxIn) c))))) :
    Proof σ W Δ (WFF.instantiate Ctx.NoSlots.slots (Term.boxtm mb) φ) := by
  have hK' := Proof.conv (WFF.holeAt_ties hS hF _ a c) hK
  have h₂ := Proof.and_elim_l (Proof.and_elim_r hK')
  have h₃ := Proof.conv (WFF.holeAt_backDup hS hF _ _ _) (Proof.and_elim_r (Proof.and_elim_r hK'))
  have hΦ' : Proof σ W Δ (WFF.instantiate Ctx.NoSlots.slots
      (Term.collapse (Ctx.collapses_boxIn_self hT W) (Term.boxtm c)) φ) :=
    Proof.conv (WFF.instantiate_congr_sig _ (congrArg (fun p =>
      (⟨_, Term.collapse (Ctx.collapses_boxIn_self hT W) p.2⟩ :
        Σ e, Term σ W (.VTypeBox A) e))
      (Term.collapse_shift_boxIn hT hF (Term.boxtm c))) φ)
      (Proof.back_here hS hT _ (Term.boxtm a) φ h₃ hΦ)
  have hS₂ := Proof.ret_swap hS hT hF e he (Term.boxtm mb)
    (Term.shift (Ctx.shifts_boxIn_boxIn hF W).boxIn c) _ hN h₂
  have hB : Proof σ W Δ ((OutLeg.nec : OutLeg W).back hS
      (Term.shift (Ctx.shifts_boxIn_boxIn hF W) (Term.boxtm c))
      (Term.collapse (Ctx.collapses_boxIn_self hT W) (Term.boxtm c))) :=
    Proof.conv (OutLeg.back_congr hS .nec (congrArg (Sigma.mk _) (Term.mono_refl _ _)) rfl)
      (Proof.back_keep hS hT hF .nec (Term.boxtm c) (Proof.dia_top hT))
  have h₄ := Proof.ret_counitC hS .nec (Term.boxtm mb)
    (Term.shift (Ctx.shifts_boxIn_boxIn hF W) (Term.boxtm c)) _ (WFF.backDD hS hF A) hS₂ hB
  exact Proof.back_dd_read hS hT hF mb _ φ (Proof.conv ((WFF.holeRead_eq_holeAt _ _).trans
    (WFF.holeAt_backDD hS hF _ _ _)) h₄) hΦ'

end Swap

/-! ## The two conclusions -/

section Lift

variable {Γ : Ctx} [Γ.NoSlots] {A : VarType}

omit [Γ.NoSlots] in
/-- A body over the `□` view, weakened through the leg's view. -/
theorem OutLeg.mono_lift {W : Ctx} : (O : OutLeg Γ) → (h : O.view.Le W) → {T : VarType} →
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) →
    WFF.mono (h.insert (.bnd 0) T) (O.lift φ) =
      WFF.mono ((O.le_view.trans h).insert (.bnd 0) T) φ
  | .nec, _, _, _ => rfl
  | .pos _ _, _, _, φ => WFF.mono_mono _ _ φ

/-- `ret_counit`'s body along the leg is the same formula in the leg's view. -/
theorem OutLeg.lift_counit {X : VarType} (ψ : WFF σ (Ctx.empty.insert (.bnd 0) X) 1) :
    (O : OutLeg Γ) → O.lift (WFF.box (WFF.holeAt
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert (.VTypeBox X)).boxIn
      (Term.eta (VarSymb.root (.bnd 0)).inner X
        (Ctx.ref_inner (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox X)))) ψ)) =
      WFF.box (WFF.holeAt ((Ctx.NoSlots.slots (Γ := O.view)).insert (.VTypeBox X)).boxIn
        (Term.eta (VarSymb.root (.bnd 0)).inner X
          (Ctx.ref_inner (Ctx.ref_insert_root O.view (.bnd 0) (.VTypeBox X)))) ψ)
  | .nec => rfl
  | .pos y _ => by
      refine congrArg WFF.box ((WFF.mono_holeAt _ _
        ((Ctx.NoSlots.slots (Γ := Γ.diaIn y)).insert (.VTypeBox X)).boxIn _ ψ).trans
        (WFF.holeAt_congr _ (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)) ψ))

/-- The tied body, its ties read. -/
theorem WFF.tiedBody_split (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) {V : Ctx}
    [V.NoSlots] (Φ : WFF σ (V.insert (.bnd 0) (.VTypeBox A)) 1) :
    WFF.tiedBody hS hF Φ = WFF.and
      (WFF.bodyRepl (Term.boxFst (Ctx.ref_insert_root V (.bnd 0) (.VTypeBox (liftTy A)))) Φ)
      (WFF.and (WFF.box (WFF.holeAt ((Ctx.NoSlots.slots (Γ := V)).insert _).boxIn
          (Term.eta (VarSymb.root (.bnd 0)).inner (liftTy A)
            (Ctx.ref_inner (Ctx.ref_insert_root V (.bnd 0) (.VTypeBox (liftTy A)))))
          (WFF.backDup hS hF A)))
        (WFF.and
          (WFF.box (WFF.box (WFF.holeAt ((Ctx.NoSlots.slots (Γ := V)).insert _).boxIn.boxIn
            (Term.pair (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (Term.boxtm (Term.eta
                (VarSymb.step (VarSymb.root (.bnd 0)).inner .snd).inner A
                (Ctx.ref_inner (Ctx.ref_snd_of (Ctx.ref_inner
                  (Ctx.ref_insert_root V (.bnd 0) (.VTypeBox (liftTy A)))))))))
              (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (Term.eta
                (VarSymb.step (VarSymb.root (.bnd 0)).inner .snd).inner A
                (Ctx.ref_inner (Ctx.ref_snd_of (Ctx.ref_inner
                  (Ctx.ref_insert_root V (.bnd 0) (.VTypeBox (liftTy A))))))))))
            (WFF.backDD hS hF A))))
          (WFF.holeAt ((Ctx.NoSlots.slots (Γ := V)).insert _) (tieTerm V A).2
            (WFF.backDup hS hF (.VTypeBox A))))) :=
  congrArg (WFF.and _) (WFF.holeAt_ties hS hF _ _ _)

/-- ⭐**The first conclusion**: `n` comes back as `t`. -/
def Proof.lift_back (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true)
    {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ) {a₁ a₂ : Ann A} (t : Term σ Γ A a₁)
    (nb : Term σ Γ.boxIn A a₂) (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1) (u : ℕ)
    (hu : O.view.RootFresh (.free u))
    (H : Proof σ Γ Δ (O.ret hS (Term.pair t (Term.boxtm nb)) (WFF.tiedBody hS hF Φ))) :
    Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm
      (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) nb))) t) := by
  refine Proof.conv ((WFF.holeRead_eq_holeAt _ _).trans (WFF.holeAt_backDup hS hF _ _ _))
    (Proof.ret_counit hS O (Term.pair t (Term.boxtm nb)) (WFF.backDup hS hF A) ?_)
  rw [OutLeg.lift_counit]
  refine Proof.ret_mono hS O _ _ _ H ?_
  rw [WFF.tiedBody_split]
  exact Proof.leg_all O _ _ u hu (Proof.and_elim_l (Proof.and_elim_r
    (Proof.lookup List.mem_cons_self)))

/-- `WFF.unitBody`, weakened and filled at a necessary object. -/
theorem WFF.instantiate_mono_unitBody {W : Ctx} [W.NoSlots] (hS : ModalSys.BStrong = true)
    (h : Γ.boxIn.Le W) {C : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) {e₀ : Ann C}
    (x : Term σ W.boxIn C e₀) :
    WFF.instantiate Ctx.NoSlots.slots (Term.boxtm x)
        (WFF.mono (h.insert (.bnd 0) (.VTypeBox C)) (WFF.unitBody hS sb θ)) =
      WFF.ret hS (Term.mono h sb) (WFF.holeAt ((Ctx.NoSlots.slots (Γ := W.boxIn)).insert _)
        (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := W.boxIn)).root _) x)
          (Term.eta (.root (.bnd 0)) (.VTypeBox A)
            (Ctx.ref_insert_root W.boxIn (.bnd 0) (.VTypeBox A)))) θ) := by
  unfold WFF.unitBody WFF.instantiate WFF.substRoot
  refine WFF.ret_congr hS ?_ ?_
  · rw [Term.mono_mono]
    exact Term.subst_single_mono h _ _ _ _ ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh
      (le_refl 0)) sb
  · change WFF.subst _ _ _ _ _ _ (WFF.mono _ (WFF.holeAt _ _ _)) = _
    rw [WFF.mono_holeAt _ _ (((Ctx.NoSlots.slots (Γ := W)).insert _).boxIn.insert _),
      WFF.subst_holeAt]
    refine WFF.holeAt_congr _ (sig_pair ?_ ?_) θ
    · rw [Term.mono_eta]
      refine Term.subst_eta_tm _ _ _ _ _ _ _ ?_
      rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
        Subst.box_at_inner_boxtm _ (Subst.at_single_root _ _)]
      rfl
    · rw [Term.mono_eta]
      exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ _ _ _ _)

/-- ⭐**The second conclusion**: `n`, kept, has `Φ` possibly.  The unit carries `n.dup` to the far
    end, where `ret_counitC` identifies `n.keep` and the object (`Proof.lift_inner`). -/
def Proof.lift_dia (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ) {a₁ a₂ : Ann A}
    (t : Term σ Γ A a₁) (nb : Term σ Γ.boxIn A a₂)
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1) (u e : ℕ)
    (hu : O.view.RootFresh (.free u))
    (he : (O.view.insert (.free u) (.VTypeBox (liftTy A))).boxIn.RootFresh (.free e))
    (H : Proof σ Γ Δ (O.ret hS (Term.pair t (Term.boxtm nb)) (WFF.tiedBody hS hF Φ))) :
    Proof σ Γ Δ (O.dia (WFF.instantiate Ctx.NoSlots.slots
      (Term.mono O.le_view (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) nb))) Φ)) := by
  have q : Proof σ Γ Δ (WFF.holeRead (Term.pair (Term.pair t (Term.boxtm nb))
      (Term.boxtm (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) nb))))
      (WFF.tieUnit A hS hF)) :=
    Proof.conv ((WFF.holeAt_tieUnit hS hF _ t nb _).symm.trans (WFF.holeRead_eq_holeAt _ _).symm)
      (Proof.nec (Proof.conv (WFF.holeAt_backDD hS hF _ _ _).symm (Proof.back_dd hS hT hF _)))
  refine Proof.leg_dia O ?_ (Proof.ret_diaS hS O _ _ (Proof.ret_unit hS O _ _ _ _ H q))
  have hV := Ctx.le_insert hu.root (.VTypeBox (liftTy A))
  let Ψ := WFF.and (WFF.tiedBody hS hF Φ) (O.lift (WFF.unitBody hS
    (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) nb)) (WFF.tieUnit A hS hF)))
  refine Proof.ex_elim u _ hu (φ := WFF.openFree u hu Ctx.NoSlots.slots Ψ)
    (Proof.conv (by rw [WFF.bindFree_openFree]; rfl) (Proof.lookup List.mem_cons_self)) ?_
  let hu₀ := Ctx.ref_insert_root O.view (.free u) (.VTypeBox (liftTy A))
  let a := Term.eta (σ := σ) (.step (VarSymb.root (.free u)).inner .fst) A
    (Ctx.ref_fst_of (Ctx.ref_inner hu₀))
  let c := Term.eta (σ := σ) (VarSymb.step (VarSymb.root (.free u)).inner .snd).inner A
    (Ctx.ref_inner (Ctx.ref_snd_of (Ctx.ref_inner hu₀)))
  have e₁ : WFF.openFree u hu Ctx.NoSlots.slots (WFF.tiedBody hS hF Φ) =
      WFF.and (WFF.instantiate Ctx.NoSlots.slots (Term.boxtm a)
          (WFF.mono (hV.insert (.bnd 0) _) Φ))
        (WFF.holeAt Ctx.NoSlots.slots (Term.pair (Term.boxtm a) (Term.boxtm (Term.boxtm c)))
          (WFF.ties A hS hF)) := by
    rw [← WFF.instantiate_eta_openFree u hu Ctx.NoSlots.slots Ctx.NoSlots.slots,
      WFF.mono_tiedBody hV hS hF Φ]
    exact WFF.instantiate_tiedBody hS hF _ a c
  have e₂ : WFF.openFree u hu Ctx.NoSlots.slots (O.lift (WFF.unitBody hS
      (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) nb)) (WFF.tieUnit A hS hF))) =
      WFF.ret hS (Term.boxtm (Term.mono (O.le_view.trans hV).boxIn
          (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) nb)))
        (WFF.counitBody hS hF (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) c))) := by
    rw [← WFF.instantiate_eta_openFree u hu Ctx.NoSlots.slots Ctx.NoSlots.slots,
      OutLeg.mono_lift O hV]
    refine (WFF.instantiate_mono_unitBody hS (O.le_view.trans hV) _ _ _).trans
      (WFF.ret_congr' hS rfl ?_)
    refine (WFF.holeAt_tieUnit hS hF _ _ _ _).trans (congrArg WFF.box ?_)
    exact congrArg (fun z => WFF.holeAt _ (Term.pair _ (Term.boxtm z)) (WFF.backDD hS hF A))
      (Term.shift_mono _ _ _ _ c)
  have hH : Proof σ _ (WFF.openFree u hu Ctx.NoSlots.slots Ψ ::
      [WFF.weaken hu.root _ (WFF.ex (.VTypeBox (liftTy A)) Ψ)]) _ :=
    Proof.lookup List.mem_cons_self
  have hL := Proof.conv e₁ (Proof.and_elim_l hH)
  refine Proof.conv ?_ (Proof.lift_inner hS hT hF e he a c
    (Term.mono (O.le_view.trans hV).boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) nb)) _
    (Proof.and_elim_l hL) (Proof.and_elim_r hL) (Proof.conv e₂ (Proof.and_elim_r hH)))
  refine Eq.symm ((WFF.mono_instantiate hV _ Ctx.NoSlots.slots _ Φ).trans ?_)
  rw [Term.mono_mono]
  rfl

end Lift

/-! ## The companion -/

section Pair

variable {W : Ctx} [W.NoSlots] {X Y : VarType}

/-- `pairUp` under a weakening of the view. -/
theorem WFF.mono_pairUp {V V' : Ctx} [V.NoSlots] [V'.NoSlots] (h : V.Le V')
    (Φ : WFF σ (V.insert (.bnd 0) (.VTypeBox (.VTypeProd X Y))) 1) :
    WFF.mono ((h.insert (.bnd 0) _).insert (.bnd 1) _) (WFF.pairUp Φ) =
      WFF.pairUp (WFF.mono (h.insert (.bnd 0) _) Φ) := by
  unfold WFF.pairUp
  rw [WFF.mono_subst, WFF.subst_mono]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) Φ
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = .VTypeBox (.VTypeProd X Y) := by simpa [Ctx.insert] using hv.symm
    change SubE.Sim _ (SubE.mono _ (Subst.set _ _ _ (.root (.bnd 0))))
      (Subst.set _ _ _ (.root (.bnd 0)))
    rw [Subst.set_root, Subst.set_root]
    change SubE.Sim _ (.tm (Term.mono _ _)) _
    unfold pairItem
    exact SubE.sim_tm_sigma (sig_boxtm (sig_pair (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _))
      (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _))))
  · change SubE.Sim T (SubE.mono _ (Subst.set _ _ _ v)) (Subst.set _ _ _ v)
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    exact .refl _

/-- ⭐**`∃`-introduction at a companion**: a body about the paired object `□⟨a, c⟩` gives
    `∃e. pairUp Ψ` at `□a`. -/
def Proof.ex_pairUp {Δ : List (WFF σ W 0)} {x₀ : Ann X} {y₀ : Ann Y} (a : Term σ W.boxIn X x₀)
    (c : Term σ W.boxIn Y y₀) (Ψ : WFF σ (W.insert (.bnd 0) (.VTypeBox (.VTypeProd X Y))) 1)
    (p : Proof σ W Δ (WFF.instantiate Ctx.NoSlots.slots (Term.boxtm (Term.pair a c)) Ψ)) :
    Proof σ W Δ (WFF.instantiate Ctx.NoSlots.slots (Term.boxtm a)
      (WFF.ex (.VTypeBox Y) (WFF.pairUp Ψ))) := by
  refine Proof.ex_intro _ (Term.boxtm c) (Proof.conv (Eq.symm ?_) p)
  unfold WFF.instantiate WFF.substRoot WFF.pairUp
  have hfr : W (.root (.bnd 0)) = none := (Ctx.NoSlots.slots (Γ := W)).root
  have hl := Ctx.le_insert hfr (.VTypeBox Y)
  have hfresh : W.RootFresh (.bnd 0) := (Ctx.NoSlots.slots (Γ := W)).rootFresh (le_refl 0)
  have hne : ∀ {v : VarSymb} {U : VarType}, v.lastProj = false → W v = some U →
      v.rt ≠ .bnd 0 ∧ v.rt ≠ .bnd 1 := fun hlp hv =>
    ⟨Ctx.ref_rt_ne hfresh ((Ctx.ref_nonproj W hlp).trans hv),
      Ctx.ref_rt_ne ((Ctx.NoSlots.slots (Γ := W)).rootFresh (Nat.zero_le 1))
        ((Ctx.ref_nonproj W hlp).trans hv)⟩
  have hw : ∀ {v : VarSymb} {U : VarType}, v.lastProj = false →
      (W.insert (.bnd 0) (.VTypeBox (.VTypeProd X Y))) v = some U → v ≠ .root (.bnd 0) →
      W v = some U := fun _ hv hvr => by simpa [Ctx.insert, hvr] using hv
  let s₁₂ : Term σ (W.insert (.bnd 0) (.VTypeBox Y)) (.VTypeBox (.VTypeProd X Y)) _ :=
    Term.boxtm (Term.pair (Term.mono hl.boxIn a)
      (Term.eta (VarSymb.root (.bnd 0)).inner Y (Ctx.ref_inner (Ctx.ref_insert_root W (.bnd 0) _))))
  have ok₁₂ := Subst.ok_single (σ := σ) (Γ := W) (r := .bnd 0)
    (T := .VTypeBox (.VTypeProd X Y)) (e := .tm s₁₂) hl rfl
  have coh₁₂ := Subst.coh_single (σ := σ) (Γ := W) (r := .bnd 0)
    (T := .VTypeBox (.VTypeProd X Y)) (e := .tm s₁₂) hfresh hl rfl
  refine Eq.trans (congrArg (WFF.subst _ _ _ _ _ _)
    (WFF.subst_comp _ _ (Subst.single (.bnd 0) (.tm s₁₂)) _ _ _ _ ok₁₂ coh₁₂ _ _ _ ?_ Ψ)) ?_
  · refine Subst.sim_of fun v U hlp hv => ?_
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      obtain rfl : U = .VTypeBox (.VTypeProd X Y) := by simpa [Ctx.insert] using hv.symm
      rw [Subst.comp_apply, Subst.set_root, Subst.single_root]
      dsimp only [SubE.comp]
      have h0 : ((Subst.single (σ := σ) (Δ := W) (.bnd 0) (.tm (Term.boxtm a))).under (0 + 1) 0
          (.VTypeBox Y) hfr).at (.root (.bnd 0)) = .tm (Term.boxtm (Term.mono hl.boxIn a)) := by
        rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_single_root]
        rfl
      exact SubE.sim_tm_sigma (sig_boxtm (sig_pair
        (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ h0))
        (Term.subst_eta_renAt _ _ _ _ _ _ _ (Ctx.ref_inner (Ctx.ref_insert_root _ (.bnd 0) _))
          (Subst.box_at_inner_ren _ (Subst.under_at_slot _ (0 + 1) 0 _ hfr))))).symm
    · obtain ⟨h0, h1⟩ := hne hlp (hw hlp hv hvr)
      rw [Subst.comp_apply, Subst.set_ne _ _ hvr,
        (Subst.at_nonproj (Subst.single (σ := σ) (.bnd 0) (.tm s₁₂)) hlp).symm,
        Subst.single_at_ne h0]
      change SubE.Sim U _ (Subst.at _ v)
      rw [Subst.at_under_ne _ _ _ h1, Subst.single_at_ne h0]
      exact .refl _
  · refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Ψ
    refine Subst.sim_of fun v U hlp hv => ?_
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      obtain rfl : U = .VTypeBox (.VTypeProd X Y) := by simpa [Ctx.insert] using hv.symm
      rw [Subst.comp_apply, Subst.single_root, Subst.single_root]
      dsimp only [SubE.comp]
      refine SubE.sim_tm_sigma (sig_boxtm (sig_pair ?_ (Term.subst_eta_tm _ _ _ _ _ _ c
        (Subst.box_at_inner_boxtm _ (Subst.at_single_root _ _))))).symm
      exact (Term.subst_single_box_mono (Ctx.Le.refl W) hl (.tm (Term.boxtm c))
        (Subst.ok_single (Ctx.Le.refl _) rfl) (Subst.coh_single hfresh (Ctx.Le.refl _) rfl)
        hfresh a).trans (congrArg (Sigma.mk _) (Term.mono_refl _ a))
    · obtain ⟨h0, _⟩ := hne hlp (hw hlp hv hvr)
      rw [Subst.comp_apply,
        (Subst.at_nonproj (Subst.single (σ := σ) (.bnd 0) (.tm s₁₂)) hlp).symm,
        (Subst.at_nonproj (Subst.single (σ := σ) (.bnd 0)
          (.tm (Term.boxtm (Term.pair a c)))) hlp).symm,
        Subst.single_at_ne h0, Subst.single_at_ne h0]
      change SubE.Sim U _ (Subst.at _ v)
      rw [Subst.single_at_ne h0]
      exact .refl _

end Pair

/-! ## Lifting -/

section Main

variable {Γ : Ctx} [Γ.NoSlots] {A : VarType}

omit [Γ.NoSlots] in
/-- The leg's view has the base's fresh roots. -/
theorem OutLeg.rootFresh {r : Root} (h : Γ.RootFresh r) : (O : OutLeg Γ) → O.view.RootFresh r
  | .nec => h.boxIn
  | .pos y _ => h.diaIn y

/-- ⭐**The ties come for free**: the object has its companion `d.dup`, tied. -/
def Proof.ret_tied (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ) {a₁ : Ann A}
    (t : Term σ Γ A a₁) (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1) (r : ℕ)
    (hr : O.view.RootFresh (.free r)) (H : Proof σ Γ Δ (O.ret hS t Φ)) :
    Proof σ Γ Δ (O.ret hS t (WFF.ex (.VTypeBox (.VTypeBox A))
      (WFF.pairUp (WFF.tiedBody hS hF Φ)))) := by
  refine Proof.ret_mono hS O t _ _ H (Proof.leg_all O _ _ r hr ?_)
  have hV := Ctx.le_insert hr.root (.VTypeBox A)
  have h₀ := Ctx.ref_insert_root O.view (.free r) (.VTypeBox A)
  rw [← WFF.instantiate_eta_openFree r hr Ctx.NoSlots.slots Ctx.NoSlots.slots
    (WFF.ex (.VTypeBox (.VTypeBox A)) _)]
  refine Proof.conv ?_ (Proof.ex_pairUp (Term.eta (σ := σ) (VarSymb.root (.free r)).inner A
    (Ctx.ref_inner h₀)) (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (Term.eta
      (VarSymb.root (.free r)).inner A (Ctx.ref_inner h₀))))
    (WFF.tiedBody hS hF (WFF.mono (hV.insert (.bnd 0) _) Φ)) ?_)
  · exact congrArg (fun φ => WFF.instantiate _ _ (WFF.ex _ φ))
      (((congrArg WFF.pairUp (WFF.mono_tiedBody hV hS hF Φ)).symm.trans
        (WFF.mono_pairUp hV _).symm))
  · refine Proof.conv (WFF.instantiate_tiedBody hS hF _ _
      (Term.shift (Ctx.shifts_boxIn_boxIn hF _) _)).symm
      (Proof.and_intro ?_ (Proof.ties_dup hS hT hF _ h₀))
    exact Proof.conv (WFF.instantiate_eta_openFree r hr Ctx.NoSlots.slots
      Ctx.NoSlots.slots Φ).symm (Proof.lookup List.mem_cons_self)

/-- ⭐⭐**Lifting a returning possibility** (T + 4, strong B): `◇[d ↦ t] Φ(d)` gives, as an
    `∃`-elimination, a fresh `c : □A` that comes back as `t` along an arrow out and such that
    possibly `Φ(c.keep)`.  Along either leg.  Ties and companion: `Proof.ret_tied`, `ret_ext`; then
    `Proof.lift_back` and `Proof.lift_dia`. -/
def Proof.ret_lift (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (O : OutLeg Γ)
    {a₁ : Ann A} (t : Term σ Γ A a₁) (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1)
    (c : ℕ) (hc : Γ.RootFresh (.free c)) (hc₁ : Γ.RootFresh (.free (c + 1)))
    (hc₂ : Γ.RootFresh (.free (c + 2)))
    (p : Proof σ Γ Δ (O.ret hS t Φ))
    (q : Proof σ (Γ.insert (.free c) (.VTypeBox A))
      (WFF.and
          (WFF.back hS .nec (Term.boxtm (Term.boxtm
            (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (Term.eta (VarSymb.root (.free c)).inner A
              (Ctx.ref_inner (Ctx.ref_insert_root Γ (.free c) (.VTypeBox A)))))))
            (Term.weaken hc.root _ t))
          ((O.mono (Ctx.le_insert hc.root _)).dia (WFF.instantiate Ctx.NoSlots.slots
            (Term.mono (O.mono (Ctx.le_insert hc.root _)).le_view (Term.boxtm
              (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (Term.eta (VarSymb.root (.free c)).inner A
                (Ctx.ref_inner (Ctx.ref_insert_root Γ (.free c) (.VTypeBox A)))))))
            (WFF.mono ((O.le_view_mono (Ctx.le_insert hc.root _)).insert (.bnd 0) _) Φ))) ::
        Δ.map (WFF.weaken hc.root _))
      (φ.weaken hc.root _)) :
    Proof σ Γ Δ φ := by
  refine Proof.ret_ext hS O t (WFF.pairUp (WFF.tiedBody hS hF Φ)) c hc
    (Proof.ret_tied hS hT hF O t Φ (c + 1) (OutLeg.rootFresh hc₁ O) p) ?_
  rw [WFF.bodySplit_pairUp, WFF.mono_tiedBody (O.le_view_mono (Ctx.le_insert hc.root _))]
  have hne₁ : Root.free c ≠ .free (c + 1) := fun h => by
    have := Root.free.inj h
    omega
  have hne₂ : Root.free c ≠ .free (c + 2) := fun h => by
    have := Root.free.inj h
    omega
  have hne₃ : Root.free (c + 1) ≠ .free (c + 2) := fun h => by
    have := Root.free.inj h
    omega
  have hu := OutLeg.rootFresh (hc₁.insert_ne hne₁ (.VTypeBox A))
    (O.mono (Ctx.le_insert hc.root (.VTypeBox A)))
  have he : ((O.mono (Ctx.le_insert hc.root (.VTypeBox A))).view.insert (.free (c + 1))
      (.VTypeBox (liftTy A))).boxIn.RootFresh (.free (c + 2)) :=
    ((OutLeg.rootFresh (hc₂.insert_ne hne₂ _) _).insert_ne hne₃ _).boxIn
  let nb := Term.eta (σ := σ) (VarSymb.root (.free c)).inner A
    (Ctx.ref_inner (Ctx.ref_insert_root Γ (.free c) (.VTypeBox A)))
  exact Proof.imp_elim (Proof.ofSubset (fun _ hx => List.mem_cons_of_mem _ hx)
    (Proof.imp_intro q)) (Proof.and_intro
      (Proof.lift_back hS hF _ _ nb _ _ hu (Proof.lookup List.mem_cons_self))
      (Proof.lift_dia hS hT hF _ _ nb _ _ _ hu he (Proof.lookup List.mem_cons_self)))

end Main

end V12M
