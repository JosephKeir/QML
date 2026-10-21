import QML.QML_v12m_BRetTruthW

/-!
# QML v12m — B's canonical model: returning children and aliases at the limit (strong B)

A returning possibility `◇[d ↦ t] Φ(d)` in a node's theory is made true by a returning successor
(docs §11.20, §11.21).  The network makes successors for **obligations** at the born root's own
shape, `◇^{S_A}[u ↦ unarrT y] Ξ(u)` valued at a root `y` (`NetSt.mkRetC`), on the generic
children: every obligation eventually has its child (`StrongChain.ret_childC`), and at the limit
an edge whose way home sends the born root `c` to `y`, with the body read at `c` (`lretC`); the
same along a witness (`lretXC`) and at witnessed shapes (`lretDC`, `lretXDC`).  A term gets an
alias at the limit (`lalias`), `Ind` to it (`lalias_ind`).

The producers that turn a user atom into an obligation, and the truth lemmas, are in
`QML_v12m_BRetOutC` (necessary shapes) and `QML_v12m_BRetOutDC` (witnessed shapes), for every T.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## Terms and bodies -/

section Body

variable {V : Ctx} [V.NoSlots]

omit [ModalSys.NoFour] in
/-- ⭐Replacing a body's slot twice is replacing it by the composed hole term. -/
theorem WFF.bodyRepl_bodyRepl {A B C : VarType} {b : Ann B} {c : Ann C}
    (X : Term σ (Ctx.empty.insert (.bnd 0) A) B b) (Y : Term σ (Ctx.empty.insert (.bnd 0) B) C c)
    (Φ : WFF σ (V.insert (.bnd 0) C) 1) :
    WFF.bodyRepl (Term.mono ((Ctx.empty_le V).insert (.bnd 0) A) X)
        (WFF.bodyRepl (Term.mono ((Ctx.empty_le V).insert (.bnd 0) B) Y) Φ) =
      WFF.bodyRepl (Term.mono ((Ctx.empty_le V).insert (.bnd 0) A) (Term.holeAt X Y)) Φ := by
  unfold WFF.bodyRepl
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = C := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    change SubE.Sim _ (((Subst.idS σ _).set (.bnd 0) _) (.root (.bnd 0)))
      ((((Subst.idS σ _).set (.bnd 0) _) (.root (.bnd 0))).comp _ _ _)
    rw [Subst.set_root, Subst.set_root]
    dsimp only [SubE.comp]
    refine SubE.sim_tm_sigma (Eq.symm ?_)
    refine (Term.subst_closed_sig _ _ _ _ (Subst.set_root _ _ _) Y).trans ?_
    exact (Term.mono_holeAt_sig _ X Y).symm
  · change SubE.Sim T (((Subst.idS σ _).set (.bnd 0) _) v)
      ((((Subst.idS σ _).set (.bnd 0) _) v).comp _ _ _)
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    change SubE.Sim T _ ((Subst.set _ _ _).at v)
    have hv' : V v = some T := by
      change (if v = VarSymb.root (.bnd 0) then _ else _) = _ at hv
      rwa [if_neg hvr] at hv
    rw [Subst.at_set_of_rt_ne _ _ (Ctx.ref_rt_ne
      ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0))
      ((Ctx.ref_nonproj _ hlp).trans hv')), Subst.at_idS]
    exact .refl _

end Body

section Pair

variable {V : Ctx} [V.NoSlots] {A Z : VarType}

omit [ModalSys.NoFour] in
/-- The slot formula for a pair's first item: `χ(⟨d, u⟩)`. -/
theorem WFF.instantiate_pairFst {c : Ann Z} (u : Term σ V Z c)
    (χ : WFF σ (V.insert (.bnd 0) (.VTypeProd A Z)) 1) {a : Ann A} (s : Term σ V A a) :
    WFF.instantiate Ctx.NoSlots.slots s (WFF.bodyRepl
      (Term.pair (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root _ _ _))
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root A) u)) χ) =
      WFF.instantiate Ctx.NoSlots.slots (Term.pair s u) χ := by
  rw [WFF.instantiate_bodyRepl]
  exact WFF.instantiate_congr_sig _ (sig_pair
    (Term.subst_eta_tm _ _ _ _ _ _ s (Subst.at_single_root _ _)) (subst_single_mono_tm s u)) χ

omit [ModalSys.NoFour] in
/-- The slot formula for a pair's second item: `χ(⟨u, d⟩)`. -/
theorem WFF.instantiate_pairSnd {c : Ann A} (u : Term σ V A c)
    (χ : WFF σ (V.insert (.bnd 0) (.VTypeProd A Z)) 1) {a : Ann Z} (s : Term σ V Z a) :
    WFF.instantiate Ctx.NoSlots.slots s (WFF.bodyRepl
      (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root Z) u)
        (Term.eta (.root (.bnd 0)) Z (Ctx.ref_insert_root _ _ _))) χ) =
      WFF.instantiate Ctx.NoSlots.slots (Term.pair u s) χ := by
  rw [WFF.instantiate_bodyRepl]
  exact WFF.instantiate_congr_sig _ (sig_pair (subst_single_mono_tm s u)
    (Term.subst_eta_tm _ _ _ _ _ _ s (Subst.at_single_root _ _))) χ

end Pair

theorem readArrowX_cx {l : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) {x : VarSymb} {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X))
    {cx cx' : ℕ} (e : cx = cx') (hcx : Δ.ref (.root (.free cx)) = some X)
    (hcx' : Δ.ref (.root (.free cx')) = some X) {B : VarType} {c : Ann B} (g : Term σ Δ B c)
    (Φ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) B) 1) :
    readArrowX himg hx hcx g Φ = readArrowX himg hx hcx' g Φ := by
  subst e
  rfl

/-! ## The chain makes aliases and returning children -/

section Chain

variable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} {hS : ModalSys.BStrong = true}
  (C : StrongChain hS M₀)

/-- ⭐Every term eventually has an alias. -/
theorem StrongChain.alias_at {n : ℕ} {s : Node} (hs : (C.net n).Live s) {A : VarType}
    {a : Ann A} (t : Term σ (ctxOf ((C.net n).st s).l) A a) :
    ∃ m, n ≤ m ∧ ∃ hsuf : ((C.net n).st s).l <:+ ((C.net m).st s).l,
      (C.net (m + 1)).st s =
        aliasStep ((C.net m).st s) (Term.mono (ctxOf_le_of_suffix hsuf) t) := by
  obtain ⟨m, hnm, hstep⟩ := C.aliasOp s ⟨_, A, a, t⟩ n
  have hlm := C.live_mono hnm hs
  have hsuf := C.lang_suffix hnm hs
  refine ⟨m, hnm, hsuf, ?_⟩
  rw [hstep hlm]
  simp only [NetSt.mkAlias, dif_pos hsuf]
  exact Function.update_self _ _ _

/-- The obligation's value, weakened, is the obligation's value in the larger list. -/
theorem mono_unarrT {l l' : List VarType} (hsuf : l <:+ l') {A : VarType} {y : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) :
    (⟨_, Term.mono (ctxOf_le_of_suffix hsuf) (unarrT (σ := σ) hy).2⟩ :
      Σ a, Term σ (ctxOf l') (A.compsFlat (bornComps A)) a) =
      unarrT (σ := σ) ((ctxOf_le_of_suffix hsuf).ref hy) :=
  (subst_arrow_tgt_mono (ctxOf_le_of_suffix hsuf) (retBackImg l A hy) _).symm

/-- The born-shape obligation atom, weakened. -/
theorem mono_ret_oblC {l l' : List VarType} (hsuf : l <:+ l') {A : VarType} {y : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (Ξ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox A)) 1) :
    WFF.mono (ctxOf_le_of_suffix hsuf)
        (WFF.retS hS (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ) =
      WFF.retS hS (.nec (bornShape A)) (unarrT (σ := σ) ((ctxOf_le_of_suffix hsuf).ref hy)).2
        (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ) := by
  change WFF.retS hS (.nec (bornShape A)) (Term.mono _ _) _ = _
  exact OutLeg.retS_congr hS .nec _ (mono_unarrT hsuf hy) rfl

/-- The child's body over the born root is the body read along the arrow at the born root. -/
theorem liftBodyR_eq_readArrow (l : List VarType) (A : VarType)
    (Ξ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox A)) 1) :
    liftBodyR l A Ξ = readArrow (rclImg l A)
      (Term.eta (.root (.free 0)) (.VTypeBox A) (rcl_born_ref l A)) Ξ := by
  unfold liftBodyR readArrow
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) Ξ
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = .VTypeBox A := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    rw [Subst.set_root, Subst.set_root]
    exact .ren_eta _ _
  · change SubE.Sim T (Subst.set _ _ _ v) (Subst.set _ _ _ v)
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    exact .refl _

/-- ⭐**Every obligation eventually has its returning child**: a child born of the obligation,
    with the parent's roots one up, its root `0` (the born root) coming back to `y`, and the
    obligation's body read there at the born root (`retChildC_body`). -/
theorem StrongChain.ret_childC {n : ℕ} {s : Node} (hs : (C.net n).Live s) {A : VarType} {y : ℕ}
    (hy : (ctxOf ((C.net n).st s).l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (Ξ : WFF σ ((ctxOf ((C.net n).st s).l).boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
    (h : WFF.retS hS (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ ∈ ((C.net n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ hsuf : ((C.net n).st s).l <:+ ((C.net m).st s).l,
      ¬ (C.net m).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).st ((C.net m).nch s :: s) =
        retChildC hS ((ctxOf_le_of_suffix hsuf).ref hy)
          (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ) ∧
      (C.net (m + 1)).kind ((C.net m).nch s :: s) = none ∧
      (C.net (m + 1)).fcl ((C.net m).nch s :: s) = ((C.net m).st s).l ∧
      (C.net (m + 1)).fimg ((C.net m).nch s :: s) = Nat.succ ∧
      (C.net (m + 1)).bcl ((C.net m).nch s :: s) = [.VTypeBox A] ∧
      (C.net (m + 1)).bimg ((C.net m).nch s :: s) = (fun _ => y) ∧
      liftBodyR ((C.net m).st s).l A
        (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ) ∈
          (retChildC hS ((ctxOf_le_of_suffix hsuf).ref hy)
            (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ)).M := by
  obtain ⟨m, hnm, hstep⟩ := C.retOp s ⟨_, A, y, Ξ⟩ n
  have hlm := C.live_mono hnm hs
  have hsuf := C.lang_suffix hnm hs
  have hg := (C.ext hnm).grows s hs
  have hM := (C.good m).mcs s hlm
  have hy' := (ctxOf_le_of_suffix hsuf).ref hy
  have hin : WFF.retS hS (.nec (bornShape A)) (unarrT (σ := σ) hy').2
      (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ) ∈ ((C.net m).st s).M := by
    rw [← mono_ret_oblC hsuf hy Ξ]
    exact hg.sub _ h
  have hst : C.net (m + 1) = (C.net m).newChild s none 0
      (retChildC hS hy' (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ))
      Nat.succ [.VTypeBox A] (fun _ => y) := by
    rw [hstep hlm]
    simp only [NetSt.mkRetC, dif_pos hsuf, dif_pos hy', if_pos hin]
  refine ⟨m, hnm, hsuf, NetSt.not_live_new s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hst]
    exact (NetSt.live_newChild hlm _ _ _ _).mpr (Or.inr rfl)
  all_goals first
    | (rw [hst]; exact Function.update_self _ _ _)
    | skip
  exact retChildC_body hS hy' hM hin

/-- ⭐⭐**A returning child at the limit**: an obligation at a stage of `s` has a forward edge
    `s → t` whose way home sends `t`'s root `0` to `y`, with the obligation's body read along the
    edge at the born root `c` (`StrongChain.ret_childC`, grown to the edge's stage). -/
theorem lretC (s : LW C.toFairChain) (i : ℕ) {A : VarType} {y : ℕ}
    (hy : (ctxOf (lat s i)).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (Ξ : WFF σ ((ctxOf (lat s i)).boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
    (h : WFF.retS hS (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ ∈
      ((C.net (birth C.toFairChain s.2 + i)).st s.1).M) :
    ∃ (t : LW C.toFairChain) (hst : LR C.toFairChain s t)
      (hcl : [VarType.VTypeBox A] <:+ lat t (lstg C.toFairChain s t i)),
      limg C.toFairChain t s 0 = y ∧
      readArrow (limgOk C.toFairChain hst i)
        (Term.eta (.root (.free 0)) (.VTypeBox A) ((ctxOf_le_of_suffix hcl).ref (born_ref A)))
        Ξ ∈ ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1).M := by
  classical
  obtain ⟨m, _, hsuf, hnot, hlive, hst, -, hfcl, hfimg, hbcl, hbimg, hmem⟩ :=
    C.ret_childC (live_birth C.toFairChain s.2 (Nat.le_add_right _ i)) hy Ξ h
  let t : LW C.toFairChain := ⟨(C.net m).nch s.1 :: s.1, m + 1, hlive⟩
  have hc : t.1 = (C.net m).nch s.1 :: s.1 := rfl
  have h' : LR C.toFairChain s t := Or.inl ⟨_, hc⟩
  have hbt : m < birth C.toFairChain t.2 := le_birth C.toFairChain t.2 hnot
  have hg : Grows ((C.net (m + 1)).st ((C.net m).nch s.1 :: s.1))
      ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1) :=
    (C.ext (by omega)).grows t.1 hlive
  rw [hst] at hg
  have hcl : [VarType.VTypeBox A] <:+ lat t (lstg C.toFairChain s t i) :=
    (rcl_suffix _ A).trans hg.suf
  refine ⟨t, h', hcl, ?_, ?_⟩
  · have hnb : ¬ ∃ c, s.1 = c :: t.1 := not_fwd_of_back (C := C.toFairChain) (t := s) hc
    rw [limg, if_neg hnb, bimgL_eq C.toFairChain hlive (by rw [hbcl]; exact Nat.zero_lt_one),
      hbimg]
  · have hm := hg.sub _ hmem
    have hag : ∀ r < (lat s i).length, Nat.succ r = limg C.toFairChain s t r := fun r hr => by
      have hlen : r < ((C.net (m + 1)).fcl t.1).length := by
        rw [hc, hfcl]
        exact lt_of_lt_of_le hr hsuf.length_le
      rw [limg, if_pos ⟨_, hc⟩, fimgL_eq C.toFairChain hlive hlen, hfimg]
    have himg₀ : ImgOk (lat s i) (ctxOf (rcl ((C.net m).st s.1).l A)) Nat.succ :=
      (rclImg ((C.net m).st s.1).l A).suffix hsuf
    have e1 := readArrow_mono_congr hsuf (Ctx.Le.refl _) himg₀ (rclImg _ A) (fun r _ => rfl)
      (Term.eta (σ := σ) (.root (.free 0)) (.VTypeBox A) (rcl_born_ref _ A)) Ξ
    rw [Term.mono_refl] at e1
    change WFF.mono _ (liftBodyR _ A _) ∈ _ at hm
    rw [liftBodyR_eq_readArrow, ← e1, WFF.mono_mono, readArrow_mono_congr (List.suffix_refl _) _
      himg₀ (limgOk C.toFairChain h' i) hag, WFF.mono_refl] at hm
    refine (congrArg (· ∈ _) (readArrow_sig _ ?_ Ξ)).mp hm
    rw [Term.mono_eta]

/-- ⭐**Aliases at the limit**: a term at a stage of `s` has, from some later stage on, an alias
    root (`l.length`, after the list `l`) with its alias formulas at every stage
    (`StrongChain.alias_at`, `aliasStep_ok`). -/
theorem lalias (s : LW C.toFairChain) (i : ℕ) {A : VarType} {a : Ann A}
    (t : Term σ (ctxOf (lat s i)) A a) :
    ∃ i₁, i ≤ i₁ ∧ ∃ (l : List VarType) (hl : lat s i <:+ l), ∀ j, i₁ ≤ j →
      ∃ hsuf : (A :: l) <:+ lat s j, ∀ ψ,
        WFF.mono (ctxOf_le_of_suffix hsuf) (aliasFormula (Term.mono (ctxOf_le_of_suffix hl) t) ψ)
          ∈ ((C.net (birth C.toFairChain s.2 + j)).st s.1).M := by
  obtain ⟨m, hnm, hsuf, hst⟩ :=
    C.alias_at (live_birth C.toFairChain s.2 (Nat.le_add_right _ i)) t
  refine ⟨m + 1 - birth C.toFairChain s.2, by omega, _, hsuf, fun j hj => ?_⟩
  have hlm : (C.net (m + 1)).Live s.1 := live_birth C.toFairChain s.2 (by omega)
  have hg := (C.ext (show m + 1 ≤ birth C.toFairChain s.2 + j by omega)).grows s.1 hlm
  have hal := (aliasStep_ok ((C.good m).mcs s.1
    (live_birth C.toFairChain s.2 (by omega))) (Term.mono (ctxOf_le_of_suffix hsuf) t)).2.2
  rw [hst] at hg
  exact ⟨hg.suf, fun ψ => hg.sub _ (hal ⟨ψ, rfl⟩)⟩

/-- The born-shape obligation atom along a witness, weakened. -/
theorem mono_retx_oblC {l l' : List VarType} (hsuf : l <:+ l') {A : VarType} {y : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) {x : VarSymb}
    {X : VarType} (hX : (ctxOf l).ref x = some (.VTypeDia X))
    (Ξ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox A)) 1) :
    WFF.mono (ctxOf_le_of_suffix hsuf)
        (WFF.retxS hS x ⟨X, hX⟩ (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ) =
      WFF.retxS hS x ⟨X, (ctxOf_le_of_suffix hsuf).ref hX⟩ (.nec (bornShape A))
        (unarrT (σ := σ) ((ctxOf_le_of_suffix hsuf).ref hy)).2
        (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ) := by
  change WFF.retxS hS x _ (.nec (bornShape A)) (Term.mono _ _) _ = _
  exact OutLeg.retS_congr hS (.pos x ⟨X, (ctxOf_le_of_suffix hsuf).ref hX⟩) _
    (mono_unarrT hsuf hy) rfl

/-- The witness child's body over the born root is the body read along the witness arrow at the
    born root. -/
theorem liftBodyXR_eq_readArrowX (l : List VarType) (A : VarType) {x : VarSymb} {X : VarType}
    (hX : (ctxOf l).ref x = some (.VTypeDia X))
    (Ξ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox A)) 1) :
    liftBodyXR l A hX Ξ = readArrowX (rclXImg l A X) hX (rclX_cx l A X)
      (Term.eta (.root (.free 0)) (.VTypeBox A) (rclX_born_ref l A X)) Ξ := by
  unfold liftBodyXR readArrowX
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) Ξ
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = .VTypeBox A := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    rw [Subst.set_root, Subst.set_root]
    exact .ren_eta _ _
  · change SubE.Sim T (Subst.set _ _ _ v) (Subst.set _ _ _ v)
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    exact .refl _

/-- ⭐**Every obligation along a witness eventually has its witness child**. -/
theorem StrongChain.ret_childXC {n : ℕ} {s : Node} (hs : (C.net n).Live s) {A : VarType}
    {y : ℕ} (hy : (ctxOf ((C.net n).st s).l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    {x : VarSymb} {X : VarType} (hX : (ctxOf ((C.net n).st s).l).ref x = some (.VTypeDia X))
    (Ξ : WFF σ (((ctxOf ((C.net n).st s).l).diaIn x).insert (.bnd 0) (.VTypeBox A)) 1)
    (h : WFF.retxS hS x ⟨X, hX⟩ (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ ∈
      ((C.net n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ hsuf : ((C.net n).st s).l <:+ ((C.net m).st s).l,
      ¬ (C.net m).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).st ((C.net m).nch s :: s) =
        retChildXC hS ((ctxOf_le_of_suffix hsuf).ref hy) ((ctxOf_le_of_suffix hsuf).ref hX)
          (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ) ∧
      (C.net (m + 1)).kind ((C.net m).nch s :: s) = some (x, X) ∧
      (C.net (m + 1)).cx ((C.net m).nch s :: s) = ((C.net m).st s).l.length + 1 ∧
      (C.net (m + 1)).fcl ((C.net m).nch s :: s) = ((C.net m).st s).l ∧
      (C.net (m + 1)).fimg ((C.net m).nch s :: s) = Nat.succ ∧
      (C.net (m + 1)).bcl ((C.net m).nch s :: s) = [.VTypeBox A] ∧
      (C.net (m + 1)).bimg ((C.net m).nch s :: s) = (fun _ => y) ∧
      liftBodyXR ((C.net m).st s).l A ((ctxOf_le_of_suffix hsuf).ref hX)
        (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ) ∈
          (retChildXC hS ((ctxOf_le_of_suffix hsuf).ref hy) ((ctxOf_le_of_suffix hsuf).ref hX)
            (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ)).M := by
  obtain ⟨m, hnm, hstep⟩ := C.retXOp s ⟨_, A, x, y, Ξ⟩ n
  have hlm := C.live_mono hnm hs
  have hsuf := C.lang_suffix hnm hs
  have hg := (C.ext hnm).grows s hs
  have hM := (C.good m).mcs s hlm
  have hy' := (ctxOf_le_of_suffix hsuf).ref hy
  have hX' := (ctxOf_le_of_suffix hsuf).ref hX
  have hin : WFF.retxS hS x ⟨X, hX'⟩ (.nec (bornShape A)) (unarrT (σ := σ) hy').2
      (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ) ∈
        ((C.net m).st s).M := by
    rw [← mono_retx_oblC hsuf hy hX Ξ]
    exact hg.sub _ h
  have hst : C.net (m + 1) = (C.net m).newChild s (some (x, X)) (((C.net m).st s).l.length + 1)
      (retChildXC hS hy' hX'
        (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ))
      Nat.succ [.VTypeBox A] (fun _ => y) := by
    rw [hstep hlm]
    simp only [NetSt.mkRetXC, dif_pos hsuf, dif_pos hy']
    split
    · rename_i X'' hX''
      obtain rfl : X'' = X := by
        rw [hX'] at hX''
        exact (VarType.VTypeDia.inj (Option.some.inj hX'')).symm
      rw [if_pos hin]
    · rename_i hne
      exact absurd hX' (hne X)
  refine ⟨m, hnm, hsuf, NetSt.not_live_new s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hst]
    exact (NetSt.live_newChild hlm _ _ _ _).mpr (Or.inr rfl)
  all_goals first
    | (rw [hst]; exact Function.update_self _ _ _)
    | skip
  exact retChildXC_body hS hy' hX' hM hin

/-- ⭐⭐**A witness child at the limit**: an obligation along `x` at a stage of `s` has a witness
    edge `s → t` for `x` whose way home sends `t`'s root `0` to `y`, with the obligation's body
    read along it at the born root (`StrongChain.ret_childXC`). -/
theorem lretXC (s : LW C.toFairChain) (i : ℕ) {A : VarType} {y : ℕ}
    (hy : (ctxOf (lat s i)).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) {x : VarSymb}
    {X : VarType} (hX : (ctxOf (lat s i)).ref x = some (.VTypeDia X))
    (Ξ : WFF σ (((ctxOf (lat s i)).diaIn x).insert (.bnd 0) (.VTypeBox A)) 1)
    (h : WFF.retxS hS x ⟨X, hX⟩ (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ ∈
      ((C.net (birth C.toFairChain s.2 + i)).st s.1).M) :
    ∃ (t : LW C.toFairChain) (hk : lkd C.toFairChain s t = some (x, X))
      (hcl : [VarType.VTypeBox A] <:+ lat t (lstg C.toFairChain s t i)),
      limg C.toFairChain t s 0 = y ∧
      readArrowX (limgOk C.toFairChain (lkdR hk) i) hX (lhcx C.toFairChain hk i)
        (Term.eta (.root (.free 0)) (.VTypeBox A) ((ctxOf_le_of_suffix hcl).ref (born_ref A)))
        Ξ ∈ ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1).M := by
  classical
  obtain ⟨m, _, hsuf, hnot, hlive, hst, hkind, hcxe, hfcl, hfimg, hbcl, hbimg, hmem⟩ :=
    C.ret_childXC (live_birth C.toFairChain s.2 (Nat.le_add_right _ i)) hy hX Ξ h
  let t : LW C.toFairChain := ⟨(C.net m).nch s.1 :: s.1, m + 1, hlive⟩
  have hc : t.1 = (C.net m).nch s.1 :: s.1 := rfl
  have hbt : m < birth C.toFairChain t.2 := le_birth C.toFairChain t.2 hnot
  have hbt' : birth C.toFairChain t.2 ≤ m + 1 := birth_le t.2 hlive
  have hkd : lkd C.toFairChain s t = some (x, X) := by
    rw [lkd, if_pos ⟨_, hc⟩, ← kind_at C.toFairChain t hbt']
    exact hkind
  have hlcx : lcx C.toFairChain s t = ((C.net m).st s.1).l.length + 1 := by
    rw [lcx, if_pos ⟨_, hc⟩]
    exact (cx_at C.toFairChain t hbt').symm.trans hcxe
  have hg : Grows ((C.net (m + 1)).st ((C.net m).nch s.1 :: s.1))
      ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1) :=
    (C.ext (by omega)).grows t.1 hlive
  rw [hst] at hg
  have hcl : [VarType.VTypeBox A] <:+ lat t (lstg C.toFairChain s t i) :=
    (rclX_suffix _ A X).trans hg.suf
  refine ⟨t, hkd, hcl, ?_, ?_⟩
  · have hnb : ¬ ∃ c, s.1 = c :: t.1 := not_fwd_of_back (C := C.toFairChain) (t := s) hc
    rw [limg, if_neg hnb, bimgL_eq C.toFairChain hlive (by rw [hbcl]; exact Nat.zero_lt_one),
      hbimg]
  · have hm := hg.sub _ hmem
    have hag : ∀ r < (lat s i).length, Nat.succ r = limg C.toFairChain s t r := fun r hr => by
      have hlen : r < ((C.net (m + 1)).fcl t.1).length := by
        rw [hc, hfcl]
        exact lt_of_lt_of_le hr hsuf.length_le
      rw [limg, if_pos ⟨_, hc⟩, fimgL_eq C.toFairChain hlive hlen, hfimg]
    have himg₀ : ImgOk (lat s i) (ctxOf (X :: rcl ((C.net m).st s.1).l A)) Nat.succ :=
      (rclXImg ((C.net m).st s.1).l A X).suffix hsuf
    have e1 := readArrowX_mono_congr hsuf (Ctx.Le.refl _) himg₀ (rclXImg _ A X)
      (fun _ _ => rfl) hX ((ctxOf_le_of_suffix hsuf).ref hX) (rclX_cx _ A X) (rclX_cx _ A X)
      (Term.eta (σ := σ) (.root (.free 0)) (.VTypeBox A) (rclX_born_ref _ A X)) Ξ
    rw [Term.mono_refl] at e1
    change WFF.mono _ (liftBodyXR _ A _ _) ∈ _ at hm
    rw [liftBodyXR_eq_readArrowX, ← e1, WFF.mono_mono, readArrowX_mono_congr
      (List.suffix_refl _) _ himg₀ (limgOk C.toFairChain (lkdR hkd) i) hag hX hX _
      (hlcx ▸ lhcx C.toFairChain hkd i), WFF.mono_refl] at hm
    rw [readArrowX_cx _ _ hlcx _ (hlcx ▸ lhcx C.toFairChain hkd i)]
    refine (congrArg (· ∈ _) (readArrowX_sig _ _ _ ?_ Ξ)).mp hm
    rw [Term.mono_eta]

/-- The witnessed born-shape obligation atom, weakened. -/
theorem mono_retD_oblC {l l' : List VarType} (hsuf : l <:+ l') {A X : VarType} {y z : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (hz : (ctxOf l).ref (.root (.free z)) = some X)
    (Ξ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (RShape.wit (bornShape A) X).ty) 1) :
    WFF.mono (ctxOf_le_of_suffix hsuf)
        (WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) hy hz).2 Ξ) =
      WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) ((ctxOf_le_of_suffix hsuf).ref hy)
          ((ctxOf_le_of_suffix hsuf).ref hz)).2
        (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ) := by
  change WFF.retS hS (.wit (bornShape A) X) (Term.pair (Term.mono _ _) (Term.mono _ _)) _ = _
  exact OutLeg.retS_congr hS .nec _ (sig_pair (mono_unarrT hsuf hy) (by rw [Term.mono_eta]))
    rfl

/-- ⭐**Every witnessed obligation eventually has its back-witness child**. -/
theorem StrongChain.ret_childDC {n : ℕ} {s : Node} (hs : (C.net n).Live s) {A X : VarType}
    {y o z : ℕ}
    (hy : (ctxOf ((C.net n).st s).l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (ho : (ctxOf ((C.net n).st s).l).ref (.root (.free o)) = some .VTypeOne)
    (hz : (ctxOf ((C.net n).st s).l).ref (.root (.free z)) = some X) (hyo : y ≠ o)
    (Ξ : WFF σ ((ctxOf ((C.net n).st s).l).boxIn.insert (.bnd 0)
      (RShape.wit (bornShape A) X).ty) 1)
    (h : WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) hy hz).2 Ξ ∈
      ((C.net n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ hsuf : ((C.net n).st s).l <:+ ((C.net m).st s).l,
      ¬ (C.net m).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).st ((C.net m).nch s :: s) =
        retChildDC hS ((ctxOf_le_of_suffix hsuf).ref hy) ((ctxOf_le_of_suffix hsuf).ref hz)
          (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ) ∧
      (C.net (m + 1)).bkind ((C.net m).nch s :: s) = some (.root (.free 1), X) ∧
      (C.net (m + 1)).bcx ((C.net m).nch s :: s) = z ∧
      (C.net (m + 1)).fcl ((C.net m).nch s :: s) = ((C.net m).st s).l ∧
      (C.net (m + 1)).fimg ((C.net m).nch s :: s) = (· + 2) ∧
      (C.net (m + 1)).bcl ((C.net m).nch s :: s) = bclD A X ∧
      (C.net (m + 1)).bimg ((C.net m).nch s :: s) = backImgD y o ∧
      liftBodyDR ((C.net m).st s).l A X
        (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ) ∈
          (retChildDC hS ((ctxOf_le_of_suffix hsuf).ref hy) ((ctxOf_le_of_suffix hsuf).ref hz)
            (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ)).M := by
  obtain ⟨m, hnm, hstep⟩ := C.retDOp s ⟨_, A, X, (y, o, z), Ξ⟩ n
  have hlm := C.live_mono hnm hs
  have hsuf := C.lang_suffix hnm hs
  have hg := (C.ext hnm).grows s hs
  have hM := (C.good m).mcs s hlm
  have hy' := (ctxOf_le_of_suffix hsuf).ref hy
  have ho' := (ctxOf_le_of_suffix hsuf).ref ho
  have hz' := (ctxOf_le_of_suffix hsuf).ref hz
  have hin : WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) hy' hz').2
      (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ) ∈
        ((C.net m).st s).M := by
    rw [← mono_retD_oblC hsuf hy hz Ξ]
    exact hg.sub _ h
  have hst : C.net (m + 1) = (C.net m).newChild s none 0
      (retChildDC hS hy' hz' (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ))
      (· + 2) (bclD A X) (backImgD y o) (some (.root (.free 1), X)) z := by
    rw [hstep hlm]
    simp only [NetSt.mkRetDC, dif_pos hsuf, dif_pos hy', if_pos ho', dif_pos hz', if_pos hin,
      if_pos hyo]
  refine ⟨m, hnm, hsuf, NetSt.not_live_new s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hst]
    exact (NetSt.live_newChild hlm _ _ _ _).mpr (Or.inr rfl)
  all_goals first
    | (rw [hst]; exact Function.update_self _ _ _)
    | skip
  exact retChildDC_body hS hy' hz' hM hin

/-- ⭐⭐**A back-witness child at the limit**: a witnessed obligation at a stage of `s` has a
    forward edge `s → t` whose way home is a witness edge for `t`'s root `e`, sending `t`'s root
    `c` to `y`, with content `z`, and the obligation's body read along the edge at `⟨c, e⟩`
    (`StrongChain.ret_childDC`). -/
theorem lretDC (s : LW C.toFairChain) (i : ℕ) {A X : VarType} {y o z : ℕ}
    (hy : (ctxOf (lat s i)).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (ho : (ctxOf (lat s i)).ref (.root (.free o)) = some .VTypeOne)
    (hz : (ctxOf (lat s i)).ref (.root (.free z)) = some X) (hyo : y ≠ o)
    (Ξ : WFF σ ((ctxOf (lat s i)).boxIn.insert (.bnd 0) (RShape.wit (bornShape A) X).ty) 1)
    (h : WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) hy hz).2 Ξ ∈
      ((C.net (birth C.toFairChain s.2 + i)).st s.1).M) :
    ∃ (t : LW C.toFairChain) (hst : LR C.toFairChain s t)
      (_ : lkd C.toFairChain t s = some (.root (.free 1), X))
      (hcl : bclD A X <:+ lat t (lstg C.toFairChain s t i)),
      limg C.toFairChain t s 0 = y ∧ lcx C.toFairChain t s = z ∧
      readArrow (limgOk C.toFairChain hst i)
        (Term.pair (Term.eta (.root (.free 0)) (.VTypeBox A)
            ((ctxOf_le_of_suffix hcl).ref (bclD_c A X)))
          (Term.eta (.root (.free 1)) (.VTypeDia X) ((ctxOf_le_of_suffix hcl).ref (bclD_e A X))))
        Ξ ∈ ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1).M := by
  classical
  obtain ⟨m, _, hsuf, hnot, hlive, hst, hbk, hbcx, hfcl, hfimg, hbcl, hbimg, hmem⟩ :=
    C.ret_childDC (live_birth C.toFairChain s.2 (Nat.le_add_right _ i)) hy ho hz hyo Ξ h
  let t : LW C.toFairChain := ⟨(C.net m).nch s.1 :: s.1, m + 1, hlive⟩
  have hc : t.1 = (C.net m).nch s.1 :: s.1 := rfl
  have h' : LR C.toFairChain s t := Or.inl ⟨_, hc⟩
  have hbt : m < birth C.toFairChain t.2 := le_birth C.toFairChain t.2 hnot
  have hbt' : birth C.toFairChain t.2 ≤ m + 1 := birth_le t.2 hlive
  have hnb : ¬ ∃ c, s.1 = c :: t.1 := not_fwd_of_back (C := C.toFairChain) (t := s) hc
  have hkd : lkd C.toFairChain t s = some (.root (.free 1), X) := by
    rw [lkd, if_neg hnb, if_pos ⟨_, hc⟩, ← bkind_at C.toFairChain t hbt']
    exact hbk
  have hlcx : lcx C.toFairChain t s = z := by
    rw [lcx, if_neg hnb]
    exact (bcx_at C.toFairChain t hbt').symm.trans hbcx
  have hg : Grows ((C.net (m + 1)).st ((C.net m).nch s.1 :: s.1))
      ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1) :=
    (C.ext (by omega)).grows t.1 hlive
  rw [hst] at hg
  have hcl : bclD A X <:+ lat t (lstg C.toFairChain s t i) :=
    (rclD_suffix _ A X).trans hg.suf
  refine ⟨t, h', hkd, hcl, ?_, hlcx, ?_⟩
  · rw [limg, if_neg hnb, bimgL_eq C.toFairChain hlive (by rw [hbcl]; simp), hbimg]
    rfl
  · have hm := hg.sub _ hmem
    have hag : ∀ r < (lat s i).length, r + 2 = limg C.toFairChain s t r := fun r hr => by
      have hlen : r < ((C.net (m + 1)).fcl t.1).length := by
        rw [hc, hfcl]
        exact lt_of_lt_of_le hr hsuf.length_le
      rw [limg, if_pos ⟨_, hc⟩, fimgL_eq C.toFairChain hlive hlen, hfimg]
    have himg₀ : ImgOk (lat s i) (ctxOf (rclD ((C.net m).st s.1).l A X)) (· + 2) :=
      (rclDImg ((C.net m).st s.1).l A X).suffix hsuf
    have e1 := readArrow_mono_congr hsuf (Ctx.Le.refl _) himg₀ (rclDImg _ A X)
      (fun r _ => rfl) (Term.pair (Term.eta (σ := σ) (.root (.free 0)) (.VTypeBox A)
        (rclD_c _ A X)) (Term.eta (.root (.free 1)) (.VTypeDia X) (rclD_e _ A X))) Ξ
    rw [Term.mono_refl] at e1
    change WFF.mono _ (readArrow (rclDImg _ A X) (Term.pair (Term.eta (.root (.free 0))
      (.VTypeBox A) (rclD_c _ A X)) (Term.eta (.root (.free 1)) (.VTypeDia X)
        (rclD_e _ A X))) _) ∈ _ at hm
    rw [← e1, WFF.mono_mono, readArrow_mono_congr (List.suffix_refl _) _ himg₀
      (limgOk C.toFairChain h' i) hag, WFF.mono_refl] at hm
    refine (congrArg (· ∈ _) (readArrow_sig _ ?_ Ξ)).mp hm
    change (⟨_, Term.pair (Term.mono _ (Term.eta _ _ _)) (Term.mono _ (Term.eta _ _ _))⟩ :
      Σ c, Term σ _ _ c) = _
    rw [Term.mono_eta, Term.mono_eta]

/-- The doubly witnessed born-shape obligation atom, weakened. -/
theorem mono_retXD_oblC {l l' : List VarType} (hsuf : l <:+ l') {A Xe : VarType} {y z : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (hz : (ctxOf l).ref (.root (.free z)) = some Xe) {x : VarSymb} {X : VarType}
    (hX : (ctxOf l).ref x = some (.VTypeDia X))
    (Ξ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (RShape.wit (bornShape A) Xe).ty) 1) :
    WFF.mono (ctxOf_le_of_suffix hsuf)
        (WFF.retxS hS x ⟨X, hX⟩ (.wit (bornShape A) Xe) (unarrDT (σ := σ) hy hz).2 Ξ) =
      WFF.retxS hS x ⟨X, (ctxOf_le_of_suffix hsuf).ref hX⟩ (.wit (bornShape A) Xe)
        (unarrDT (σ := σ) ((ctxOf_le_of_suffix hsuf).ref hy)
          ((ctxOf_le_of_suffix hsuf).ref hz)).2
        (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ) := by
  change WFF.retxS hS x _ (.wit (bornShape A) Xe) (Term.pair (Term.mono _ _) (Term.mono _ _))
    _ = _
  exact OutLeg.retS_congr hS (.pos x ⟨X, (ctxOf_le_of_suffix hsuf).ref hX⟩) _
    (sig_pair (mono_unarrT hsuf hy) (by rw [Term.mono_eta])) rfl

/-- ⭐**Every doubly witnessed obligation eventually has its child**. -/
theorem StrongChain.ret_childXDC {n : ℕ} {s : Node} (hs : (C.net n).Live s) {A Xe : VarType}
    {y o z : ℕ}
    (hy : (ctxOf ((C.net n).st s).l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (ho : (ctxOf ((C.net n).st s).l).ref (.root (.free o)) = some .VTypeOne)
    (hz : (ctxOf ((C.net n).st s).l).ref (.root (.free z)) = some Xe) (hyo : y ≠ o)
    {x : VarSymb} {X : VarType} (hX : (ctxOf ((C.net n).st s).l).ref x = some (.VTypeDia X))
    (Ξ : WFF σ (((ctxOf ((C.net n).st s).l).diaIn x).insert (.bnd 0)
      (RShape.wit (bornShape A) Xe).ty) 1)
    (h : WFF.retxS hS x ⟨X, hX⟩ (.wit (bornShape A) Xe) (unarrDT (σ := σ) hy hz).2 Ξ ∈
      ((C.net n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ hsuf : ((C.net n).st s).l <:+ ((C.net m).st s).l,
      ¬ (C.net m).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).st ((C.net m).nch s :: s) =
        retChildXDC hS ((ctxOf_le_of_suffix hsuf).ref hy) ((ctxOf_le_of_suffix hsuf).ref hz)
          ((ctxOf_le_of_suffix hsuf).ref hX)
          (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ) ∧
      (C.net (m + 1)).kind ((C.net m).nch s :: s) = some (x, X) ∧
      (C.net (m + 1)).cx ((C.net m).nch s :: s) = ((C.net m).st s).l.length + 2 ∧
      (C.net (m + 1)).bkind ((C.net m).nch s :: s) = some (.root (.free 1), Xe) ∧
      (C.net (m + 1)).bcx ((C.net m).nch s :: s) = z ∧
      (C.net (m + 1)).fcl ((C.net m).nch s :: s) = ((C.net m).st s).l ∧
      (C.net (m + 1)).fimg ((C.net m).nch s :: s) = (· + 2) ∧
      (C.net (m + 1)).bcl ((C.net m).nch s :: s) = bclD A Xe ∧
      (C.net (m + 1)).bimg ((C.net m).nch s :: s) = backImgD y o ∧
      liftBodyXDR ((C.net m).st s).l A Xe ((ctxOf_le_of_suffix hsuf).ref hX)
        (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ) ∈
          (retChildXDC hS ((ctxOf_le_of_suffix hsuf).ref hy) ((ctxOf_le_of_suffix hsuf).ref hz)
            ((ctxOf_le_of_suffix hsuf).ref hX)
            (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ)).M := by
  obtain ⟨m, hnm, hstep⟩ := C.retXDOp s ⟨_, A, Xe, x, (y, o, z), Ξ⟩ n
  have hlm := C.live_mono hnm hs
  have hsuf := C.lang_suffix hnm hs
  have hg := (C.ext hnm).grows s hs
  have hM := (C.good m).mcs s hlm
  have hy' := (ctxOf_le_of_suffix hsuf).ref hy
  have ho' := (ctxOf_le_of_suffix hsuf).ref ho
  have hz' := (ctxOf_le_of_suffix hsuf).ref hz
  have hX' := (ctxOf_le_of_suffix hsuf).ref hX
  have hin : WFF.retxS hS x ⟨X, hX'⟩ (.wit (bornShape A) Xe) (unarrDT (σ := σ) hy' hz').2
      (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ) ∈
        ((C.net m).st s).M := by
    rw [← mono_retXD_oblC hsuf hy hz hX Ξ]
    exact hg.sub _ h
  have hst : C.net (m + 1) = (C.net m).newChild s (some (x, X)) (((C.net m).st s).l.length + 2)
      (retChildXDC hS hy' hz' hX'
        (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ))
      (· + 2) (bclD A Xe) (backImgD y o) (some (.root (.free 1), Xe)) z := by
    rw [hstep hlm]
    simp only [NetSt.mkRetXDC, dif_pos hsuf, dif_pos hy', if_pos ho', dif_pos hz', if_pos hyo]
    split
    · rename_i X'' hX''
      obtain rfl : X'' = X := by
        rw [hX'] at hX''
        exact (VarType.VTypeDia.inj (Option.some.inj hX'')).symm
      rw [if_pos hin]
    · rename_i hne
      exact absurd hX' (hne X)
  refine ⟨m, hnm, hsuf, NetSt.not_live_new s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hst]
    exact (NetSt.live_newChild hlm _ _ _ _).mpr (Or.inr rfl)
  all_goals first
    | (rw [hst]; exact Function.update_self _ _ _)
    | skip
  exact retChildXDC_body hS hy' hz' hX' hM hin

/-- ⭐⭐**A doubly witnessed child at the limit**: a doubly witnessed obligation along `x` at a
    stage of `s` has a witness edge `s → t` for `x` whose way home is a witness edge for `t`'s
    root `e`, sending `t`'s root `c` to `y`, with content `z`, and the obligation's body read
    along the edge at `⟨c, e⟩` (`StrongChain.ret_childXDC`). -/
theorem lretXDC (s : LW C.toFairChain) (i : ℕ) {A Xe : VarType} {y o z : ℕ}
    (hy : (ctxOf (lat s i)).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (ho : (ctxOf (lat s i)).ref (.root (.free o)) = some .VTypeOne)
    (hz : (ctxOf (lat s i)).ref (.root (.free z)) = some Xe) (hyo : y ≠ o) {x : VarSymb}
    {X : VarType} (hX : (ctxOf (lat s i)).ref x = some (.VTypeDia X))
    (Ξ : WFF σ (((ctxOf (lat s i)).diaIn x).insert (.bnd 0) (RShape.wit (bornShape A) Xe).ty) 1)
    (h : WFF.retxS hS x ⟨X, hX⟩ (.wit (bornShape A) Xe) (unarrDT (σ := σ) hy hz).2 Ξ ∈
      ((C.net (birth C.toFairChain s.2 + i)).st s.1).M) :
    ∃ (t : LW C.toFairChain) (hk : lkd C.toFairChain s t = some (x, X))
      (_ : lkd C.toFairChain t s = some (.root (.free 1), Xe))
      (hcl : bclD A Xe <:+ lat t (lstg C.toFairChain s t i)),
      limg C.toFairChain t s 0 = y ∧ lcx C.toFairChain t s = z ∧
      readArrowX (limgOk C.toFairChain (lkdR hk) i) hX (lhcx C.toFairChain hk i)
        (Term.pair (Term.eta (.root (.free 0)) (.VTypeBox A)
            ((ctxOf_le_of_suffix hcl).ref (bclD_c A Xe)))
          (Term.eta (.root (.free 1)) (.VTypeDia Xe)
            ((ctxOf_le_of_suffix hcl).ref (bclD_e A Xe)))) Ξ ∈
          ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1).M := by
  classical
  obtain ⟨m, _, hsuf, hnot, hlive, hst, hkind, hcxe, hbk, hbcx, hfcl, hfimg, hbcl, hbimg,
    hmem⟩ := C.ret_childXDC (live_birth C.toFairChain s.2 (Nat.le_add_right _ i)) hy ho hz hyo
      hX Ξ h
  let t : LW C.toFairChain := ⟨(C.net m).nch s.1 :: s.1, m + 1, hlive⟩
  have hc : t.1 = (C.net m).nch s.1 :: s.1 := rfl
  have hbt : m < birth C.toFairChain t.2 := le_birth C.toFairChain t.2 hnot
  have hbt' : birth C.toFairChain t.2 ≤ m + 1 := birth_le t.2 hlive
  have hnb : ¬ ∃ c, s.1 = c :: t.1 := not_fwd_of_back (C := C.toFairChain) (t := s) hc
  have hkd : lkd C.toFairChain s t = some (x, X) := by
    rw [lkd, if_pos ⟨_, hc⟩, ← kind_at C.toFairChain t hbt']
    exact hkind
  have hlcx : lcx C.toFairChain s t = ((C.net m).st s.1).l.length + 2 := by
    rw [lcx, if_pos ⟨_, hc⟩]
    exact (cx_at C.toFairChain t hbt').symm.trans hcxe
  have hkdb : lkd C.toFairChain t s = some (.root (.free 1), Xe) := by
    rw [lkd, if_neg hnb, if_pos ⟨_, hc⟩, ← bkind_at C.toFairChain t hbt']
    exact hbk
  have hlcxb : lcx C.toFairChain t s = z := by
    rw [lcx, if_neg hnb]
    exact (bcx_at C.toFairChain t hbt').symm.trans hbcx
  have hg : Grows ((C.net (m + 1)).st ((C.net m).nch s.1 :: s.1))
      ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1) :=
    (C.ext (by omega)).grows t.1 hlive
  rw [hst] at hg
  have hcl : bclD A Xe <:+ lat t (lstg C.toFairChain s t i) :=
    (rclXD_suffix _ A X Xe).trans hg.suf
  refine ⟨t, hkd, hkdb, hcl, ?_, hlcxb, ?_⟩
  · rw [limg, if_neg hnb, bimgL_eq C.toFairChain hlive (by rw [hbcl]; simp), hbimg]
    rfl
  · have hm := hg.sub _ hmem
    have hag : ∀ r < (lat s i).length, r + 2 = limg C.toFairChain s t r := fun r hr => by
      have hlen : r < ((C.net (m + 1)).fcl t.1).length := by
        rw [hc, hfcl]
        exact lt_of_lt_of_le hr hsuf.length_le
      rw [limg, if_pos ⟨_, hc⟩, fimgL_eq C.toFairChain hlive hlen, hfimg]
    have himg₀ : ImgOk (lat s i) (ctxOf (X :: rclD ((C.net m).st s.1).l A Xe)) (· + 2) :=
      (rclXDImg ((C.net m).st s.1).l A X Xe).suffix hsuf
    have e1 := readArrowX_mono_congr hsuf (Ctx.Le.refl _) himg₀ (rclXDImg _ A X Xe)
      (fun _ _ => rfl) hX ((ctxOf_le_of_suffix hsuf).ref hX) (rclXD_cx _ A X Xe)
      (rclXD_cx _ A X Xe) (Term.pair (Term.eta (σ := σ) (.root (.free 0)) (.VTypeBox A)
        (rclXD_c _ A X Xe)) (Term.eta (.root (.free 1)) (.VTypeDia Xe) (rclXD_e _ A X Xe))) Ξ
    rw [Term.mono_refl] at e1
    change WFF.mono _ (readArrowX (rclXDImg _ A X Xe) ((ctxOf_le_of_suffix hsuf).ref hX)
      (rclXD_cx _ A X Xe) (Term.pair (Term.eta (.root (.free 0)) (.VTypeBox A)
        (rclXD_c _ A X Xe)) (Term.eta (.root (.free 1)) (.VTypeDia Xe) (rclXD_e _ A X Xe))) _)
      ∈ _ at hm
    rw [← e1, WFF.mono_mono, readArrowX_mono_congr (List.suffix_refl _) _ himg₀
      (limgOk C.toFairChain (lkdR hkd) i) hag hX hX _ (hlcx ▸ lhcx C.toFairChain hkd i),
      WFF.mono_refl] at hm
    rw [readArrowX_cx _ _ hlcx _ (hlcx ▸ lhcx C.toFairChain hkd i)]
    refine (congrArg (· ∈ _) (readArrowX_sig _ _ _ ?_ Ξ)).mp hm
    change (⟨_, Term.pair (Term.mono _ (Term.eta _ _ _)) (Term.mono _ (Term.eta _ _ _))⟩ :
      Σ c, Term σ _ _ c) = _
    rw [Term.mono_eta, Term.mono_eta]

end Chain

/-! ## The limit -/

section LimitOut

variable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} {hS : ModalSys.BStrong = true}
  (C : StrongChain hS M₀)

/-- The stage an edge commits a stage at grows with it. -/
theorem lstg_mono {s t : LW C.toFairChain} (h : LR C.toFairChain s t) {i i' : ℕ}
    (hii : i ≤ i') : lstg C.toFairChain s t i ≤ lstg C.toFairChain s t i' := by
  classical
  have hP := lstg_spec C.toFairChain h i'
  have hP' : StgP C.toFairChain s t i (lstg C.toFairChain s t i') :=
    ⟨by have := hP.1; omega, le_trans (C.lang_suffix (by omega)
      (live_birth C.toFairChain s.2 (Nat.le_add_right _ i))).length_le hP.2⟩
  rw [lstg, dif_pos ⟨_, hP'⟩]
  exact Nat.find_min' _ hP'

/-- ⭐**An alias is `Ind` to its term**: its alias formulas at every later stage make the two
    interchangeable there (`alias_interch`), so `DTerm.Rel`. -/
theorem lalias_ind (s : LW C.toFairChain) {i i₁ : ℕ}
    {A : VarType} {a : Ann A} (t : Term σ (ctxOf (lat s i)) A a) {l : List VarType}
    (hl : lat s i <:+ l)
    (hal : ∀ j, i₁ ≤ j → ∃ hsuf : (A :: l) <:+ lat s j, ∀ ψ,
      WFF.mono (ctxOf_le_of_suffix hsuf) (aliasFormula (Term.mono (ctxOf_le_of_suffix hl) t) ψ)
        ∈ ((C.net (birth C.toFairChain s.2 + j)).st s.1).M)
    (hy₁ : (ctxOf (lat s i₁)).ref (.root (.free l.length)) = some A) :
    (bdataS C).Ind
      ((bdataS C).toDom A s ((bdataS C).rden s i₁ (Ctx.Le.refl _)
        (Term.eta (.root (.free l.length)) A hy₁)) (BData.definable_rden _ _))
      ((bdataS C).toDom A s ((bdataS C).rden s i (Ctx.Le.refl _) t)
        (BData.definable_rden _ _)) := by
  refine ⟨⟨i₁, _, Term.eta (.root (.free l.length)) A hy₁⟩, ⟨i, a, t⟩,
    (BData.fromDom_toDom _ _ _ _ _).symm, (BData.fromDom_toDom _ _ _ _ _).symm, fun j h h' φ => ?_⟩
  obtain ⟨hsufj, halj⟩ := hal j h
  have hi := alias_interch hsufj ((C.good _).mcs s.1
    (live_birth C.toFairChain s.2 (Nat.le_add_right _ j))) (Term.mono (ctxOf_le_of_suffix hl) t)
    halj φ
  rw [Term.mono_eta, Term.mono_mono, Term.mono_mono] at hi
  rw [BWorld.mem_T, BWorld.mem_T]
  change WFF.instantiate _ (Term.mono _ (Term.eta _ A hy₁)) φ ∈ _ ↔
    WFF.instantiate _ (Term.mono _ t) φ ∈ _
  rw [Term.mono_eta]
  exact hi

end LimitOut

/-! ## Terms of `□` and product types -/

section Products

omit [ModalSys.NoFour] in
theorem exists_boxtm {Γ : Ctx} {A : VarType} {c : Ann (.VTypeBox A)}
    (x : Term σ Γ (.VTypeBox A) c) :
    ∃ (b : Ann A) (s : Term σ Γ.boxIn A b), (⟨c, x⟩ : Σ e, Term σ Γ (.VTypeBox A) e) =
      ⟨_, Term.boxtm s⟩ := by
  cases x with
  | boxtm s => exact ⟨_, s, rfl⟩

/-- Reading a necessary pair's first item. -/
theorem holeAt_box_fst {Γ : Ctx} {A B : VarType} {a : Ann A} {b : Ann B}
    (s : Term σ Γ.boxIn A a) (t : Term σ Γ.boxIn B b) (h : _) :
    (⟨_, Term.holeAt (Term.boxtm (Term.pair s t))
        (Term.boxtm (Term.eta (.step (VarSymb.root (.bnd 0)).inner .fst) A h))⟩ :
      Σ e, Term σ Γ (.VTypeBox A) e) = ⟨_, Term.boxtm s⟩ := by
  refine sig_boxtm (Term.subst_eta_tm _ _ _ _ _ _ s ?_)
  rw [Subst.at_proj _ _ rfl, Subst.box_at_inner_boxtm _ (by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl)]
  rfl

/-- Reading a necessary pair's second item. -/
theorem holeAt_box_snd {Γ : Ctx} {A B : VarType} {a : Ann A} {b : Ann B}
    (s : Term σ Γ.boxIn A a) (t : Term σ Γ.boxIn B b) (h : _) :
    (⟨_, Term.holeAt (Term.boxtm (Term.pair s t))
        (Term.boxtm (Term.eta (.step (VarSymb.root (.bnd 0)).inner .snd) B h))⟩ :
      Σ e, Term σ Γ (.VTypeBox B) e) = ⟨_, Term.boxtm t⟩ := by
  refine sig_boxtm (Term.subst_eta_tm _ _ _ _ _ _ t ?_)
  rw [Subst.at_proj _ _ rfl, Subst.box_at_inner_boxtm _ (by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl)]
  rfl

omit [ModalSys.NoFour] in
/-- Every term of a product type is a pair. -/
theorem Term.exists_pair {Γ : Ctx} {A B : VarType} {c : Ann (.VTypeProd A B)}
    (g : Term σ Γ (.VTypeProd A B) c) :
    ∃ (a : Ann A) (b : Ann B) (t₁ : Term σ Γ A a) (t₂ : Term σ Γ B b),
      (⟨c, g⟩ : Σ e, Term σ Γ (.VTypeProd A B) e) = ⟨_, Term.pair t₁ t₂⟩ := by
  match g with
  | .pair t₁ t₂ => exact ⟨_, _, t₁, t₂, rfl⟩

end Products

/-! ## Products, semantically -/

namespace BData

variable {B : BData σ}

/-- A representative of an object is one of the value under a hole term, filled (as
    `BData.rden_holeAt`). -/
theorem rden_holeAt_ret {s : B.W} {A : VarType} {o : B.model.frame.Dom A s}
    (u : Canon.DTerm (B.w s).sys (B.w s).T A)
    (hu : B.rden s u.i (Ctx.Le.refl _) u.t = B.fromDom A s o)
    {C : VarType} {c : Ann C} (hh : Term σ (Ctx.empty.insert (.bnd 0) A) C c) :
    B.rden s u.i (Ctx.Le.refl _) (Term.holeAt u.t hh) = B.fromDom C s (B.model.holeVal hh o) := by
  have e1 := interp_canon (Term.holeAt u.t hh) (env := B.canonEnv s u.i)
    (e := Ctx.Le.refl _) (fun _ _ _ => rfl)
  have e2 : Model.interp (B.canonEnv s u.i) u.t = o := by
    rw [interp_canon u.t (env := B.canonEnv s u.i) (e := Ctx.Le.refl _) (fun _ _ _ => rfl)]
    exact (B.toDom_congr hu _ _).trans (B.toDom_fromDom A s o)
  rw [Model.interp_holeAt, e2] at e1
  rw [e1, B.fromDom_toDom]

/-- Canonical `Ind` is a congruence for hole terms (as `BData.indInvariant`'s `map`). -/
theorem ind_map {s : B.W} {A C : VarType} {c : Ann C}
    (hh : Term σ (Ctx.empty.insert (.bnd 0) A) C c) {o o' : B.frame.Dom A s}
    (h : B.Ind o o') : B.Ind (B.model.holeVal hh o) (B.model.holeVal hh o') := by
  obtain ⟨u, u', hu, hu', hrel⟩ := h
  exact ⟨⟨u.i, _, Term.holeAt u.t hh⟩, ⟨u'.i, _, Term.holeAt u'.t hh⟩, rden_holeAt_ret u hu hh,
    rden_holeAt_ret u' hu' hh, hrel.holeAt hh⟩

/-- A necessary pair's first item, read along an arrow. -/
theorem necEval_boxFst {k : B.W} {X Y : VarType}
    (E : B.model.frame.Dom (.VTypeBox (.VTypeProd X Y)) k) (acc : B.model.frame.Acc k) (h : _) :
    B.model.necEval (B.model.holeVal (Term.boxtm (Term.eta (σ := σ)
        (.step (VarSymb.root (.bnd 0)).inner .fst) X h)) E : B.model.frame.Nec X k) acc =
      (B.model.necEval (E : B.model.frame.Nec (.VTypeProd X Y) k) acc).1 := by
  have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox (.VTypeProd X Y))
  unfold Model.holeVal
  rw [Model.box_beta, Model.interp_eta, Model.Env.ref_fst _ (Ctx.ref_inner hu) h,
    Model.Env.ref_inner _ _ hu]
  have he : ((Model.Env.empty (M := B.model) k).extend (.bnd 0) E).ref (.root (.bnd 0)) hu = E :=
    Model.Env.extend_root _ _ _ _
  rw [he]

/-- A necessary pair's second item, read along an arrow. -/
theorem necEval_boxSnd {k : B.W} {X Y : VarType}
    (E : B.model.frame.Dom (.VTypeBox (.VTypeProd X Y)) k) (acc : B.model.frame.Acc k) (h : _) :
    B.model.necEval (B.model.holeVal (Term.boxtm (Term.eta (σ := σ)
        (.step (VarSymb.root (.bnd 0)).inner .snd) Y h)) E : B.model.frame.Nec Y k) acc =
      (B.model.necEval (E : B.model.frame.Nec (.VTypeProd X Y) k) acc).2 := by
  have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox (.VTypeProd X Y))
  unfold Model.holeVal
  rw [Model.box_beta, Model.interp_eta, Model.Env.ref_snd _ (Ctx.ref_inner hu) h,
    Model.Env.ref_inner _ _ hu]
  have he : ((Model.Env.empty (M := B.model) k).extend (.bnd 0) E).ref (.root (.bnd 0)) hu = E :=
    Model.Env.extend_root _ _ _ _
  rw [he]

/-- ⭐**A canonical witness variable's possible object comes back** along the witness edge home:
    the way home is in its extent, with content the edge's content variable (`dia_beta`,
    `diaPush_canon_at`). -/
theorem posEval_eta_home {k s : B.W} {j : ℕ} {e : VarSymb} {Z : VarType}
    (he : ((B.w k).ctx j).ref e = some (.VTypeDia Z)) (hk : B.kd k s = some (e, Z))
    {o : B.model.frame.Dom Z s}
    (hI : B.Ind (B.toDom Z s (B.rden s (B.stg k s j) (Ctx.Le.refl _)
      (Term.eta (.root (.free (B.cx k s e))) Z (B.hcx hk j))) (definable_rden _ _)) o) :
    ∃ h : (⟨s, ⟨Or.inl (B.kdR hk)⟩⟩ : B.model.frame.Acc k) ∈ (B.model.posEval
        (Model.interp (B.canonEnv k j) (Term.eta e (.VTypeDia Z) he) :
          B.model.frame.Pos Z k)).1,
      B.Ind ((B.model.posEval (Model.interp (B.canonEnv k j) (Term.eta e (.VTypeDia Z) he) :
        B.model.frame.Pos Z k)).2 ⟨_, h⟩) o := by
  have hD : B.model.posEval (Model.interp (B.canonEnv k j) (Term.eta e (.VTypeDia Z) he) :
      B.model.frame.Pos Z k) = ⟨_, fun w' => Model.interp ((B.canonEnv k j).diaPush e he w')
        (Term.eta (σ := σ) (.step e .dia) Z (Ctx.ref_diaIn_of he))⟩ :=
    Model.dia_beta _ ⟨Z, he⟩ he _
  generalize B.model.posEval (Model.interp (B.canonEnv k j) (Term.eta e (.VTypeDia Z) he) :
      B.model.frame.Pos Z k) = Q at hD ⊢
  subst hD
  have hmem : (⟨s, ⟨Or.inl (B.kdR hk)⟩⟩ : B.Acc k) ∈
      (B.model.posEval ((B.canonEnv k j).ref e he)).1 := by
    rw [canonEnv_extent k j he]
    exact Or.inl ⟨Z, B.kd_lb hk⟩
  refine ⟨hmem, ?_⟩
  dsimp only
  rw [diaPush_canon_at k j he ⟨_, hmem⟩ hk le_rfl,
    ← Model.interp_subst (ι := arrowXIdx (B.img k s) e (B.cx k s e)) _ _
      (coh_arrowXS ((B.imgOk (B.kdR hk) j).mono ((B.w s).le le_rfl)) he
        (((B.w s).le le_rfl).ref (B.hcx hk j)))]
  rw [← interp_canon_eta] at hI
  refine (congrArg (fun x => B.Ind x o) ?_).mpr hI
  refine congrArg (fun p : Σ b, Term σ ((B.w s).ctx (B.stg k s j)) Z b =>
    Model.interp (B.canonEnv s (B.stg k s j)) p.2) (Term.subst_eta_renAt _ _ _ Z _ _ _ _ ?_)
  change (if Step.isProj .dia then _ else _) = _
  rw [if_neg (by decide)]
  change (if e = e then _ else _) = _
  exact if_pos rfl

end BData

end BArrow

end V12M
