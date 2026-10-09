import QML.QML_v12m_BRetChildX
import QML.QML_v12m_RetKD

/-!
# QML v12m — strong B on the network: the back-witness child (T off)

The third kind of returning successor (docs §11.20): an atom `◇[d ↦ y; e ⇝ z] Φ` of a node, a
returning possibility at the witnessed shape `□C × ◇X`, gets a **back-witness child**: its way
home lies in the extent of its own root `e : ◇X`, with content `z` at the parent.  The child's
variables are `c : □A` (root 0) and `e : ◇X` (root 1), then the parent's at their `bc` types two
up (`rclD`).  The parent's roots are committed forward under `+ 2`; `c` back to `y` and `e` to a
unit root `o` (`(◇X).bc = 𝟙`).

* `retSeedD`: the atom's body read at the child (`liftBodyW`), and `¬Θ` for every
  `¬◇[d ↦ y; e ⇝ z] Θ` of the parent.
* ⭐`retSeedD_consistent`: by the K-law with a possible part (`Proof.retD_K_node`) and the
  pull-back into the parent's `□` view with the slot opened (`retPullD`: `c ↦ □(u.fst.box.fst.snd)`,
  `e ↦ u.snd`; ⭐`subst_retPullD_liftBodyW`).
* ⭐`RetData.retBirthD`: born with `RetInvX` out along `e` (`ret_unitD`, read at the child by
  `liftBodyW_unitBodyD`) and `RetInvW` home (by the seed).
* `NetSt.mkRetD`, ⭐`GoodS.mkRetD`, `Ext.mkRetD`: the network operation, with the back arrow's
  witness recorded in `bkind`.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## The back-witness child's variables -/

section Layout

variable (l : List VarType) (A X : VarType)

/-- The back-committed roots: `e : ◇X` and `c : □A` (the oldest). -/
abbrev bclD : List VarType := [.VTypeDia X, .VTypeBox A]

/-- The back-witness child's variables. -/
abbrev rclD : List VarType := l.map VarType.bc ++ bclD A X

theorem rootTy_rclD_zero : rootTy (rclD l A X) 0 = .VTypeBox A := by
  simp [rootTy]

theorem rootTy_rclD_one : rootTy (rclD l A X) 1 = .VTypeDia X := by
  simp [rootTy]

theorem rootTy_rclD_add (r : ℕ) : rootTy (rclD l A X) (r + 2) = rootTy (l.map VarType.bc) r := by
  simp [rootTy, List.getD_eq_getElem?_getD]

theorem length_rclD : (rclD l A X).length = l.length + 2 := by simp

theorem rclD_suffix : bclD A X <:+ rclD l A X := List.suffix_append _ _

/-- The parent's roots go two up in the child. -/
theorem rclDImg : ImgOk l (ctxOf (rclD l A X)) (· + 2) := by
  intro r hr
  change (ctxOf (rclD l A X)).ref (.root (.free (r + 2))) = _
  rw [Ctx.ref_nonproj _ rfl, ctxOf_root_lt (by rw [length_rclD]; omega), rootTy_rclD_add,
    rootTy_map_bc l r hr]

/-- The child's root `e`. -/
theorem bclD_e : (ctxOf (bclD A X)).ref (.root (.free 1)) = some (.VTypeDia X) :=
  ctxOf_ref_new (.VTypeDia X) [.VTypeBox A]

/-- The back images: `c ↦ y`, `e ↦ o`. -/
def backImgD (y o : ℕ) : ℕ → ℕ := fun r => if r = 0 then y else o

theorem backImgD_ok {y o : ℕ} (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (ho : (ctxOf l).ref (.root (.free o)) = some .VTypeOne) :
    ImgOk (bclD A X) (ctxOf l) (backImgD y o) := by
  intro r hr
  match r, hr with
  | 0, _ => exact hy
  | 1, _ => exact ho

end Layout

/-! ## Pulling the back-witness child back, with the slot opened -/

/-- The parent's `□` view with a witnessed body's slot opened at `u = l.length`. -/
abbrev pullCtxD (l : List VarType) (A X : VarType) : Ctx :=
  (ctxOf l).boxIn.insert (.free l.length) (RShape.wit (.box (bcT (bclD A X))) X).ty

/-- The object coming back, inside the opened slot. -/
theorem pullCtxD_ref_c (l : List VarType) (A X : VarType) :
    (pullCtxD l A X).boxIn.ref
      (.step (.step (VarSymb.step (.root (.free l.length)) .fst).inner .fst) .snd) =
      some (VarType.VTypeBox A).bc :=
  Ctx.ref_snd_of (Ctx.ref_fst_of (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))

/-- The opened slot's possible part. -/
theorem pullCtxD_ref_e (l : List VarType) (A X : VarType) :
    (pullCtxD l A X).ref (.step (.root (.free l.length)) .snd) = some (.VTypeDia X) :=
  Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)

variable [ModalSys.NoFour]

/-- ⭐Pulling the back-witness child back into the parent's `□` view with the slot opened at `u`:
    `c` goes to `□(u.fst.box.fst.snd)`, `e` to `u.snd`, and root `r + 2` to the tuple of root
    `r`'s items. -/
def retPullD (hT : ModalSys.T = false) (σ : Signature) (l : List VarType) (A X : VarType) :
    Subst σ (pullCtxD l A X) := fun v =>
  match v with
  | .root (.free 0) => .tm (Term.boxtm
      (Term.eta (.step (.step (VarSymb.step (.root (.free l.length)) .fst).inner .fst) .snd) A
        ((pullCtxD_ref_c l A X).trans (congrArg some (bc_box_noT hT A)))))
  | .root (.free 1) => .ren (.step (.root (.free l.length)) .snd)
  | .root (.free (r + 2)) =>
      if h : r < l.length then .tm (Term.mono (Ctx.le_insert (pullCtx_fresh l).root _)
        (tup (.root (.free r)) (rootTy l r) (by
          rw [Ctx.ref_nonproj _ rfl]; exact ctxOf_root_lt h)))
      else .hide
  | _ => .hide

/-- Where pulling back sends annotation indices: along the entry at the index's root. -/
def retPullDIdx (hT : ModalSys.T = false) (σ : Signature) (l : List VarType) (A X : VarType)
    (a : VarSymb) : VarSymb :=
  match a.rt with
  | .free r => (retPullD hT σ l A X (.root (.free r))).idxAlong a.path
  | .bnd _ => a

section PullD

variable (hT : ModalSys.T = false) (l : List VarType) (A X : VarType)

theorem retPullD_add {r : ℕ} (h : r < l.length) :
    retPullD hT σ l A X (.root (.free (r + 2))) = .tm (Term.mono
      (Ctx.le_insert (pullCtx_fresh l).root _) (tup (.root (.free r)) (rootTy l r) (by
          rw [Ctx.ref_nonproj _ rfl]; exact ctxOf_root_lt h))) :=
  dif_pos h

theorem ok_retPullD : Subst.Ok (ctxOf (rclD l A X)) (retPullD hT σ l A X) := by
  intro v T _ hv
  obtain ⟨r, rfl⟩ := ctxOf_decl hv
  have hr : r < (rclD l A X).length := by
    by_contra hge
    rw [(ctxOf_fresh (l := rclD l A X) (Nat.le_of_not_lt hge)) _ rfl] at hv
    cases hv
  rw [ctxOf_root_lt hr] at hv
  cases hv
  match r, hr with
  | 0, _ =>
      rw [rootTy_rclD_zero]
      rfl
  | 1, _ =>
      rw [rootTy_rclD_one]
      exact pullCtxD_ref_e l A X
  | r + 2, hr =>
      have hr' : r < l.length := by rw [length_rclD] at hr; omega
      rw [rootTy_rclD_add, rootTy_map_bc l r hr', retPullD_add hT l A X hr']
      rfl

theorem coh_retPullD :
    Subst.Coh (retPullDIdx hT σ l A X) (ctxOf (rclD l A X)) (retPullD hT σ l A X) := by
  refine Subst.coh_of (ok_retPullD hT l A X) ?_
  intro v T _ hv p
  obtain ⟨r, rfl⟩ := ctxOf_decl hv
  have hrt : ((VarSymb.root (.free r)).ext p).rt = .free r := VarSymb.ext_rt _ _
  rw [retPullDIdx, hrt, VarSymb.ext_path]
  rfl

/-- Pulling back along an encoded projection path from root `r + 2` reaches the tuple of the
    component. -/
theorem at_retPullD_tup : ∀ {u : VarSymb} {U : VarType} (hu : (ctxOf l).ref u = some U) (r : ℕ),
    u.rt = .free r →
      (retPullD hT σ l A X).at ((VarSymb.root (.free (r + 2))).ext (encPath u.path)) =
        .tm (Term.mono (Ctx.le_insert (pullCtx_fresh l).root _) (tup u U hu))
  | .root (.free r'), U, hu, r, hrt => by
      change Root.free r' = Root.free r at hrt
      cases hrt
      obtain ⟨r₀, e, hr', -⟩ := ref_rt hu
      cases e
      have hU := hu
      rw [Ctx.ref_nonproj _ rfl, ctxOf_root_lt hr'] at hU
      cases hU
      exact retPullD_add hT l A X hr'
  | .root (.bnd _), _, _, _, hrt => by cases hrt
  | .step u s, U, hu, r, hrt => by
      have hproj : s.isProj = true := (reach_ppath hu).1 s (by simp [VarSymb.path])
      have hu' := hu
      simp only [Ctx.ref, if_pos hproj] at hu'
      cases hU : (ctxOf l).ref u with
      | none => rw [hU] at hu'; cases hu'
      | some U' =>
          rw [hU] at hu'
          have ih := at_retPullD_tup hU r hrt
          change (retPullD hT σ l A X).at
            ((VarSymb.root (.free (r + 2))).ext (encPath (u.path ++ [s]))) = _
          rw [show encPath (u.path ++ [s]) = encPath u.path ++ [encStep s] from
            List.map_append, VarSymb.ext_step, Subst.at_proj _ _ (encStep_proj hproj), ih]
          exact proj_tupB_mono _ rfl hU hproj hu' hu

/-- An item of the parent's `□` view, sent along the child's arrow and pulled back, is itself. -/
theorem at_retPullD_item {w : VarSymb} {T : VarType} (hw : (ctxOf l).ref w = some (.VTypeBox T)) :
    (retPullD hT σ l A X).at (itemAt (imgRoot (· + 2) w.rt) w) =
      .tm (Term.eta (.step w .box) T ((Ctx.le_insert (pullCtx_fresh l).root _).ref
        (Ctx.ref_boxIn_of ModalSys.NoFour.keepOnly hw))) := by
  obtain ⟨r, hr, _, _⟩ := ref_rt hw
  rw [hr]
  change (retPullD hT σ l A X).at (itemAt (.free (r + 2)) w) = _
  rw [at_item_of_tupB_mono _ _ _ hw ModalSys.T rfl (at_retPullD_tup hT l A X hw r hr),
    Term.mono_eta]

/-- The witnessed slot's entry at the child, pulled back: the opened slot. -/
theorem subst_retPullD_entry :
    (⟨_, Term.subst (retPullDIdx hT σ l A X) (retPullD hT σ l A X) (ok_retPullD hT l A X)
        (coh_retPullD hT l A X) (Term.pair
          (Term.boxtm (Term.mono (ctxOf_le_of_suffix (rclD_suffix l A X)).boxIn
            (tupT (σ := σ) (bclD A X)).2))
          (Term.eta (.root (.free 1)) (.VTypeDia X)
            ((ctxOf_le_of_suffix (rclD_suffix l A X)).ref (bclD_e A X))))⟩ :
        Σ a, Term σ (pullCtxD l A X) (RShape.wit (.box (bcT (bclD A X))) X).ty a) =
      ⟨_, Term.eta (.root (.free l.length)) _ (Ctx.ref_insert_root _ _ _)⟩ := by
  have hs := Subst.box_at_inner_boxtm (retPullD hT σ l A X) (v := .root (.free 0)) rfl
  rw [VarSymb.inner_box ModalSys.NoFour.keepOnly] at hs
  refine sig_pair ?_ (Term.subst_eta_renAt _ _ _ _ _ _ _ (pullCtxD_ref_e l A X) rfl)
  refine sig_boxtm ?_
  rw [Term.subst_mono]
  change (⟨_, Term.pair (Term.subst _ _ _ _ (Term.mono _ (tupT (σ := σ) [.VTypeBox A]).2))
      (Term.subst _ _ _ _ (tup (.root (.free 1)) (.VTypeDia X) (ctxOf_ref_new _ _)))⟩ :
      Σ a, Term σ (pullCtxD l A X).boxIn (bcT (bclD A X)) a) =
    ⟨_, Term.pair (Term.pair Term.unit
      (Term.eta (.step (.step (VarSymb.step (.root (.free l.length)) .fst).inner .fst) .snd) _
        (pullCtxD_ref_c l A X))) Term.unit⟩
  refine sig_pair ?_ rfl
  rw [Term.subst_mono]
  exact sig_pair rfl (subst_tupB_box_noT hT _ _ _ (ctxOf_ref_new _ []) ModalSys.T rfl
    (pullCtxD_ref_c l A X) _ hs)

/-- ⭐**Pulling back opens the slot, for a back-witness child**: a witnessed body read at the
    child, pulled back, is the body with its slot opened at `u`. -/
theorem subst_retPullD_liftBodyW (Ξ : WFF σ (bodyCtxW (bclD A X) l X) 1) :
    WFF.subst (retPullDIdx hT σ l A X) (retPullD hT σ l A X) (ok_retPullD hT l A X)
        (coh_retPullD hT l A X) Ctx.NoSlots.slots Ctx.NoSlots.slots
        (liftBodyW (rclD_suffix l A X) (rclDImg l A X) (bclD_e A X) Ξ) =
      WFF.openFree l.length (pullCtx_fresh l) Ctx.NoSlots.slots Ξ := by
  unfold liftBodyW WFF.openFree
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Ξ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = (RShape.wit (.box (bcT (bclD A X))) X).ty := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    rw [Subst.toFree_root]
    dsimp only [Subst.comp]
    rw [Subst.set_root]
    dsimp only [SubE.comp]
    rw [subE_tm_sig (subst_retPullD_entry hT l A X)]
    exact .ren_eta _ _
  · obtain ⟨w, rfl, hw⟩ := bodyW_item hv hvr
    rw [Subst.toFree_ne _ _ _ _ hvr]
    dsimp only [Subst.comp]
    rw [Subst.set_ne _ _ hvr]
    change SubE.Sim T (((Subst.idRen _) (.step w .box)).mono _)
      ((retPullD hT σ l A X).at (itemAt (imgRoot (· + 2) w.rt) w))
    rw [at_retPullD_item hT l A X hw]
    exact .ren_eta _ _

end PullD

omit [ModalSys.NoFour] in
/-- A returning possibility at any shape whose body the `□` view refutes is absurd. -/
def Proof.retS_refute {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)}
    (hS : ModalSys.BStrong = true) (S : RShape) {a : Ann S.flat} (t : Term σ Γ S.flat a)
    (Ξ : WFF σ (Γ.boxIn.insert (.bnd 0) S.ty) 1)
    (q : Proof σ Γ.boxIn [] (WFF.neg (WFF.ex S.ty Ξ)))
    (p : Proof σ Γ Δ (WFF.retS hS S t Ξ)) : Proof σ Γ Δ .bot :=
  Proof.imp_elim (Proof.ret_diaS hS .nec t _ p)
    (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.K_box (Δ := []) q))

/-! ## The seed and its consistency -/

section Seed

variable (hS : ModalSys.BStrong = true) {l : List VarType} {A X : VarType} {y o z : ℕ}
  (himg : ImgOk (bclD A X) (ctxOf l) (backImgD y o))
  (hz : (ctxOf l).ref (.root (.free z)) = some X)

/-- ⭐The seed of the back-witness child of `◇[d ↦ y; e ⇝ z] Φ`: the atom's body, and `¬Θ` for
    every `¬◇[d ↦ y; e ⇝ z] Θ` of the parent, read at the child. -/
def retSeedD (M : Set (WFF σ (ctxOf l) 0)) (Φ : WFF σ (bodyCtxW (bclD A X) l X) 1) :
    Set (WFF σ (ctxOf (rclD l A X)) 0) :=
  {liftBodyW (rclD_suffix l A X) (rclDImg l A X) (bclD_e A X) Φ} ∪
    {φ | ∃ Θ, WFF.neg (WFF.retS hS (.wit (.box (bcT (bclD A X))) X)
        (Term.pair (tupImgT (bclD A X) (backImgD y o) himg).2 (Term.eta (.root (.free z)) X hz))
        Θ) ∈ M ∧
      φ = liftBodyW (rclD_suffix l A X) (rclDImg l A X) (bclD_e A X) (WFF.neg Θ)}

/-- Finitely many seed formulas reduce to one body with a witnessed returning possibility at the
    parent, by the K-law with a possible part. -/
theorem retSeedD_list {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.IsMCS M)
    {Φ : WFF σ (bodyCtxW (bclD A X) l X) 1}
    (hΦ : WFF.retS hS (.wit (.box (bcT (bclD A X))) X)
      (Term.pair (tupImgT (bclD A X) (backImgD y o) himg).2 (Term.eta (.root (.free z)) X hz))
      Φ ∈ M) :
    ∀ L : List (WFF σ (ctxOf (rclD l A X)) 0), (∀ δ ∈ L, δ ∈ retSeedD hS himg hz M Φ) →
      ∃ Ξ, WFF.retS hS (.wit (.box (bcT (bclD A X))) X)
          (Term.pair (tupImgT (bclD A X) (backImgD y o) himg).2
            (Term.eta (.root (.free z)) X hz)) Ξ ∈ M ∧
        Theory.Derives {liftBodyW (rclD_suffix l A X) (rclDImg l A X) (bclD_e A X) Ξ}
          (liftBodyW (rclD_suffix l A X) (rclDImg l A X) (bclD_e A X) Φ) ∧
        ∀ δ ∈ L, Theory.Derives
          {liftBodyW (rclD_suffix l A X) (rclDImg l A X) (bclD_e A X) Ξ} δ
  | [], _ => ⟨Φ, hΦ, Theory.Derives.of_mem rfl, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨Ξ₀, hΞ₀, hΦ₀, hL⟩ := retSeedD_list hM hΦ L
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      rcases h δ List.mem_cons_self with hδ | ⟨Θ, hΘ, rfl⟩
      · refine ⟨Ξ₀, hΞ₀, hΦ₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · rw [Set.mem_singleton_iff.mp hδ]
          exact hΦ₀
        · exact hL d hd
      · have hand : ∀ φ, Proof σ _
            [liftBodyW (rclD_suffix l A X) (rclDImg l A X) (bclD_e A X) (Ξ₀.and Θ.neg)] φ →
            Theory.Derives
              {liftBodyW (rclD_suffix l A X) (rclDImg l A X) (bclD_e A X) (Ξ₀.and Θ.neg)} φ :=
          fun φ p => ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; rfl, ⟨p⟩⟩
        have h₀ := hand _ (Proof.and_elim_l
          (ψ := liftBodyW (rclD_suffix l A X) (rclDImg l A X) (bclD_e A X) Θ.neg)
          (Proof.lookup List.mem_cons_self))
        have h₁ := hand _ (Proof.and_elim_r
          (φ := liftBodyW (rclD_suffix l A X) (rclDImg l A X) (bclD_e A X) Ξ₀)
          (Proof.lookup List.mem_cons_self))
        have htr : ∀ d, Theory.Derives
            {liftBodyW (rclD_suffix l A X) (rclDImg l A X) (bclD_e A X) Ξ₀} d →
            Theory.Derives
              {liftBodyW (rclD_suffix l A X) (rclDImg l A X) (bclD_e A X) (Ξ₀.and Θ.neg)} d :=
          fun d hd => Derives.trans (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact h₀) hd
        refine ⟨Ξ₀.and Θ.neg, hM.closed ⟨[_, _], fun x hx => ?_,
          ⟨Proof.retD_K_node hS _ Ξ₀ Θ (Proof.lookup List.mem_cons_self)
            (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩,
          htr _ hΦ₀, fun d hd => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hΞ₀
          · rw [List.mem_singleton.mp hx]; exact hΘ
        rcases List.mem_cons.mp hd with rfl | hd
        · exact h₁
        · exact htr d (hL d hd)

/-- ⭐**The back-witness child's seed is consistent** (T off): finitely many seed formulas reduce
    to one body `Ξ` with `◇[d ↦ y; e ⇝ z] Ξ` at the parent (`retSeedD_list`); a refutation of `Ξ`
    read at the child pulls back to one of `Ξ` with its slot opened
    (`subst_retPullD_liftBodyW`), against `◇∃⟨d, e⟩. Ξ` (`Proof.retS_refute`). -/
theorem retSeedD_consistent (hT : ModalSys.T = false) {M : Set (WFF σ (ctxOf l) 0)}
    (hM : Theory.IsMCS M) {Φ : WFF σ (bodyCtxW (bclD A X) l X) 1}
    (hΦ : WFF.retS hS (.wit (.box (bcT (bclD A X))) X)
      (Term.pair (tupImgT (bclD A X) (backImgD y o) himg).2 (Term.eta (.root (.free z)) X hz))
      Φ ∈ M) :
    Theory.Consistent (retSeedD hS himg hz M Φ) := by
  rintro ⟨L, hL, hp⟩
  obtain ⟨Ξ, hΞ, -, hder⟩ := retSeedD_list hS himg hz hM hΦ L hL
  obtain ⟨Δ, hΔ, ⟨p⟩⟩ := Derives.trans (fun x hx => hder x hx) ⟨L, fun x hx => hx, hp⟩
  have p' : Proof σ (ctxOf (rclD l A X))
      [liftBodyW (rclD_suffix l A X) (rclDImg l A X) (bclD_e A X) Ξ] .bot :=
    Proof.ofSubset (fun x hx => by
      rw [Set.mem_singleton_iff.mp (hΔ x hx)]; exact List.mem_cons_self) p
  haveI : (pullCtxD l A X).Presented :=
    Ctx.Presented.insertFree inferInstance _ (pullCtx_fresh l) _
  have q := Proof.subst p' (retPullD hT σ l A X) (ok_retPullD hT l A X) (coh_retPullD hT l A X)
    Ctx.NoSlots.slots
  simp only [List.map_cons, List.map_nil, subst_retPullD_liftBodyW] at q
  refine hM.1 ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hΞ,
    ⟨Proof.retS_refute hS _ _ Ξ ?_ (Proof.lookup List.mem_cons_self)⟩⟩
  refine Proof.imp_intro (Proof.ex_elim l.length _ (pullCtx_fresh l)
    (φ := WFF.openFree _ (pullCtx_fresh l) Ctx.NoSlots.slots Ξ) (ψ := .bot)
    (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
      (Proof.lookup List.mem_cons_self)) ?_)
  exact Proof.ofSubset (fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_self) q

end Seed

/-! ## The back-witness child, born with the invariants -/

section Birth

variable (hS : ModalSys.BStrong = true) {tp : NodeSt σ} {A X : VarType} {y o z : ℕ}
  (himg : ImgOk (bclD A X) (ctxOf tp.l) (backImgD y o))
  (hz : (ctxOf tp.l).ref (.root (.free z)) = some X)

/-- ⭐The back-witness child of the atom `◇[d ↦ y; e ⇝ z] Φ` of `tp`. -/
noncomputable def retChildD (Φ : WFF σ (bodyCtxW (bclD A X) tp.l X) 1) : NodeSt σ :=
  ⟨rclD tp.l A X, complete (retSeedD hS himg hz tp.M Φ)⟩

variable (hT : ModalSys.T = false) (hM : Theory.IsMCS tp.M)
  {Φ : WFF σ (bodyCtxW (bclD A X) tp.l X) 1}
  (hΦ : WFF.retS hS (.wit (.box (bcT (bclD A X))) X)
    (Term.pair (tupImgT (bclD A X) (backImgD y o) himg).2 (Term.eta (.root (.free z)) X hz))
    Φ ∈ tp.M)

include hT hM hΦ

theorem retChildD_spec : retSeedD hS himg hz tp.M Φ ⊆ (retChildD hS himg hz Φ).M ∧
    Theory.IsMCS (retChildD hS himg hz Φ).M :=
  complete_spec (retSeedD_consistent hS himg hz hT hM hΦ)

/-- ⭐**The way home at birth**, in `e`'s extent: a witnessed body true at the child is a
    witnessed returning possibility at the parent — or else the seed has its negation. -/
theorem retChildD_back :
    RetInvW hS (retChildD hS himg hz Φ) tp (bclD A X) (backImgD y o) tp.l (· + 2)
      (.root (.free 1)) X z := by
  obtain ⟨hsub, hmcs⟩ := retChildD_spec hS himg hz hT hM hΦ
  refine ⟨rclD_suffix tp.l A X, himg, List.suffix_refl _, rclDImg tp.l A X, bclD_e A X, hz,
    fun Θ hΘ => ?_⟩
  rw [WFF.mono_refl]
  by_contra hn
  have h₁ := hsub (Or.inr ⟨Θ, hM.neg_mem_iff.mpr hn, rfl⟩)
  refine hmcs.1 ⟨[_, _], fun x hx => ?_, ⟨Proof.imp_elim
    (φ := liftBodyW (rclD_suffix tp.l A X) (rclDImg tp.l A X) (bclD_e A X) Θ)
    (Proof.lookup List.mem_cons_self)
    (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁
  · rw [List.mem_singleton.mp hx]; exact hΘ

/-- ⭐**The forward arrow at birth**, along `e`: a body over `e`'s view true at the parent is the
    unit along the possible part read at the child (`liftBodyW_unitBodyD`); its negation at the far
    end would clash with the unit (`ret_unitD`, `retS_absurd`), so the seed has `¬¬U`. -/
theorem retChildD_fwd :
    RetInvX hS tp (retChildD hS himg hz Φ) tp.l (· + 2) (bclD A X) (backImgD y o)
      (.root (.free 1)) X z := by
  obtain ⟨hsub, hmcs⟩ := retChildD_spec hS himg hz hT hM hΦ
  refine ⟨List.suffix_refl _, rclDImg tp.l A X, rclD_suffix tp.l A X, himg, bclD_e A X, hz,
    fun Ψ hΨ => ?_⟩
  refine (congrArg (· ∈ (retChildD hS himg hz Φ).M) (liftBodyW_unitBodyD (rclD_suffix tp.l A X)
    (rclDImg tp.l A X) (bclD_e A X) hS Ψ)).mp ?_
  have hle := ctxOf_le_of_suffix (List.suffix_refl tp.l)
  have e : WFF.unitBodyD (Γ := ctxOf tp.l) hS (Term.mono hle.boxIn (tupT tp.l).2)
      (pack2X (.VTypeBox (bcT tp.l)) (bclD_e A X) Ψ) =
      WFF.unitBodyD (Γ := ctxOf tp.l) hS (tupT tp.l).2
        (pack2X (.VTypeBox (bcT tp.l)) (bclD_e A X) Ψ) := by
    rw [Term.mono_refl]
  have hU : WFF.neg (WFF.retS hS (.wit (.box (bcT (bclD A X))) X)
      (Term.pair (tupImgT (bclD A X) (backImgD y o) himg).2 (Term.eta (.root (.free z)) X hz))
      (WFF.neg (WFF.unitBodyD (Γ := ctxOf tp.l) hS (tupT tp.l).2
        (pack2X (.VTypeBox (bcT tp.l)) (bclD_e A X) Ψ)))) ∈ tp.M := by
    refine hM.neg_mem_iff.mpr fun hr => hM.1 ⟨[WFF.retS hS (.wit (.box (bcT (bclD A X))) X)
      (Term.pair (tupImgT (bclD A X) (backImgD y o) himg).2 (Term.eta (.root (.free z)) X hz))
      (WFF.neg (WFF.unitBodyD (Γ := ctxOf tp.l) hS (tupT tp.l).2
        (pack2X (.VTypeBox (bcT tp.l)) (bclD_e A X) Ψ))),
      liftBodyX (List.suffix_refl tp.l) himg (bclD_e A X) hz Ψ], fun x hx => ?_, ⟨?_⟩⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hr
      · rw [List.mem_singleton.mp hx]; exact hΨ
    refine Proof.retS_absurd hS _ _ _ (ctxOf_fresh (l := tp.l) le_rfl) (Proof.conv (by rw [e])
      (Proof.ret_unitD hS _ _ (Term.mono hle.boxIn (tupT tp.l).2) _
        (Proof.lookup List.mem_cons_self) ?_))
    exact Proof.conv (holeRead_tupImgT_pack2X himg (bclD_e A X) hz
      (Term.boxtm (Term.mono hle.boxIn (tupT tp.l).2)) Ψ).symm
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
  have h₁ := hsub (Or.inr ⟨_, hU, rfl⟩)
  exact hmcs.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact h₁,
    ⟨Proof.byContra (Proof.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.lookup List.mem_cons_self))⟩⟩

/-- ⭐**The back-witness child is born with the invariants**: `RetInvX` out along `e`, `RetInvW`
    home in `e`'s extent. -/
theorem RetData.retBirthD : RetData hS tp (retChildD hS himg hz Φ) none
    (some (.root (.free 1), X)) z tp.l (· + 2) (bclD A X) (backImgD y o) :=
  ⟨retChildD_fwd hS himg hz hT hM hΦ, retChildD_back hS himg hz hT hM hΦ⟩

end Birth

/-! ## The operation -/

namespace NetSt

/-- A returning-possibility obligation with a possible part: over a list of a node's variables,
    the types `A` and `X`, the alias `y`, a unit root `o`, the content `z`, and the atom's body. -/
abbrev RetOblD (σ : Signature) :=
  Σ l : List VarType, Σ A : VarType, Σ X : VarType,
    (ℕ × ℕ × ℕ) × WFF σ (bodyCtxW (bclD A X) l X) 1

open Classical in
/-- ⭐Give the node `s` the back-witness child of its atom `◇[d ↦ y; e ⇝ z] Φ`, if it has it. -/
noncomputable def mkRetD (hS : ModalSys.BStrong = true) (N : NetSt σ) (s : Node) :
    RetOblD σ → NetSt σ
  | ⟨l, A, X, (y, o, z), Φ⟩ =>
      if h : l <:+ (N.st s).l then
        if himg : ImgOk (bclD A X) (ctxOf (N.st s).l) (backImgD y o) then
          if hz : (ctxOf (N.st s).l).ref (.root (.free z)) = some X then
            if WFF.retS hS (.wit (.box (bcT (bclD A X))) X)
                (Term.pair (tupImgT (bclD A X) (backImgD y o) himg).2
                  (Term.eta (.root (.free z)) X hz))
                (WFF.mono ((ctxOf_le_of_suffix h).boxIn.insert (.bnd 0) _) Φ) ∈ (N.st s).M then
              N.newChild s none z
                (retChildD hS himg hz (WFF.mono ((ctxOf_le_of_suffix h).boxIn.insert (.bnd 0) _) Φ))
                (· + 2) (bclD A X) (backImgD y o) (some (.root (.free 1), X))
            else N
          else N
        else N
      else N

/-- ⭐The back-witness child keeps the invariants (T off). -/
theorem GoodS.mkRetD {hS : ModalSys.BStrong = true} (hT : ModalSys.T = false) {N : NetSt σ}
    (hN : N.GoodS hS) {s : Node} (hs : N.Live s) (o : RetOblD σ) :
    (N.mkRetD hS s o).GoodS hS := by
  obtain ⟨l, A, X, ⟨y, o, z⟩, Φ⟩ := o
  simp only [NetSt.mkRetD]
  split_ifs with h himg hz hΦ
  · exact hN.newChild hs (retChildD_spec hS himg hz hT (hN.mcs s hs) hΦ).2
      (RetData.retBirthD hS himg hz hT (hN.mcs s hs) hΦ)
  all_goals exact hN

theorem Ext.mkRetD {hS : ModalSys.BStrong = true} {N : NetSt σ} {s : Node} (hs : N.Live s)
    (o : RetOblD σ) : Ext N (N.mkRetD hS s o) := by
  obtain ⟨l, A, X, ⟨y, o, z⟩, Φ⟩ := o
  simp only [NetSt.mkRetD]
  split_ifs
  · exact Ext.newChild hs _ _ _ _ _ _ _
  all_goals exact Ext.refl N

end NetSt

end BArrow

end V12M
