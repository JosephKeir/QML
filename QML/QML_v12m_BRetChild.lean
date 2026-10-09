import QML.QML_v12m_BAlias
import QML.QML_v12m_RetK

/-!
# QML v12m — strong B on the network: the child of a returning possibility (T off)

A returning-possibility atom `◇[d ↦ V] Φ` of a node, valued at an alias `y` (`V` the one-root
tuple of `y`), gets a child whose oldest root `c : □A` comes back as `y` (docs §11.20).  The
child's variables are `c` and, one up, the parent's at their `bc` types (`rcl`): the parent's
roots are committed forward under `succ`, and `c` back to `y`.

* `retSeed`: the atom's body read at the child, and `¬Θ` for every `¬◇[d ↦ V] Θ` of the parent.
* ⭐`retSeed_consistent`: finitely many seed formulas reduce to one body `Ξ` with `◇[d ↦ V] Ξ` at
  the parent, by the K-law (`retSeed_list`); a refutation of `Ξ` read at the child pulls back into
  the parent's `□` view with the slot opened (`retPullS`, ⭐`subst_retPull_liftBody`), giving
  `□¬∃d. Ξ` against `◇∃d. Ξ` (`ret_dia`).
* ⭐`RetData.retBirth`: the child is born with the invariants both ways — back by the seed, forward
  by `ret_unit` and `liftBody_unitBody`.

Without T, `(□A).bc = A`, so `c`'s only item is the object coming back: the second component of
the opened slot (`retPullS`).  Under T, `c` also has an item here; that is left for later
(docs §11.20).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## The child's variables -/

section Layout

variable (l : List VarType) (A : VarType)

/-- The child's variables: the parent's at their `bc` types, after the root `c : □A` coming back
    (root 0, the oldest, so that it is the first committed back). -/
abbrev rcl : List VarType := l.map VarType.bc ++ [.VTypeBox A]

theorem rootTy_rcl_zero : rootTy (rcl l A) 0 = .VTypeBox A := by
  simp [rootTy]

theorem rootTy_rcl_succ (r : ℕ) : rootTy (rcl l A) (r + 1) = rootTy (l.map VarType.bc) r := by
  simp [rootTy, List.getD_eq_getElem?_getD]

theorem length_rcl : (rcl l A).length = l.length + 1 := by simp

theorem rcl_suffix : [VarType.VTypeBox A] <:+ rcl l A := List.suffix_append _ _

/-- The parent's roots go one up in the child. -/
theorem rclImg : ImgOk l (ctxOf (rcl l A)) Nat.succ := by
  intro r hr
  change (ctxOf (rcl l A)).ref (.root (.free (r + 1))) = _
  rw [Ctx.ref_nonproj _ rfl, ctxOf_root_lt (by rw [length_rcl]; omega), rootTy_rcl_succ,
    rootTy_map_bc l r hr]

/-- The root coming back goes to the alias `y`. -/
theorem retBackImg {y : ℕ} (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) :
    ImgOk [.VTypeBox A] (ctxOf l) (fun _ => y) := by
  intro r hr
  obtain rfl : r = 0 := by simpa using hr
  exact hy

end Layout

/-! ## Pulling the child back, with the slot opened -/

/-- A view `V` of the parent (its `□` view, or a witness's view) with a body's slot opened at
    `u = l.length`. -/
abbrev pullCtx (V : Ctx) (l : List VarType) (A : VarType) : Ctx :=
  V.insert (.free l.length) (.VTypeBox (bcT [.VTypeBox A]))

theorem pullCtx_fresh (l : List VarType) : (ctxOf l).boxIn.RootFresh (.free l.length) :=
  (ctxOf_fresh le_rfl).boxIn

theorem bc_box_noT (hT : ModalSys.T = false) (A : VarType) : (VarType.VTypeBox A).bc = A := by
  simp [VarType.bcB, hT]

/-- The opened slot's second component: the object coming back. -/
theorem pullCtx_ref_c (V : Ctx) (l : List VarType) (A : VarType) :
    (pullCtx V l A).boxIn.ref (.step (VarSymb.root (.free l.length)).inner .snd) =
      some (VarType.VTypeBox A).bc :=
  Ctx.ref_snd_of (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))

theorem subE_tm_sig {Δ : Ctx} {T : VarType} {a a' : Ann T} {s : Term σ Δ T a}
    {s' : Term σ Δ T a'} (h : (⟨a, s⟩ : Σ c, Term σ Δ T c) = ⟨a', s'⟩) :
    SubE.tm s = SubE.tm s' := by
  cases h
  rfl

variable [ModalSys.NoFour]

/-- ⭐Pulling a child back into a view `V` of the parent containing its `□` view, with the slot
    opened at `u`: `c` goes to the necessary object `□(u.snd)`, root `r + 1` to the tuple of root
    `r`'s items, and the root after those (a witness child's content) to `e`. -/
def retPullS (hT : ModalSys.T = false) (σ : Signature) (l : List VarType) (A : VarType)
    {V : Ctx} (hV : (ctxOf l).boxIn.Le V) (hu : V.RootFresh (.free l.length))
    (e : SubE σ (pullCtx V l A)) : Subst σ (pullCtx V l A) := fun v =>
  match v with
  | .root (.free 0) => .tm (Term.boxtm (Term.eta (.step (VarSymb.root (.free l.length)).inner .snd)
      A ((pullCtx_ref_c V l A).trans (congrArg some (bc_box_noT hT A)))))
  | .root (.free (r + 1)) =>
      if h : r < l.length then .tm (Term.mono (hV.trans (Ctx.le_insert hu.root _))
        (tup (.root (.free r)) (rootTy l r) (by
          rw [Ctx.ref_nonproj _ rfl]; exact ctxOf_root_lt h)))
      else if r = l.length then e else .hide
  | _ => .hide

/-- Where pulling back sends annotation indices: along the entry at the index's root. -/
def retPullIdx (hT : ModalSys.T = false) (σ : Signature) (l : List VarType) (A : VarType)
    {V : Ctx} (hV : (ctxOf l).boxIn.Le V) (hu : V.RootFresh (.free l.length))
    (e : SubE σ (pullCtx V l A)) (a : VarSymb) : VarSymb :=
  match a.rt with
  | .free r => (retPullS hT σ l A hV hu e (.root (.free r))).idxAlong a.path
  | .bnd _ => a

section Pull

variable (hT : ModalSys.T = false) (l : List VarType) (A : VarType) {V : Ctx}
  (hV : (ctxOf l).boxIn.Le V) (hu : V.RootFresh (.free l.length)) (e : SubE σ (pullCtx V l A))

theorem retPull_succ {r : ℕ} (h : r < l.length) :
    retPullS hT σ l A hV hu e (.root (.free (r + 1))) = .tm (Term.mono
      (hV.trans (Ctx.le_insert hu.root _)) (tup (.root (.free r)) (rootTy l r) (by
          rw [Ctx.ref_nonproj _ rfl]; exact ctxOf_root_lt h))) :=
  dif_pos h

theorem retPull_last : retPullS hT σ l A hV hu e (.root (.free (l.length + 1))) = e := by
  change (if h : l.length < l.length then _ else if l.length = l.length then _ else _) = _
  rw [dif_neg (lt_irrefl _), if_pos rfl]

/-- The entries at the roots of `rcl` are well typed, whatever `e` is. -/
theorem retPull_okRef {r : ℕ} (hr : r < (rcl l A).length) :
    (retPullS hT σ l A hV hu e (.root (.free r))).OkRef (rootTy (rcl l A) r) := by
  cases r with
  | zero =>
      rw [rootTy_rcl_zero]
      rfl
  | succ r =>
      have hr' : r < l.length := by rw [length_rcl] at hr; omega
      rw [rootTy_rcl_succ, rootTy_map_bc l r hr', retPull_succ hT l A hV hu e hr']
      rfl

theorem ok_retPullS : Subst.Ok (ctxOf (rcl l A)) (retPullS hT σ l A hV hu e) := by
  intro v T _ hv
  obtain ⟨r, rfl⟩ := ctxOf_decl hv
  have hr : r < (rcl l A).length := by
    by_contra hge
    rw [(ctxOf_fresh (l := rcl l A) (Nat.le_of_not_lt hge)) _ rfl] at hv
    cases hv
  rw [ctxOf_root_lt hr] at hv
  cases hv
  exact retPull_okRef hT l A hV hu e hr

/-- A witness child's content root, after the parent's, is pulled back to `e`, of its type. -/
theorem ok_retPullS_X {X : VarType} (he : e.OkRef X) :
    Subst.Ok (ctxOf (X :: rcl l A)) (retPullS hT σ l A hV hu e) := by
  intro v T _ hv
  obtain ⟨r, rfl⟩ := ctxOf_decl hv
  have hr : r < (rcl l A).length + 1 := by
    by_contra hge
    rw [(ctxOf_fresh (l := X :: rcl l A) (by simp only [List.length_cons]; omega)) _ rfl] at hv
    cases hv
  rw [ctxOf_root_lt (by simp only [List.length_cons]; omega)] at hv
  cases hv
  by_cases hlt : r < (rcl l A).length
  · rw [rootTy_old hlt]
    exact retPull_okRef hT l A hV hu e hlt
  · obtain rfl : r = (rcl l A).length := by omega
    rw [rootTy_new, length_rcl, retPull_last]
    exact he

theorem coh_retPullS_of {kl : List VarType}
    (hok : Subst.Ok (ctxOf kl) (retPullS hT σ l A hV hu e)) :
    Subst.Coh (retPullIdx hT σ l A hV hu e) (ctxOf kl) (retPullS hT σ l A hV hu e) := by
  refine Subst.coh_of hok ?_
  intro v T _ hv p
  obtain ⟨r, rfl⟩ := ctxOf_decl hv
  have hrt : ((VarSymb.root (.free r)).ext p).rt = .free r := VarSymb.ext_rt _ _
  rw [retPullIdx, hrt, VarSymb.ext_path]
  rfl

/-- Pulling back along an encoded projection path from root `r + 1` reaches the tuple of the
    component (`at_pull_tup`, one up and weakened). -/
theorem at_retPull_tup : ∀ {u : VarSymb} {U : VarType} (hu' : (ctxOf l).ref u = some U) (r : ℕ),
    u.rt = .free r →
      (retPullS hT σ l A hV hu e).at ((VarSymb.root (.free (r + 1))).ext (encPath u.path)) =
        .tm (Term.mono (hV.trans (Ctx.le_insert hu.root _)) (tup u U hu'))
  | .root (.free r'), U, hu', r, hrt => by
      change Root.free r' = Root.free r at hrt
      cases hrt
      obtain ⟨r₀, e', hr', -⟩ := ref_rt hu'
      cases e'
      have hU := hu'
      rw [Ctx.ref_nonproj _ rfl, ctxOf_root_lt hr'] at hU
      cases hU
      exact retPull_succ hT l A hV hu e hr'
  | .root (.bnd _), _, _, _, hrt => by cases hrt
  | .step u s, U, hu', r, hrt => by
      have hproj : s.isProj = true := (reach_ppath hu').1 s (by simp [VarSymb.path])
      have hu'' := hu'
      simp only [Ctx.ref, if_pos hproj] at hu''
      cases hU : (ctxOf l).ref u with
      | none => rw [hU] at hu''; cases hu''
      | some U' =>
          rw [hU] at hu''
          have ih := at_retPull_tup hU r hrt
          change (retPullS hT σ l A hV hu e).at
            ((VarSymb.root (.free (r + 1))).ext (encPath (u.path ++ [s]))) = _
          rw [show encPath (u.path ++ [s]) = encPath u.path ++ [encStep s] from
            List.map_append, VarSymb.ext_step, Subst.at_proj _ _ (encStep_proj hproj), ih]
          exact proj_tupB_mono _ rfl hU hproj hu'' hu'

/-- An item of the parent's `□` view, sent along the child's arrow and pulled back, is itself. -/
theorem at_retPull_item {w : VarSymb} {T : VarType} (hw : (ctxOf l).ref w = some (.VTypeBox T)) :
    (retPullS hT σ l A hV hu e).at (itemAt (imgRoot Nat.succ w.rt) w) =
      .tm (Term.eta (.step w .box) T ((hV.trans (Ctx.le_insert hu.root _)).ref
        (Ctx.ref_boxIn_of ModalSys.NoFour.keepOnly hw))) := by
  obtain ⟨r, hr, _, _⟩ := ref_rt hw
  rw [hr]
  change (retPullS hT σ l A hV hu e).at (itemAt (.free (r + 1)) w) = _
  rw [at_item_of_tupB_mono _ _ _ hw ModalSys.T rfl (at_retPull_tup hT l A hV hu e hw r hr),
    Term.mono_eta]

end Pull

/-- Without T, the tuple of `c : □A` is its item, which a substitution sending `c` to `□s` sends
    to `s`. -/
theorem subst_tupB_box_noT (hT : ModalSys.T = false) {Γ Δ : Ctx} {ι : VarSymb → VarSymb}
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ.boxIn θ) (hc : Subst.Coh ι Γ.boxIn θ) {c : VarSymb}
    {A : VarType} (h : Γ.ref c = some (.VTypeBox A)) (b : Bool) (hb : ModalSys.T = b)
    {w : VarSymb} (hw : Δ.ref w = some ((VarType.VTypeBox A).bcB b))
    (hwA : Δ.ref w = some A) (hs : θ.at (.step c .box) = .tm (Term.eta w A hwA)) :
    (⟨_, Term.subst ι θ hθ hc (tupB c (.VTypeBox A) b hb h)⟩ :
        Σ a, Term σ Δ ((VarType.VTypeBox A).bcB b) a) = ⟨_, Term.eta w _ hw⟩ := by
  cases b with
  | true => exact absurd (hb.symm.trans hT) (by decide)
  | false => exact Term.subst_eta_tm θ hθ hc A _ _ _ hs

section Pull

variable (hT : ModalSys.T = false) (l : List VarType) (A : VarType) {V : Ctx}
  (hV : (ctxOf l).boxIn.Le V) (hu : V.RootFresh (.free l.length)) (e : SubE σ (pullCtx V l A))

/-- The necessary object holding `c`'s item, pulled back: the opened slot. -/
theorem subst_retPull_entry {kl : List VarType} (hs : [VarType.VTypeBox A] <:+ kl)
    (hθ : Subst.Ok (ctxOf kl) (retPullS hT σ l A hV hu e))
    (hc : Subst.Coh (retPullIdx hT σ l A hV hu e) (ctxOf kl) (retPullS hT σ l A hV hu e)) :
    (⟨_, Term.subst (retPullIdx hT σ l A hV hu e) (retPullS hT σ l A hV hu e) hθ hc
        (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn
          (tupT (σ := σ) [.VTypeBox A]).2))⟩ :
        Σ a, Term σ (pullCtx V l A) (.VTypeBox (bcT [.VTypeBox A])) a) =
      ⟨_, Term.eta (.root (.free l.length)) _ (Ctx.ref_insert_root _ _ _)⟩ := by
  have hs' := Subst.box_at_inner_boxtm (retPullS hT σ l A hV hu e) (v := .root (.free 0)) rfl
  rw [VarSymb.inner_box ModalSys.NoFour.keepOnly] at hs'
  change (⟨_, Term.boxtm (Term.subst _ _ _ _ (Term.mono _ _))⟩ :
      Σ a, Term σ (pullCtx V l A) (.VTypeBox (bcT [.VTypeBox A])) a) =
    ⟨_, Term.boxtm (Term.pair Term.unit
      (Term.eta (.step (VarSymb.root (.free l.length)).inner .snd) _ (pullCtx_ref_c V l A)))⟩
  rw [Term.subst_mono]
  exact sig_boxtm (sig_pair rfl (subst_tupB_box_noT hT _ _ _ (ctxOf_ref_new _ []) ModalSys.T rfl
    (pullCtx_ref_c V l A) _ hs'))

end Pull

/-- ⭐**Pulling back opens the slot**: a body read at the child, pulled back into the parent's `□`
    view, is the body with its slot opened at `u` — its items go back to the parent's items
    (`at_retPull_item`), and the necessary object holding `c`'s item to the slot
    (`subst_retPull_entry`). -/
theorem subst_retPull_liftBody (hT : ModalSys.T = false) (l : List VarType) (A : VarType)
    (Ξ : WFF σ (bodyCtx [.VTypeBox A] l) 1) :
    WFF.subst (retPullIdx hT σ l A (Ctx.Le.refl _) (pullCtx_fresh l) .hide)
        (retPullS hT σ l A (Ctx.Le.refl _) (pullCtx_fresh l) .hide)
        (ok_retPullS hT l A _ _ _) (coh_retPullS_of hT l A _ _ _ (ok_retPullS hT l A _ _ _))
        Ctx.NoSlots.slots Ctx.NoSlots.slots (liftBody (rcl_suffix l A) (rclImg l A) Ξ) =
      WFF.openFree l.length (pullCtx_fresh l) Ctx.NoSlots.slots Ξ := by
  unfold liftBody WFF.openFree
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Ξ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = .VTypeBox (bcT [.VTypeBox A]) := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    rw [Subst.toFree_root]
    dsimp only [Subst.comp]
    rw [Subst.set_root]
    dsimp only [SubE.comp]
    rw [subE_tm_sig (subst_retPull_entry hT l A _ _ _ (rcl_suffix l A) _ _)]
    exact .ren_eta _ _
  · obtain ⟨w, rfl, hw⟩ := body_item hlp hv hvr
    rw [Subst.toFree_ne _ _ _ _ hvr]
    dsimp only [Subst.comp]
    rw [Subst.set_ne _ _ hvr]
    change SubE.Sim T (((Subst.idRen _) (.step w .box)).mono _)
      ((retPullS hT σ l A (Ctx.Le.refl _) (pullCtx_fresh l) .hide).at
        (itemAt (imgRoot Nat.succ w.rt) w))
    rw [at_retPull_item hT l A _ _ _ hw]
    exact .ren_eta _ _

/-! ## The K-law at a node, and refuting a returning possibility -/

/-- At a node every body is a hole formula at the roots' items and the slot (`pack2`). -/
theorem kPsi_pack2 {l : List VarType} {B : VarType}
    (Θ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox B)) 1) :
    kPsi (Γ := ctxOf l) (tupT l).2 (pack2 l (.VTypeBox B) Θ) = Θ :=
  (holeAt_tupT_pack2 (Ctx.Le.refl _) Θ).trans (WFF.mono_refl _ Θ)

/-- ⭐**The K-law at a node**: `◇[d ↦ t] Φ, ¬◇[d ↦ t] Θ ⊢ ◇[d ↦ t](Φ ∧ ¬Θ)`, for any body. -/
def Proof.ret_K_node (hS : ModalSys.BStrong = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)} {B : VarType} {b : Ann B} (t : Term σ (ctxOf l) B b)
    (Φ Θ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox B)) 1)
    (p : Proof σ (ctxOf l) Δ (WFF.ret hS t Φ))
    (q : Proof σ (ctxOf l) Δ (WFF.neg (WFF.ret hS t Θ))) :
    Proof σ (ctxOf l) Δ (WFF.ret hS t (WFF.and Φ (WFF.neg Θ))) :=
  Proof.conv (by rw [kPsi_pack2]) (Proof.ret_K hS t Φ (tupT l).2 (pack2 l (.VTypeBox B) Θ) p
    (Proof.conv (by rw [kPsi_pack2]) q))

omit [ModalSys.NoFour] in
/-- A returning possibility whose body the `□` view refutes is absurd (`ret_dia`). -/
def Proof.ret_refute {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)}
    (hS : ModalSys.BStrong = true) {B : VarType} {b : Ann B} (t : Term σ Γ B b)
    (Ξ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox B)) 1)
    (q : Proof σ Γ.boxIn [] (WFF.neg (WFF.ex (.VTypeBox B) Ξ)))
    (p : Proof σ Γ Δ (WFF.ret hS t Ξ)) : Proof σ Γ Δ .bot :=
  Proof.imp_elim (Proof.ret_dia hS .nec t _ p)
    (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.K_box (Δ := []) q))

/-! ## The seed and its consistency -/

section Seed

variable (hS : ModalSys.BStrong = true) {l : List VarType} {A : VarType} {y : ℕ}
  (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)

/-- ⭐The seed of the child of `◇[d ↦ y] Φ`: the atom's body, and `¬Θ` for every `¬◇[d ↦ y] Θ`
    of the parent, read at the child. -/
def retSeed (M : Set (WFF σ (ctxOf l) 0)) (Φ : WFF σ (bodyCtx [.VTypeBox A] l) 1) :
    Set (WFF σ (ctxOf (rcl l A)) 0) :=
  {liftBody (rcl_suffix l A) (rclImg l A) Φ} ∪
    {φ | ∃ Θ, WFF.neg (WFF.ret hS (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg l A hy)).2 Θ)
      ∈ M ∧ φ = liftBody (rcl_suffix l A) (rclImg l A) (WFF.neg Θ)}

/-- Finitely many seed formulas reduce to one body with a returning possibility at the parent:
    the atom's body, with the negated bodies conjoined by the K-law. -/
theorem retSeed_list {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.IsMCS M)
    {Φ : WFF σ (bodyCtx [.VTypeBox A] l) 1}
    (hΦ : WFF.ret hS (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg l A hy)).2 Φ ∈ M) :
    ∀ L : List (WFF σ (ctxOf (rcl l A)) 0), (∀ δ ∈ L, δ ∈ retSeed hS hy M Φ) →
      ∃ Ξ, WFF.ret hS (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg l A hy)).2 Ξ ∈ M ∧
        Theory.Derives {liftBody (rcl_suffix l A) (rclImg l A) Ξ}
          (liftBody (rcl_suffix l A) (rclImg l A) Φ) ∧
        ∀ δ ∈ L, Theory.Derives {liftBody (rcl_suffix l A) (rclImg l A) Ξ} δ
  | [], _ => ⟨Φ, hΦ, Theory.Derives.of_mem rfl, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨Ξ₀, hΞ₀, hΦ₀, hL⟩ := retSeed_list hM hΦ L
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      rcases h δ List.mem_cons_self with hδ | ⟨Θ, hΘ, rfl⟩
      · refine ⟨Ξ₀, hΞ₀, hΦ₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · rw [Set.mem_singleton_iff.mp hδ]
          exact hΦ₀
        · exact hL d hd
      · have hand : ∀ φ, Proof σ _ [liftBody (rcl_suffix l A) (rclImg l A) (Ξ₀.and Θ.neg)] φ →
            Theory.Derives {liftBody (rcl_suffix l A) (rclImg l A) (Ξ₀.and Θ.neg)} φ :=
          fun φ p => ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; rfl, ⟨p⟩⟩
        have h₀ := hand _ (Proof.and_elim_l (ψ := liftBody (rcl_suffix l A) (rclImg l A) Θ.neg)
          (Proof.lookup List.mem_cons_self))
        have h₁ := hand _ (Proof.and_elim_r (φ := liftBody (rcl_suffix l A) (rclImg l A) Ξ₀)
          (Proof.lookup List.mem_cons_self))
        have htr : ∀ d, Theory.Derives {liftBody (rcl_suffix l A) (rclImg l A) Ξ₀} d →
            Theory.Derives {liftBody (rcl_suffix l A) (rclImg l A) (Ξ₀.and Θ.neg)} d :=
          fun d hd => Derives.trans (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact h₀) hd
        refine ⟨Ξ₀.and Θ.neg, hM.closed ⟨[_, _], fun x hx => ?_,
          ⟨Proof.ret_K_node hS _ Ξ₀ Θ (Proof.lookup List.mem_cons_self)
            (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩,
          htr _ hΦ₀, fun d hd => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hΞ₀
          · rw [List.mem_singleton.mp hx]; exact hΘ
        rcases List.mem_cons.mp hd with rfl | hd
        · exact h₁
        · exact htr d (hL d hd)

/-- ⭐**The seed is consistent** (T off): finitely many seed formulas reduce to one body `Ξ` with
    `◇[d ↦ y] Ξ` at the parent (`retSeed_list`); a refutation of `Ξ` read at the child pulls back
    to a refutation of `Ξ` with its slot opened (`subst_retPull_liftBody`), so `□¬∃d. Ξ` holds at
    the parent, against `◇∃d. Ξ` (`Proof.ret_refute`). -/
theorem retSeed_consistent (hT : ModalSys.T = false) {M : Set (WFF σ (ctxOf l) 0)}
    (hM : Theory.IsMCS M) {Φ : WFF σ (bodyCtx [.VTypeBox A] l) 1}
    (hΦ : WFF.ret hS (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg l A hy)).2 Φ ∈ M) :
    Theory.Consistent (retSeed hS hy M Φ) := by
  rintro ⟨L, hL, hp⟩
  obtain ⟨Ξ, hΞ, -, hder⟩ := retSeed_list hS hy hM hΦ L hL
  obtain ⟨Δ, hΔ, ⟨p⟩⟩ := Derives.trans (fun x hx => hder x hx) ⟨L, fun x hx => hx, hp⟩
  have p' : Proof σ (ctxOf (rcl l A)) [liftBody (rcl_suffix l A) (rclImg l A) Ξ] .bot :=
    Proof.ofSubset (fun x hx => by
      rw [Set.mem_singleton_iff.mp (hΔ x hx)]; exact List.mem_cons_self) p
  haveI : (pullCtx (ctxOf l).boxIn l A).Presented :=
    Ctx.Presented.insertFree inferInstance _ (pullCtx_fresh l) _
  have q := Proof.subst p' (retPullS hT σ l A (Ctx.Le.refl _) (pullCtx_fresh l) .hide)
    (ok_retPullS hT l A _ _ _) (coh_retPullS_of hT l A _ _ _ (ok_retPullS hT l A _ _ _))
    Ctx.NoSlots.slots
  simp only [List.map_cons, List.map_nil, subst_retPull_liftBody] at q
  refine hM.1 ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hΞ,
    ⟨Proof.ret_refute hS _ Ξ ?_ (Proof.lookup List.mem_cons_self)⟩⟩
  refine Proof.imp_intro (Proof.ex_elim l.length _ (pullCtx_fresh l)
    (φ := WFF.openFree _ (pullCtx_fresh l) Ctx.NoSlots.slots Ξ) (ψ := .bot)
    (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
      (Proof.lookup List.mem_cons_self)) ?_)
  exact Proof.ofSubset (fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_self) q

end Seed

/-! ## The child, born with the invariants -/

section Birth

variable (hS : ModalSys.BStrong = true) {tp : NodeSt σ} {A : VarType} {y : ℕ}
  (hy : (ctxOf tp.l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)

/-- ⭐The child of the atom `◇[d ↦ y] Φ` of `tp`. -/
noncomputable def retChild (Φ : WFF σ (bodyCtx [.VTypeBox A] tp.l) 1) : NodeSt σ :=
  ⟨rcl tp.l A, complete (retSeed hS hy tp.M Φ)⟩

variable (hT : ModalSys.T = false) (hM : Theory.IsMCS tp.M)
  {Φ : WFF σ (bodyCtx [.VTypeBox A] tp.l) 1}
  (hΦ : WFF.ret hS (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg tp.l A hy)).2 Φ ∈ tp.M)

include hT hM hΦ

theorem retChild_spec : retSeed hS hy tp.M Φ ⊆ (retChild hS hy Φ).M ∧
    Theory.IsMCS (retChild hS hy Φ).M :=
  complete_spec (retSeed_consistent hS hy hT hM hΦ)

/-- The child holds the atom's body. -/
theorem retChild_body :
    liftBody (rcl_suffix tp.l A) (rclImg tp.l A) Φ ∈ (retChild hS hy Φ).M :=
  (retChild_spec hS hy hT hM hΦ).1 (Or.inl rfl)

/-- ⭐**The back arrow at birth**: a body true at the child is a returning possibility at the
    parent — or else the seed has its negation. -/
theorem retChild_back :
    RetInv hS (retChild hS hy Φ) tp [.VTypeBox A] (fun _ => y) tp.l Nat.succ := by
  obtain ⟨hsub, hmcs⟩ := retChild_spec hS hy hT hM hΦ
  refine ⟨rcl_suffix tp.l A, retBackImg tp.l A hy, List.suffix_refl _, rclImg tp.l A,
    fun Θ hΘ => ?_⟩
  rw [WFF.mono_refl]
  by_contra hn
  have h₁ := hsub (Or.inr ⟨Θ, hM.neg_mem_iff.mpr hn, rfl⟩)
  refine hmcs.1 ⟨[_, _], fun x hx => ?_, ⟨Proof.imp_elim
    (φ := liftBody (rcl_suffix tp.l A) (rclImg tp.l A) Θ) (Proof.lookup List.mem_cons_self)
    (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁
  · rw [List.mem_singleton.mp hx]; exact hΘ

/-- ⭐**The forward arrow at birth**: a body true at the parent of its roots' necessary object is
    `ret_unit`'s conjunct read at the child (`liftBody_unitBody`); its negation at the far end
    would clash with the unit (`ret_absurd`), so the parent has `¬◇[d ↦ y]¬U` and the seed has
    `¬¬U`. -/
theorem retChild_fwd :
    RetInv hS tp (retChild hS hy Φ) tp.l Nat.succ [.VTypeBox A] (fun _ => y) := by
  obtain ⟨hsub, hmcs⟩ := retChild_spec hS hy hT hM hΦ
  refine ⟨List.suffix_refl _, rclImg tp.l A, rcl_suffix tp.l A, retBackImg tp.l A hy,
    fun Ψ hΨ => ?_⟩
  refine (congrArg (· ∈ (retChild hS hy Φ).M)
    (liftBody_unitBody (rcl_suffix tp.l A) (rclImg tp.l A) hS Ψ)).mp ?_
  have hrefl := (ctxOf_le_of_suffix (List.suffix_refl tp.l)).boxIn
  have e : WFF.unitBody (Γ := ctxOf tp.l) hS (Term.mono hrefl (tupT tp.l).2)
      (pack2 [.VTypeBox A] (.VTypeBox (bcT tp.l)) Ψ) =
      WFF.unitBody (Γ := ctxOf tp.l) hS (tupT tp.l).2
        (pack2 [.VTypeBox A] (.VTypeBox (bcT tp.l)) Ψ) := by
    rw [Term.mono_refl]
  have hU : WFF.neg (WFF.ret hS (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg tp.l A hy)).2
      (WFF.neg (WFF.unitBody (Γ := ctxOf tp.l) hS (tupT tp.l).2
        (pack2 [.VTypeBox A] (.VTypeBox (bcT tp.l)) Ψ)))) ∈ tp.M := by
    refine hM.neg_mem_iff.mpr fun hr => hM.1 ⟨[WFF.ret hS
      (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg tp.l A hy)).2
        (WFF.neg (WFF.unitBody (Γ := ctxOf tp.l) hS (tupT tp.l).2
          (pack2 [.VTypeBox A] (.VTypeBox (bcT tp.l)) Ψ))),
      liftBody (List.suffix_refl tp.l) (retBackImg tp.l A hy) Ψ], fun x hx => ?_, ⟨?_⟩⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hr
      · rw [List.mem_singleton.mp hx]; exact hΨ
    refine Proof.ret_absurd hS _ _ (ctxOf_fresh (l := tp.l) le_rfl) (Proof.conv (by rw [e]; rfl)
      (Proof.ret_unit hS .nec _ _ (Term.mono hrefl (tupT tp.l).2) _
        (Proof.lookup List.mem_cons_self) ?_))
    exact Proof.conv (holeRead_tupImgT_pack2 (retBackImg tp.l A hy)
      (Term.boxtm (Term.mono hrefl (tupT tp.l).2)) Ψ).symm
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
  have h₁ := hsub (Or.inr ⟨_, hU, rfl⟩)
  exact hmcs.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact h₁,
    ⟨Proof.byContra (Proof.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.lookup List.mem_cons_self))⟩⟩

/-- ⭐**The child is born with the invariants** both ways. -/
theorem RetData.retBirth : RetData hS tp (retChild hS hy Φ) none 0 tp.l Nat.succ
    [.VTypeBox A] (fun _ => y) :=
  ⟨retChild_fwd hS hy hT hM hΦ, retChild_back hS hy hT hM hΦ⟩

end Birth

/-! ## The operation -/

namespace NetSt

/-- A returning-possibility obligation: over a list of a node's variables, the type `A` of what
    comes back, the alias `y` and the atom's body. -/
abbrev RetObl (σ : Signature) :=
  Σ l : List VarType, Σ A : VarType, ℕ × WFF σ (bodyCtx [.VTypeBox A] l) 1

open Classical in
/-- ⭐Give the node `s` the child of its atom `◇[d ↦ y] Φ`, if it has it — `Φ` over an earlier list
    of its variables, and `y` one of them, of type `(□A).bc`. -/
noncomputable def mkRet (hS : ModalSys.BStrong = true) (N : NetSt σ) (s : Node) :
    RetObl σ → NetSt σ
  | ⟨l, A, y, Φ⟩ =>
      if h : l <:+ (N.st s).l then
        if hy : (ctxOf (N.st s).l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc then
          if WFF.ret hS (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg _ A hy)).2
              (WFF.mono ((ctxOf_le_of_suffix h).boxIn.insert (.bnd 0) _) Φ) ∈ (N.st s).M then
            N.newChild s none 0
              (retChild hS hy (WFF.mono ((ctxOf_le_of_suffix h).boxIn.insert (.bnd 0) _) Φ))
              Nat.succ [.VTypeBox A] (fun _ => y)
          else N
        else N
      else N

/-- ⭐The child of a returning possibility keeps the invariants (T off): it is born with them. -/
theorem GoodS.mkRet {hS : ModalSys.BStrong = true} (hT : ModalSys.T = false) {N : NetSt σ}
    (hN : N.GoodS hS) {s : Node} (hs : N.Live s) (o : RetObl σ) : (N.mkRet hS s o).GoodS hS := by
  obtain ⟨l, A, y, Φ⟩ := o
  simp only [NetSt.mkRet]
  split_ifs with h hy hΦ
  · exact hN.newChild hs (retChild_spec hS hy hT (hN.mcs s hs) hΦ).2
      (RetData.retBirth hS hy hT (hN.mcs s hs) hΦ)
  all_goals exact hN

theorem Ext.mkRet {hS : ModalSys.BStrong = true} {N : NetSt σ} {s : Node} (hs : N.Live s)
    (o : RetObl σ) : Ext N (N.mkRet hS s o) := by
  obtain ⟨l, A, y, Φ⟩ := o
  simp only [NetSt.mkRet]
  split_ifs
  · exact Ext.newChild hs _ _ _ _ _ _
  all_goals exact Ext.refl N

end NetSt

end BArrow

end V12M
