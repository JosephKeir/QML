import QML.QML_v12m_BRetChild
import QML.QML_v12m_RetKXD

/-!
# QML v12m — strong B on the network: the child of a returning possibility, for either T

The flag-generic replacement of `QML_v12m_BRetChild` (docs §11.21, stage 3c).  The obligation
binds the born root itself, `u : □A` with **all** its companions (`bornShape A`, `□A` with T off),
valued at the alias `y`'s components (`unarrT`): the born root's value with companions sent along
the back arrow.  So the seed's pull-back sends the born root `c` to the opened slot `u` itself,
coherent by construction, and needs no fact about `bc`.

* `liftBodyR`: a body over the born root read at the child, with `c` in the slot.
* `retSeedC`: the obligation's body, and `¬Θ` for every `¬◇^{S_A}[u ↦ W] Θ` of the parent.
* ⭐`retSeedC_consistent`: the K-law at the born root's shape (`Proof.ret_KC_node`) reduces finitely
  many seed formulas to one body; a refutation of it at the child pulls back (`retPullC`,
  `subst_retPullC_liftBodyR`) to `□¬∃u. Ξ` against `◇∃u. Ξ`.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## The born root's shape and value -/

/-- All the companions of a born root `□A` (none with T off). -/
abbrev bornComps (A : VarType) : List (List Step) := A.compsAllB ModalSys.T

omit [ModalSys.NoFour] in
theorem bornComps_ok (A : VarType) : A.CompOk (bornComps A) :=
  VarType.compOk_compsAllB _ rfl A

/-- The shape a born root is bound at: `□A` with all its companions. -/
abbrev bornShape (A : VarType) : NShape := .boxC A (bornComps A) (bornComps_ok A)

omit [ModalSys.NoFour] in
/-- The born root `c` (root 0 of `[□A]`) is a `□A` object. -/
theorem born_ref (A : VarType) : (ctxOf [VarType.VTypeBox A]).ref (.root (.free 0)) =
    some (.VTypeBox A) :=
  ctxOf_ref_new (VarType.VTypeBox A) []

/-- ⭐The obligation's value: the born root's value with companions, sent along the back arrow
    `c ↦ y` — `y`'s components, one per companion. -/
def unarrT {l : List VarType} {A : VarType} {y : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) :
    Σ a, Term σ (ctxOf l) (A.compsFlat (bornComps A)) a :=
  ⟨_, Term.subst (arrowIdx (fun _ => y)) (arrowS σ (ctxOf l) (fun _ => y))
    (ok_arrowS (retBackImg l A hy)) (coh_arrowS (retBackImg l A hy))
    (compsSlot (σ := σ) (born_ref A) (Ctx.Le.refl _) (bornComps A) (bornComps_ok A)).2⟩

/-! ## Reading a body over the born root at the child -/

omit [ModalSys.NoFour] in
/-- The child's root `c` is the born root. -/
theorem rcl_born_ref (l : List VarType) (A : VarType) :
    (ctxOf (rcl l A)).ref (.root (.free 0)) = some (.VTypeBox A) :=
  (ctxOf_le_of_suffix (rcl_suffix l A)).ref (born_ref A)

/-- ⭐A body over the born root `u`, read at the child: the parent's items along the arrow to
    the child, `u` the child's root `c`. -/
def liftBodyR (l : List VarType) (A : VarType)
    (Ξ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox A)) 1) : WFF σ (ctxOf (rcl l A)) 0 :=
  WFF.subst (Subst.setIdx (arrowIdx Nat.succ) (.bnd 0) (.ren (.root (.free 0))))
    ((arrowS σ (ctxOf (rcl l A)) Nat.succ).set (.bnd 0) (.ren (.root (.free 0))))
    (Subst.ok_set (ok_arrowS (rclImg l A)) (rcl_born_ref l A))
    (Subst.coh_set (ok_arrowS (rclImg l A)) (coh_arrowS (rclImg l A))
      ((Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).rootFresh (le_refl 0)) (rcl_born_ref l A))
    ((Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).insert _) Ctx.NoSlots.slots Ξ

/-! ## Pulling the child back, with the born root to the opened slot -/

/-- A view `V` of the parent with the slot opened at `u = l.length`, at the born root's type. -/
abbrev pullCtxC (V : Ctx) (l : List VarType) (A : VarType) : Ctx :=
  V.insert (.free l.length) (.VTypeBox A)

/-- ⭐Pulling the child back into a view `V` of the parent: `c` to the opened slot `u` itself,
    root `r + 1` to the tuple of root `r`'s items, and the root after those (a witness child's
    content) to `e`.  No fact about `bc` is used: the born root goes to a variable of its own
    type. -/
def retPullC (σ : Signature) (l : List VarType) (A : VarType)
    {V : Ctx} (hV : (ctxOf l).boxIn.Le V) (hu : V.RootFresh (.free l.length))
    (e : SubE σ (pullCtxC V l A)) : Subst σ (pullCtxC V l A) := fun v =>
  match v with
  | .root (.free 0) => .ren (.root (.free l.length))
  | .root (.free (r + 1)) =>
      if h : r < l.length then .tm (Term.mono (hV.trans (Ctx.le_insert hu.root _))
        (tup (.root (.free r)) (rootTy l r) (by
          rw [Ctx.ref_nonproj _ rfl]; exact ctxOf_root_lt h)))
      else if r = l.length then e else .hide
  | _ => .hide

/-- Where pulling back sends annotation indices: along the entry at the index's root. -/
def retPullIdxC (σ : Signature) (l : List VarType) (A : VarType)
    {V : Ctx} (hV : (ctxOf l).boxIn.Le V) (hu : V.RootFresh (.free l.length))
    (e : SubE σ (pullCtxC V l A)) (a : VarSymb) : VarSymb :=
  match a.rt with
  | .free r => (retPullC σ l A hV hu e (.root (.free r))).idxAlong a.path
  | .bnd _ => a

section Pull

variable (l : List VarType) (A : VarType) {V : Ctx}
  (hV : (ctxOf l).boxIn.Le V) (hu : V.RootFresh (.free l.length)) (e : SubE σ (pullCtxC V l A))

theorem retPullC_succ {r : ℕ} (h : r < l.length) :
    retPullC σ l A hV hu e (.root (.free (r + 1))) = .tm (Term.mono
      (hV.trans (Ctx.le_insert hu.root _)) (tup (.root (.free r)) (rootTy l r) (by
          rw [Ctx.ref_nonproj _ rfl]; exact ctxOf_root_lt h))) :=
  dif_pos h

theorem retPullC_last : retPullC σ l A hV hu e (.root (.free (l.length + 1))) = e := by
  change (if h : l.length < l.length then _ else if l.length = l.length then _ else _) = _
  rw [dif_neg (lt_irrefl _), if_pos rfl]

theorem retPullC_okRef {r : ℕ} (hr : r < (rcl l A).length) :
    (retPullC σ l A hV hu e (.root (.free r))).OkRef (rootTy (rcl l A) r) := by
  cases r with
  | zero =>
      rw [rootTy_rcl_zero]
      exact Ctx.ref_insert_root _ _ _
  | succ r =>
      have hr' : r < l.length := by rw [length_rcl] at hr; omega
      rw [rootTy_rcl_succ, rootTy_map_bc l r hr', retPullC_succ l A hV hu e hr']
      rfl

theorem ok_retPullC : Subst.Ok (ctxOf (rcl l A)) (retPullC σ l A hV hu e) := by
  intro v T _ hv
  obtain ⟨r, rfl⟩ := ctxOf_decl hv
  have hr : r < (rcl l A).length := by
    by_contra hge
    rw [(ctxOf_fresh (l := rcl l A) (Nat.le_of_not_lt hge)) _ rfl] at hv
    cases hv
  rw [ctxOf_root_lt hr] at hv
  cases hv
  exact retPullC_okRef l A hV hu e hr

/-- A witness child's content root, after the parent's, is pulled back to `e`, of its type. -/
theorem ok_retPullC_X {X : VarType} (he : e.OkRef X) :
    Subst.Ok (ctxOf (X :: rcl l A)) (retPullC σ l A hV hu e) := by
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
    exact retPullC_okRef l A hV hu e hlt
  · obtain rfl : r = (rcl l A).length := by omega
    rw [rootTy_new, length_rcl, retPullC_last]
    exact he

theorem coh_retPullC_of {kl : List VarType}
    (hok : Subst.Ok (ctxOf kl) (retPullC σ l A hV hu e)) :
    Subst.Coh (retPullIdxC σ l A hV hu e) (ctxOf kl) (retPullC σ l A hV hu e) := by
  refine Subst.coh_of hok ?_
  intro v T _ hv p
  obtain ⟨r, rfl⟩ := ctxOf_decl hv
  have hrt : ((VarSymb.root (.free r)).ext p).rt = .free r := VarSymb.ext_rt _ _
  rw [retPullIdxC, hrt, VarSymb.ext_path]
  rfl

/-- Pulling back along an encoded projection path from root `r + 1` reaches the tuple of the
    component. -/
theorem at_retPullC_tup : ∀ {u : VarSymb} {U : VarType} (hu' : (ctxOf l).ref u = some U) (r : ℕ),
    u.rt = .free r →
      (retPullC σ l A hV hu e).at ((VarSymb.root (.free (r + 1))).ext (encPath u.path)) =
        .tm (Term.mono (hV.trans (Ctx.le_insert hu.root _)) (tup u U hu'))
  | .root (.free r'), U, hu', r, hrt => by
      change Root.free r' = Root.free r at hrt
      cases hrt
      obtain ⟨r₀, e', hr', -⟩ := ref_rt hu'
      cases e'
      have hU := hu'
      rw [Ctx.ref_nonproj _ rfl, ctxOf_root_lt hr'] at hU
      cases hU
      exact retPullC_succ l A hV hu e hr'
  | .root (.bnd _), _, _, _, hrt => by cases hrt
  | .step u s, U, hu', r, hrt => by
      have hproj : s.isProj = true := (reach_ppath hu').1 s (by simp [VarSymb.path])
      have hu'' := hu'
      simp only [Ctx.ref, if_pos hproj] at hu''
      cases hU : (ctxOf l).ref u with
      | none => rw [hU] at hu''; cases hu''
      | some U' =>
          rw [hU] at hu''
          have ih := at_retPullC_tup hU r hrt
          change (retPullC σ l A hV hu e).at
            ((VarSymb.root (.free (r + 1))).ext (encPath (u.path ++ [s]))) = _
          rw [show encPath (u.path ++ [s]) = encPath u.path ++ [encStep s] from
            List.map_append, VarSymb.ext_step, Subst.at_proj _ _ (encStep_proj hproj), ih]
          exact proj_tupB_mono _ rfl hU hproj hu'' hu'

/-- An item of the parent's `□` view, sent along the child's arrow and pulled back, is itself. -/
theorem at_retPullC_item {w : VarSymb} {T : VarType}
    (hw : (ctxOf l).ref w = some (.VTypeBox T)) :
    (retPullC σ l A hV hu e).at (itemAt (imgRoot Nat.succ w.rt) w) =
      .tm (Term.eta (.step w .box) T ((hV.trans (Ctx.le_insert hu.root _)).ref
        (Ctx.ref_boxIn_of ModalSys.NoFour.keepOnly hw))) := by
  obtain ⟨r, hr, _, _⟩ := ref_rt hw
  rw [hr]
  change (retPullC σ l A hV hu e).at (itemAt (.free (r + 1)) w) = _
  rw [at_item_of_tupB_mono _ _ _ hw ModalSys.T rfl (at_retPullC_tup l A hV hu e hw r hr),
    Term.mono_eta]

end Pull

/-- A non-slot variable of a body's context over any slot type is an item of the view. -/
theorem body_itemT {clt : List VarType} {T : VarType} {v : VarSymb} {U : VarType}
    (hv : ((ctxOf clt).boxIn.insert (.bnd 0) T) v = some U) (hvr : v ≠ .root (.bnd 0)) :
    ∃ u, v = .step u .box ∧ (ctxOf clt).ref u = some (.VTypeBox U) := by
  change (if v = VarSymb.root (.bnd 0) then _ else (ctxOf clt).boxIn v) = _ at hv
  rw [if_neg hvr] at hv
  exact boxIn_item hv

/-- ⭐**Pulling back opens the slot**: a body over the born root read at the child, pulled back
    into the parent's `□` view, is the body with its slot opened at `u`. -/
theorem subst_retPullC_liftBodyR (l : List VarType) (A : VarType)
    (Ξ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox A)) 1) :
    WFF.subst (retPullIdxC σ l A (Ctx.Le.refl _) (pullCtx_fresh l) .hide)
        (retPullC σ l A (Ctx.Le.refl _) (pullCtx_fresh l) .hide)
        (ok_retPullC l A _ _ _) (coh_retPullC_of l A _ _ _ (ok_retPullC l A _ _ _))
        Ctx.NoSlots.slots Ctx.NoSlots.slots (liftBodyR l A Ξ) =
      WFF.openFree l.length (pullCtx_fresh l) Ctx.NoSlots.slots Ξ := by
  unfold liftBodyR WFF.openFree
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Ξ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = .VTypeBox A := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    rw [Subst.toFree_root]
    dsimp only [Subst.comp]
    rw [Subst.set_root]
    exact .refl _
  · obtain ⟨w, rfl, hw⟩ := body_itemT hv hvr
    rw [Subst.toFree_ne _ _ _ _ hvr]
    dsimp only [Subst.comp]
    rw [Subst.set_ne _ _ hvr]
    change SubE.Sim T (((Subst.idRen _) (.step w .box)).mono _)
      ((retPullC σ l A (Ctx.Le.refl _) (pullCtx_fresh l) .hide).at
        (itemAt (imgRoot Nat.succ w.rt) w))
    rw [at_retPullC_item l A _ _ _ hw]
    exact .ren_eta _ _

/-! ## The K-law at a node, and refuting a returning possibility at any shape -/

/-- ⭐**The K-law at a node, at an object with companions**, for any body. -/
def Proof.ret_KC_node (hS : ModalSys.BStrong = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)} {B : VarType} (co : List (List Step)) (ho : B.CompOk co)
    {b : Ann (B.compsFlat co)} (t : Term σ (ctxOf l) (B.compsFlat co) b)
    (Φ Θ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox B)) 1)
    (p : Proof σ (ctxOf l) Δ (WFF.retS hS (.nec (.boxC B co ho)) t Φ))
    (q : Proof σ (ctxOf l) Δ (WFF.neg (WFF.retS hS (.nec (.boxC B co ho)) t Θ))) :
    Proof σ (ctxOf l) Δ (WFF.retS hS (.nec (.boxC B co ho)) t (WFF.and Φ (WFF.neg Θ))) :=
  Proof.conv (by rw [kPsi_pack2]) (Proof.ret_KC hS co ho t Φ (tupT l).2
    (pack2 l (.VTypeBox B) Θ) p (Proof.conv (by rw [kPsi_pack2]) q))

omit [ModalSys.NoFour] in
/-- A returning possibility, at any shape, whose body the `□` view refutes is absurd. -/
def Proof.ret_refuteS {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)}
    (hS : ModalSys.BStrong = true) (S : RShape) {a : Ann S.flat} (t : Term σ Γ S.flat a)
    (Ξ : WFF σ (Γ.boxIn.insert (.bnd 0) S.ty) 1)
    (q : Proof σ Γ.boxIn [] (WFF.neg (WFF.ex S.ty Ξ)))
    (p : Proof σ Γ Δ (WFF.retS hS S t Ξ)) : Proof σ Γ Δ .bot :=
  Proof.imp_elim (Proof.ret_diaS hS .nec t _ p)
    (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.K_box (Δ := []) q))

/-! ## The seed and its consistency -/

section Seed

variable (hS : ModalSys.BStrong = true) {l : List VarType} {A : VarType} {y : ℕ}
  (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)

/-- ⭐The seed of the child of `◇^{S_A}[u ↦ W] Ξ`: the obligation's body, and `¬Θ` for every
    `¬◇^{S_A}[u ↦ W] Θ` of the parent, read at the child. -/
def retSeedC (M : Set (WFF σ (ctxOf l) 0))
    (Ξ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox A)) 1) :
    Set (WFF σ (ctxOf (rcl l A)) 0) :=
  {liftBodyR l A Ξ} ∪
    {φ | ∃ Θ, WFF.neg (WFF.retS hS (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Θ) ∈ M ∧
      φ = liftBodyR l A (WFF.neg Θ)}

/-- Finitely many seed formulas reduce to one body with the obligation at the parent. -/
theorem retSeedC_list {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.IsMCS M)
    {Ξ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox A)) 1}
    (hΞ : WFF.retS hS (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ ∈ M) :
    ∀ L : List (WFF σ (ctxOf (rcl l A)) 0), (∀ δ ∈ L, δ ∈ retSeedC hS hy M Ξ) →
      ∃ Ξ', WFF.retS hS (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ' ∈ M ∧
        Theory.Derives {liftBodyR l A Ξ'} (liftBodyR l A Ξ) ∧
        ∀ δ ∈ L, Theory.Derives {liftBodyR l A Ξ'} δ
  | [], _ => ⟨Ξ, hΞ, Theory.Derives.of_mem rfl, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨Ξ₀, hΞ₀, hΦ₀, hL⟩ := retSeedC_list hM hΞ L
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      rcases h δ List.mem_cons_self with hδ | ⟨Θ, hΘ, rfl⟩
      · refine ⟨Ξ₀, hΞ₀, hΦ₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · rw [Set.mem_singleton_iff.mp hδ]
          exact hΦ₀
        · exact hL d hd
      · have hand : ∀ φ, Proof σ _ [liftBodyR l A (Ξ₀.and Θ.neg)] φ →
            Theory.Derives {liftBodyR l A (Ξ₀.and Θ.neg)} φ :=
          fun φ p => ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; rfl, ⟨p⟩⟩
        have h₀ := hand _ (Proof.and_elim_l (ψ := liftBodyR l A Θ.neg)
          (Proof.lookup List.mem_cons_self))
        have h₁ := hand _ (Proof.and_elim_r (φ := liftBodyR l A Ξ₀)
          (Proof.lookup List.mem_cons_self))
        have htr : ∀ d, Theory.Derives {liftBodyR l A Ξ₀} d →
            Theory.Derives {liftBodyR l A (Ξ₀.and Θ.neg)} d :=
          fun d hd => Derives.trans (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact h₀) hd
        refine ⟨Ξ₀.and Θ.neg, hM.closed ⟨[_, _], fun x hx => ?_,
          ⟨Proof.ret_KC_node hS (bornComps A) (bornComps_ok A) _ Ξ₀ Θ
            (Proof.lookup List.mem_cons_self)
            (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩,
          htr _ hΦ₀, fun d hd => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hΞ₀
          · rw [List.mem_singleton.mp hx]; exact hΘ
        rcases List.mem_cons.mp hd with rfl | hd
        · exact h₁
        · exact htr d (hL d hd)

/-- ⭐**The seed is consistent**, for either value of T: finitely many seed formulas reduce to one
    body `Ξ'` with the obligation at the parent (`retSeedC_list`); a refutation of `Ξ'` read at the
    child pulls back to a refutation of `Ξ'` with its slot opened (`subst_retPullC_liftBodyR`),
    so `□¬∃u. Ξ'` holds at the parent, against `◇∃u. Ξ'` (`Proof.ret_refuteS`). -/
theorem retSeedC_consistent {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.IsMCS M)
    {Ξ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox A)) 1}
    (hΞ : WFF.retS hS (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ ∈ M) :
    Theory.Consistent (retSeedC hS hy M Ξ) := by
  rintro ⟨L, hL, hp⟩
  obtain ⟨Ξ', hΞ', -, hder⟩ := retSeedC_list hS hy hM hΞ L hL
  obtain ⟨Δ, hΔ, ⟨p⟩⟩ := Derives.trans (fun x hx => hder x hx) ⟨L, fun x hx => hx, hp⟩
  have p' : Proof σ (ctxOf (rcl l A)) [liftBodyR l A Ξ'] .bot :=
    Proof.ofSubset (fun x hx => by
      rw [Set.mem_singleton_iff.mp (hΔ x hx)]; exact List.mem_cons_self) p
  haveI : (pullCtxC (ctxOf l).boxIn l A).Presented :=
    Ctx.Presented.insertFree inferInstance _ (pullCtx_fresh l) _
  have q := Proof.subst p' (retPullC σ l A (Ctx.Le.refl _) (pullCtx_fresh l) .hide)
    (ok_retPullC l A _ _ _) (coh_retPullC_of l A _ _ _ (ok_retPullC l A _ _ _))
    Ctx.NoSlots.slots
  simp only [List.map_cons, List.map_nil, subst_retPullC_liftBodyR] at q
  refine hM.1 ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hΞ',
    ⟨Proof.ret_refuteS hS _ _ Ξ' ?_ (Proof.lookup List.mem_cons_self)⟩⟩
  refine Proof.imp_intro (Proof.ex_elim l.length _ (pullCtx_fresh l)
    (φ := WFF.openFree _ (pullCtx_fresh l) Ctx.NoSlots.slots Ξ') (ψ := .bot)
    (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
      (Proof.lookup List.mem_cons_self)) ?_)
  exact Proof.ofSubset (fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_self) q

end Seed

/-! ## Terms at the born root: the tuple of its items, and its companions

The identities the births rest on hold for either value of the flag, and are proved for a
general `b` (as `tupB`'s are), then read at `b = T`. -/

/-- The tuple of the born root's items, at a value `b` of the flag. -/
def tup1B (A : VarType) (b : Bool) (hb : ModalSys.T = b) :
    Σ a, Term σ (ctxOf [VarType.VTypeBox A]).boxIn (tupOneTy A b) a :=
  ⟨_, Term.pair Term.unit (tupB (.root (.free 0)) (.VTypeBox A) b hb (born_ref A))⟩

theorem tupT_born (A : VarType) : tupT (σ := σ) [VarType.VTypeBox A] = tup1B A ModalSys.T rfl :=
  rfl

/-- Under T, the tree of a variable's items is its tuple (`inner` is `box` without 4). -/
theorem itemsTree_tupB (hT : ModalSys.T = true) : ∀ (R : VarType) {Γ : Ctx} (u : VarSymb)
    (hu : Γ.ref u = some R),
    (itemsTree (σ := σ) hT u R hu : Σ a, Term σ Γ.boxIn (R.bcB true) a) =
      ⟨_, tupB u R true hT hu⟩
  | .VTypeBox C, _, u, hu => sig_pair
      (eta_addr_congr (VarSymb.inner_box ModalSys.NoFour.keepOnly) _ _)
      (itemsTree_tupB hT C (.step u .here) (Ctx.ref_here_of hT hu))
  | .VTypeProd X Y, _, u, hu => sig_pair
      (itemsTree_tupB hT X (.step u .fst) (Ctx.ref_fst_of hu))
      (itemsTree_tupB hT Y (.step u .snd) (Ctx.ref_snd_of hu))
  | .Var, _, _, _ => rfl
  | .VTypeOne, _, _, _ => rfl
  | .VTypeDia _, _, _, _ => rfl

omit [ModalSys.NoFour] in
/-- Substituting a tree of items substitutes its leaves. -/
theorem Term.subst_bcTree {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) : ∀ (Z : VarType)
    (get : ∀ q, q ∈ Z.hereChains → Σ c, Term σ Γ ((Z.compAt q).getD .VTypeOne) c),
    (⟨_, Term.subst ι θ hθ hc (bcTree Z get).2⟩ : Σ c, Term σ Δ (Z.bcB true) c) =
      bcTree Z (fun q hq => ⟨_, Term.subst ι θ hθ hc (get q hq).2⟩)
  | .VTypeBox C, _ => sig_pair rfl (Term.subst_bcTree θ hθ hc C _)
  | .VTypeProd X Y, _ => sig_pair (Term.subst_bcTree θ hθ hc X _) (Term.subst_bcTree θ hθ hc Y _)
  | .Var, _ => rfl
  | .VTypeOne, _ => rfl
  | .VTypeDia _, _ => rfl

omit [ModalSys.NoFour] in
/-- Under a valid companion list, each companion is a necessary object of the bound one. -/
theorem VarType.CompOk.ref_mem {Γ : Ctx} {u : VarSymb} {A : VarType} {cs : List (List Step)}
    (h : A.CompOk cs) {q : List Step} (hq : q ∈ cs) (hu : Γ.ref u = some (.VTypeBox A)) :
    Γ.ref ((VarSymb.step u .here).ext q) = some (.VTypeBox ((A.compAt q).getD .VTypeOne)) := by
  obtain ⟨hT, hall, -⟩ := h.resolve_left (List.ne_nil_of_mem hq)
  obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp (hall q hq)
  rw [hC]
  exact Ctx.ref_compAt hT q (Ctx.ref_here_of hT hu) hC

omit [ModalSys.NoFour] in
/-- A substitution holding a value with companions at `v` holds the object's own contents along
    the first components. -/
theorem at_compsFst_compsSlot {Δ₀ Δ' : Ctx} (θ : Subst σ Δ') {u : VarSymb} {C : VarType}
    (hu : Δ₀.ref u = some (.VTypeBox C)) (hle : Δ₀.boxIn.Le Δ') :
    ∀ (cs : List (List Step)) (h : C.CompOk cs) (v : VarSymb),
      θ.at v = .tm (compsSlot (σ := σ) hu hle cs h).2 →
      θ.at (v.ext (compsFst cs)) = .tm (Term.eta u.inner C (hle.ref (Ctx.ref_inner hu)))
  | [], _, _, hv => hv
  | _ :: ps, h, v, hv => by
      change θ.at ((VarSymb.step v .fst).ext (compsFst ps)) = _
      exact at_compsFst_compsSlot θ hu hle ps h.tail _ (by rw [Subst.at_proj θ v rfl, hv]; rfl)

omit [ModalSys.NoFour] in
/-- … and each companion's contents at its index. -/
theorem at_compsIdx_compsSlot {Δ₀ Δ' : Ctx} (θ : Subst σ Δ') {u : VarSymb} {C : VarType}
    (hu : Δ₀.ref u = some (.VTypeBox C)) (hle : Δ₀.boxIn.Le Δ') :
    ∀ (cs : List (List Step)) (h : C.CompOk cs) (q : List Step) (hq : q ∈ cs) (v : VarSymb),
      θ.at v = .tm (compsSlot (σ := σ) hu hle cs h).2 →
      θ.at (v.ext (compsIdx cs q)) = .tm (Term.eta ((VarSymb.step u .here).ext q).inner
        ((C.compAt q).getD .VTypeOne) (hle.ref (Ctx.ref_inner (VarType.CompOk.ref_mem h hq hu))))
  | [], _, _, hq, _, _ => absurd hq List.not_mem_nil
  | p :: ps, h, q, hq, v, hv => by
      by_cases hqp : q = p
      · subst hqp
        have e : v.ext (compsIdx (q :: ps) q) = .step v .snd := by simp [compsIdx, VarSymb.ext]
        rw [e, Subst.at_proj θ v rfl, hv]
        rfl
      · have hq' : q ∈ ps := (List.mem_cons.mp hq).resolve_left hqp
        have e : v.ext (compsIdx (p :: ps) q) = (VarSymb.step v .fst).ext (compsIdx ps q) := by
          simp [compsIdx, hqp, VarSymb.ext]
        rw [e]
        exact at_compsIdx_compsSlot θ hu hle ps h.tail q hq' _
          (by rw [Subst.at_proj θ v rfl, hv]; rfl)

/-- ⭐Under T, along a companion path of a tuple of items, the collapsed tuple's projections are
    the η-expansions of the companions it decodes to (`bcDec`): the term counterpart of
    `compBack_itemsTree`. -/
theorem Subst.at_ext_collapse_tupB (hT : ModalSys.T = true) {Γ : Ctx} (θ : Subst σ Γ) :
    ∀ (R : VarType) (x : VarSymb) (hx : Γ.ref x = some R) (p : List Step),
      p ∈ (R.bcB true).hereChains → ∀ (v : VarSymb) (C : VarType),
      (R.bcB true).compAt p = some C →
      ∀ (h' : Γ.ref (x.ext (R.bcDec p)) = some (.VTypeBox C)),
      θ.at v = .tm (Term.collapse (Ctx.collapses_boxIn_self hT Γ) (tupB x R true hT hx)) →
      θ.at (v.ext p) = .tm (Term.eta (x.ext (R.bcDec p)) (.VTypeBox C) h')
  | .VTypeBox C', x, hx, p, hp, v, C, hC, h', hv => by
      rcases List.mem_append.mp hp with hq | hq
      · obtain ⟨q, -, rfl⟩ := List.mem_map.mp hq
        have h1 : θ.at (.step v .fst) =
            .tm (Term.eta (.step x .here) C' (Ctx.ref_here_of hT hx)) := by
          rw [Subst.at_proj θ v rfl, hv]
          change SubE.tm (Term.collapse _ (Term.eta (.step x .box) C' _)) = _
          refine SubE.tm_eq_of_sig ((Term.collapse_eta _ _ C' _).trans
            (Term.eta_congr ?_ C' _ _))
          rw [← VarSymb.inner_box ModalSys.NoFour.keepOnly]
          exact VarSymb.inner_collapse_zero x
        exact Subst.at_ext_eta hT θ q (Ctx.ref_here_of hT hx) hC h' h1
      · obtain ⟨q, hq₀, rfl⟩ := List.mem_map.mp hq
        exact Subst.at_ext_collapse_tupB hT θ C' (.step x .here) (Ctx.ref_here_of hT hx) q hq₀
          (.step v .snd) C hC h' (by rw [Subst.at_proj θ v rfl, hv]; rfl)
  | .VTypeProd X Y, x, hx, p, hp, v, C, hC, h', hv => by
      rcases List.mem_append.mp hp with hq | hq
      · obtain ⟨q, hq₀, rfl⟩ := List.mem_map.mp hq
        exact Subst.at_ext_collapse_tupB hT θ X (.step x .fst) (Ctx.ref_fst_of hx) q hq₀
          (.step v .fst) C hC h' (by rw [Subst.at_proj θ v rfl, hv]; rfl)
      · obtain ⟨q, hq₀, rfl⟩ := List.mem_map.mp hq
        exact Subst.at_ext_collapse_tupB hT θ Y (.step x .snd) (Ctx.ref_snd_of hx) q hq₀
          (.step v .snd) C hC h' (by rw [Subst.at_proj θ v rfl, hv]; rfl)
  | .Var, _, _, _, hp, _, _, _, _, _ => by cases hp
  | .VTypeOne, _, _, _, hp, _, _, _, _, _ => by cases hp
  | .VTypeDia _, _, _, _, hp, _, _, _, _, _ => by cases hp

omit [ModalSys.NoFour] in
/-- The born root's companion that a companion of its tuple decodes to is a necessary object. -/
theorem born_comp_ref (hT : ModalSys.T = true) (A : VarType) (p : List Step)
    (hp : p ∈ (tupOneTy A true).hereChains) :
    (ctxOf [VarType.VTypeBox A]).ref
        ((VarSymb.root (.free 0)).ext ((VarType.VTypeBox A).bcDec p.tail)) =
      some (.VTypeBox (((tupOneTy A true).compAt p).getD .VTypeOne)) := by
  rcases List.mem_append.mp hp with hq | hq
  · obtain ⟨_, hq, _⟩ := List.mem_map.mp hq
    cases hq
  obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hq
  have hs := VarType.compAt_hereChains _ p' hp'
  obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp hs
  change (ctxOf [VarType.VTypeBox A]).ref ((VarSymb.root (.free 0)).ext
    ((VarType.VTypeBox A).bcDec p')) = some (.VTypeBox ((((VarType.VTypeBox A).bcB true).compAt
      p').getD .VTypeOne))
  rw [hC]
  rw [VarType.compAt_bcDec _ p' hp'] at hC
  exact Ctx.ref_compAt hT _ (born_ref A) hC

/-- ⭐Under T, the contents of the born root's tuple's companion `p`: the item of the born root's
    companion it decodes to. -/
theorem compVal_tup1 (hT : ModalSys.T = true) (A : VarType) (p : List Step)
    {ps : List (List Step)} (h : (tupOneTy A true).CompOk (p :: ps))
    (hp : p ∈ (tupOneTy A true).hereChains) :
    compVal (σ := σ) (tup1B A true hT).2 p h =
      ⟨_, Term.eta ((VarSymb.root (.free 0)).ext ((VarType.VTypeBox A).bcDec p.tail)).inner
        (((tupOneTy A true).compAt p).getD .VTypeOne)
        (Ctx.ref_inner (born_comp_ref hT A p hp))⟩ := by
  rcases List.mem_append.mp hp with hq | hq
  · obtain ⟨_, hq, _⟩ := List.mem_map.mp hq
    cases hq
  obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hq
  have hC : ((VarType.VTypeBox A).bcB true).compAt p' =
      some ((((VarType.VTypeBox A).bcB true).compAt p').getD .VTypeOne) := by
    obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp (VarType.compAt_hereChains _ p' hp')
    rw [hC]
    rfl
  let θ := Subst.single (σ := σ) (Δ := ctxOf [VarType.VTypeBox A]) (.bnd 0)
    (.tm (Term.boxtm (tup1B A true hT).2))
  have h0 : θ.at (.step (.step (.root (.bnd 0)) .here) .snd) =
      .tm (Term.collapse (Ctx.collapses_boxIn_self hT _)
        (tupB (.root (.free 0)) (.VTypeBox A) true hT (born_ref A))) := by
    rw [Subst.at_proj θ _ rfl, Subst.at_proj θ _ rfl, Subst.at_single_root,
      SubE.proj_boxtm_here _ hT]
    rfl
  have h2 := Subst.at_ext_collapse_tupB hT θ (.VTypeBox A) (.root (.free 0)) (born_ref A) p' hp'
    _ _ hC (born_comp_ref hT A (.snd :: p') hp) h0
  exact Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm θ h2)

omit [ModalSys.NoFour] in
/-- `at_compsIdx_compsSlot` at any type the companion's contents are declared at. -/
theorem at_compsIdx_compsSlot' {Δ₀ Δ' : Ctx} (θ : Subst σ Δ') {u : VarSymb} {C : VarType}
    (hu : Δ₀.ref u = some (.VTypeBox C)) (hle : Δ₀.boxIn.Le Δ') (cs : List (List Step))
    (h : C.CompOk cs) (q : List Step) (hq : q ∈ cs) (v : VarSymb)
    (hv : θ.at v = .tm (compsSlot (σ := σ) hu hle cs h).2) (T : VarType)
    (h'' : Δ'.ref ((VarSymb.step u .here).ext q).inner = some T) :
    θ.at (v.ext (compsIdx cs q)) = .tm (Term.eta ((VarSymb.step u .here).ext q).inner T h'') := by
  obtain rfl : T = (C.compAt q).getD .VTypeOne :=
    Option.some.inj (h''.symm.trans (hle.ref (Ctx.ref_inner (VarType.CompOk.ref_mem h hq hu))))
  exact at_compsIdx_compsSlot θ hu hle cs h q hq v hv

/-- The tuple's value with companions, read off the born root's value with companions under T. -/
theorem holeRead_compsSlot_tupCVal (hT : ModalSys.T = true) (A : VarType) :
    ∀ (cs : List (List Step)) (hcs : ∀ p ∈ cs, p ∈ (tupOneTy A true).hereChains)
      (h : (tupOneTy A true).CompOk cs),
      (⟨_, Term.holeRead (compsSlot (σ := σ) (born_ref A) (Ctx.Le.refl _) A.hereChains
          (VarType.compOk_compsAllB true hT A)).2 (tupCVal A hT cs hcs).2⟩ :
        Σ a, Term σ (ctxOf [VarType.VTypeBox A]).boxIn ((tupOneTy A true).compsFlat cs) a) =
        compsVal (tup1B A true hT).2 cs h
  | [], _, _ => by
      have hv : (Subst.single (σ := σ) (Δ := (ctxOf [VarType.VTypeBox A]).boxIn) (.bnd 0)
          (.tm (compsSlot (σ := σ) (born_ref A) (Ctx.Le.refl _) A.hereChains
            (VarType.compOk_compsAllB true hT A)).2)).at (.root (.bnd 0)) =
          .tm (compsSlot (σ := σ) (born_ref A) (Ctx.Le.refl _) A.hereChains
            (VarType.compOk_compsAllB true hT A)).2 := by
        rw [Subst.at_nonproj _ rfl, Subst.single_root]
      unfold Term.holeRead
      rw [Term.subst_mono]
      refine sig_pair rfl (sig_pair ?_ ?_)
      · refine (Term.subst_eta_tm _ _ _ _ _ _ _
          (at_compsFst_compsSlot _ _ _ _ _ _ hv)).trans ?_
        exact eta_addr_congr (VarSymb.inner_box ModalSys.NoFour.keepOnly) _ _
      · refine (Term.subst_bcTree _ _ _ A _).trans ?_
        refine (congrArg (bcTree A) (funext fun q => funext fun hq => ?_)).trans
          (itemsTree_tupB hT A (.step (.root (.free 0)) .here) (Ctx.ref_here_of hT (born_ref A)))
        exact Term.subst_eta_tm _ _ _ _ _ _ _ (at_compsIdx_compsSlot' _ _ _ _ _ q hq _ hv _ _)
  | p :: ps, hcs, h => by
      have hv : (Subst.single (σ := σ) (Δ := (ctxOf [VarType.VTypeBox A]).boxIn) (.bnd 0)
          (.tm (compsSlot (σ := σ) (born_ref A) (Ctx.Le.refl _) A.hereChains
            (VarType.compOk_compsAllB true hT A)).2)).at (.root (.bnd 0)) =
          .tm (compsSlot (σ := σ) (born_ref A) (Ctx.Le.refl _) A.hereChains
            (VarType.compOk_compsAllB true hT A)).2 := by
        rw [Subst.at_nonproj _ rfl, Subst.single_root]
      have hp := hcs p List.mem_cons_self
      refine sig_pair (holeRead_compsSlot_tupCVal hT A ps _ h.tail) ?_
      rw [compVal_tup1 hT A p h hp]
      try unfold Term.holeRead
      rw [Term.subst_mono]
      refine (Term.subst_eta_tm _ _ _ _ _ _ _ (at_compsIdx_compsSlot' _ _ _ _ _ _
        (tupCompOf_spec A p hp).1 _ hv _ ?_)).trans ?_
      · rw [(tupCompOf_spec A p hp).2]
        exact Ctx.ref_inner (VarType.CompOk.ref_mem (VarType.compOk_compsAllB true hT A)
          (tupCompOf_spec A p hp).1 (born_ref A))
      · refine eta_addr_congr (congrArg VarSymb.inner ?_) _ _
        rcases List.mem_append.mp hp with hq | hq
        · obtain ⟨_, hq, _⟩ := List.mem_map.mp hq
          cases hq
        obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hq
        change _ = (VarSymb.root (.free 0)).ext ((VarType.VTypeBox A).bcDec p')
        rw [VarType.bcDec_box A p' hp']
        rfl

/-- ⭐**P3′**: `tupC`'s value read at the born root's value with companions is the born root's
    tuple's value with companions, for either value of the flag. -/
theorem holeRead_compsSlot_tupC (A : VarType) : ∀ (b : Bool) (hb : ModalSys.T = b),
    (⟨_, Term.holeRead (compsSlot (σ := σ) (born_ref A) (Ctx.Le.refl _) (A.compsAllB b)
        (VarType.compOk_compsAllB b hb A)).2 (ShapeMap.tupC (σ := σ) A b hb).val.2⟩ :
      Σ a, Term σ (ctxOf [VarType.VTypeBox A]).boxIn
        ((tupOneTy A b).compsFlat ((tupOneTy A b).compsAllB b)) a) =
      compsVal (tup1B A b hb).2 ((tupOneTy A b).compsAllB b) (VarType.compOk_compsAllB b hb _)
  | false, _ => by
      unfold Term.holeRead
      dsimp only [ShapeMap.val]
      rw [Term.subst_mono]
      refine sig_pair rfl ((Term.subst_eta_tm _ _ _ _ _ _ _
        (by rw [Subst.at_nonproj _ rfl, Subst.single_root])).trans ?_)
      exact eta_addr_congr (VarSymb.inner_box ModalSys.NoFour.keepOnly) _ _
  | true, hb => holeRead_compsSlot_tupCVal hb A _ _ _

/-- A body over the born root's tuple read at the child, at a value `b` of the flag: `liftBody`'s
    reading, with the slot the necessary object of the child's tuple of `c`'s items. -/
def liftBody1B (l : List VarType) (A : VarType) (b : Bool) (hb : ModalSys.T = b)
    (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox (tupOneTy A b))) 1) :
    WFF σ (ctxOf (rcl l A)) 0 :=
  WFF.subst (Subst.setIdx (arrowIdx Nat.succ) (.bnd 0)
      (.tm (Term.boxtm (Term.mono (ctxOf_le_of_suffix (rcl_suffix l A)).boxIn (tup1B A b hb).2))))
    ((arrowS σ (ctxOf (rcl l A)) Nat.succ).set (.bnd 0)
      (.tm (Term.boxtm (Term.mono (ctxOf_le_of_suffix (rcl_suffix l A)).boxIn (tup1B A b hb).2))))
    (Subst.ok_set (ok_arrowS (rclImg l A)) rfl)
    (Subst.coh_set (ok_arrowS (rclImg l A)) (coh_arrowS (rclImg l A))
      ((Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).rootFresh (le_refl 0)) rfl)
    ((Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).insert _) Ctx.NoSlots.slots Φ

theorem liftBody_born (l : List VarType) (A : VarType)
    (Φ : WFF σ (bodyCtx [VarType.VTypeBox A] l) 1) :
    liftBody (rcl_suffix l A) (rclImg l A) Φ = liftBody1B l A ModalSys.T rfl Φ :=
  rfl

/-- `tupC`'s object with its slot the child's born root: the child's tuple object. -/
theorem subst_tupC_obj (l : List VarType) (A : VarType) : ∀ (b : Bool) (hb : ModalSys.T = b),
    (⟨_, Term.subst (Subst.setIdx (arrowIdx Nat.succ) (.bnd 0) (.ren (.root (.free 0))))
        ((arrowS σ (ctxOf (rcl l A)) Nat.succ).set (.bnd 0) (.ren (.root (.free 0))))
        (Subst.ok_set (ok_arrowS (rclImg l A)) (rcl_born_ref l A))
        (Subst.coh_set (ok_arrowS (rclImg l A)) (coh_arrowS (rclImg l A))
          ((Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).rootFresh (le_refl 0)) (rcl_born_ref l A))
        (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
          (ShapeMap.tupC (σ := σ) A b hb).obj.2)⟩ :
      Σ c, Term σ (ctxOf (rcl l A)) (.VTypeBox (tupOneTy A b)) c) =
      ⟨_, Term.boxtm (Term.mono (ctxOf_le_of_suffix (rcl_suffix l A)).boxIn (tup1B A b hb).2)⟩
  | false, hb => by
      have h0 : ((arrowS σ (ctxOf (rcl l A)) Nat.succ).set (.bnd 0)
          (.ren (.root (.free 0)))).at (.root (.bnd 0)) = .ren (.root (.free 0)) := by
        rw [Subst.at_nonproj _ rfl, Subst.set_root]
      dsimp only [ShapeMap.obj]
      rw [Term.subst_mono]
      refine sig_boxtm (sig_pair rfl ((Term.subst_eta_renAt _ _ _ A _ _ _
        (Ctx.ref_inner (rcl_born_ref l A)) (Subst.box_at_inner_ren _ h0)).trans ?_))
      exact (eta_addr_congr (VarSymb.inner_box ModalSys.NoFour.keepOnly) _ _).trans
        (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm)
  | true, hb => by
      have h0 : ((arrowS σ (ctxOf (rcl l A)) Nat.succ).set (.bnd 0)
          (.ren (.root (.free 0)))).at (.root (.bnd 0)) = .ren (.root (.free 0)) := by
        rw [Subst.at_nonproj _ rfl, Subst.set_root]
      dsimp only [ShapeMap.obj]
      rw [Term.subst_mono]
      refine sig_boxtm (sig_pair rfl ((Term.subst_bcTree _ _ _ (.VTypeBox A) _).trans ?_))
      refine (congrArg (bcTree (.VTypeBox A)) (funext fun q => funext fun hq => ?_)).trans
        ((itemsTree_tupB hb (.VTypeBox A) (.root (.free 0)) (rcl_born_ref l A)).trans
          (congrArg (Sigma.mk _)
            (mono_tupB (ctxOf_le_of_suffix (rcl_suffix l A)) _ _ _ _ _).symm))
      exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.box_at_inner_ren _
        (Subst.at_ext_ren _ q h0 (VarType.compAt_isProj _ q (VarType.compAt_hereChains _ q hq))))

/-- ⭐**P2**: a body over the born root's tuple, re-read through `tupC`'s object and read at the
    child, is the body read at the child's tuple — for either value of the flag. -/
theorem liftBodyR_tupC (l : List VarType) (A : VarType) (b : Bool) (hb : ModalSys.T = b)
    (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox (tupOneTy A b))) 1) :
    liftBodyR l A (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
        (ShapeMap.tupC (σ := σ) A b hb).obj.2) Φ) = liftBody1B l A b hb Φ := by
  unfold liftBodyR WFF.bodyRepl liftBody1B
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = .VTypeBox (tupOneTy A b) := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp]
    rw [Subst.set_root, Subst.set_root]
    exact SubE.sim_tm_sigma (subst_tupC_obj l A b hb).symm
  · dsimp only [Subst.comp]
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr, show (Subst.idS σ _ v) = .ren v from rfl,
      SubE.comp_ren, Subst.at_nonproj _ hlp, Subst.set_ne _ _ hvr]
    exact .refl _

/-- The arrow sends a tuple's value with companions to the images' (`tupCompsImg`). -/
theorem subst_arrow_compsVal {Δ : Ctx} {img : ℕ → ℕ} :
    ∀ (cls : List VarType) (himg : ImgOk cls Δ img) (cs : List (List Step))
      (h : (bcT cls).CompOk cs),
      (⟨_, Term.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS himg) (coh_arrowS himg)
        (compsVal (tupT cls).2 cs h).2⟩ : Σ a, Term σ Δ ((bcT cls).compsFlat cs) a) =
        tupCompsImg cls img himg cs h
  | cls, himg, [], _ => subst_arrow_tupT cls himg
  | cls, himg, _ :: ps, h => sig_pair (subst_arrow_compsVal cls himg ps h.tail) rfl

/-- ⭐**P3**: `tupC`'s value read at the obligation's value is the child's back image of its
    tuple with companions. -/
theorem holeRead_unarrT_tupC {l : List VarType} {A : VarType} {y : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) :
    (⟨_, Term.holeRead (unarrT (σ := σ) hy).2
        (ShapeMap.tupC (σ := σ) A ModalSys.T rfl).val.2⟩ :
      Σ a, Term σ (ctxOf l) ((bcT [VarType.VTypeBox A]).compsFlat
        ((bcT [VarType.VTypeBox A]).compsAllB ModalSys.T)) a) =
      tupCompsImg [VarType.VTypeBox A] (fun _ => y) (retBackImg l A hy) _
        (VarType.compOk_compsAllB _ rfl _) :=
  (Term.subst_holeRead_sig _ _ _ _ _).symm.trans
    ((sig_subst _ _ _ (holeRead_compsSlot_tupC A ModalSys.T rfl)).trans
      (subst_arrow_compsVal [VarType.VTypeBox A] (retBackImg l A hy) _ _))

/-! ## The forward arrow's body, read through the born root's value -/

omit [ModalSys.NoFour] in
theorem sig_holeAt {Γ : Ctx} {A : VarType} {a a' : Ann A} {t : Term σ Γ A a}
    {t' : Term σ Γ A a'} (h : (⟨a, t⟩ : Σ b, Term σ Γ A b) = ⟨a', t'⟩) {B : VarType} {b : Ann B}
    (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    (⟨_, Term.holeAt t s⟩ : Σ c, Term σ Γ B c) = ⟨_, Term.holeAt t' s⟩ := by
  cases h
  rfl

omit [ModalSys.NoFour] in
theorem at_compsFst_compsVal {Γ : Ctx} (θ : Subst σ Γ.boxIn) {A : VarType} {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) : ∀ (cs : List (List Step)) (h : A.CompOk cs) (v : VarSymb),
      θ.at v = .tm (compsVal sb cs h).2 → θ.at (v.ext (compsFst cs)) = .tm sb
  | [], _, _, hv => hv
  | _ :: ps, h, v, hv => by
      change θ.at ((VarSymb.step v .fst).ext (compsFst ps)) = _
      exact at_compsFst_compsVal θ sb ps h.tail _ (by rw [Subst.at_proj θ v rfl, hv]; rfl)

omit [ModalSys.NoFour] in
/-- Forgetting a value with companions' companions leaves the value. -/
theorem holeAt_forgetC_compsVal {Γ : Ctx} {A : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀)
    (cs : List (List Step)) (h : A.CompOk cs) :
    (⟨_, Term.holeAt (compsVal sb cs h).2 (ShapeMap.forgetC (σ := σ) A cs h).val.2⟩ :
      Σ c, Term σ Γ.boxIn A c) = ⟨_, sb⟩ := by
  unfold Term.holeAt
  dsimp only [ShapeMap.val]
  exact Term.subst_eta_tm _ _ _ _ _ _ _
    (at_compsFst_compsVal _ sb cs h _ (by rw [Subst.at_nonproj _ rfl, Subst.single_root]))

/-- The born root's tuple, read off its value with companions: `tupC`'s value, companions
    forgotten. -/
def arrT (A : VarType) :
    Σ c, Term σ (Ctx.empty.insert (.bnd 0) (A.compsFlat (bornComps A))) (bcT [.VTypeBox A]) c :=
  ⟨_, Term.holeAt (ShapeMap.tupC (σ := σ) A ModalSys.T rfl).val.2
    (ShapeMap.forgetC (σ := σ) (bcT [.VTypeBox A]) _ (VarType.compOk_compsAllB _ rfl _)).val.2⟩

/-- At home, `arrT` reads the obligation's value as the back images' tuple. -/
theorem holeAt_unarrT_arrT {l : List VarType} {A : VarType} {y : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) :
    (⟨_, Term.holeAt (unarrT (σ := σ) hy).2 (arrT A).2⟩ :
      Σ c, Term σ (ctxOf l) (bcT [.VTypeBox A]) c) =
      tupImgT [.VTypeBox A] (fun _ => y) (retBackImg l A hy) := by
  refine (Term.holeAt_holeAt_sig _ _ _).trans ?_
  rw [← Term.holeRead_eq_holeAt]
  refine (sig_holeAt (holeRead_unarrT_tupC hy) _).trans ?_
  rw [← Term.holeRead_eq_holeAt]
  exact holeRead_forgetC_tupCompsImg _ _ _ _ _

/-- At the born root's slot, `arrT` reads its value with companions as its tuple. -/
theorem holeAt_compsSlot_arrT (A : VarType) :
    (⟨_, Term.holeAt (compsSlot (σ := σ) (born_ref A) (Ctx.Le.refl _) (bornComps A)
        (bornComps_ok A)).2 (arrT A).2⟩ :
      Σ c, Term σ (ctxOf [VarType.VTypeBox A]).boxIn (bcT [.VTypeBox A]) c) =
      tupT [.VTypeBox A] := by
  refine (Term.holeAt_holeAt_sig _ _ _).trans ?_
  rw [← Term.holeRead_eq_holeAt]
  refine (sig_holeAt (holeRead_compsSlot_tupC A ModalSys.T rfl) _).trans ?_
  exact holeAt_forgetC_compsVal _ _ _

omit [ModalSys.NoFour] in
/-- `compsSlot` depends on the object's home only through proofs. -/
theorem compsSlot_home {Δ₁ Δ₂ Δ' : Ctx} {u : VarSymb} {C : VarType}
    (hu₁ : Δ₁.ref u = some (.VTypeBox C)) (hle₁ : Δ₁.boxIn.Le Δ')
    (hu₂ : Δ₂.ref u = some (.VTypeBox C)) (hle₂ : Δ₂.boxIn.Le Δ') :
    ∀ (cs : List (List Step)) (h : C.CompOk cs),
      compsSlot (σ := σ) hu₁ hle₁ cs h = compsSlot hu₂ hle₂ cs h
  | [], _ => rfl
  | _ :: ps, h => by
      change (⟨_, Term.pair (compsSlot hu₁ hle₁ ps h.tail).2 _⟩ : Σ c, _) =
        ⟨_, Term.pair (compsSlot hu₂ hle₂ ps h.tail).2 _⟩
      rw [compsSlot_home hu₁ hle₁ hu₂ hle₂ ps h.tail]

/-- ⭐The forward arrow's body as the unit's hole formula: the parent's body over the child's
    roots and its own tuple (`Ψ`), the born root's items read off its value with companions
    (`arrT`). -/
def thetaF {l : List VarType} (A : VarType) (Ψ : WFF σ (bodyCtx l [.VTypeBox A]) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (A.compsFlat (bornComps A)) (.VTypeBox (bcT l)))) 1 :=
  WFF.holeAt (Ctx.slotsFrom_empty.insert _)
    (Term.pair
      (Term.holeAt (Term.eta (.step (.root (.bnd 0)) .fst) (A.compsFlat (bornComps A))
        (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))) (arrT A).2)
      (Term.eta (.step (.root (.bnd 0)) .snd) (.VTypeBox (bcT l))
        (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))
    (pack2 [.VTypeBox A] (.VTypeBox (bcT l)) Ψ)

/-- **F1**: at home, the hole formula read at the obligation's value is the body read at the
    back images. -/
theorem holeRead_thetaF {l : List VarType} {A : VarType} {y : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) {x : Ann (bcT l)}
    (X : Term σ (ctxOf l).boxIn (bcT l) x) (Ψ : WFF σ (bodyCtx l [.VTypeBox A]) 1) :
    WFF.holeRead (Term.pair (unarrT hy).2 (Term.boxtm X)) (thetaF A Ψ) =
      WFF.holeRead (Term.pair (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg l A hy)).2
        (Term.boxtm X)) (pack2 [.VTypeBox A] (.VTypeBox (bcT l)) Ψ) := by
  rw [WFF.holeRead_eq_holeAt, WFF.holeRead_eq_holeAt]
  unfold thetaF
  refine (WFF.subst_holeAt _ _ _ _ _ _ _).trans (WFF.holeAt_congr _ (sig_pair ?_ ?_) _)
  · refine (Term.holeAt_holeAt_sig _ _ _).trans ((sig_holeAt (Term.holeAt_pair_fst _ _) _).trans ?_)
    exact holeAt_unarrT_arrT hy
  · exact Term.holeAt_pair_snd _ _

/-- **F2**: the unit's conjunct at the parent's tuple, read at the child, is the forward
    arrow's returning possibility, the tuple coming back with its companions. -/
theorem liftBodyR_unitBodyC_thetaF (hS : ModalSys.BStrong = true) (l : List VarType)
    (A : VarType) (Ψ : WFF σ (bodyCtx l [.VTypeBox A]) 1) (cs : List (List Step))
    (h : (bcT l).CompOk cs) :
    liftBodyR l A (WFF.unitBodyC hS (bornComps A) (bornComps_ok A) (tupT l).2 cs h
        (thetaF A Ψ)) =
      WFF.retS hS (.nec (.boxC (bcT l) cs h)) (tupCompsImg l Nat.succ (rclImg l A) cs h).2
        (WFF.mono ((ctxOf_le_of_suffix (rcl_suffix l A)).boxIn.insert (.bnd 0) _) Ψ) := by
  unfold liftBodyR WFF.unitBodyC
  refine WFF.retS_congr hS _ ?_ ?_
  · rw [Term.subst_mono]
    refine (Term.subst_congr _ (arrowS σ (ctxOf (rcl l A)) Nat.succ) _ (ok_arrowS (rclImg l A)) _
      (coh_arrowS (rclImg l A)) ?_ _).trans (subst_arrow_compsVal l (rclImg l A) cs h)
    refine Subst.sim_of fun v T _ hv => ?_
    obtain ⟨u, rfl, _⟩ := boxIn_item hv
    rw [Subst.set_ne _ _ (fun h => by cases h)]
    exact .refl _
  · rw [WFF.subst_holeAt]
    refine (WFF.holeAt_congr _ (sig_pair
      (Term.subst_compsSlot _ _ (rcl_born_ref l A)
        (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf (rcl l A)).boxIn)).root _) _ _ _
        (fun q _ hq _ => ?_) _ _)
      (Term.subst_eta_renAt _ _ _ _ _ (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)
        (Subst.under_at_slot _ (0 + 1) 0 _ _))) _).trans ?_
    · rw [Subst.at_under_ne _ _ _ (by
          rw [VarSymb.inner_rt, VarSymb.ext_rt]; exact fun h => by cases h),
        Subst.box_at_inner_ren _ (Subst.at_ext_ren _ q
          (by rw [Subst.at_nonproj _ rfl, Subst.set_root]) hq)]
      rfl
    · unfold thetaF
      refine (WFF.subst_holeAt _ _ _ _ _ _ _).trans ?_
      refine (WFF.holeAt_congr _ (sig_pair ?_ (Term.holeAt_pair_snd _ _)) _).trans
        (holeAt_tupT_pack2 (ctxOf_le_of_suffix (rcl_suffix l A)).boxIn Ψ)
      refine (Term.holeAt_holeAt_sig _ _ _).trans
        ((sig_holeAt (Term.holeAt_pair_fst _ _) _).trans ?_)
      rw [compsSlot_home (rcl_born_ref l A) _ (born_ref A)
        ((ctxOf_le_of_suffix (rcl_suffix l A)).boxIn.trans
          (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf (rcl l A)).boxIn)).root _))]
      refine (sig_holeAt (mono_compsSlot (born_ref A) (Ctx.Le.refl _)
        ((ctxOf_le_of_suffix (rcl_suffix l A)).boxIn.trans
          (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf (rcl l A)).boxIn)).root _))
        (bornComps A) (bornComps_ok A)).symm _).trans ?_
      refine (Term.mono_holeAt_sig _ _ _).symm.trans ?_
      exact sig_mono _ (holeAt_compsSlot_arrT A)

omit [ModalSys.NoFour] in
/-- A returning possibility, at any shape, with a contradictory body is absurd. -/
def Proof.ret_absurdS {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)}
    (hS : ModalSys.BStrong = true) (S : RShape) {a : Ann S.flat} (t : Term σ Γ S.flat a)
    (U : WFF σ (Γ.boxIn.insert (.bnd 0) S.ty) 1) {u : ℕ} (hu : Γ.RootFresh (.free u))
    (p : Proof σ Γ Δ (WFF.retS hS S t (WFF.and (WFF.neg U) U))) : Proof σ Γ Δ .bot := by
  have hd := Proof.ret_diaS hS .nec t _ p
  have q : Proof σ Γ.boxIn [] (WFF.neg (WFF.ex S.ty (WFF.and (WFF.neg U) U))) := by
    refine Proof.imp_intro (Proof.ex_elim u S.ty hu.boxIn
      (φ := WFF.openFree u hu.boxIn Ctx.NoSlots.slots (WFF.and (WFF.neg U) U)) (ψ := .bot)
      (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
        (Proof.lookup List.mem_cons_self)) ?_)
    exact Proof.imp_elim (Proof.and_elim_l (Proof.lookup List.mem_cons_self))
      (Proof.and_elim_r (Proof.lookup List.mem_cons_self))
  exact Proof.imp_elim hd
    (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.K_box (Δ := []) q))

/-! ## The child, born with the back invariant -/

section BirthC

variable (hS : ModalSys.BStrong = true) {tp : NodeSt σ} {A : VarType} {y : ℕ}
  (hy : (ctxOf tp.l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)

/-- ⭐The child of the obligation `◇^{S_A}[u ↦ W] Ξ` of `tp`. -/
noncomputable def retChildC (Ξ : WFF σ ((ctxOf tp.l).boxIn.insert (.bnd 0) (.VTypeBox A)) 1) :
    NodeSt σ :=
  ⟨rcl tp.l A, complete (retSeedC hS hy tp.M Ξ)⟩

variable (hM : Theory.IsMCS tp.M) {Ξ : WFF σ ((ctxOf tp.l).boxIn.insert (.bnd 0) (.VTypeBox A)) 1}
  (hΞ : WFF.retS hS (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ ∈ tp.M)

include hM hΞ

theorem retChildC_spec : retSeedC hS hy tp.M Ξ ⊆ (retChildC hS hy Ξ).M ∧
    Theory.IsMCS (retChildC hS hy Ξ).M :=
  complete_spec (retSeedC_consistent hS hy hM hΞ)

/-- The child holds the obligation's body. -/
theorem retChildC_body : liftBodyR tp.l A Ξ ∈ (retChildC hS hy Ξ).M :=
  (retChildC_spec hS hy hM hΞ).1 (Or.inl rfl)

/-- ⭐**The back arrow at birth, with companions**: a body true at the child is a returning
    possibility at the parent, the tuple coming back with its companions — or else, through
    `tupC` (`ret_map`, P2 and P3), the seed has its negation. -/
theorem retChildC_back :
    RetInvB hS ModalSys.T rfl (retChildC hS hy Ξ) tp [.VTypeBox A] (fun _ => y) tp.l
      Nat.succ := by
  obtain ⟨hsub, hmcs⟩ := retChildC_spec hS hy hM hΞ
  refine ⟨rcl_suffix tp.l A, retBackImg tp.l A hy, List.suffix_refl _, rclImg tp.l A,
    fun Φ hΦ => ?_⟩
  rw [WFF.mono_refl]
  by_contra hn
  have hn' : WFF.neg (WFF.retS hS (.nec (bornShape A)) (unarrT (σ := σ) hy).2
      (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
        (ShapeMap.tupC (σ := σ) A ModalSys.T rfl).obj.2) Φ)) ∈ tp.M := by
    refine hM.neg_mem_iff.mpr fun hr => hn ?_
    refine hM.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hr, ⟨?_⟩⟩
    exact Proof.conv (WFF.retS_congr hS _ (holeRead_unarrT_tupC hy) rfl)
      (Proof.ret_map hS .nec (S := .nec (bornShape A)) (ShapeMap.tupC A ModalSys.T rfl) _ Φ
        (Proof.lookup List.mem_cons_self))
  have h₁ := hsub (Or.inr ⟨_, hn', rfl⟩)
  have e : liftBodyR tp.l A (WFF.neg (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
      (ShapeMap.tupC (σ := σ) A ModalSys.T rfl).obj.2) Φ)) =
      WFF.neg (liftBody (rcl_suffix tp.l A) (rclImg tp.l A) Φ) := by
    rw [liftBody_born, ← liftBodyR_tupC]
    rfl
  rw [e] at h₁
  refine hmcs.1 ⟨[_, _], fun x hx => ?_, ⟨Proof.imp_elim
    (φ := liftBody (rcl_suffix tp.l A) (rclImg tp.l A) Φ) (Proof.lookup List.mem_cons_self)
    (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁
  · rw [List.mem_singleton.mp hx]; exact hΦ

/-- ⭐**The forward arrow at birth, with companions**: a body true at the parent of its roots'
    tuple is the companion unit's conjunct read at the child (F2); its negation at the far end
    would clash with the unit (`ret_absurdS`, F1), so the parent has `¬◇^{S_A}[u ↦ W]¬U` and the
    seed has `¬¬U`. -/
theorem retChildC_fwd :
    RetInvB hS ModalSys.T rfl tp (retChildC hS hy Ξ) tp.l Nat.succ [.VTypeBox A]
      (fun _ => y) := by
  obtain ⟨hsub, hmcs⟩ := retChildC_spec hS hy hM hΞ
  refine ⟨List.suffix_refl _, rclImg tp.l A, rcl_suffix tp.l A, retBackImg tp.l A hy,
    fun Ψ hΨ => ?_⟩
  refine (congrArg (· ∈ (retChildC hS hy Ξ).M) (liftBodyR_unitBodyC_thetaF hS tp.l A Ψ _
    (VarType.compOk_compsAllB _ rfl _))).mp ?_
  have hrefl := (ctxOf_le_of_suffix (List.suffix_refl tp.l)).boxIn
  have e : WFF.unitBodyC hS (bornComps A) (bornComps_ok A) (Term.mono hrefl (tupT tp.l).2) _
      (VarType.compOk_compsAllB _ rfl (bcT tp.l)) (thetaF A Ψ) =
      WFF.unitBodyC hS (bornComps A) (bornComps_ok A) (tupT tp.l).2 _
        (VarType.compOk_compsAllB _ rfl (bcT tp.l)) (thetaF A Ψ) := by
    rw [Term.mono_refl]
  have hU : WFF.neg (WFF.retS hS (.nec (bornShape A)) (unarrT (σ := σ) hy).2
      (WFF.neg (WFF.unitBodyC hS (bornComps A) (bornComps_ok A) (tupT tp.l).2 _
        (VarType.compOk_compsAllB _ rfl (bcT tp.l)) (thetaF A Ψ)))) ∈ tp.M := by
    refine hM.neg_mem_iff.mpr fun hr => hM.1 ⟨[WFF.retS hS (.nec (bornShape A))
      (unarrT (σ := σ) hy).2 (WFF.neg (WFF.unitBodyC hS (bornComps A) (bornComps_ok A)
        (tupT tp.l).2 _ (VarType.compOk_compsAllB _ rfl (bcT tp.l)) (thetaF A Ψ))),
      liftBody (List.suffix_refl tp.l) (retBackImg tp.l A hy) Ψ], fun x hx => ?_, ⟨?_⟩⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hr
      · rw [List.mem_singleton.mp hx]; exact hΨ
    refine Proof.ret_absurdS hS _ _ _ (ctxOf_fresh (l := tp.l) le_rfl)
      (Proof.conv (by rw [e]; rfl)
      (Proof.ret_unitC hS .nec (bornComps A) (bornComps_ok A) _ _
        (Term.mono hrefl (tupT tp.l).2) _ (VarType.compOk_compsAllB _ rfl (bcT tp.l)) _
        (Proof.lookup List.mem_cons_self) ?_))
    exact Proof.conv ((holeRead_thetaF hy (Term.mono hrefl (tupT tp.l).2) Ψ).trans
      (holeRead_tupImgT_pack2 (retBackImg tp.l A hy)
        (Term.boxtm (Term.mono hrefl (tupT tp.l).2)) Ψ)).symm
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
  have h₁ := hsub (Or.inr ⟨_, hU, rfl⟩)
  exact hmcs.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact h₁,
    ⟨Proof.byContra (Proof.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.lookup List.mem_cons_self))⟩⟩

end BirthC

end BArrow

end V12M
