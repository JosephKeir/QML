import QML.QML_v12m_BRetChildXC
import QML.QML_v12m_BRetChildD

/-!
# QML v12m — strong B on the network: the back-witness child, for either T

The flag-generic replacement of `QML_v12m_BRetChildD` (docs §11.21, stage 3c): the child of an
obligation `◇^{S_A × ◇X}[⟨u, e⟩ ↦ ⟨W, z⟩] Ξ`, its way home in the extent of its own root
`e : ◇X`.  The obligation binds the born root itself with all its companions next to the possible
part (`.wit (bornShape A) X`), valued at `unarrT` and the content `z`.  The child's variables are
`rclD` (`c : □A`, `e : ◇X`, then the parent's two up), and the seed's pull-back sends `c` and `e`
to the opened slot's components.

* `liftBodyDR`: a body over the born root and the possible part read at the child.
* ⭐`retSeedDC_consistent`: by the K-law with a possible part at the born root's shape
  (`Proof.retD_KC_node`) and the pull-back (`retPullDC`, ⭐`subst_retPullDC_liftBodyDR`).
* The back-committed roots are `[◇X, □A]`, so the child's tuple is the born root's padded with
  `()`: the map `mapD = tupC ; padC` (`holeAt_compsVal_padC`, `compVal_padC`).
* ⭐`retChildDC_back`: born with `RetInvWB` home in `e`'s extent, through `mapD` (`ret_map`, P2
  `liftBodyDR_mapD`, P3 `holeRead_unarrDT_mapD`, contraposed).
* ⭐`retChildDC_fwd`: born with `RetInvXB` out along `e`, through the companion unit along the
  returned possible part (`ret_unitDC`, F1 `holeRead_thetaD`, F2
  `liftBodyDR_unitBodyDC_thetaD`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## The back-witness child's roots -/

section Layout

variable (l : List VarType) (A X : VarType)

omit [ModalSys.NoFour] in
/-- The back-committed root `c`. -/
theorem bclD_c : (ctxOf (bclD A X)).ref (.root (.free 0)) = some (.VTypeBox A) :=
  (ctxOf_le_append [.VTypeDia X] [.VTypeBox A]).ref (born_ref A)

omit [ModalSys.NoFour] in
theorem rclD_c : (ctxOf (rclD l A X)).ref (.root (.free 0)) = some (.VTypeBox A) :=
  (ctxOf_le_of_suffix (rclD_suffix l A X)).ref (bclD_c A X)

omit [ModalSys.NoFour] in
theorem rclD_e : (ctxOf (rclD l A X)).ref (.root (.free 1)) = some (.VTypeDia X) :=
  (ctxOf_le_of_suffix (rclD_suffix l A X)).ref (bclD_e A X)

/-- The slot's entry at the child: the pair of its roots `c` and `e`. -/
def entryD : SubE σ (ctxOf (rclD l A X)) :=
  .tm (Term.pair (Term.eta (.root (.free 0)) (.VTypeBox A) (rclD_c l A X))
    (Term.eta (.root (.free 1)) (.VTypeDia X) (rclD_e l A X)))

end Layout

/-! ## Reading a body over the born root and the possible part at the child -/

/-- ⭐A body over the born root and the possible part, read at the back-witness child: the
    parent's items along the arrow (`· + 2`), the slot the pair of the child's roots `⟨c, e⟩`. -/
def liftBodyDR (l : List VarType) (A X : VarType)
    (Ξ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (RShape.wit (bornShape A) X).ty) 1) :
    WFF σ (ctxOf (rclD l A X)) 0 :=
  WFF.subst (Subst.setIdx (arrowIdx (· + 2)) (.bnd 0) (entryD (σ := σ) l A X))
    ((arrowS σ (ctxOf (rclD l A X)) (· + 2)).set (.bnd 0) (entryD l A X))
    (Subst.ok_set (ok_arrowS (rclDImg l A X)) rfl)
    (Subst.coh_set (ok_arrowS (rclDImg l A X)) (coh_arrowS (rclDImg l A X))
      ((Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).rootFresh (le_refl 0)) rfl)
    ((Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).insert _) Ctx.NoSlots.slots Ξ

/-! ## Pulling the child back, with its roots to the opened slot's components -/

/-- The parent's `□` view with the slot opened at `u = l.length`, at the obligation's type. -/
abbrev pullCtxDC (l : List VarType) (A X : VarType) : Ctx :=
  (ctxOf l).boxIn.insert (.free l.length) (RShape.wit (bornShape A) X).ty

/-- ⭐Pulling the back-witness child back into the parent's `□` view with the slot opened at `u`:
    `c` to `u.fst`, `e` to `u.snd`, and root `r + 2` to the tuple of root `r`'s items.  No fact
    about `bc` is used. -/
def retPullDC (σ : Signature) (l : List VarType) (A X : VarType) :
    Subst σ (pullCtxDC l A X) := fun v =>
  match v with
  | .root (.free 0) => .ren (.step (.root (.free l.length)) .fst)
  | .root (.free 1) => .ren (.step (.root (.free l.length)) .snd)
  | .root (.free (r + 2)) =>
      if h : r < l.length then .tm (Term.mono (Ctx.le_insert (pullCtx_fresh l).root _)
        (tup (.root (.free r)) (rootTy l r) (by
          rw [Ctx.ref_nonproj _ rfl]; exact ctxOf_root_lt h)))
      else .hide
  | _ => .hide

/-- Where pulling back sends annotation indices: along the entry at the index's root. -/
def retPullDCIdx (σ : Signature) (l : List VarType) (A X : VarType) (a : VarSymb) : VarSymb :=
  match a.rt with
  | .free r => (retPullDC σ l A X (.root (.free r))).idxAlong a.path
  | .bnd _ => a

section PullDC

variable (l : List VarType) (A X : VarType)

theorem retPullDC_add {r : ℕ} (h : r < l.length) :
    retPullDC σ l A X (.root (.free (r + 2))) = .tm (Term.mono
      (Ctx.le_insert (pullCtx_fresh l).root _) (tup (.root (.free r)) (rootTy l r) (by
          rw [Ctx.ref_nonproj _ rfl]; exact ctxOf_root_lt h))) :=
  dif_pos h

omit [ModalSys.NoFour] in
theorem pullCtxDC_ref_fst :
    (pullCtxDC l A X).ref (.step (.root (.free l.length)) .fst) = some (.VTypeBox A) :=
  Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)

omit [ModalSys.NoFour] in
theorem pullCtxDC_ref_snd :
    (pullCtxDC l A X).ref (.step (.root (.free l.length)) .snd) = some (.VTypeDia X) :=
  Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)

theorem ok_retPullDC : Subst.Ok (ctxOf (rclD l A X)) (retPullDC σ l A X) := by
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
      exact pullCtxDC_ref_fst l A X
  | 1, _ =>
      rw [rootTy_rclD_one]
      exact pullCtxDC_ref_snd l A X
  | r + 2, hr =>
      have hr' : r < l.length := by rw [length_rclD] at hr; omega
      rw [rootTy_rclD_add, rootTy_map_bc l r hr', retPullDC_add l A X hr']
      rfl

theorem coh_retPullDC :
    Subst.Coh (retPullDCIdx σ l A X) (ctxOf (rclD l A X)) (retPullDC σ l A X) := by
  refine Subst.coh_of (ok_retPullDC l A X) ?_
  intro v T _ hv p
  obtain ⟨r, rfl⟩ := ctxOf_decl hv
  have hrt : ((VarSymb.root (.free r)).ext p).rt = .free r := VarSymb.ext_rt _ _
  rw [retPullDCIdx, hrt, VarSymb.ext_path]
  rfl

/-- Pulling back along an encoded projection path from root `r + 2` reaches the tuple of the
    component. -/
theorem at_retPullDC_tup : ∀ {u : VarSymb} {U : VarType} (hu : (ctxOf l).ref u = some U) (r : ℕ),
    u.rt = .free r →
      (retPullDC σ l A X).at ((VarSymb.root (.free (r + 2))).ext (encPath u.path)) =
        .tm (Term.mono (Ctx.le_insert (pullCtx_fresh l).root _) (tup u U hu))
  | .root (.free r'), U, hu, r, hrt => by
      change Root.free r' = Root.free r at hrt
      cases hrt
      obtain ⟨r₀, e, hr', -⟩ := ref_rt hu
      cases e
      have hU := hu
      rw [Ctx.ref_nonproj _ rfl, ctxOf_root_lt hr'] at hU
      cases hU
      exact retPullDC_add l A X hr'
  | .root (.bnd _), _, _, _, hrt => by cases hrt
  | .step u s, U, hu, r, hrt => by
      have hproj : s.isProj = true := (reach_ppath hu).1 s (by simp [VarSymb.path])
      have hu' := hu
      simp only [Ctx.ref, if_pos hproj] at hu'
      cases hU : (ctxOf l).ref u with
      | none => rw [hU] at hu'; cases hu'
      | some U' =>
          rw [hU] at hu'
          have ih := at_retPullDC_tup hU r hrt
          change (retPullDC σ l A X).at
            ((VarSymb.root (.free (r + 2))).ext (encPath (u.path ++ [s]))) = _
          rw [show encPath (u.path ++ [s]) = encPath u.path ++ [encStep s] from
            List.map_append, VarSymb.ext_step, Subst.at_proj _ _ (encStep_proj hproj), ih]
          exact proj_tupB_mono _ rfl hU hproj hu' hu

/-- An item of the parent's `□` view, sent along the child's arrow and pulled back, is itself. -/
theorem at_retPullDC_item {w : VarSymb} {T : VarType}
    (hw : (ctxOf l).ref w = some (.VTypeBox T)) :
    (retPullDC σ l A X).at (itemAt (imgRoot (· + 2) w.rt) w) =
      .tm (Term.eta (.step w .box) T ((Ctx.le_insert (pullCtx_fresh l).root _).ref
        (Ctx.ref_boxIn_of ModalSys.NoFour.keepOnly hw))) := by
  obtain ⟨r, hr, _, _⟩ := ref_rt hw
  rw [hr]
  change (retPullDC σ l A X).at (itemAt (.free (r + 2)) w) = _
  rw [at_item_of_tupB_mono _ _ _ hw ModalSys.T rfl (at_retPullDC_tup l A X hw r hr),
    Term.mono_eta]

/-- The slot's entry at the child, pulled back: the opened slot, η-expanded. -/
theorem subst_retPullDC_entry :
    (⟨_, Term.subst (retPullDCIdx σ l A X) (retPullDC σ l A X) (ok_retPullDC l A X)
        (coh_retPullDC l A X) (Term.pair
          (Term.eta (.root (.free 0)) (.VTypeBox A) (rclD_c l A X))
          (Term.eta (.root (.free 1)) (.VTypeDia X) (rclD_e l A X)))⟩ :
        Σ a, Term σ (pullCtxDC l A X) (RShape.wit (bornShape A) X).ty a) =
      ⟨_, Term.eta (.root (.free l.length)) _ (Ctx.ref_insert_root _ _ _)⟩ :=
  sig_pair (Term.subst_eta_renAt _ _ _ _ _ _ _ (pullCtxDC_ref_fst l A X) rfl)
    (Term.subst_eta_renAt _ _ _ _ _ _ _ (pullCtxDC_ref_snd l A X) rfl)

/-- ⭐**Pulling back opens the slot, for a back-witness child**: a body read at the child, pulled
    back, is the body with its slot opened at `u`. -/
theorem subst_retPullDC_liftBodyDR
    (Ξ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (RShape.wit (bornShape A) X).ty) 1) :
    WFF.subst (retPullDCIdx σ l A X) (retPullDC σ l A X) (ok_retPullDC l A X)
        (coh_retPullDC l A X) Ctx.NoSlots.slots Ctx.NoSlots.slots (liftBodyDR l A X Ξ) =
      WFF.openFree l.length (pullCtx_fresh l) Ctx.NoSlots.slots Ξ := by
  unfold liftBodyDR WFF.openFree
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Ξ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = (RShape.wit (bornShape A) X).ty := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    rw [Subst.toFree_root]
    dsimp only [Subst.comp]
    rw [Subst.set_root]
    dsimp only [entryD, SubE.comp]
    rw [subE_tm_sig (subst_retPullDC_entry l A X)]
    exact .ren_eta _ _
  · obtain ⟨w, rfl, hw⟩ := body_itemT hv hvr
    rw [Subst.toFree_ne _ _ _ _ hvr]
    dsimp only [Subst.comp]
    rw [Subst.set_ne _ _ hvr]
    change SubE.Sim T (((Subst.idRen _) (.step w .box)).mono _)
      ((retPullDC σ l A X).at (itemAt (imgRoot (· + 2) w.rt) w))
    rw [at_retPullDC_item l A X hw]
    exact .ren_eta _ _

end PullDC

/-! ## The seed and its consistency -/

section SeedDC

variable (hS : ModalSys.BStrong = true) {l : List VarType} {A X : VarType} {y z : ℕ}
  (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
  (hz : (ctxOf l).ref (.root (.free z)) = some X)

/-- The obligation's value: the born root's value with companions sent along the back arrow, and
    the content `z`. -/
abbrev unarrDT : Σ a, Term σ (ctxOf l) (RShape.wit (bornShape A) X).flat a :=
  ⟨_, Term.pair (unarrT (σ := σ) hy).2 (Term.eta (.root (.free z)) X hz)⟩

/-- ⭐The seed of the back-witness child of `◇^{S_A × ◇X}[⟨u, e⟩ ↦ ⟨W, z⟩] Ξ`: the obligation's
    body, and `¬Θ` for every `¬◇^{S_A × ◇X}[⟨u, e⟩ ↦ ⟨W, z⟩] Θ` of the parent, read at the
    child. -/
def retSeedDC (M : Set (WFF σ (ctxOf l) 0))
    (Ξ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (RShape.wit (bornShape A) X).ty) 1) :
    Set (WFF σ (ctxOf (rclD l A X)) 0) :=
  {liftBodyDR l A X Ξ} ∪
    {φ | ∃ Θ, WFF.neg (WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) hy hz).2 Θ) ∈ M ∧
      φ = liftBodyDR l A X (WFF.neg Θ)}

theorem retSeedDC_list {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.IsMCS M)
    {Ξ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (RShape.wit (bornShape A) X).ty) 1}
    (hΞ : WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) hy hz).2 Ξ ∈ M) :
    ∀ L : List (WFF σ (ctxOf (rclD l A X)) 0), (∀ δ ∈ L, δ ∈ retSeedDC hS hy hz M Ξ) →
      ∃ Ξ', WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) hy hz).2 Ξ' ∈ M ∧
        Theory.Derives {liftBodyDR l A X Ξ'} (liftBodyDR l A X Ξ) ∧
        ∀ δ ∈ L, Theory.Derives {liftBodyDR l A X Ξ'} δ
  | [], _ => ⟨Ξ, hΞ, Theory.Derives.of_mem rfl, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨Ξ₀, hΞ₀, hΦ₀, hL⟩ := retSeedDC_list hM hΞ L
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      rcases h δ List.mem_cons_self with hδ | ⟨Θ, hΘ, rfl⟩
      · refine ⟨Ξ₀, hΞ₀, hΦ₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · rw [Set.mem_singleton_iff.mp hδ]
          exact hΦ₀
        · exact hL d hd
      · have hand : ∀ φ, Proof σ _ [liftBodyDR l A X (Ξ₀.and Θ.neg)] φ →
            Theory.Derives {liftBodyDR l A X (Ξ₀.and Θ.neg)} φ :=
          fun φ p => ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; rfl, ⟨p⟩⟩
        have h₀ := hand _ (Proof.and_elim_l (ψ := liftBodyDR l A X Θ.neg)
          (Proof.lookup List.mem_cons_self))
        have h₁ := hand _ (Proof.and_elim_r (φ := liftBodyDR l A X Ξ₀)
          (Proof.lookup List.mem_cons_self))
        have htr : ∀ d, Theory.Derives {liftBodyDR l A X Ξ₀} d →
            Theory.Derives {liftBodyDR l A X (Ξ₀.and Θ.neg)} d :=
          fun d hd => Derives.trans (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact h₀) hd
        refine ⟨Ξ₀.and Θ.neg, hM.closed ⟨[_, _], fun x hx => ?_,
          ⟨Proof.retD_KC_node hS (bornComps A) (bornComps_ok A) _ Ξ₀ Θ
            (Proof.lookup List.mem_cons_self)
            (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩,
          htr _ hΦ₀, fun d hd => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hΞ₀
          · rw [List.mem_singleton.mp hx]; exact hΘ
        rcases List.mem_cons.mp hd with rfl | hd
        · exact h₁
        · exact htr d (hL d hd)

/-- ⭐**The back-witness child's seed is consistent**, for either value of T. -/
theorem retSeedDC_consistent {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.IsMCS M)
    {Ξ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (RShape.wit (bornShape A) X).ty) 1}
    (hΞ : WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) hy hz).2 Ξ ∈ M) :
    Theory.Consistent (retSeedDC hS hy hz M Ξ) := by
  rintro ⟨L, hL, hp⟩
  obtain ⟨Ξ', hΞ', -, hder⟩ := retSeedDC_list hS hy hz hM hΞ L hL
  obtain ⟨Δ, hΔ, ⟨p⟩⟩ := Derives.trans (fun x hx => hder x hx) ⟨L, fun x hx => hx, hp⟩
  have p' : Proof σ (ctxOf (rclD l A X)) [liftBodyDR l A X Ξ'] .bot :=
    Proof.ofSubset (fun x hx => by
      rw [Set.mem_singleton_iff.mp (hΔ x hx)]; exact List.mem_cons_self) p
  haveI : (pullCtxDC l A X).Presented :=
    Ctx.Presented.insertFree inferInstance _ (pullCtx_fresh l) _
  have q := Proof.subst p' (retPullDC σ l A X) (ok_retPullDC l A X) (coh_retPullDC l A X)
    Ctx.NoSlots.slots
  simp only [List.map_cons, List.map_nil, subst_retPullDC_liftBodyDR] at q
  refine hM.1 ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hΞ',
    ⟨Proof.ret_refuteS hS _ _ Ξ' ?_ (Proof.lookup List.mem_cons_self)⟩⟩
  refine Proof.imp_intro (Proof.ex_elim l.length _ (pullCtx_fresh l)
    (φ := WFF.openFree _ (pullCtx_fresh l) Ctx.NoSlots.slots Ξ') (ψ := .bot)
    (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
      (Proof.lookup List.mem_cons_self)) ?_)
  exact Proof.ofSubset (fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_self) q

end SeedDC

/-! ## Padding, on terms

The back-witness child's back-committed roots are `[◇X, □A]`, so its tuple is the born root's
padded with `()`: the map `mapD = tupC ; padC`.  The identities below are `tupC`'s (P2, P3)
followed by `padC`'s. -/

omit [ModalSys.NoFour] in
theorem sig_unboxtm {Γ : Ctx} {A : VarType} {a a' : Ann (.VTypeBox A)}
    {t : Term σ Γ (.VTypeBox A) a} {t' : Term σ Γ (.VTypeBox A) a'}
    (h : (⟨a, t⟩ : Σ c, Term σ Γ (.VTypeBox A) c) = ⟨a', t'⟩) :
    Term.unboxtm t = Term.unboxtm t' := by
  cases h
  rfl

omit [ModalSys.NoFour] in
theorem sig_holeAt_right {Γ : Ctx} {A : VarType} {a : Ann A} (t : Term σ Γ A a) {B : VarType}
    {b b' : Ann B} {s : Term σ (Ctx.empty.insert (.bnd 0) A) B b}
    {s' : Term σ (Ctx.empty.insert (.bnd 0) A) B b'}
    (h : (⟨b, s⟩ : Σ c, Term σ (Ctx.empty.insert (.bnd 0) A) B c) = ⟨b', s'⟩) :
    (⟨_, Term.holeAt t s⟩ : Σ c, Term σ Γ B c) = ⟨_, Term.holeAt t s'⟩ := by
  cases h
  rfl

/-- Padding a necessary object `□sb`: `□⟨sb, ()⟩`. -/
theorem holeAt_boxtm_padC_obj {Γ : Ctx} {Z : VarType} {a₀ : Ann Z} (sb : Term σ Γ.boxIn Z a₀)
    (b : Bool) (hb : ModalSys.T = b) :
    (⟨_, Term.holeAt (Term.boxtm sb) (ShapeMap.padC (σ := σ) Z b hb).obj.2⟩ :
      Σ c, Term σ Γ (.VTypeBox (.VTypeProd Z .VTypeOne)) c) =
      ⟨_, Term.boxtm (Term.pair sb Term.unit)⟩ := by
  unfold Term.holeAt
  dsimp only [ShapeMap.obj]
  exact sig_boxtm (sig_pair (Term.subst_eta_tm _ _ _ _ _ _ sb
    (Subst.box_at_inner_boxtm _ (Subst.at_single_root _ _))) rfl)

/-- Under T, a padded value's companion `fst :: q` is the value's companion `q`. -/
theorem compVal_padC {Γ : Ctx} {Z : VarType} {a₀ : Ann Z} (sb : Term σ Γ.boxIn Z a₀)
    (q : List Step) {ps ps' : List (List Step)}
    (h : (VarType.VTypeProd Z .VTypeOne).CompOk ((.fst :: q) :: ps))
    (hq : Z.CompOk (q :: ps')) :
    compVal (σ := σ) (Term.pair sb Term.unit) (.fst :: q) h = compVal sb q hq := by
  obtain ⟨hT, hall, -⟩ := hq.resolve_left (List.cons_ne_nil _ _)
  have hC : Z.compAt q = some ((Z.compAt q).getD .VTypeOne) := by
    obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp (hall q List.mem_cons_self)
    rw [hC]
    rfl
  have hr := Ctx.ref_insert_root Ctx.empty (.bnd 0) (VarType.VTypeBox Z)
  let θ := Subst.single (σ := σ) (Δ := Ctx.empty.insert (.bnd 0) (.VTypeBox Z)) (.bnd 0)
    (.tm (ShapeMap.padC (σ := σ) Z true hT).obj.2)
  have h0 : θ.at (.step (.step (.root (.bnd 0)) .here) .fst) =
      .tm (Term.eta (.step (.root (.bnd 0)) .here) Z (Ctx.ref_here_of hT hr)) := by
    rw [Subst.at_proj θ _ rfl, Subst.at_proj θ _ rfl, Subst.at_single_root]
    dsimp only [ShapeMap.obj]
    rw [SubE.proj_boxtm_here _ hT]
    change SubE.tm (Term.collapse _ (Term.eta (VarSymb.root (.bnd 0)).inner Z _)) = _
    exact SubE.tm_eq_of_sig ((Term.collapse_eta _ _ Z _).trans
      (Term.eta_congr (VarSymb.inner_collapse_zero _) Z _ _))
  have h' := Ctx.ref_compAt hT q (Ctx.ref_here_of hT hr) hC
  have h2 := Subst.at_ext_eta hT θ q (Ctx.ref_here_of hT hr) hC h' h0
  have key : (⟨_, Term.holeAt (ShapeMap.padC (σ := σ) Z true hT).obj.2 (Term.boxtm (Term.eta
      ((VarSymb.step (.root (.bnd 0)) .here).ext (.fst :: q)).inner
      (((VarType.VTypeProd Z .VTypeOne).compAt (.fst :: q)).getD .VTypeOne)
      (Ctx.ref_inner (h.ref_head (Ctx.ref_insert_root _ _ _)))))⟩ :
      Σ c, Term σ (Ctx.empty.insert (.bnd 0) (.VTypeBox Z)) (.VTypeBox ((Z.compAt q).getD
        .VTypeOne)) c) =
      ⟨_, Term.boxtm (Term.eta ((VarSymb.step (.root (.bnd 0)) .here).ext q).inner
        ((Z.compAt q).getD .VTypeOne) (Ctx.ref_inner h'))⟩ :=
    sig_boxtm (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm θ h2))
  unfold compVal
  exact sig_unboxtm ((sig_holeAt (holeAt_boxtm_padC_obj sb true hT).symm _).trans
    ((Term.holeAt_holeAt_sig _ _ _).symm.trans (sig_holeAt_right _ key)))

omit [ModalSys.NoFour] in
/-- A substitution holding a value with companions at `v` holds each companion's contents at its
    index. -/
theorem at_compsIdx_compsVal {Γ : Ctx} (θ : Subst σ Γ.boxIn) {A : VarType} {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) : ∀ (cs : List (List Step)) (h : A.CompOk cs) (q : List Step),
      q ∈ cs → ∀ {ps' : List (List Step)} (hq : A.CompOk (q :: ps')) (v : VarSymb),
      θ.at v = .tm (compsVal sb cs h).2 → θ.at (v.ext (compsIdx cs q)) = .tm (compVal sb q hq).2
  | [], _, _, hq, _, _, _, _ => absurd hq List.not_mem_nil
  | p :: ps, h, q, hq, ps', hq', v, hv => by
      by_cases hqp : q = p
      · subst hqp
        have e : v.ext (compsIdx (q :: ps) q) = .step v .snd := by simp [compsIdx, VarSymb.ext]
        rw [e, Subst.at_proj θ v rfl, hv]
        rfl
      · have hq₁ : q ∈ ps := (List.mem_cons.mp hq).resolve_left hqp
        have e : v.ext (compsIdx (p :: ps) q) = (VarSymb.step v .fst).ext (compsIdx ps q) := by
          simp [compsIdx, hqp, VarSymb.ext]
        rw [e]
        exact at_compsIdx_compsVal θ sb ps h.tail q hq₁ hq' _
          (by rw [Subst.at_proj θ v rfl, hv]; rfl)

/-- Under T, padding a value with companions: `⟨sb, ()⟩`, with `sb`'s companions under `fst`. -/
theorem holeAt_padCVal_compsVal {Γ : Ctx} {Z : VarType} {a₀ : Ann Z} (sb : Term σ Γ.boxIn Z a₀)
    (hZ : Z.CompOk Z.hereChains) :
    ∀ (cs : List (List Step)) (hcs : ∀ p ∈ cs, p ∈ (VarType.VTypeProd Z .VTypeOne).hereChains)
      (h : (VarType.VTypeProd Z .VTypeOne).CompOk cs),
      (⟨_, Term.holeAt (compsVal sb Z.hereChains hZ).2 (padCVal (σ := σ) Z cs hcs).2⟩ :
        Σ c, Term σ Γ.boxIn ((VarType.VTypeProd Z .VTypeOne).compsFlat cs) c) =
        compsVal (Term.pair sb Term.unit) cs h
  | [], _, _ =>
      sig_pair (Term.subst_eta_tm _ _ _ _ _ _ sb
        (at_compsFst_compsVal _ sb _ hZ _ (Subst.at_single_root _ _))) rfl
  | p :: ps, hcs, h => by
      refine sig_pair (holeAt_padCVal_compsVal sb hZ ps _ h.tail) ?_
      obtain ⟨hp, hq⟩ := padC_mem (hcs p List.mem_cons_self)
      rcases p with _ | ⟨s, q⟩
      · cases hp
      cases hp
      obtain ⟨hT, -, -⟩ := h.resolve_left (List.cons_ne_nil _ _)
      have hq₁ : Z.CompOk [q] :=
        Or.inr ⟨hT, fun p' hp' => by
          rw [List.mem_singleton.mp hp']
          exact VarType.compAt_hereChains _ q hq, List.nodup_singleton q⟩
      exact (Term.subst_eta_tm _ _ _ _ _ _ _ (at_compsIdx_compsVal _ sb _ hZ q hq hq₁ _
        (Subst.at_single_root _ _))).trans (compVal_padC sb q h hq₁).symm

/-- ⭐**Padding a value with companions**, for either value of the flag. -/
theorem holeAt_compsVal_padC {Γ : Ctx} {Z : VarType} {a₀ : Ann Z} (sb : Term σ Γ.boxIn Z a₀) :
    ∀ (b : Bool) (hb : ModalSys.T = b),
      (⟨_, Term.holeAt (compsVal sb (Z.compsAllB b) (VarType.compOk_compsAllB b hb Z)).2
          (ShapeMap.padC (σ := σ) Z b hb).val.2⟩ :
        Σ c, Term σ Γ.boxIn ((VarType.VTypeProd Z .VTypeOne).compsFlat
          ((VarType.VTypeProd Z .VTypeOne).compsAllB b)) c) =
        compsVal (Term.pair sb Term.unit) _ (VarType.compOk_compsAllB b hb _)
  | false, _ => by
      dsimp only [ShapeMap.val]
      exact sig_pair (Term.subst_eta_tm _ _ _ _ _ _ sb (Subst.at_single_root _ _)) rfl
  | true, hb => holeAt_padCVal_compsVal sb _ _ _ _

omit [ModalSys.NoFour] in
/-- A companion's contents of a weakened value: the contents weakened. -/
theorem mono_compVal {Γ Γ' : Ctx} (hle : Γ.Le Γ') {A : VarType} {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) (p : List Step) {ps : List (List Step)}
    (h : A.CompOk (p :: ps)) :
    compVal (Term.mono hle.boxIn sb) p h = ⟨_, Term.mono hle.boxIn (compVal sb p h).2⟩ :=
  (sig_unboxtm (Term.mono_holeAt_sig hle (Term.boxtm sb) (Term.boxtm (Term.eta
    ((VarSymb.step (.root (.bnd 0)) .here).ext p).inner ((A.compAt p).getD .VTypeOne)
      (Ctx.ref_inner (h.ref_head (Ctx.ref_insert_root _ _ _))))))).symm

omit [ModalSys.NoFour] in
/-- A weakened value with companions: the value with companions weakened. -/
theorem mono_compsVal {Γ Γ' : Ctx} (hle : Γ.Le Γ') {A : VarType} {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) : ∀ (cs : List (List Step)) (h : A.CompOk cs),
      compsVal (Term.mono hle.boxIn sb) cs h = ⟨_, Term.mono hle.boxIn (compsVal sb cs h).2⟩
  | [], _ => rfl
  | p :: ps, h => sig_pair (mono_compsVal hle sb ps h.tail) (mono_compVal hle sb p h)

/-- An arrow on a term weakened from a shorter list is the arrow from the shorter list, if the
    images agree on its roots. -/
theorem subst_arrow_mono {l l' : List VarType} (hl : (ctxOf l).Le (ctxOf l')) {Δ : Ctx}
    {img img' : ℕ → ℕ} (himg : ImgOk l Δ img) (himg' : ImgOk l' Δ img')
    (he : ∀ r, r < l.length → img' r = img r) {T : VarType} {a : Ann T}
    (t : Term σ (ctxOf l).boxIn T a) :
    (⟨_, Term.subst (arrowIdx img') (arrowS σ Δ img') (ok_arrowS himg') (coh_arrowS himg')
        (Term.mono hl.boxIn t)⟩ : Σ c, Term σ Δ T c) =
      ⟨_, Term.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS himg) (coh_arrowS himg) t⟩ := by
  rw [Term.subst_mono]
  refine Term.subst_congr _ _ _ _ _ _ (Subst.sim_of fun v U _ hv => ?_) t
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  obtain ⟨r, hr, hlt, -⟩ := ref_rt hu
  change SubE.Sim U (.ren (itemAt (imgRoot img' u.rt) u)) (.ren (itemAt (imgRoot img u.rt) u))
  rw [hr]
  change SubE.Sim U (.ren (itemAt (.free (img' r)) u)) (.ren (itemAt (.free (img r)) u))
  rw [he r hlt]
  exact .refl _

/-- The back-witness child's tuple map: the born root's tuple, padded with `()`. -/
abbrev mapD (A X : VarType) : ShapeMap σ (bornShape A) (tupShape ModalSys.T rfl (bclD A X)) :=
  .comp (.tupC A ModalSys.T rfl) (.padC (tupOneTy A ModalSys.T) ModalSys.T rfl)

/-- Padding the born root's tuple with companions, at the back images: the tuple of
    `[◇X, □A]`. -/
theorem tupCompsImg_padC {l : List VarType} {A X : VarType} {y o : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (himg : ImgOk (bclD A X) (ctxOf l) (backImgD y o)) :
    (⟨_, Term.holeAt (tupCompsImg (σ := σ) [VarType.VTypeBox A] (fun _ => y) (retBackImg l A hy)
        _ (VarType.compOk_compsAllB ModalSys.T rfl _)).2
        (ShapeMap.padC (σ := σ) (tupOneTy A ModalSys.T) ModalSys.T rfl).val.2⟩ :
      Σ c, Term σ (ctxOf l)
        ((bcT (bclD A X)).compsFlat ((bcT (bclD A X)).compsAllB ModalSys.T)) c) =
      tupCompsImg (bclD A X) (backImgD y o) himg _ (VarType.compOk_compsAllB ModalSys.T rfl _) := by
  refine (sig_holeAt (subst_arrow_compsVal [VarType.VTypeBox A] (retBackImg l A hy) _ _).symm
    _).trans ?_
  refine (Term.subst_holeAt_sig _ _ _ _ _).symm.trans ?_
  refine (sig_subst _ _ _
    (holeAt_compsVal_padC (tupT (σ := σ) [VarType.VTypeBox A]).2 ModalSys.T rfl)).trans ?_
  refine Eq.trans ?_ (subst_arrow_compsVal (bclD A X) himg _ _)
  refine (subst_arrow_mono (ctxOf_le_append [.VTypeDia X] [.VTypeBox A]) (retBackImg l A hy) himg
    (fun r hr => ?_) _).symm.trans (sig_subst _ _ _ (mono_compsVal
      (ctxOf_le_append [.VTypeDia X] [.VTypeBox A])
      (Term.pair (tupT (σ := σ) [VarType.VTypeBox A]).2 Term.unit) _ _).symm)
  obtain rfl : r = 0 := by simpa using hr
  rfl

omit [ModalSys.NoFour] in
/-- A map at a witnessed shape, read at a pair: the map on the necessary part, the content
    kept. -/
theorem holeRead_liftVal_wit {Γ : Ctx} [Γ.NoSlots] {N T : NShape} {X : VarType}
    (F : ShapeMap σ N T) {a : Ann N.flat} (t : Term σ Γ N.flat a) {b : Ann X}
    (u : Term σ Γ X b) :
    (⟨_, Term.holeRead (Term.pair t u) (ShapeMap.liftVal (.wit N X) F).2⟩ :
      Σ c, Term σ Γ (RShape.wit T X).flat c) = ⟨_, Term.pair (Term.holeAt t F.val.2) u⟩ := by
  rw [Term.holeRead_eq_holeAt]
  dsimp only [ShapeMap.liftVal]
  exact sig_pair ((Term.holeAt_holeAt_sig _ _ _).trans (sig_holeAt (Term.holeAt_pair_fst _ _) _))
    (Term.holeAt_pair_snd _ _)

/-- ⭐**P3 for a back-witness child**: the padded tuple map's value read at the obligation's value
    is the back images' tuple with companions, and the content. -/
theorem holeRead_unarrDT_mapD {l : List VarType} {A X : VarType} {y o z : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (hz : (ctxOf l).ref (.root (.free z)) = some X)
    (himg : ImgOk (bclD A X) (ctxOf l) (backImgD y o)) :
    (⟨_, Term.holeRead (unarrDT (σ := σ) hy hz).2
        (ShapeMap.liftVal (.wit (bornShape A) X) (mapD A X)).2⟩ :
      Σ c, Term σ (ctxOf l) (RShape.wit (tupShape ModalSys.T rfl (bclD A X)) X).flat c) =
      ⟨_, Term.pair (tupCompsImg (bclD A X) (backImgD y o) himg _
        (VarType.compOk_compsAllB ModalSys.T rfl _)).2 (Term.eta (.root (.free z)) X hz)⟩ := by
  refine (holeRead_liftVal_wit (Γ := ctxOf l) (mapD A X) (unarrT (σ := σ) hy).2
    (Term.eta (.root (.free z)) X hz)).trans (sig_pair ?_ rfl)
  have h3 := holeRead_unarrT_tupC (σ := σ) hy
  rw [Term.holeRead_eq_holeAt] at h3
  exact (Term.holeAt_holeAt_sig _ _ _).trans ((sig_holeAt h3 _).trans (tupCompsImg_padC hy himg))

/-- `tupC`'s object at an η-expanded necessary object `u`: the tuple object of `u`'s items. -/
theorem holeAt_eta_tupC_obj {Γ : Ctx} (A : VarType) {u : VarSymb}
    (hu : Γ.ref u = some (.VTypeBox A)) : ∀ (b : Bool) (hb : ModalSys.T = b),
    (⟨_, Term.holeAt (Term.eta u (.VTypeBox A) hu) (ShapeMap.tupC (σ := σ) A b hb).obj.2⟩ :
      Σ c, Term σ Γ (.VTypeBox (tupOneTy A b)) c) =
      ⟨_, Term.boxtm (Term.pair Term.unit (tupB u (.VTypeBox A) b hb hu))⟩
  | false, hb => by
      have h0 : (Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm (Term.eta u (.VTypeBox A) hu))).at
          (.root (.bnd 0)) = .tm (Term.boxtm (Term.eta u.inner A (Ctx.ref_inner hu))) :=
        Subst.at_single_root _ _
      unfold Term.holeAt
      dsimp only [ShapeMap.obj]
      refine sig_boxtm (sig_pair rfl ((Term.subst_eta_tm _ _ _ _ _ _ _
        (Subst.box_at_inner_boxtm _ h0)).trans ?_))
      exact eta_addr_congr (VarSymb.inner_box ModalSys.NoFour.keepOnly) _ _
  | true, hb => by
      have h0 : (Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm (Term.eta u (.VTypeBox A) hu))).at
          (.root (.bnd 0)) = .tm (Term.eta u (.VTypeBox A) hu) := Subst.at_single_root _ _
      unfold Term.holeAt
      dsimp only [ShapeMap.obj]
      refine sig_boxtm (sig_pair rfl ((Term.subst_bcTree _ _ _ (.VTypeBox A) _).trans ?_))
      refine (congrArg (bcTree (.VTypeBox A)) (funext fun q => funext fun hq => ?_)).trans
        (itemsTree_tupB hb (.VTypeBox A) u hu)
      have hC : (VarType.VTypeBox A).compAt q =
          some (((VarType.VTypeBox A).compAt q).getD .VTypeOne) := by
        obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp (VarType.compAt_hereChains _ q hq)
        rw [hC]
        rfl
      exact Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _
        (Subst.at_ext_eta hb _ q hu hC (Ctx.ref_compAt hb q hu hC) h0))

/-- **P2's entry, for a back-witness child**: the padded tuple map's object, by any substitution
    sending the slot to the child's roots `⟨c, e⟩`, is the child's committed tuple object paired
    with `e`. -/
theorem subst_liftObj_mapD {V Δ : Ctx} (A X : VarType) (hcΔ : (ctxOf (bclD A X)).Le Δ)
    {ι : VarSymb → VarSymb} (θ : Subst σ Δ)
    (hθ : Subst.Ok (V.insert (.bnd 0) (RShape.wit (bornShape A) X).ty) θ)
    (hc : Subst.Coh ι (V.insert (.bnd 0) (RShape.wit (bornShape A) X).ty) θ)
    (h0 : θ.at (.root (.bnd 0)) = .tm (Term.pair
      (Term.eta (.root (.free 0)) (.VTypeBox A) (hcΔ.ref (bclD_c A X)))
      (Term.eta (.root (.free 1)) (.VTypeDia X) (hcΔ.ref (bclD_e A X))))) :
    (⟨_, Term.subst ι θ hθ hc (Term.mono ((Ctx.empty_le V).insert (.bnd 0) _)
        (ShapeMap.liftObj (σ := σ) (.wit (bornShape A) X) (mapD A X)).2)⟩ :
      Σ c, Term σ Δ (RShape.wit (tupShape ModalSys.T rfl (bclD A X)) X).ty c) =
      ⟨_, Term.pair (Term.boxtm (Term.mono hcΔ.boxIn (tupT (σ := σ) (bclD A X)).2))
        (Term.eta (.root (.free 1)) (.VTypeDia X) (hcΔ.ref (bclD_e A X)))⟩ := by
  rw [Term.subst_mono]
  dsimp only [ShapeMap.liftObj]
  refine sig_pair ?_ (Term.subst_eta_tm _ _ _ _ _ _
    (Term.eta (.root (.free 1)) (.VTypeDia X) (hcΔ.ref (bclD_e A X)))
    (by rw [Subst.at_proj _ _ rfl, h0]; rfl))
  refine (Term.subst_holeAt_sig _ _ _ _ _).trans ?_
  refine (sig_holeAt (Term.subst_eta_tm _ _ _ _ _ _
    (Term.eta (.root (.free 0)) (.VTypeBox A) (hcΔ.ref (bclD_c A X)))
    (by rw [Subst.at_proj _ _ rfl, h0]; rfl)) _).trans ?_
  refine (Term.holeAt_holeAt_sig _ _ _).trans ?_
  refine (sig_holeAt (holeAt_eta_tupC_obj A (hcΔ.ref (bclD_c A X)) ModalSys.T rfl) _).trans ?_
  refine (holeAt_boxtm_padC_obj _ ModalSys.T rfl).trans ?_
  refine sig_boxtm (sig_pair (sig_pair rfl (congrArg (Sigma.mk _) ?_)) rfl)
  rw [mono_tupB (ctxOf_le_append [.VTypeDia X] [.VTypeBox A]), mono_tupB hcΔ]
  rfl

/-- ⭐**P2 for a back-witness child**: a body over the child's tuple and `e`, re-read through the
    padded tuple map's object and read at the child, is the body read at the child's tuple. -/
theorem liftBodyDR_mapD (l : List VarType) (A X : VarType)
    (Φ : WFF σ (bodyCtxW (bclD A X) l X) 1) :
    liftBodyDR l A X (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
        (ShapeMap.liftObj (σ := σ) (.wit (bornShape A) X) (mapD A X)).2) Φ) =
      liftBodyW (rclD_suffix l A X) (rclDImg l A X) (bclD_e A X) Φ := by
  unfold liftBodyDR WFF.bodyRepl liftBodyW
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = (RShape.wit (.box (bcT (bclD A X))) X).ty := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp]
    rw [Subst.set_root, Subst.set_root]
    exact SubE.sim_tm_sigma (subst_liftObj_mapD A X (ctxOf_le_of_suffix (rclD_suffix l A X)) _
      _ _ (by rw [Subst.at_nonproj _ rfl, Subst.set_root]; rfl)).symm
  · dsimp only [Subst.comp]
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr, show (Subst.idS σ _ v) = .ren v from rfl,
      SubE.comp_ren, Subst.at_nonproj _ hlp, Subst.set_ne _ _ hvr]
    exact .refl _

/-! ## The back-witness child, born with the invariants -/

section BirthDC

variable (hS : ModalSys.BStrong = true) {tp : NodeSt σ} {A X : VarType} {y z : ℕ}
  (hy : (ctxOf tp.l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
  (hz : (ctxOf tp.l).ref (.root (.free z)) = some X)

/-- ⭐The back-witness child of the obligation `◇^{S_A × ◇X}[⟨u, e⟩ ↦ ⟨W, z⟩] Ξ` of `tp`. -/
noncomputable def retChildDC
    (Ξ : WFF σ ((ctxOf tp.l).boxIn.insert (.bnd 0) (RShape.wit (bornShape A) X).ty) 1) :
    NodeSt σ :=
  ⟨rclD tp.l A X, complete (retSeedDC hS hy hz tp.M Ξ)⟩

variable (hM : Theory.IsMCS tp.M)
  {Ξ : WFF σ ((ctxOf tp.l).boxIn.insert (.bnd 0) (RShape.wit (bornShape A) X).ty) 1}
  (hΞ : WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) hy hz).2 Ξ ∈ tp.M)

include hM hΞ

theorem retChildDC_spec : retSeedDC hS hy hz tp.M Ξ ⊆ (retChildDC hS hy hz Ξ).M ∧
    Theory.IsMCS (retChildDC hS hy hz Ξ).M :=
  complete_spec (retSeedDC_consistent hS hy hz hM hΞ)

theorem retChildDC_body : liftBodyDR tp.l A X Ξ ∈ (retChildDC hS hy hz Ξ).M :=
  (retChildDC_spec hS hy hz hM hΞ).1 (Or.inl rfl)

/-- ⭐**The way home at birth, with companions**, in `e`'s extent: a body over the child's tuple
    and `e` true at the child is a returning possibility at the parent, the tuple coming back
    with its companions — or else, through the padded tuple map (`ret_map`, P2 and P3), the seed
    has its negation. -/
theorem retChildDC_back {o : ℕ} (ho : (ctxOf tp.l).ref (.root (.free o)) = some .VTypeOne) :
    RetInvWB hS ModalSys.T rfl (retChildDC hS hy hz Ξ) tp (bclD A X) (backImgD y o) tp.l (· + 2)
      (.root (.free 1)) X z := by
  obtain ⟨hsub, hmcs⟩ := retChildDC_spec hS hy hz hM hΞ
  refine ⟨rclD_suffix tp.l A X, backImgD_ok tp.l A X hy ho, List.suffix_refl _,
    rclDImg tp.l A X, bclD_e A X, hz, fun Φ hΦ => ?_⟩
  rw [WFF.mono_refl]
  by_contra hn
  have hn' : WFF.neg (WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) hy hz).2
      (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
        (ShapeMap.liftObj (σ := σ) (.wit (bornShape A) X) (mapD A X)).2) Φ)) ∈ tp.M := by
    refine hM.neg_mem_iff.mpr fun hr => hn ?_
    refine hM.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hr, ⟨?_⟩⟩
    exact Proof.conv (WFF.retS_congr hS _
        (holeRead_unarrDT_mapD hy hz (backImgD_ok tp.l A X hy ho)) rfl)
      (Proof.ret_map hS .nec (S := .wit (bornShape A) X) (mapD A X) _ Φ
        (Proof.lookup List.mem_cons_self))
  have h₁ := hsub (Or.inr ⟨_, hn', rfl⟩)
  have e : liftBodyDR tp.l A X (WFF.neg (WFF.bodyRepl
      (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
        (ShapeMap.liftObj (σ := σ) (.wit (bornShape A) X) (mapD A X)).2) Φ)) =
      WFF.neg (liftBodyW (rclD_suffix tp.l A X) (rclDImg tp.l A X) (bclD_e A X) Φ) := by
    rw [← liftBodyDR_mapD]
    rfl
  rw [e] at h₁
  refine hmcs.1 ⟨[_, _], fun x hx => ?_, ⟨Proof.imp_elim
    (φ := liftBodyW (rclD_suffix tp.l A X) (rclDImg tp.l A X) (bclD_e A X) Φ)
    (Proof.lookup List.mem_cons_self)
    (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁
  · rw [List.mem_singleton.mp hx]; exact hΦ

end BirthDC

/-! ## The forward arrow's body along `e`, read through the born root's value -/

omit [ModalSys.NoFour] in
/-- `Term.subst_compsSlot` for an object sent to an η-expanded one: each listed companion's
    contents goes to the image's. -/
theorem Term.subst_compsSlot_tm {ι : VarSymb → VarSymb} {Δ₀ Δ₀' Δ₁ Δ₂ : Ctx} {u₁ u₂ : VarSymb}
    {C : VarType} (hu₁ : Δ₀.ref u₁ = some (.VTypeBox C)) (hle₁ : Δ₀.boxIn.Le Δ₁)
    (hu₂ : Δ₀'.ref u₂ = some (.VTypeBox C)) (hle₂ : Δ₀'.boxIn.Le Δ₂) (θ : Subst σ Δ₂)
    (hθ : Subst.Ok Δ₁ θ) (hc : Subst.Coh ι Δ₁ θ) (cs : List (List Step))
    (hat : ∀ (q : List Step) (C' : VarType), (q = [] ∨ ∃ p ∈ cs, q = .here :: p) →
      ∀ (h₂ : Δ₂.ref (u₂.ext q).inner = some C'),
      θ.at (u₁.ext q).inner = .tm (Term.eta (u₂.ext q).inner C' h₂)) :
    ∀ (cs' : List (List Step)) (h : C.CompOk cs'), (∀ p ∈ cs', p ∈ cs) →
      (⟨_, Term.subst ι θ hθ hc (compsSlot hu₁ hle₁ cs' h).2⟩ :
        Σ a, Term σ Δ₂ (C.compsFlat cs') a) = compsSlot hu₂ hle₂ cs' h
  | [], _, _ => Term.subst_eta_tm _ _ _ C _ _ _ (hat [] C (Or.inl rfl) _)
  | p :: ps, h, hsub =>
      sig_pair (Term.subst_compsSlot_tm hu₁ hle₁ hu₂ hle₂ θ hθ hc cs hat ps h.tail
          (fun p' hp' => hsub p' (List.mem_cons_of_mem _ hp')))
        (Term.subst_eta_tm _ _ _ _ _ _ _
          (hat (.here :: p) _ (Or.inr ⟨p, hsub p List.mem_cons_self, rfl⟩) _))

/-- The back-witness child's tuple, read off the born root's value with companions:
    `⟨items c, ()⟩`. -/
def arrDT (A X : VarType) :
    Σ c, Term σ (Ctx.empty.insert (.bnd 0) (A.compsFlat (bornComps A))) (bcT (bclD A X)) c :=
  ⟨_, Term.pair (arrT A).2 Term.unit⟩

/-- ⭐The forward arrow's body along `e` as the unit's hole formula: the parent's body over `e`'s
    view and its own tuple (`Ψ`), the child's tuple read off the born root's value
    (`arrDT`). -/
noncomputable def thetaD {U : VarType} (A X : VarType)
    (Ψ : WFF σ (((ctxOf (bclD A X)).diaIn (.root (.free 1))).insert (.bnd 0) U) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd (A.compsFlat (bornComps A)) X) U)) 1 :=
  WFF.holeAt (Ctx.slotsFrom_empty.insert _)
    (Term.pair
      (Term.pair
        (Term.holeAt (Term.eta (.step (.step (.root (.bnd 0)) .fst) .fst)
          (A.compsFlat (bornComps A))
          (Ctx.ref_fst_of (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))) (arrDT A X).2)
        (Term.eta (.step (.step (.root (.bnd 0)) .fst) .snd) X
          (Ctx.ref_snd_of (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))))
      (Term.eta (.step (.root (.bnd 0)) .snd) U (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))
    (pack2X U (bclD_e A X) Ψ)

/-- **F1 along `e`**: at home, the hole formula read at the obligation's value is the body read at
    the back images and the content. -/
theorem holeRead_thetaD {l : List VarType} {A X : VarType} {y o z : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (hz : (ctxOf l).ref (.root (.free z)) = some X)
    (himg : ImgOk (bclD A X) (ctxOf l) (backImgD y o)) {U : VarType} {u : Ann U}
    (B : Term σ (ctxOf l) U u)
    (Ψ : WFF σ (((ctxOf (bclD A X)).diaIn (.root (.free 1))).insert (.bnd 0) U) 1) :
    WFF.holeRead (Term.pair (unarrDT hy hz).2 B) (thetaD A X Ψ) =
      WFF.holeRead (Term.pair (Term.pair (tupImgT (bclD A X) (backImgD y o) himg).2
        (Term.eta (.root (.free z)) X hz)) B) (pack2X _ (bclD_e A X) Ψ) := by
  rw [WFF.holeRead_eq_holeAt, WFF.holeRead_eq_holeAt]
  unfold thetaD
  refine (WFF.subst_holeAt _ _ _ _ _ _ _).trans (WFF.holeAt_congr _ (sig_pair (sig_pair ?_
    (Term.holeAt_pair_fst_snd _ _ _)) (Term.holeAt_pair_snd _ _)) _)
  refine (Term.holeAt_holeAt_sig _ _ _).trans
    ((sig_holeAt (Term.holeAt_pair_fst_fst _ _ _) _).trans ?_)
  exact sig_pair (holeAt_unarrT_arrT hy) rfl

/-- **F2 along `e`**: the companion unit's conjunct along the returned possible part, at the
    parent's tuple, read at the back-witness child, is the forward arrow's returning possibility
    along `e`, the tuple coming back with its companions. -/
theorem liftBodyDR_unitBodyDC_thetaD (hS : ModalSys.BStrong = true) (l : List VarType)
    (A X : VarType) (Ψ : WFF σ (((ctxOf (bclD A X)).diaIn (.root (.free 1))).insert (.bnd 0)
      (.VTypeBox (bcT l))) 1) (cs : List (List Step)) (h : (bcT l).CompOk cs) :
    liftBodyDR l A X (WFF.unitBodyDC hS (bornComps A) (bornComps_ok A) (tupT l).2 cs h
        (thetaD A X Ψ)) =
      (OutLeg.pos (.root (.free 1)) ⟨X, rclD_e l A X⟩ : OutLeg (ctxOf (rclD l A X))).retS hS
        (.nec (.boxC (bcT l) cs h)) (tupCompsImg l (· + 2) (rclDImg l A X) cs h).2
        (WFF.mono (((ctxOf_le_of_suffix (rclD_suffix l A X)).diaIn (.root (.free 1))).insert
          (.bnd 0) _) Ψ) := by
  have hle := ctxOf_le_of_suffix (rclD_suffix l A X)
  have hu := Ctx.ref_insert_root (ctxOf l).boxIn (.bnd 0) (RShape.wit (.box A) X).ty
  have hsnd := Ctx.ref_snd_of hu
  have hθ : Subst.Ok ((ctxOf l).boxIn.insert (.bnd 0) (RShape.wit (bornShape A) X).ty)
      ((arrowS σ (ctxOf (rclD l A X)) (· + 2)).set (.bnd 0) (entryD l A X)) :=
    Subst.ok_set (ok_arrowS (rclDImg l A X)) rfl
  have hc : Subst.Coh (Subst.setIdx (arrowIdx (· + 2)) (.bnd 0) (entryD (σ := σ) l A X))
      ((ctxOf l).boxIn.insert (.bnd 0) (RShape.wit (bornShape A) X).ty)
      ((arrowS σ (ctxOf (rclD l A X)) (· + 2)).set (.bnd 0) (entryD l A X)) :=
    Subst.coh_set (ok_arrowS (rclDImg l A X)) (coh_arrowS (rclDImg l A X))
      ((Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).rootFresh (le_refl 0)) rfl
  have h0 : ((arrowS σ (ctxOf (rclD l A X)) (· + 2)).set (.bnd 0) (entryD l A X)).at
      (.root (.bnd 0)) = entryD l A X := by rw [Subst.at_nonproj _ rfl, Subst.set_root]
  have hfst : ((arrowS σ (ctxOf (rclD l A X)) (· + 2)).set (.bnd 0) (entryD l A X)).at
      (.step (.root (.bnd 0)) .fst) =
      .tm (Term.eta (.root (.free 0)) (.VTypeBox A) (rclD_c l A X)) := by
    rw [Subst.at_proj _ _ rfl, h0]
    rfl
  have hw : (((arrowS σ (ctxOf (rclD l A X)) (· + 2)).set (.bnd 0) (entryD l A X)).at
      (.step (.root (.bnd 0)) .snd)).idxAlong [] = .root (.free 1) := rfl
  have hle₂ : (ctxOf (rclD l A X)).boxIn.Le
      (((ctxOf (rclD l A X)).diaIn (.root (.free 1))).insert (.bnd 0) (.VTypeBox (bcT l))) :=
    (Ctx.le_boxIn_diaIn _ _).trans
      (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf (rclD l A X)).diaIn (.root (.free 1)))).root
        _)
  unfold liftBodyDR WFF.unitBodyDC
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ (.root (.free 1)) rfl ⟨X, rclD_e l A X⟩
    ((Ctx.NoSlots.slots (Γ := ctxOf (rclD l A X))).diaIn _) (Subst.ok_dia hθ ⟨X, hsnd⟩ hw)
    (Subst.coh_dia hθ hc ⟨X, hsnd⟩)]
  refine WFF.retxS_congr hS _ _ _ ?_ ?_
  · rw [Term.subst_mono]
    refine (Term.subst_congr _ (arrowS σ (ctxOf (rclD l A X)) (· + 2)) _
      (ok_arrowS (rclDImg l A X)) _ (coh_arrowS (rclDImg l A X)) ?_ _).trans
      (subst_arrow_compsVal l (rclDImg l A X) cs h)
    refine Subst.sim_of fun v T _ hv => ?_
    obtain ⟨u, rfl, _⟩ := boxIn_item hv
    rw [Subst.set_ne _ _ (fun h => by cases h)]
    exact .refl _
  · rw [WFF.subst_holeAt]
    refine (WFF.holeAt_congr _ (sig_pair (sig_pair
      (Term.subst_compsSlot_tm (Ctx.ref_fst_of hu) _ (rclD_c l A X) hle₂ _ _ _
        (bornComps A) ?_ _ _ (fun _ hp => hp))
      ((Term.subst_eta_tm _ _ _ _ _ _
        (Term.mono (Ctx.le_insert
          (Ctx.NoSlots.slots (Γ := (ctxOf (rclD l A X)).diaIn (.root (.free 1)))).root _)
          (Term.eta ((VarSymb.root (.free 1)).step .dia) X
            (Ctx.ref_diaIn_of (rclD_e l A X)))) ?_).trans
        (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _))))
      (Term.subst_eta_renAt _ _ _ _ _ (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)
        (Subst.under_at_slot _ (0 + 1) 0 _ _))) _).trans ?_
    · intro q C' hq h₂
      rw [Subst.at_under_ne _ _ _ (by
        rw [VarSymb.inner_rt, VarSymb.ext_rt]; exact fun h => by cases h)]
      rcases hq with rfl | ⟨p, hp, rfl⟩
      · obtain rfl : C' = A :=
          Option.some.inj (h₂.symm.trans (hle₂.ref (Ctx.ref_inner (rclD_c l A X))))
        dsimp only [VarSymb.ext]
        rw [Subst.dia_eq_box_mono (Δ₁ := (ctxOf l).boxIn.insert (.bnd 0) _) _ _ _ _ _
          (Ctx.ref_inner (Ctx.ref_fst_of hu)), Subst.box_at_inner_boxtm _ hfst]
        exact congrArg SubE.tm ((Term.mono_mono _ _ _).trans (Term.mono_eta _ _ _ _))
      · obtain ⟨hT, hall, -⟩ := (bornComps_ok A).resolve_left (List.ne_nil_of_mem hp)
        have hC : (VarType.VTypeBox A).compAt (.here :: p) =
            some ((A.compAt p).getD .VTypeOne) := by
          obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp (hall p hp)
          change A.compAt p = _
          rw [hC]
          rfl
        obtain rfl : C' = (A.compAt p).getD .VTypeOne :=
          Option.some.inj (h₂.symm.trans (hle₂.ref (Ctx.ref_inner
            (Ctx.ref_compAt hT _ (rclD_c l A X) hC))))
        rw [Subst.dia_eq_box_mono (Δ₁ := (ctxOf l).boxIn.insert (.bnd 0) _) _ _ _ _ _
          (Ctx.ref_inner (Ctx.ref_compAt hT _ (Ctx.ref_fst_of hu) hC)),
          Subst.box_at_inner_boxtm _ (Subst.at_ext_eta hT _ (.here :: p) (rclD_c l A X) hC
            (Ctx.ref_compAt hT _ (rclD_c l A X) hC) hfst)]
        exact congrArg SubE.tm ((Term.mono_mono _ _ _).trans (Term.mono_eta _ _ _ _))
    · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_nonproj _ rfl]
      dsimp only [Subst.dia]
      rw [if_pos rfl, Subst.at_proj _ _ rfl]
      change SubE.mono _ (SubE.diaBody (.root (.free 1))
        ((Subst.set _ _ _ (.root (.bnd 0))).proj .snd)) = _
      rw [Subst.set_root]
      change SubE.mono _ (SubE.diaBody (.root (.free 1)) (SubE.tm (Term.diatm (.root (.free 1)) _
        (Term.eta ((VarSymb.root (.free 1)).step .dia) X _)))) = _
      rw [SubE.diaBody_diatm]
      rfl
    · unfold thetaD
      refine (WFF.subst_holeAt _ _ _ _ _ _ _).trans ?_
      refine (WFF.holeAt_congr _ (sig_pair (sig_pair ?_ (Term.holeAt_pair_fst_snd _ _ _))
        (Term.holeAt_pair_snd _ _)) _).trans
        (holeAt_tupT_pack2X (hle.diaIn (.root (.free 1))) (bclD_e A X) Ψ)
      refine (Term.holeAt_holeAt_sig _ _ _).trans
        ((sig_holeAt (Term.holeAt_pair_fst_fst _ _ _) _).trans ?_)
      refine sig_pair ?_ rfl
      have hB : (ctxOf [VarType.VTypeBox A]).boxIn.Le
          (((ctxOf (rclD l A X)).diaIn (.root (.free 1))).insert (.bnd 0) (.VTypeBox (bcT l))) :=
        (ctxOf_le_append [.VTypeDia X] [.VTypeBox A]).boxIn.trans
          (((Ctx.le_boxIn_diaIn _ _).trans (hle.diaIn (.root (.free 1)))).trans
            (Ctx.le_insert (Ctx.NoSlots.slots
              (Γ := (ctxOf (rclD l A X)).diaIn (.root (.free 1)))).root _))
      rw [compsSlot_home (rclD_c l A X) _ (born_ref A) hB]
      refine (sig_holeAt (mono_compsSlot (born_ref A) (Ctx.Le.refl _) hB (bornComps A)
        (bornComps_ok A)).symm _).trans ?_
      refine (Term.mono_holeAt_sig _ _ _).symm.trans ?_
      refine (sig_mono _ (holeAt_compsSlot_arrT A)).trans ?_
      rw [Term.mono_mono]
      rfl

section BirthDCFwd

variable (hS : ModalSys.BStrong = true) {tp : NodeSt σ} {A X : VarType} {y z : ℕ}
  (hy : (ctxOf tp.l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
  (hz : (ctxOf tp.l).ref (.root (.free z)) = some X) (hM : Theory.IsMCS tp.M)
  {Ξ : WFF σ ((ctxOf tp.l).boxIn.insert (.bnd 0) (RShape.wit (bornShape A) X).ty) 1}
  (hΞ : WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) hy hz).2 Ξ ∈ tp.M)

include hM hΞ

/-- ⭐**The forward arrow at birth, with companions**, along `e`: a body over `e`'s view true at
    the parent is the unit's conjunct along the possible part read at the child (F2); its
    negation at the far end would clash with the unit (`ret_unitDC`, `ret_absurdS`, F1), so the
    parent has `¬◇^{S_A × ◇X}[⟨u, e⟩ ↦ ⟨W, z⟩]¬U` and the seed has `¬¬U`. -/
theorem retChildDC_fwd {o : ℕ} (ho : (ctxOf tp.l).ref (.root (.free o)) = some .VTypeOne) :
    RetInvXB hS ModalSys.T rfl tp (retChildDC hS hy hz Ξ) tp.l (· + 2) (bclD A X) (backImgD y o)
      (.root (.free 1)) X z := by
  obtain ⟨hsub, hmcs⟩ := retChildDC_spec hS hy hz hM hΞ
  have himg := backImgD_ok tp.l A X hy ho
  refine ⟨List.suffix_refl _, rclDImg tp.l A X, rclD_suffix tp.l A X, himg, bclD_e A X, hz,
    fun Ψ hΨ => ?_⟩
  refine (congrArg (· ∈ (retChildDC hS hy hz Ξ).M) (liftBodyDR_unitBodyDC_thetaD hS tp.l A X Ψ
    _ (VarType.compOk_compsAllB _ rfl _))).mp ?_
  have hle := ctxOf_le_of_suffix (List.suffix_refl tp.l)
  have e : WFF.unitBodyDC hS (bornComps A) (bornComps_ok A) (Term.mono hle.boxIn (tupT tp.l).2)
      _ (VarType.compOk_compsAllB _ rfl (bcT tp.l)) (thetaD A X Ψ) =
      WFF.unitBodyDC hS (bornComps A) (bornComps_ok A) (tupT tp.l).2 _
        (VarType.compOk_compsAllB _ rfl (bcT tp.l)) (thetaD A X Ψ) := by
    rw [Term.mono_refl]
  have hU : WFF.neg (WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) hy hz).2
      (WFF.neg (WFF.unitBodyDC hS (bornComps A) (bornComps_ok A) (tupT tp.l).2 _
        (VarType.compOk_compsAllB _ rfl (bcT tp.l)) (thetaD A X Ψ)))) ∈ tp.M := by
    refine hM.neg_mem_iff.mpr fun hr => hM.1 ⟨[WFF.retS hS (.wit (bornShape A) X)
      (unarrDT (σ := σ) hy hz).2 (WFF.neg (WFF.unitBodyDC hS (bornComps A) (bornComps_ok A)
        (tupT tp.l).2 _ (VarType.compOk_compsAllB _ rfl (bcT tp.l)) (thetaD A X Ψ))),
      liftBodyX (List.suffix_refl tp.l) himg (bclD_e A X) hz Ψ], fun x hx => ?_, ⟨?_⟩⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hr
      · rw [List.mem_singleton.mp hx]; exact hΨ
    refine Proof.ret_absurdS hS _ _ _ (ctxOf_fresh (l := tp.l) le_rfl)
      (Proof.conv (by dsimp only [OutLeg.lift, OutLeg.retS, OutLeg.retSH]; rw [e])
      (Proof.ret_unitDC hS .nec (bornComps A) (bornComps_ok A) _ _
        (Term.mono hle.boxIn (tupT tp.l).2) _ (VarType.compOk_compsAllB _ rfl (bcT tp.l)) _
        (Proof.lookup List.mem_cons_self) ?_))
    exact Proof.conv ((holeRead_thetaD hy hz himg
        (Term.boxtm (Term.mono hle.boxIn (tupT tp.l).2)) Ψ).trans
      (holeRead_tupImgT_pack2X himg (bclD_e A X) hz
        (Term.boxtm (Term.mono hle.boxIn (tupT tp.l).2)) Ψ)).symm
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
  have h₁ := hsub (Or.inr ⟨_, hU, rfl⟩)
  exact hmcs.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact h₁,
    ⟨Proof.byContra (Proof.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.lookup List.mem_cons_self))⟩⟩

end BirthDCFwd

end BArrow

end V12M
