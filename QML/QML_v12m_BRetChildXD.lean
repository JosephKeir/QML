import QML.QML_v12m_BRetChildD
import QML.QML_v12m_BRetWD

/-!
# QML v12m — strong B on the network: the doubly witnessed child (T off)

The fourth kind of returning successor (docs §11.20): an atom `◇_x[d ↦ y; e ⇝ z] Φ` of a node, a
returning possibility along `x` at the witnessed shape `□C × ◇Xe`, gets a **doubly witnessed
child**: reached along `x`'s arrow, with its way home in the extent of its own root `e : ◇Xe`
(content `z` at the parent).  Its variables are the back-witness child's (`rclD`: `c : □A` root
0, `e` root 1, the parent's at their `bc` types two up) with `x`'s content `X` newest.  The
parent's roots are committed forward under `+ 2` with `x ⇝ l.length + 2`; `c` back to `y` and `e`
to a unit root `o`.

* `retSeedXD`: the atom's body read at the child (`liftBodyWD`), and `¬Θ` for every
  `¬◇_x[d ↦ y; e ⇝ z] Θ` of the parent.
* ⭐`retSeedXD_consistent`: by the doubly witnessed K-law (`Proof.retxD_K_node`) and the pull-back
  into `x`'s view with the slot opened (`retPullXD`; ⭐`subst_retPullXD_liftBodyWD`).
* ⭐`RetData.retBirthXD`: born with `RetInvWD` both ways — out by `ret_unitWD` (read at the child
  by `liftBodyWD_unitBodyWD`), home by the seed.
* `NetSt.mkRetXD`, ⭐`GoodS.mkRetXD`, `Ext.mkRetXD`: the network operation.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## The doubly witnessed child's variables -/

section Layout

variable (l : List VarType) (A X Xe : VarType)

theorem rclXD_suffix : bclD A Xe <:+ X :: rclD l A Xe :=
  (rclD_suffix l A Xe).trans (List.suffix_cons _ _)

/-- The parent's roots go two up in the doubly witnessed child. -/
theorem rclXDImg : ImgOk l (ctxOf (X :: rclD l A Xe)) (· + 2) := fun r hr =>
  (ctxOf_le_append [X] (rclD l A Xe)).ref (rclDImg l A Xe r hr)

/-- `x`'s content is the child's newest root. -/
theorem rclXD_cx : (ctxOf (X :: rclD l A Xe)).ref (.root (.free (l.length + 2))) = some X := by
  have := ctxOf_ref_new X (rclD l A Xe)
  rwa [length_rclD] at this

end Layout

/-! ## Pulling the doubly witnessed child back into a view, with the slot opened -/

/-- A view `V` of the parent with a body's witnessed slot opened at `u = l.length`. -/
abbrev pullCtxXD (V : Ctx) (l : List VarType) (A Xe : VarType) : Ctx :=
  V.insert (.free l.length) (RShape.wit (.box (bcT (bclD A Xe))) Xe).ty

/-- The object coming back, inside the opened slot. -/
theorem pullCtxXD_ref_c (V : Ctx) (l : List VarType) (A Xe : VarType) :
    (pullCtxXD V l A Xe).boxIn.ref
      (.step (.step (VarSymb.step (.root (.free l.length)) .fst).inner .fst) .snd) =
      some (VarType.VTypeBox A).bc :=
  Ctx.ref_snd_of (Ctx.ref_fst_of (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))

/-- The opened slot's possible part. -/
theorem pullCtxXD_ref_e (V : Ctx) (l : List VarType) (A Xe : VarType) :
    (pullCtxXD V l A Xe).ref (.step (.root (.free l.length)) .snd) = some (.VTypeDia Xe) :=
  Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)

variable [ModalSys.NoFour]

/-- ⭐Pulling the doubly witnessed child back into a view `V` of the parent containing its `□`
    view, with the slot opened at `u`: `c` goes to `□(u.fst.box.fst.snd)`, `e` to `u.snd`, root
    `r + 2` to the tuple of root `r`'s items, and the root after those (`x`'s content) to `ex`. -/
def retPullXD (hT : ModalSys.T = false) (σ : Signature) (l : List VarType) (A Xe : VarType)
    {V : Ctx} (hV : (ctxOf l).boxIn.Le V) (hu : V.RootFresh (.free l.length))
    (ex : SubE σ (pullCtxXD V l A Xe)) : Subst σ (pullCtxXD V l A Xe) := fun v =>
  match v with
  | .root (.free 0) => .tm (Term.boxtm
      (Term.eta (.step (.step (VarSymb.step (.root (.free l.length)) .fst).inner .fst) .snd) A
        ((pullCtxXD_ref_c V l A Xe).trans (congrArg some (bc_box_noT hT A)))))
  | .root (.free 1) => .ren (.step (.root (.free l.length)) .snd)
  | .root (.free (r + 2)) =>
      if h : r < l.length then .tm (Term.mono (hV.trans (Ctx.le_insert hu.root _))
        (tup (.root (.free r)) (rootTy l r) (by
          rw [Ctx.ref_nonproj _ rfl]; exact ctxOf_root_lt h)))
      else if r = l.length then ex else .hide
  | _ => .hide

/-- Where pulling back sends annotation indices: along the entry at the index's root. -/
def retPullXDIdx (hT : ModalSys.T = false) (σ : Signature) (l : List VarType) (A Xe : VarType)
    {V : Ctx} (hV : (ctxOf l).boxIn.Le V) (hu : V.RootFresh (.free l.length))
    (ex : SubE σ (pullCtxXD V l A Xe)) (a : VarSymb) : VarSymb :=
  match a.rt with
  | .free r => (retPullXD hT σ l A Xe hV hu ex (.root (.free r))).idxAlong a.path
  | .bnd _ => a

section PullXD

variable (hT : ModalSys.T = false) (l : List VarType) (A Xe : VarType) {V : Ctx}
  (hV : (ctxOf l).boxIn.Le V) (hu : V.RootFresh (.free l.length))
  (ex : SubE σ (pullCtxXD V l A Xe))

theorem retPullXD_add {r : ℕ} (h : r < l.length) :
    retPullXD hT σ l A Xe hV hu ex (.root (.free (r + 2))) = .tm (Term.mono
      (hV.trans (Ctx.le_insert hu.root _)) (tup (.root (.free r)) (rootTy l r) (by
          rw [Ctx.ref_nonproj _ rfl]; exact ctxOf_root_lt h))) :=
  dif_pos h

theorem retPullXD_last : retPullXD hT σ l A Xe hV hu ex (.root (.free (l.length + 2))) = ex := by
  change (if h : l.length < l.length then _ else if l.length = l.length then _ else _) = _
  rw [dif_neg (lt_irrefl _), if_pos rfl]

theorem ok_retPullXD {X : VarType} (hex : ex.OkRef X) :
    Subst.Ok (ctxOf (X :: rclD l A Xe)) (retPullXD hT σ l A Xe hV hu ex) := by
  intro v T _ hv
  obtain ⟨r, rfl⟩ := ctxOf_decl hv
  have hr : r < (rclD l A Xe).length + 1 := by
    by_contra hge
    rw [(ctxOf_fresh (l := X :: rclD l A Xe) (by simp only [List.length_cons]; omega)) _ rfl]
      at hv
    cases hv
  rw [ctxOf_root_lt (by simp only [List.length_cons]; omega)] at hv
  cases hv
  by_cases hlt : r < (rclD l A Xe).length
  · rw [rootTy_old hlt]
    match r, hlt with
    | 0, _ =>
        rw [rootTy_rclD_zero]
        rfl
    | 1, _ =>
        rw [rootTy_rclD_one]
        exact pullCtxXD_ref_e V l A Xe
    | r + 2, hr =>
        have hr' : r < l.length := by rw [length_rclD] at hr; omega
        rw [rootTy_rclD_add, rootTy_map_bc l r hr', retPullXD_add hT l A Xe hV hu ex hr']
        rfl
  · obtain rfl : r = (rclD l A Xe).length := by omega
    rw [rootTy_new, length_rclD, retPullXD_last]
    exact hex

theorem coh_retPullXD_of {kl : List VarType}
    (hok : Subst.Ok (ctxOf kl) (retPullXD hT σ l A Xe hV hu ex)) :
    Subst.Coh (retPullXDIdx hT σ l A Xe hV hu ex) (ctxOf kl) (retPullXD hT σ l A Xe hV hu ex) := by
  refine Subst.coh_of hok ?_
  intro v T _ hv p
  obtain ⟨r, rfl⟩ := ctxOf_decl hv
  have hrt : ((VarSymb.root (.free r)).ext p).rt = .free r := VarSymb.ext_rt _ _
  rw [retPullXDIdx, hrt, VarSymb.ext_path]
  rfl

/-- Pulling back along an encoded projection path from root `r + 2` reaches the tuple of the
    component. -/
theorem at_retPullXD_tup : ∀ {u : VarSymb} {U : VarType} (hu' : (ctxOf l).ref u = some U)
    (r : ℕ), u.rt = .free r →
      (retPullXD hT σ l A Xe hV hu ex).at ((VarSymb.root (.free (r + 2))).ext (encPath u.path)) =
        .tm (Term.mono (hV.trans (Ctx.le_insert hu.root _)) (tup u U hu'))
  | .root (.free r'), U, hu', r, hrt => by
      change Root.free r' = Root.free r at hrt
      cases hrt
      obtain ⟨r₀, e', hr', -⟩ := ref_rt hu'
      cases e'
      have hU := hu'
      rw [Ctx.ref_nonproj _ rfl, ctxOf_root_lt hr'] at hU
      cases hU
      exact retPullXD_add hT l A Xe hV hu ex hr'
  | .root (.bnd _), _, _, _, hrt => by cases hrt
  | .step u s, U, hu', r, hrt => by
      have hproj : s.isProj = true := (reach_ppath hu').1 s (by simp [VarSymb.path])
      have hu'' := hu'
      simp only [Ctx.ref, if_pos hproj] at hu''
      cases hU : (ctxOf l).ref u with
      | none => rw [hU] at hu''; cases hu''
      | some U' =>
          rw [hU] at hu''
          have ih := at_retPullXD_tup hU r hrt
          change (retPullXD hT σ l A Xe hV hu ex).at
            ((VarSymb.root (.free (r + 2))).ext (encPath (u.path ++ [s]))) = _
          rw [show encPath (u.path ++ [s]) = encPath u.path ++ [encStep s] from
            List.map_append, VarSymb.ext_step, Subst.at_proj _ _ (encStep_proj hproj), ih]
          exact proj_tupB_mono _ rfl hU hproj hu'' hu'

/-- An item of the parent's `□` view, sent along the child's arrow and pulled back, is itself. -/
theorem at_retPullXD_item {w : VarSymb} {T : VarType}
    (hw : (ctxOf l).ref w = some (.VTypeBox T)) :
    (retPullXD hT σ l A Xe hV hu ex).at (itemAt (imgRoot (· + 2) w.rt) w) =
      .tm (Term.eta (.step w .box) T ((hV.trans (Ctx.le_insert hu.root _)).ref
        (Ctx.ref_boxIn_of ModalSys.NoFour.keepOnly hw))) := by
  obtain ⟨r, hr, _, _⟩ := ref_rt hw
  rw [hr]
  change (retPullXD hT σ l A Xe hV hu ex).at (itemAt (.free (r + 2)) w) = _
  rw [at_item_of_tupB_mono _ _ _ hw ModalSys.T rfl (at_retPullXD_tup hT l A Xe hV hu ex hw r hr),
    Term.mono_eta]

/-- The witnessed slot's entry at the child, pulled back: the opened slot. -/
theorem subst_retPullXD_entry {kl : List VarType} (hs : bclD A Xe <:+ kl)
    (hθ : Subst.Ok (ctxOf kl) (retPullXD hT σ l A Xe hV hu ex))
    (hc : Subst.Coh (retPullXDIdx hT σ l A Xe hV hu ex) (ctxOf kl)
      (retPullXD hT σ l A Xe hV hu ex)) :
    (⟨_, Term.subst (retPullXDIdx hT σ l A Xe hV hu ex) (retPullXD hT σ l A Xe hV hu ex) hθ hc
        (Term.pair
          (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT (σ := σ) (bclD A Xe)).2))
          (Term.eta (.root (.free 1)) (.VTypeDia Xe)
            ((ctxOf_le_of_suffix hs).ref (bclD_e A Xe))))⟩ :
        Σ a, Term σ (pullCtxXD V l A Xe) (RShape.wit (.box (bcT (bclD A Xe))) Xe).ty a) =
      ⟨_, Term.eta (.root (.free l.length)) _ (Ctx.ref_insert_root _ _ _)⟩ := by
  have hs' := Subst.box_at_inner_boxtm (retPullXD hT σ l A Xe hV hu ex) (v := .root (.free 0)) rfl
  rw [VarSymb.inner_box ModalSys.NoFour.keepOnly] at hs'
  refine sig_pair ?_ (Term.subst_eta_renAt _ _ _ _ _ _ _ (pullCtxXD_ref_e V l A Xe) rfl)
  refine sig_boxtm ?_
  rw [Term.subst_mono]
  change (⟨_, Term.pair (Term.subst _ _ _ _ (Term.mono _ (tupT (σ := σ) [.VTypeBox A]).2))
      (Term.subst _ _ _ _ (tup (.root (.free 1)) (.VTypeDia Xe) (ctxOf_ref_new _ _)))⟩ :
      Σ a, Term σ (pullCtxXD V l A Xe).boxIn (bcT (bclD A Xe)) a) =
    ⟨_, Term.pair (Term.pair Term.unit
      (Term.eta (.step (.step (VarSymb.step (.root (.free l.length)) .fst).inner .fst) .snd) _
        (pullCtxXD_ref_c V l A Xe))) Term.unit⟩
  refine sig_pair ?_ rfl
  rw [Term.subst_mono]
  exact sig_pair rfl (subst_tupB_box_noT hT _ _ _ (ctxOf_ref_new _ []) ModalSys.T rfl
    (pullCtxXD_ref_c V l A Xe) _ hs')

end PullXD

section PullX

variable (hT : ModalSys.T = false) (l : List VarType) (A Xe : VarType) {x : VarSymb} {X : VarType}
  (hX : (ctxOf l).ref x = some (.VTypeDia X))

omit [ModalSys.NoFour] in
include hX in
/-- The content root goes to `x.dia`. -/
theorem okRef_diaXD :
    (SubE.ren (.step x .dia) : SubE σ (pullCtxXD ((ctxOf l).diaIn x) l A Xe)).OkRef X :=
  (Ctx.le_insert (pullCtxX_fresh l x).root _).ref (Ctx.ref_diaIn_of hX)

include hX in
theorem ok_retPullXDX :
    Subst.Ok (ctxOf (X :: rclD l A Xe)) (retPullXD hT σ l A Xe (Ctx.le_boxIn_diaIn _ x)
      (pullCtxX_fresh l x) (.ren (.step x .dia))) :=
  ok_retPullXD hT l A Xe _ _ _ (okRef_diaXD l A Xe hX)

/-- ⭐**Pulling back opens the slot, for a doubly witnessed child**: a doubly witnessed body read
    at the child, pulled back into `x`'s view, is the body with its slot opened at `u`; `x`'s
    content root goes back to `x.dia`. -/
theorem subst_retPullXD_liftBodyWD (Ξ : WFF σ (bodyCtxWD (bclD A Xe) l x Xe) 1) :
    WFF.subst (retPullXDIdx hT σ l A Xe (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x)
          (.ren (.step x .dia)))
        (retPullXD hT σ l A Xe (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x)
          (.ren (.step x .dia)))
        (ok_retPullXDX hT l A Xe hX) (coh_retPullXD_of hT l A Xe _ _ _ (ok_retPullXDX hT l A Xe hX))
        Ctx.NoSlots.slots Ctx.NoSlots.slots
        (liftBodyWD (rclXD_suffix l A X Xe) (rclXDImg l A X Xe) (bclD_e A Xe) hX
          (rclXD_cx l A X Xe) Ξ) =
      WFF.openFree l.length (pullCtxX_fresh l x) Ctx.NoSlots.slots Ξ := by
  unfold liftBodyWD WFF.openFree
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Ξ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = (RShape.wit (.box (bcT (bclD A Xe))) Xe).ty := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    rw [Subst.toFree_root]
    dsimp only [Subst.comp]
    rw [Subst.set_root]
    dsimp only [SubE.comp]
    rw [subE_tm_sig (subst_retPullXD_entry hT l A Xe _ _ _ (rclXD_suffix l A X Xe) _ _)]
    exact .ren_eta _ _
  · rw [Subst.toFree_ne _ _ _ _ hvr]
    dsimp only [Subst.comp]
    rw [Subst.set_ne _ _ hvr]
    rcases bodyWD_item hv hvr with ⟨w, rfl, hw⟩ | ⟨rfl, _⟩
    · change SubE.Sim T (((Subst.idRen _) (.step w .box)).mono _)
        ((retPullXD hT σ l A Xe (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x)
          (.ren (.step x .dia))).at (itemAt (imgRoot (· + 2) w.rt) w))
      rw [at_retPullXD_item hT l A Xe _ _ _ hw]
      exact .ren_eta _ _
    · change SubE.Sim T (((Subst.idRen _) (.step x .dia)).mono _)
        ((if x = x then SubE.ren (.root (.free (l.length + 2))) else .hide).comp _ _ _)
      rw [if_pos rfl]
      change SubE.Sim T _ (retPullXD hT σ l A Xe (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x)
        (.ren (.step x .dia)) (.root (.free (l.length + 2))))
      rw [retPullXD_last]
      exact .refl _

end PullX

omit [ModalSys.NoFour] in
/-- A returning possibility along `x`, at any shape, whose body `x`'s view refutes is absurd. -/
def Proof.retxS_refute {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)}
    (hS : ModalSys.BStrong = true) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (S : RShape) {a : Ann S.flat} (t : Term σ Γ S.flat a)
    (Ξ : WFF σ ((Γ.diaIn x).insert (.bnd 0) S.ty) 1)
    (q : Proof σ (Γ.diaIn x) [WFF.ex S.ty Ξ] .bot)
    (p : Proof σ Γ Δ (WFF.retxS hS x hx S t Ξ)) : Proof σ Γ Δ .bot :=
  Proof.dia_bot x hx (Proof.imp_elim (Proof.ofSubset (fun _ h => by simp at h)
    (Proof.imp_intro (Proof.K_dia x hx (Δ₁ := []) (Δ₂ := []) q)))
    (Proof.ret_diaS hS (.pos x hx) t _ p))

/-! ## The seed and its consistency -/

section Seed

variable (hS : ModalSys.BStrong = true) {l : List VarType} {A Xe : VarType} {y o z : ℕ}
  (himg : ImgOk (bclD A Xe) (ctxOf l) (backImgD y o))
  (hz : (ctxOf l).ref (.root (.free z)) = some Xe) {x : VarSymb} {X : VarType}
  (hX : (ctxOf l).ref x = some (.VTypeDia X))

/-- ⭐The seed of the doubly witnessed child of `◇_x[d ↦ y; e ⇝ z] Φ`: the atom's body, and `¬Θ`
    for every `¬◇_x[d ↦ y; e ⇝ z] Θ` of the parent, read at the child. -/
def retSeedXD (M : Set (WFF σ (ctxOf l) 0)) (Φ : WFF σ (bodyCtxWD (bclD A Xe) l x Xe) 1) :
    Set (WFF σ (ctxOf (X :: rclD l A Xe)) 0) :=
  {liftBodyWD (rclXD_suffix l A X Xe) (rclXDImg l A X Xe) (bclD_e A Xe) hX (rclXD_cx l A X Xe)
      Φ} ∪
    {φ | ∃ Θ, WFF.neg (WFF.retxS hS x ⟨X, hX⟩ (.wit (.box (bcT (bclD A Xe))) Xe)
        (Term.pair (tupImgT (bclD A Xe) (backImgD y o) himg).2
          (Term.eta (.root (.free z)) Xe hz)) Θ) ∈ M ∧
      φ = liftBodyWD (rclXD_suffix l A X Xe) (rclXDImg l A X Xe) (bclD_e A Xe) hX
        (rclXD_cx l A X Xe) (WFF.neg Θ)}

/-- Finitely many seed formulas reduce to one body with a doubly witnessed returning possibility
    at the parent, by the doubly witnessed K-law. -/
theorem retSeedXD_list {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.IsMCS M)
    {Φ : WFF σ (bodyCtxWD (bclD A Xe) l x Xe) 1}
    (hΦ : WFF.retxS hS x ⟨X, hX⟩ (.wit (.box (bcT (bclD A Xe))) Xe)
      (Term.pair (tupImgT (bclD A Xe) (backImgD y o) himg).2 (Term.eta (.root (.free z)) Xe hz))
      Φ ∈ M) :
    ∀ L : List (WFF σ (ctxOf (X :: rclD l A Xe)) 0),
      (∀ δ ∈ L, δ ∈ retSeedXD hS himg hz hX M Φ) →
      ∃ Ξ, WFF.retxS hS x ⟨X, hX⟩ (.wit (.box (bcT (bclD A Xe))) Xe)
          (Term.pair (tupImgT (bclD A Xe) (backImgD y o) himg).2
            (Term.eta (.root (.free z)) Xe hz)) Ξ ∈ M ∧
        Theory.Derives {liftBodyWD (rclXD_suffix l A X Xe) (rclXDImg l A X Xe) (bclD_e A Xe) hX
            (rclXD_cx l A X Xe) Ξ}
          (liftBodyWD (rclXD_suffix l A X Xe) (rclXDImg l A X Xe) (bclD_e A Xe) hX
            (rclXD_cx l A X Xe) Φ) ∧
        ∀ δ ∈ L, Theory.Derives
          {liftBodyWD (rclXD_suffix l A X Xe) (rclXDImg l A X Xe) (bclD_e A Xe) hX
            (rclXD_cx l A X Xe) Ξ} δ
  | [], _ => ⟨Φ, hΦ, Theory.Derives.of_mem rfl, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨Ξ₀, hΞ₀, hΦ₀, hL⟩ := retSeedXD_list hM hΦ L
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      rcases h δ List.mem_cons_self with hδ | ⟨Θ, hΘ, rfl⟩
      · refine ⟨Ξ₀, hΞ₀, hΦ₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · rw [Set.mem_singleton_iff.mp hδ]
          exact hΦ₀
        · exact hL d hd
      · have hand : ∀ φ, Proof σ _
            [liftBodyWD (rclXD_suffix l A X Xe) (rclXDImg l A X Xe) (bclD_e A Xe) hX
              (rclXD_cx l A X Xe) (Ξ₀.and Θ.neg)] φ →
            Theory.Derives
              {liftBodyWD (rclXD_suffix l A X Xe) (rclXDImg l A X Xe) (bclD_e A Xe) hX
                (rclXD_cx l A X Xe) (Ξ₀.and Θ.neg)} φ :=
          fun φ p => ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; rfl, ⟨p⟩⟩
        have h₀ := hand _ (Proof.and_elim_l
          (ψ := liftBodyWD (rclXD_suffix l A X Xe) (rclXDImg l A X Xe) (bclD_e A Xe) hX
            (rclXD_cx l A X Xe) Θ.neg)
          (Proof.lookup List.mem_cons_self))
        have h₁ := hand _ (Proof.and_elim_r
          (φ := liftBodyWD (rclXD_suffix l A X Xe) (rclXDImg l A X Xe) (bclD_e A Xe) hX
            (rclXD_cx l A X Xe) Ξ₀)
          (Proof.lookup List.mem_cons_self))
        have htr : ∀ d, Theory.Derives
            {liftBodyWD (rclXD_suffix l A X Xe) (rclXDImg l A X Xe) (bclD_e A Xe) hX
              (rclXD_cx l A X Xe) Ξ₀} d →
            Theory.Derives
              {liftBodyWD (rclXD_suffix l A X Xe) (rclXDImg l A X Xe) (bclD_e A Xe) hX
                (rclXD_cx l A X Xe) (Ξ₀.and Θ.neg)} d :=
          fun d hd => Derives.trans (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact h₀) hd
        refine ⟨Ξ₀.and Θ.neg, hM.closed ⟨[_, _], fun x hx => ?_,
          ⟨Proof.retxD_K_node hS hX _ Ξ₀ Θ (Proof.lookup List.mem_cons_self)
            (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩,
          htr _ hΦ₀, fun d hd => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hΞ₀
          · rw [List.mem_singleton.mp hx]; exact hΘ
        rcases List.mem_cons.mp hd with rfl | hd
        · exact h₁
        · exact htr d (hL d hd)

/-- ⭐**The doubly witnessed child's seed is consistent** (T off): finitely many seed formulas
    reduce to one body `Ξ` with `◇_x[d ↦ y; e ⇝ z] Ξ` at the parent (`retSeedXD_list`); a
    refutation of `Ξ` read at the child pulls back to one of `Ξ` with its slot opened in `x`'s
    view (`subst_retPullXD_liftBodyWD`), against `◇_x ∃⟨d, e⟩. Ξ` (`Proof.retxS_refute`). -/
theorem retSeedXD_consistent (hT : ModalSys.T = false) {M : Set (WFF σ (ctxOf l) 0)}
    (hM : Theory.IsMCS M) {Φ : WFF σ (bodyCtxWD (bclD A Xe) l x Xe) 1}
    (hΦ : WFF.retxS hS x ⟨X, hX⟩ (.wit (.box (bcT (bclD A Xe))) Xe)
      (Term.pair (tupImgT (bclD A Xe) (backImgD y o) himg).2 (Term.eta (.root (.free z)) Xe hz))
      Φ ∈ M) :
    Theory.Consistent (retSeedXD hS himg hz hX M Φ) := by
  rintro ⟨L, hL, hp⟩
  obtain ⟨Ξ, hΞ, -, hder⟩ := retSeedXD_list hS himg hz hX hM hΦ L hL
  obtain ⟨Δ, hΔ, ⟨p⟩⟩ := Derives.trans (fun x hx => hder x hx) ⟨L, fun x hx => hx, hp⟩
  have p' : Proof σ (ctxOf (X :: rclD l A Xe))
      [liftBodyWD (rclXD_suffix l A X Xe) (rclXDImg l A X Xe) (bclD_e A Xe) hX
        (rclXD_cx l A X Xe) Ξ] .bot :=
    Proof.ofSubset (fun x hx => by
      rw [Set.mem_singleton_iff.mp (hΔ x hx)]; exact List.mem_cons_self) p
  haveI : (pullCtxXD ((ctxOf l).diaIn x) l A Xe).Presented :=
    Ctx.Presented.insertFree inferInstance _ (pullCtxX_fresh l x) _
  have q := Proof.subst p' (retPullXD hT σ l A Xe (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x)
    (.ren (.step x .dia))) (ok_retPullXDX hT l A Xe hX)
    (coh_retPullXD_of hT l A Xe _ _ _ (ok_retPullXDX hT l A Xe hX)) Ctx.NoSlots.slots
  simp only [List.map_cons, List.map_nil, subst_retPullXD_liftBodyWD] at q
  refine hM.1 ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hΞ,
    ⟨Proof.retxS_refute hS _ _ _ Ξ ?_ (Proof.lookup List.mem_cons_self)⟩⟩
  refine Proof.ex_elim l.length _ (pullCtxX_fresh l x)
    (φ := WFF.openFree _ (pullCtxX_fresh l x) Ctx.NoSlots.slots Ξ) (ψ := .bot)
    (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
      (Proof.lookup List.mem_cons_self)) ?_
  exact Proof.ofSubset (fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_self) q

end Seed

/-! ## The doubly witnessed child, born with the invariants -/

section Birth

variable (hS : ModalSys.BStrong = true) {tp : NodeSt σ} {A Xe : VarType} {y o z : ℕ}
  (himg : ImgOk (bclD A Xe) (ctxOf tp.l) (backImgD y o))
  (hz : (ctxOf tp.l).ref (.root (.free z)) = some Xe) {x : VarSymb} {X : VarType}
  (hX : (ctxOf tp.l).ref x = some (.VTypeDia X))

/-- ⭐The doubly witnessed child of the atom `◇_x[d ↦ y; e ⇝ z] Φ` of `tp`. -/
noncomputable def retChildXD (Φ : WFF σ (bodyCtxWD (bclD A Xe) tp.l x Xe) 1) : NodeSt σ :=
  ⟨X :: rclD tp.l A Xe, complete (retSeedXD hS himg hz hX tp.M Φ)⟩

variable (hT : ModalSys.T = false) (hM : Theory.IsMCS tp.M)
  {Φ : WFF σ (bodyCtxWD (bclD A Xe) tp.l x Xe) 1}
  (hΦ : WFF.retxS hS x ⟨X, hX⟩ (.wit (.box (bcT (bclD A Xe))) Xe)
    (Term.pair (tupImgT (bclD A Xe) (backImgD y o) himg).2 (Term.eta (.root (.free z)) Xe hz))
    Φ ∈ tp.M)

include hT hM hΦ

theorem retChildXD_spec : retSeedXD hS himg hz hX tp.M Φ ⊆ (retChildXD hS himg hz hX Φ).M ∧
    Theory.IsMCS (retChildXD hS himg hz hX Φ).M :=
  complete_spec (retSeedXD_consistent hS himg hz hX hT hM hΦ)

/-- ⭐**The way home at birth**, along `x` and in `e`'s extent: a doubly witnessed body true at the
    child is the fourth returning form at the parent — or else the seed has its negation. -/
theorem retChildXD_back :
    RetInvWD hS (retChildXD hS himg hz hX Φ) tp (bclD A Xe) (backImgD y o) tp.l (· + 2)
      (.root (.free 1)) Xe z x X (tp.l.length + 2) := by
  obtain ⟨hsub, hmcs⟩ := retChildXD_spec hS himg hz hX hT hM hΦ
  refine ⟨rclXD_suffix tp.l A X Xe, himg, List.suffix_refl _, rclXDImg tp.l A X Xe, bclD_e A Xe,
    hz, hX, rclXD_cx tp.l A X Xe, fun Θ hΘ => ?_⟩
  rw [WFF.mono_refl]
  by_contra hn
  have h₁ := hsub (Or.inr ⟨Θ, hM.neg_mem_iff.mpr hn, rfl⟩)
  refine hmcs.1 ⟨[_, _], fun x hx => ?_, ⟨Proof.imp_elim
    (φ := liftBodyWD (rclXD_suffix tp.l A X Xe) (rclXDImg tp.l A X Xe) (bclD_e A Xe) hX
      (rclXD_cx tp.l A X Xe) Θ)
    (Proof.lookup List.mem_cons_self)
    (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁
  · rw [List.mem_singleton.mp hx]; exact hΘ

/-- ⭐**The forward arrow at birth**: a doubly witnessed body true at the parent is the doubly
    witnessed unit's conjunct read at the child (`liftBodyWD_unitBodyWD`); its negation at the far
    end would clash with the unit (`ret_unitWD` with `u := x.dia`, `retxS_absurd`), so the seed
    has `¬¬U`. -/
theorem retChildXD_fwd :
    RetInvWD hS tp (retChildXD hS himg hz hX Φ) tp.l (· + 2) (bclD A Xe) (backImgD y o) x X
      (tp.l.length + 2) (.root (.free 1)) Xe z := by
  obtain ⟨hsub, hmcs⟩ := retChildXD_spec hS himg hz hX hT hM hΦ
  refine ⟨List.suffix_refl _, rclXDImg tp.l A X Xe, rclXD_suffix tp.l A X Xe, himg, hX,
    rclXD_cx tp.l A X Xe, bclD_e A Xe, hz, fun Ψ hΨ => ?_⟩
  refine (congrArg (· ∈ (retChildXD hS himg hz hX Φ).M)
    (liftBodyWD_unitBodyWD (rclXD_suffix tp.l A X Xe) (rclXDImg tp.l A X Xe) (bclD_e A Xe) hX
      (rclXD_cx tp.l A X Xe) hS Ψ)).mp ?_
  have hle := ctxOf_le_of_suffix (List.suffix_refl tp.l)
  have e : WFF.unitBodyWD (Γ := ctxOf tp.l) hS (Term.mono hle.boxIn (tupT tp.l).2)
      (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))
      (pack2X (RShape.wit (.box (bcT tp.l)) X).ty (bclD_e A Xe) Ψ) =
      WFF.unitBodyWD (Γ := ctxOf tp.l) hS (tupT tp.l).2
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))
        (pack2X (RShape.wit (.box (bcT tp.l)) X).ty (bclD_e A Xe) Ψ) := by
    rw [Term.mono_refl]
  have hU : WFF.neg (WFF.retxS hS x ⟨X, hX⟩ (.wit (.box (bcT (bclD A Xe))) Xe)
      (Term.pair (tupImgT (bclD A Xe) (backImgD y o) himg).2 (Term.eta (.root (.free z)) Xe hz))
      (WFF.neg (WFF.unitBodyWD (Γ := ctxOf tp.l) hS (tupT tp.l).2
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))
        (pack2X (RShape.wit (.box (bcT tp.l)) X).ty (bclD_e A Xe) Ψ)))) ∈ tp.M := by
    refine hM.neg_mem_iff.mpr fun hr => hM.1 ⟨[WFF.retxS hS x ⟨X, hX⟩
      (.wit (.box (bcT (bclD A Xe))) Xe)
      (Term.pair (tupImgT (bclD A Xe) (backImgD y o) himg).2 (Term.eta (.root (.free z)) Xe hz))
      (WFF.neg (WFF.unitBodyWD (Γ := ctxOf tp.l) hS (tupT tp.l).2
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))
        (pack2X (RShape.wit (.box (bcT tp.l)) X).ty (bclD_e A Xe) Ψ))),
      liftBodyWD (List.suffix_refl tp.l) himg hX (bclD_e A Xe) hz Ψ], fun x hx => ?_, ⟨?_⟩⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hr
      · rw [List.mem_singleton.mp hx]; exact hΨ
    refine Proof.retxS_absurd hS ⟨X, hX⟩ _ _ _ (ctxOf_fresh (l := tp.l) le_rfl)
      (Proof.conv (by rw [e]) (Proof.ret_unitWD hS ⟨X, hX⟩ _ _
        (Term.mono hle.boxIn (tupT tp.l).2) (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) _
        (Proof.lookup List.mem_cons_self) ?_))
    exact Proof.conv (holeRead_tupImgT_pack2WD (List.suffix_refl tp.l) himg hX (bclD_e A Xe) hz
      Ψ).symm (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
  have h₁ := hsub (Or.inr ⟨_, hU, rfl⟩)
  exact hmcs.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact h₁,
    ⟨Proof.byContra (Proof.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.lookup List.mem_cons_self))⟩⟩

/-- ⭐**The doubly witnessed child is born with the invariants**: `RetInvWD` both ways. -/
theorem RetData.retBirthXD : RetData hS tp (retChildXD hS himg hz hX Φ) (some (x, X))
    (some (.root (.free 1), Xe)) (tp.l.length + 2) z tp.l (· + 2) (bclD A Xe) (backImgD y o) :=
  ⟨retChildXD_fwd hS himg hz hX hT hM hΦ, retChildXD_back hS himg hz hX hT hM hΦ⟩

end Birth

/-! ## The operation -/

namespace NetSt

/-- A doubly witnessed returning-possibility obligation: over a list of a node's variables, the
    types `A` and `Xe`, the witness `x`, the alias `y`, a unit root `o`, the content `z`, and the
    atom's body. -/
abbrev RetOblXD (σ : Signature) :=
  Σ l : List VarType, Σ A : VarType, Σ Xe : VarType, Σ x : VarSymb,
    (ℕ × ℕ × ℕ) × WFF σ (bodyCtxWD (bclD A Xe) l x Xe) 1

open Classical in
/-- ⭐Give the node `s` the doubly witnessed child of its atom `◇_x[d ↦ y; e ⇝ z] Φ`, if it has
    it; the two born roots go back to distinct roots (`y ≠ o`). -/
noncomputable def mkRetXD (hS : ModalSys.BStrong = true) (N : NetSt σ) (s : Node) :
    RetOblXD σ → NetSt σ
  | ⟨l, A, Xe, x, (y, o, z), Φ⟩ =>
      if h : l <:+ (N.st s).l then
        if himg : ImgOk (bclD A Xe) (ctxOf (N.st s).l) (backImgD y o) then
          if hz : (ctxOf (N.st s).l).ref (.root (.free z)) = some Xe then
            if y ≠ o then
              match hX : (ctxOf (N.st s).l).ref x with
              | some (.VTypeDia X) =>
                  if WFF.retxS hS x ⟨X, hX⟩ (.wit (.box (bcT (bclD A Xe))) Xe)
                      (Term.pair (tupImgT (bclD A Xe) (backImgD y o) himg).2
                        (Term.eta (.root (.free z)) Xe hz))
                      (WFF.mono (((ctxOf_le_of_suffix h).diaIn x).insert (.bnd 0) _) Φ) ∈
                      (N.st s).M then
                    N.newChild s (some (x, X)) ((N.st s).l.length + 2)
                      (retChildXD hS himg hz hX
                        (WFF.mono (((ctxOf_le_of_suffix h).diaIn x).insert (.bnd 0) _) Φ))
                      (· + 2) (bclD A Xe) (backImgD y o) (some (.root (.free 1), Xe)) z
                  else N
              | _ => N
            else N
          else N
        else N
      else N

theorem Ext.mkRetXD {hS : ModalSys.BStrong = true} {N : NetSt σ} {s : Node} (hs : N.Live s)
    (o : RetOblXD σ) : Ext N (N.mkRetXD hS s o) := by
  obtain ⟨l, A, Xe, x, ⟨y, o, z⟩, Φ⟩ := o
  simp only [NetSt.mkRetXD]
  split_ifs
  · split
    · split_ifs
      · exact Ext.newChild hs _ _ _ _ _ _ _ _
      · exact Ext.refl N
    · exact Ext.refl N
  all_goals exact Ext.refl N

end NetSt

end BArrow

end V12M
