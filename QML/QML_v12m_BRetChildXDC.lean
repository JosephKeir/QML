import QML.QML_v12m_BRetChildDC
import QML.QML_v12m_BRetChildXD

/-!
# QML v12m — strong B on the network: the doubly witnessed child, for either T

The flag-generic replacement of `QML_v12m_BRetChildXD` (docs §11.21, stage 3c): the child of an
obligation `◇_x^{S_A × ◇Xe}[⟨u, e⟩ ↦ ⟨W, z⟩] Ξ` along a witness `x`, its way home in the extent of
its own root `e : ◇Xe`.  It mirrors `QML_v12m_BRetChildDC` along `x`'s view: the child's
variables are `X :: rclD` (`x`'s content newest), and the seed's pull-back sends `c` and `e` to
the opened slot's components and the content root to `x.dia`.

* `RetInvWDB`: `RetInvWD` with the tuple's companions (`RetInvWD` at `false`).
* ⭐`retSeedXDC_consistent`: by the doubly witnessed K-law at the born root's shape
  (`Proof.retxD_KC_node`) and the pull-back (`retPullXDC`, ⭐`subst_retPullXDC_liftBodyXDR`).
* ⭐`retChildXDC_back`: born with `RetInvWDB` home, through the padded tuple map `mapD` along `x`
  (`ret_map`, P2 `liftBodyXDR_mapD`, P3 `holeRead_unarrDT_mapD`).
* ⭐`retChildXDC_fwd`: born with `RetInvWDB` out, through the doubly witnessed companion unit
  (`ret_unitWDC`, F1 `holeRead_thetaD`, F2 `liftBodyXDR_unitBodyWDC_thetaD`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## The doubly witnessed invariant with companions -/

/-- `RetInvWD` with the tuple's companions (`tupShape`, `tupCompsImg`); `RetInvWD` at `false`. -/
def RetInvWDB (hS : ModalSys.BStrong = true) (b : Bool) (hb : ModalSys.T = b) (tv tw : NodeSt σ)
    (cls : List VarType) (imgs : ℕ → ℕ) (clt : List VarType) (imgt : ℕ → ℕ) (x : VarSymb)
    (X : VarType) (cxw : ℕ) (e : VarSymb) (E : VarType) (cxv : ℕ) : Prop :=
  ∃ (hs : cls <:+ tv.l) (himgs : ImgOk cls (ctxOf tw.l) imgs) (ht : clt <:+ tw.l)
    (himgt : ImgOk clt (ctxOf tv.l) imgt) (hx : (ctxOf cls).ref x = some (.VTypeDia X))
    (hcxw : (ctxOf tw.l).ref (.root (.free cxw)) = some X)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf tv.l).ref (.root (.free cxv)) = some E),
    ∀ Φ : WFF σ (bodyCtxWD cls clt e X) 1, liftBodyWD hs himgt hx he hcxv Φ ∈ tv.M →
      WFF.retxS hS e ⟨E, (ctxOf_le_of_suffix ht).ref he⟩ (.wit (tupShape b hb cls) X)
        (Term.pair (tupCompsImg cls imgs himgs _ (VarType.compOk_compsAllB b hb _)).2
          (Term.eta (.root (.free cxw)) X hcxw))
        (WFF.mono (((ctxOf_le_of_suffix ht).diaIn e).insert (.bnd 0) _) Φ) ∈ tw.M

theorem retInvWDB_false {hS : ModalSys.BStrong = true} (hT : ModalSys.T = false)
    {tv tw : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x e : VarSymb}
    {X E : VarType} {cxw cxv : ℕ} :
    RetInvWDB hS false hT tv tw cls imgs clt imgt x X cxw e E cxv ↔
      RetInvWD hS tv tw cls imgs clt imgt x X cxw e E cxv :=
  Iff.rfl

/-- The flag can be taken to be T itself. -/
theorem retInvWDB_flag {hS : ModalSys.BStrong = true} {b : Bool} (hb : ModalSys.T = b)
    {tv tw : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x e : VarSymb}
    {X E : VarType} {cxw cxv : ℕ} :
    RetInvWDB hS ModalSys.T rfl tv tw cls imgs clt imgt x X cxw e E cxv ↔
      RetInvWDB hS b hb tv tw cls imgs clt imgt x X cxw e E cxv := by
  cases hb
  exact Iff.rfl

/-! ## The doubly witnessed child's roots -/

section Layout

variable (l : List VarType) (A X Xe : VarType)

omit [ModalSys.NoFour] in
theorem rclXD_c : (ctxOf (X :: rclD l A Xe)).ref (.root (.free 0)) = some (.VTypeBox A) :=
  (ctxOf_le_of_suffix (rclXD_suffix l A X Xe)).ref (bclD_c A Xe)

omit [ModalSys.NoFour] in
theorem rclXD_e : (ctxOf (X :: rclD l A Xe)).ref (.root (.free 1)) = some (.VTypeDia Xe) :=
  (ctxOf_le_of_suffix (rclXD_suffix l A X Xe)).ref (bclD_e A Xe)

/-- The slot's entry at the child: the pair of its roots `c` and `e`. -/
def entryXD : SubE σ (ctxOf (X :: rclD l A Xe)) :=
  .tm (Term.pair (Term.eta (.root (.free 0)) (.VTypeBox A) (rclXD_c l A X Xe))
    (Term.eta (.root (.free 1)) (.VTypeDia Xe) (rclXD_e l A X Xe)))

end Layout

/-! ## Reading a body along `x` over the born root and the possible part at the child -/

/-- ⭐A body along `x` over the born root and the possible part, read at the doubly witnessed
    child: the parent's items and `x`'s content along the arrow, the slot `⟨c, e⟩`. -/
noncomputable def liftBodyXDR (l : List VarType) (A Xe : VarType) {x : VarSymb} {X : VarType}
    (hX : (ctxOf l).ref x = some (.VTypeDia X))
    (Ξ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (RShape.wit (bornShape A) Xe).ty) 1) :
    WFF σ (ctxOf (X :: rclD l A Xe)) 0 :=
  WFF.subst (Subst.setIdx (arrowXIdx (· + 2) x (l.length + 2)) (.bnd 0)
      (entryXD (σ := σ) l A X Xe))
    ((arrowXS σ (ctxOf (X :: rclD l A Xe)) (· + 2) x (l.length + 2)).set (.bnd 0)
      (entryXD l A X Xe))
    (Subst.ok_set (ok_arrowXS (rclXDImg l A X Xe) hX (rclXD_cx l A X Xe)) rfl)
    (Subst.coh_set (ok_arrowXS (rclXDImg l A X Xe) hX (rclXD_cx l A X Xe))
      (coh_arrowXS (rclXDImg l A X Xe) hX (rclXD_cx l A X Xe))
      ((Ctx.NoSlots.slots (Γ := (ctxOf l).diaIn x)).rootFresh (le_refl 0)) rfl)
    ((Ctx.NoSlots.slots (Γ := (ctxOf l).diaIn x)).insert _) Ctx.NoSlots.slots Ξ

/-! ## Pulling the child back into `x`'s view -/

/-- A view `V` of the parent with the slot opened at `u = l.length`, at the obligation's type. -/
abbrev pullCtxXDC (V : Ctx) (l : List VarType) (A Xe : VarType) : Ctx :=
  V.insert (.free l.length) (RShape.wit (bornShape A) Xe).ty

/-- ⭐Pulling the doubly witnessed child back into a view `V` of the parent: `c` to `u.fst`, `e`
    to `u.snd`, root `r + 2` to the tuple of root `r`'s items, and the root after those (`x`'s
    content) to `ex`. -/
def retPullXDC (σ : Signature) (l : List VarType) (A Xe : VarType)
    {V : Ctx} (hV : (ctxOf l).boxIn.Le V) (hu : V.RootFresh (.free l.length))
    (ex : SubE σ (pullCtxXDC V l A Xe)) : Subst σ (pullCtxXDC V l A Xe) := fun v =>
  match v with
  | .root (.free 0) => .ren (.step (.root (.free l.length)) .fst)
  | .root (.free 1) => .ren (.step (.root (.free l.length)) .snd)
  | .root (.free (r + 2)) =>
      if h : r < l.length then .tm (Term.mono (hV.trans (Ctx.le_insert hu.root _))
        (tup (.root (.free r)) (rootTy l r) (by
          rw [Ctx.ref_nonproj _ rfl]; exact ctxOf_root_lt h)))
      else if r = l.length then ex else .hide
  | _ => .hide

/-- Where pulling back sends annotation indices: along the entry at the index's root. -/
def retPullXDCIdx (σ : Signature) (l : List VarType) (A Xe : VarType)
    {V : Ctx} (hV : (ctxOf l).boxIn.Le V) (hu : V.RootFresh (.free l.length))
    (ex : SubE σ (pullCtxXDC V l A Xe)) (a : VarSymb) : VarSymb :=
  match a.rt with
  | .free r => (retPullXDC σ l A Xe hV hu ex (.root (.free r))).idxAlong a.path
  | .bnd _ => a

section PullXDC

variable (l : List VarType) (A Xe : VarType) {V : Ctx}
  (hV : (ctxOf l).boxIn.Le V) (hu : V.RootFresh (.free l.length))
  (ex : SubE σ (pullCtxXDC V l A Xe))

theorem retPullXDC_add {r : ℕ} (h : r < l.length) :
    retPullXDC σ l A Xe hV hu ex (.root (.free (r + 2))) = .tm (Term.mono
      (hV.trans (Ctx.le_insert hu.root _)) (tup (.root (.free r)) (rootTy l r) (by
          rw [Ctx.ref_nonproj _ rfl]; exact ctxOf_root_lt h))) :=
  dif_pos h

theorem retPullXDC_last :
    retPullXDC σ l A Xe hV hu ex (.root (.free (l.length + 2))) = ex := by
  change (if h : l.length < l.length then _ else if l.length = l.length then _ else _) = _
  rw [dif_neg (lt_irrefl _), if_pos rfl]

omit [ModalSys.NoFour] in
theorem pullCtxXDC_ref_fst :
    (pullCtxXDC V l A Xe).ref (.step (.root (.free l.length)) .fst) = some (.VTypeBox A) :=
  Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)

omit [ModalSys.NoFour] in
theorem pullCtxXDC_ref_snd :
    (pullCtxXDC V l A Xe).ref (.step (.root (.free l.length)) .snd) = some (.VTypeDia Xe) :=
  Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)

theorem ok_retPullXDC {X : VarType} (hex : ex.OkRef X) :
    Subst.Ok (ctxOf (X :: rclD l A Xe)) (retPullXDC σ l A Xe hV hu ex) := by
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
        exact pullCtxXDC_ref_fst l A Xe
    | 1, _ =>
        rw [rootTy_rclD_one]
        exact pullCtxXDC_ref_snd l A Xe
    | r + 2, hr =>
        have hr' : r < l.length := by rw [length_rclD] at hr; omega
        rw [rootTy_rclD_add, rootTy_map_bc l r hr', retPullXDC_add l A Xe hV hu ex hr']
        rfl
  · obtain rfl : r = (rclD l A Xe).length := by omega
    rw [rootTy_new, length_rclD, retPullXDC_last]
    exact hex

theorem coh_retPullXDC_of {kl : List VarType}
    (hok : Subst.Ok (ctxOf kl) (retPullXDC σ l A Xe hV hu ex)) :
    Subst.Coh (retPullXDCIdx σ l A Xe hV hu ex) (ctxOf kl) (retPullXDC σ l A Xe hV hu ex) := by
  refine Subst.coh_of hok ?_
  intro v T _ hv p
  obtain ⟨r, rfl⟩ := ctxOf_decl hv
  have hrt : ((VarSymb.root (.free r)).ext p).rt = .free r := VarSymb.ext_rt _ _
  rw [retPullXDCIdx, hrt, VarSymb.ext_path]
  rfl

/-- Pulling back along an encoded projection path from root `r + 2` reaches the tuple of the
    component. -/
theorem at_retPullXDC_tup : ∀ {u : VarSymb} {U : VarType} (hu' : (ctxOf l).ref u = some U)
    (r : ℕ), u.rt = .free r →
      (retPullXDC σ l A Xe hV hu ex).at ((VarSymb.root (.free (r + 2))).ext (encPath u.path)) =
        .tm (Term.mono (hV.trans (Ctx.le_insert hu.root _)) (tup u U hu'))
  | .root (.free r'), U, hu', r, hrt => by
      change Root.free r' = Root.free r at hrt
      cases hrt
      obtain ⟨r₀, e', hr', -⟩ := ref_rt hu'
      cases e'
      have hU := hu'
      rw [Ctx.ref_nonproj _ rfl, ctxOf_root_lt hr'] at hU
      cases hU
      exact retPullXDC_add l A Xe hV hu ex hr'
  | .root (.bnd _), _, _, _, hrt => by cases hrt
  | .step u s, U, hu', r, hrt => by
      have hproj : s.isProj = true := (reach_ppath hu').1 s (by simp [VarSymb.path])
      have hu'' := hu'
      simp only [Ctx.ref, if_pos hproj] at hu''
      cases hU : (ctxOf l).ref u with
      | none => rw [hU] at hu''; cases hu''
      | some U' =>
          rw [hU] at hu''
          have ih := at_retPullXDC_tup hU r hrt
          change (retPullXDC σ l A Xe hV hu ex).at
            ((VarSymb.root (.free (r + 2))).ext (encPath (u.path ++ [s]))) = _
          rw [show encPath (u.path ++ [s]) = encPath u.path ++ [encStep s] from
            List.map_append, VarSymb.ext_step, Subst.at_proj _ _ (encStep_proj hproj), ih]
          exact proj_tupB_mono _ rfl hU hproj hu'' hu'

/-- An item of the parent's `□` view, sent along the child's arrow and pulled back, is itself. -/
theorem at_retPullXDC_item {w : VarSymb} {T : VarType}
    (hw : (ctxOf l).ref w = some (.VTypeBox T)) :
    (retPullXDC σ l A Xe hV hu ex).at (itemAt (imgRoot (· + 2) w.rt) w) =
      .tm (Term.eta (.step w .box) T ((hV.trans (Ctx.le_insert hu.root _)).ref
        (Ctx.ref_boxIn_of ModalSys.NoFour.keepOnly hw))) := by
  obtain ⟨r, hr, _, _⟩ := ref_rt hw
  rw [hr]
  change (retPullXDC σ l A Xe hV hu ex).at (itemAt (.free (r + 2)) w) = _
  rw [at_item_of_tupB_mono _ _ _ hw ModalSys.T rfl (at_retPullXDC_tup l A Xe hV hu ex hw r hr),
    Term.mono_eta]

/-- The slot's entry at the child, pulled back: the opened slot, η-expanded. -/
theorem subst_retPullXDC_entry {X : VarType}
    (hθ : Subst.Ok (ctxOf (X :: rclD l A Xe)) (retPullXDC σ l A Xe hV hu ex))
    (hc : Subst.Coh (retPullXDCIdx σ l A Xe hV hu ex) (ctxOf (X :: rclD l A Xe))
      (retPullXDC σ l A Xe hV hu ex)) :
    (⟨_, Term.subst (retPullXDCIdx σ l A Xe hV hu ex) (retPullXDC σ l A Xe hV hu ex) hθ hc
        (Term.pair (Term.eta (.root (.free 0)) (.VTypeBox A) (rclXD_c l A X Xe))
          (Term.eta (.root (.free 1)) (.VTypeDia Xe) (rclXD_e l A X Xe)))⟩ :
        Σ a, Term σ (pullCtxXDC V l A Xe) (RShape.wit (bornShape A) Xe).ty a) =
      ⟨_, Term.eta (.root (.free l.length)) _ (Ctx.ref_insert_root _ _ _)⟩ :=
  sig_pair (Term.subst_eta_renAt _ _ _ _ _ _ _ (pullCtxXDC_ref_fst l A Xe) rfl)
    (Term.subst_eta_renAt _ _ _ _ _ _ _ (pullCtxXDC_ref_snd l A Xe) rfl)

end PullXDC

section PullXDCX

variable (l : List VarType) (A Xe : VarType) {x : VarSymb} {X : VarType}
  (hX : (ctxOf l).ref x = some (.VTypeDia X))

omit [ModalSys.NoFour] in
include hX in
/-- The content root goes to `x.dia`. -/
theorem okRef_diaXDC :
    (SubE.ren (.step x .dia) : SubE σ (pullCtxXDC ((ctxOf l).diaIn x) l A Xe)).OkRef X :=
  (Ctx.le_insert (pullCtxX_fresh l x).root _).ref (Ctx.ref_diaIn_of hX)

include hX in
theorem ok_retPullXDCX :
    Subst.Ok (ctxOf (X :: rclD l A Xe)) (retPullXDC σ l A Xe (Ctx.le_boxIn_diaIn _ x)
      (pullCtxX_fresh l x) (.ren (.step x .dia))) :=
  ok_retPullXDC l A Xe _ _ _ (okRef_diaXDC l A Xe hX)

/-- ⭐**Pulling back opens the slot, for a doubly witnessed child**: a body along `x` read at the
    child, pulled back into `x`'s view, is the body with its slot opened at `u`; `x`'s content
    root goes back to `x.dia`. -/
theorem subst_retPullXDC_liftBodyXDR
    (Ξ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (RShape.wit (bornShape A) Xe).ty) 1) :
    WFF.subst (retPullXDCIdx σ l A Xe (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x)
          (.ren (.step x .dia)))
        (retPullXDC σ l A Xe (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x)
          (.ren (.step x .dia)))
        (ok_retPullXDCX l A Xe hX) (coh_retPullXDC_of l A Xe _ _ _ (ok_retPullXDCX l A Xe hX))
        Ctx.NoSlots.slots Ctx.NoSlots.slots (liftBodyXDR l A Xe hX Ξ) =
      WFF.openFree l.length (pullCtxX_fresh l x) Ctx.NoSlots.slots Ξ := by
  unfold liftBodyXDR WFF.openFree
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Ξ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = (RShape.wit (bornShape A) Xe).ty := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    rw [Subst.toFree_root]
    dsimp only [Subst.comp]
    rw [Subst.set_root]
    dsimp only [entryXD, SubE.comp]
    rw [subE_tm_sig (subst_retPullXDC_entry l A Xe _ _ _ _ _)]
    exact .ren_eta _ _
  · rw [Subst.toFree_ne _ _ _ _ hvr]
    dsimp only [Subst.comp]
    rw [Subst.set_ne _ _ hvr]
    have hv' : bodyCtxWD (bclD A Xe) l x Xe v = some T := by
      change (if v = VarSymb.root (.bnd 0) then _ else _) = _
      change (if v = VarSymb.root (.bnd 0) then _ else _) = _ at hv
      rw [if_neg hvr] at hv ⊢
      exact hv
    rcases bodyWD_item hv' hvr with ⟨w, rfl, hw⟩ | ⟨rfl, _⟩
    · change SubE.Sim T (((Subst.idRen _) (.step w .box)).mono _)
        ((retPullXDC σ l A Xe (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x)
          (.ren (.step x .dia))).at (itemAt (imgRoot (· + 2) w.rt) w))
      rw [at_retPullXDC_item l A Xe _ _ _ hw]
      exact .ren_eta _ _
    · change SubE.Sim T (((Subst.idRen _) (.step x .dia)).mono _)
        ((if x = x then SubE.ren (.root (.free (l.length + 2))) else .hide).comp _ _ _)
      rw [if_pos rfl]
      change SubE.Sim T _ (retPullXDC σ l A Xe (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x)
        (.ren (.step x .dia)) (.root (.free (l.length + 2))))
      rw [retPullXDC_last]
      exact .refl _

end PullXDCX

/-! ## The seed and its consistency -/

section SeedXDC

variable (hS : ModalSys.BStrong = true) {l : List VarType} {A Xe : VarType} {y z : ℕ}
  (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
  (hz : (ctxOf l).ref (.root (.free z)) = some Xe) {x : VarSymb} {X : VarType}
  (hX : (ctxOf l).ref x = some (.VTypeDia X))

/-- ⭐The seed of the doubly witnessed child of `◇_x^{S_A × ◇Xe}[⟨u, e⟩ ↦ ⟨W, z⟩] Ξ`. -/
def retSeedXDC (M : Set (WFF σ (ctxOf l) 0))
    (Ξ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (RShape.wit (bornShape A) Xe).ty) 1) :
    Set (WFF σ (ctxOf (X :: rclD l A Xe)) 0) :=
  {liftBodyXDR l A Xe hX Ξ} ∪
    {φ | ∃ Θ, WFF.neg (WFF.retxS hS x ⟨X, hX⟩ (.wit (bornShape A) Xe)
        (unarrDT (σ := σ) hy hz).2 Θ) ∈ M ∧ φ = liftBodyXDR l A Xe hX (WFF.neg Θ)}

theorem retSeedXDC_list {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.IsMCS M)
    {Ξ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (RShape.wit (bornShape A) Xe).ty) 1}
    (hΞ : WFF.retxS hS x ⟨X, hX⟩ (.wit (bornShape A) Xe) (unarrDT (σ := σ) hy hz).2 Ξ ∈ M) :
    ∀ L : List (WFF σ (ctxOf (X :: rclD l A Xe)) 0), (∀ δ ∈ L, δ ∈ retSeedXDC hS hy hz hX M Ξ) →
      ∃ Ξ', WFF.retxS hS x ⟨X, hX⟩ (.wit (bornShape A) Xe) (unarrDT (σ := σ) hy hz).2 Ξ' ∈ M ∧
        Theory.Derives {liftBodyXDR l A Xe hX Ξ'} (liftBodyXDR l A Xe hX Ξ) ∧
        ∀ δ ∈ L, Theory.Derives {liftBodyXDR l A Xe hX Ξ'} δ
  | [], _ => ⟨Ξ, hΞ, Theory.Derives.of_mem rfl, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨Ξ₀, hΞ₀, hΦ₀, hL⟩ := retSeedXDC_list hM hΞ L
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      rcases h δ List.mem_cons_self with hδ | ⟨Θ, hΘ, rfl⟩
      · refine ⟨Ξ₀, hΞ₀, hΦ₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · rw [Set.mem_singleton_iff.mp hδ]
          exact hΦ₀
        · exact hL d hd
      · have hand : ∀ φ, Proof σ _ [liftBodyXDR l A Xe hX (Ξ₀.and Θ.neg)] φ →
            Theory.Derives {liftBodyXDR l A Xe hX (Ξ₀.and Θ.neg)} φ :=
          fun φ p => ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; rfl, ⟨p⟩⟩
        have h₀ := hand _ (Proof.and_elim_l (ψ := liftBodyXDR l A Xe hX Θ.neg)
          (Proof.lookup List.mem_cons_self))
        have h₁ := hand _ (Proof.and_elim_r (φ := liftBodyXDR l A Xe hX Ξ₀)
          (Proof.lookup List.mem_cons_self))
        have htr : ∀ d, Theory.Derives {liftBodyXDR l A Xe hX Ξ₀} d →
            Theory.Derives {liftBodyXDR l A Xe hX (Ξ₀.and Θ.neg)} d :=
          fun d hd => Derives.trans (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact h₀) hd
        refine ⟨Ξ₀.and Θ.neg, hM.closed ⟨[_, _], fun x hx => ?_,
          ⟨Proof.retxD_KC_node hS hX (bornComps A) (bornComps_ok A) _ Ξ₀ Θ
            (Proof.lookup List.mem_cons_self)
            (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩,
          htr _ hΦ₀, fun d hd => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hΞ₀
          · rw [List.mem_singleton.mp hx]; exact hΘ
        rcases List.mem_cons.mp hd with rfl | hd
        · exact h₁
        · exact htr d (hL d hd)

/-- ⭐**The doubly witnessed child's seed is consistent**, for either value of T. -/
theorem retSeedXDC_consistent {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.IsMCS M)
    {Ξ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (RShape.wit (bornShape A) Xe).ty) 1}
    (hΞ : WFF.retxS hS x ⟨X, hX⟩ (.wit (bornShape A) Xe) (unarrDT (σ := σ) hy hz).2 Ξ ∈ M) :
    Theory.Consistent (retSeedXDC hS hy hz hX M Ξ) := by
  rintro ⟨L, hL, hp⟩
  obtain ⟨Ξ', hΞ', -, hder⟩ := retSeedXDC_list hS hy hz hX hM hΞ L hL
  obtain ⟨Δ, hΔ, ⟨p⟩⟩ := Derives.trans (fun x hx => hder x hx) ⟨L, fun x hx => hx, hp⟩
  have p' : Proof σ (ctxOf (X :: rclD l A Xe)) [liftBodyXDR l A Xe hX Ξ'] .bot :=
    Proof.ofSubset (fun x hx => by
      rw [Set.mem_singleton_iff.mp (hΔ x hx)]; exact List.mem_cons_self) p
  haveI : (pullCtxXDC ((ctxOf l).diaIn x) l A Xe).Presented :=
    Ctx.Presented.insertFree inferInstance _ (pullCtxX_fresh l x) _
  have q := Proof.subst p' (retPullXDC σ l A Xe (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x)
    (.ren (.step x .dia))) (ok_retPullXDCX l A Xe hX)
    (coh_retPullXDC_of l A Xe _ _ _ (ok_retPullXDCX l A Xe hX)) Ctx.NoSlots.slots
  simp only [List.map_cons, List.map_nil, subst_retPullXDC_liftBodyXDR] at q
  refine hM.1 ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hΞ',
    ⟨Proof.retx_refuteS hS _ _ _ Ξ' ?_ (Proof.lookup List.mem_cons_self)⟩⟩
  refine Proof.ex_elim l.length _ (pullCtxX_fresh l x)
    (φ := WFF.openFree _ (pullCtxX_fresh l x) Ctx.NoSlots.slots Ξ') (ψ := .bot)
    (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
      (Proof.lookup List.mem_cons_self)) ?_
  exact Proof.ofSubset (fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_self) q

end SeedXDC

/-! ## The births' identities along `x` -/

/-- ⭐**P2 for a doubly witnessed child**: a body along `x` over the child's tuple and `e`,
    re-read through the padded tuple map's object and read at the child, is the body read at the
    child's tuple. -/
theorem liftBodyXDR_mapD (l : List VarType) (A Xe : VarType) {x : VarSymb} {X : VarType}
    (hX : (ctxOf l).ref x = some (.VTypeDia X)) (Φ : WFF σ (bodyCtxWD (bclD A Xe) l x Xe) 1) :
    liftBodyXDR l A Xe hX (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
        (ShapeMap.liftObj (σ := σ) (.wit (bornShape A) Xe) (mapD A Xe)).2) Φ) =
      liftBodyWD (rclXD_suffix l A X Xe) (rclXDImg l A X Xe) (bclD_e A Xe) hX
        (rclXD_cx l A X Xe) Φ := by
  unfold liftBodyXDR WFF.bodyRepl liftBodyWD
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = (RShape.wit (.box (bcT (bclD A Xe))) Xe).ty := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp]
    rw [Subst.set_root, Subst.set_root]
    exact SubE.sim_tm_sigma (subst_liftObj_mapD A Xe
      (ctxOf_le_of_suffix (rclXD_suffix l A X Xe)) _ _ _
      (by rw [Subst.at_nonproj _ rfl, Subst.set_root]; rfl)).symm
  · dsimp only [Subst.comp]
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr, show (Subst.idS σ _ v) = .ren v from rfl,
      SubE.comp_ren, Subst.at_nonproj _ hlp, Subst.set_ne _ _ hvr]
    exact .refl _

/-- **F2 for a doubly witnessed child**: the doubly witnessed companion unit's conjunct at the
    parent's tuple and `x`, read at the child, is the forward arrow's returning possibility along
    `e`, the tuple coming back with its companions and `x` with content its newest root. -/
theorem liftBodyXDR_unitBodyWDC_thetaD (hS : ModalSys.BStrong = true) (l : List VarType)
    (A Xe : VarType) {x : VarSymb} {X : VarType} (hX : (ctxOf l).ref x = some (.VTypeDia X))
    (Ψ : WFF σ (bodyCtxWD l (bclD A Xe) (.root (.free 1)) X) 1) (cs : List (List Step))
    (h : (bcT l).CompOk cs) :
    liftBodyXDR l A Xe hX (WFF.unitBodyWDC hS (bornComps A) (bornComps_ok A) (tupT l).2
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) cs h (thetaD A Xe Ψ)) =
      WFF.retxS hS (.root (.free 1)) ⟨Xe, rclXD_e l A X Xe⟩ (.wit (.boxC (bcT l) cs h) X)
        (Term.pair (tupCompsImg l (· + 2) (rclXDImg l A X Xe) cs h).2
          (Term.eta (.root (.free (l.length + 2))) X (rclXD_cx l A X Xe)))
        (WFF.mono (((ctxOf_le_of_suffix (rclXD_suffix l A X Xe)).diaIn (.root (.free 1))).insert
          (.bnd 0) _) Ψ) := by
  have hle := ctxOf_le_of_suffix (rclXD_suffix l A X Xe)
  have hu := Ctx.ref_insert_root ((ctxOf l).diaIn x) (.bnd 0) (RShape.wit (.box A) Xe).ty
  have hsnd := Ctx.ref_snd_of hu
  have hθ : Subst.Ok (((ctxOf l).diaIn x).insert (.bnd 0) (RShape.wit (bornShape A) Xe).ty)
      ((arrowXS σ (ctxOf (X :: rclD l A Xe)) (· + 2) x (l.length + 2)).set (.bnd 0)
        (entryXD l A X Xe)) :=
    Subst.ok_set (ok_arrowXS (rclXDImg l A X Xe) hX (rclXD_cx l A X Xe)) rfl
  have hc : Subst.Coh (Subst.setIdx (arrowXIdx (· + 2) x (l.length + 2)) (.bnd 0)
      (entryXD (σ := σ) l A X Xe))
      (((ctxOf l).diaIn x).insert (.bnd 0) (RShape.wit (bornShape A) Xe).ty)
      ((arrowXS σ (ctxOf (X :: rclD l A Xe)) (· + 2) x (l.length + 2)).set (.bnd 0)
        (entryXD l A X Xe)) :=
    Subst.coh_set (ok_arrowXS (rclXDImg l A X Xe) hX (rclXD_cx l A X Xe))
      (coh_arrowXS (rclXDImg l A X Xe) hX (rclXD_cx l A X Xe))
      ((Ctx.NoSlots.slots (Γ := (ctxOf l).diaIn x)).rootFresh (le_refl 0)) rfl
  have h0 : ((arrowXS σ (ctxOf (X :: rclD l A Xe)) (· + 2) x (l.length + 2)).set (.bnd 0)
      (entryXD l A X Xe)).at (.root (.bnd 0)) = entryXD l A X Xe := by
    rw [Subst.at_nonproj _ rfl, Subst.set_root]
  have hfst : ((arrowXS σ (ctxOf (X :: rclD l A Xe)) (· + 2) x (l.length + 2)).set (.bnd 0)
      (entryXD l A X Xe)).at (.step (.root (.bnd 0)) .fst) =
      .tm (Term.eta (.root (.free 0)) (.VTypeBox A) (rclXD_c l A X Xe)) := by
    rw [Subst.at_proj _ _ rfl, h0]
    rfl
  have hw : (((arrowXS σ (ctxOf (X :: rclD l A Xe)) (· + 2) x (l.length + 2)).set (.bnd 0)
      (entryXD l A X Xe)).at (.step (.root (.bnd 0)) .snd)).idxAlong [] = .root (.free 1) := rfl
  have hle₂ : (ctxOf (X :: rclD l A Xe)).boxIn.Le
      (((ctxOf (X :: rclD l A Xe)).diaIn (.root (.free 1))).insert (.bnd 0)
        (RShape.wit (.box (bcT l)) X).ty) :=
    (Ctx.le_boxIn_diaIn _ _).trans (Ctx.le_insert
      (Ctx.NoSlots.slots (Γ := (ctxOf (X :: rclD l A Xe)).diaIn (.root (.free 1)))).root _)
  unfold liftBodyXDR WFF.unitBodyWDC
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ (.root (.free 1)) rfl ⟨Xe, rclXD_e l A X Xe⟩
    ((Ctx.NoSlots.slots (Γ := ctxOf (X :: rclD l A Xe))).diaIn _) (Subst.ok_dia hθ ⟨Xe, hsnd⟩ hw)
    (Subst.coh_dia hθ hc ⟨Xe, hsnd⟩)]
  refine WFF.retxS_congr hS _ _ _ (sig_pair ?_ ?_) ?_
  · rw [Term.subst_mono]
    refine (Term.subst_congr _ (arrowS σ (ctxOf (X :: rclD l A Xe)) (· + 2)) _
      (ok_arrowS (rclXDImg l A X Xe)) _ (coh_arrowS (rclXDImg l A X Xe)) ?_ _).trans
      (subst_arrow_compsVal l (rclXDImg l A X Xe) cs h)
    refine Subst.sim_of fun v T _ hv => ?_
    obtain ⟨u, rfl, _⟩ := boxIn_item hv
    rw [Subst.set_ne _ _ (fun h => by cases h)]
    exact .refl _
  · rw [Term.subst_mono]
    refine Term.subst_eta_renAt _ _ _ _ _ _ _ _ ?_
    rw [Subst.at_nonproj _ rfl, Subst.set_ne _ _ (fun h => by cases h)]
    exact if_pos rfl
  · rw [WFF.subst_holeAt]
    refine (WFF.holeAt_congr _ (sig_pair (sig_pair
      (Term.subst_compsSlot_tm (Ctx.ref_fst_of hu) _ (rclXD_c l A X Xe) hle₂ _ _ _
        (bornComps A) ?_ _ _ (fun _ hp => hp))
      ((Term.subst_eta_tm _ _ _ _ _ _
        (Term.mono (Ctx.le_insert
          (Ctx.NoSlots.slots (Γ := (ctxOf (X :: rclD l A Xe)).diaIn (.root (.free 1)))).root _)
          (Term.eta ((VarSymb.root (.free 1)).step .dia) Xe
            (Ctx.ref_diaIn_of (rclXD_e l A X Xe)))) ?_).trans
        (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _))))
      (Term.subst_eta_renAt _ _ _ _ _ (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)
        (Subst.under_at_slot _ (0 + 1) 0 _ _))) _).trans ?_
    · intro q C' hq h₂
      rw [Subst.at_under_ne _ _ _ (by
        rw [VarSymb.inner_rt, VarSymb.ext_rt]; exact fun h => by cases h)]
      rcases hq with rfl | ⟨p, hp, rfl⟩
      · obtain rfl : C' = A :=
          Option.some.inj (h₂.symm.trans (hle₂.ref (Ctx.ref_inner (rclXD_c l A X Xe))))
        dsimp only [VarSymb.ext]
        rw [Subst.dia_eq_box_mono (Δ₁ := ((ctxOf l).diaIn x).insert (.bnd 0) _) _ _ _ _ _
          (Ctx.ref_inner (Ctx.ref_fst_of hu)), Subst.box_at_inner_boxtm _ hfst]
        exact congrArg SubE.tm ((Term.mono_mono _ _ _).trans (Term.mono_eta _ _ _ _))
      · obtain ⟨hT, hall⟩ := (bornComps_ok A).resolve_left (List.ne_nil_of_mem hp)
        have hC : (VarType.VTypeBox A).compAt (.here :: p) =
            some ((A.compAt p).getD .VTypeOne) := by
          obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp (hall p hp)
          change A.compAt p = _
          rw [hC]
          rfl
        obtain rfl : C' = (A.compAt p).getD .VTypeOne :=
          Option.some.inj (h₂.symm.trans (hle₂.ref (Ctx.ref_inner
            (Ctx.ref_compAt hT _ (rclXD_c l A X Xe) hC))))
        rw [Subst.dia_eq_box_mono (Δ₁ := ((ctxOf l).diaIn x).insert (.bnd 0) _) _ _ _ _ _
          (Ctx.ref_inner (Ctx.ref_compAt hT _ (Ctx.ref_fst_of hu) hC)),
          Subst.box_at_inner_boxtm _ (Subst.at_ext_eta hT _ (.here :: p) (rclXD_c l A X Xe) hC
            (Ctx.ref_compAt hT _ (rclXD_c l A X Xe) hC) hfst)]
        exact congrArg SubE.tm ((Term.mono_mono _ _ _).trans (Term.mono_eta _ _ _ _))
    · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_nonproj _ rfl]
      dsimp only [Subst.dia]
      rw [if_pos rfl, Subst.at_proj _ _ rfl]
      change SubE.mono _ (SubE.diaBody (.root (.free 1))
        ((Subst.set _ _ _ (.root (.bnd 0))).proj .snd)) = _
      rw [Subst.set_root]
      change SubE.mono _ (SubE.diaBody (.root (.free 1)) (SubE.tm (Term.diatm (.root (.free 1)) _
        (Term.eta ((VarSymb.root (.free 1)).step .dia) Xe _)))) = _
      rw [SubE.diaBody_diatm]
      rfl
    · unfold thetaD
      refine (WFF.subst_holeAt _ _ _ _ _ _ _).trans ?_
      refine (WFF.holeAt_congr _ (sig_pair (sig_pair ?_ (Term.holeAt_pair_fst_snd _ _ _))
        (Term.holeAt_pair_snd _ _)) _).trans
        (holeAt_tupT_pack2X (hle.diaIn (.root (.free 1))) (bclD_e A Xe) Ψ)
      refine (Term.holeAt_holeAt_sig _ _ _).trans
        ((sig_holeAt (Term.holeAt_pair_fst_fst _ _ _) _).trans ?_)
      refine sig_pair ?_ rfl
      have hB : (ctxOf [VarType.VTypeBox A]).boxIn.Le
          (((ctxOf (X :: rclD l A Xe)).diaIn (.root (.free 1))).insert (.bnd 0)
            (RShape.wit (.box (bcT l)) X).ty) :=
        (ctxOf_le_append [.VTypeDia Xe] [.VTypeBox A]).boxIn.trans
          (((Ctx.le_boxIn_diaIn _ _).trans (hle.diaIn (.root (.free 1)))).trans
            (Ctx.le_insert (Ctx.NoSlots.slots
              (Γ := (ctxOf (X :: rclD l A Xe)).diaIn (.root (.free 1)))).root _))
      rw [compsSlot_home (rclXD_c l A X Xe) _ (born_ref A) hB]
      refine (sig_holeAt (mono_compsSlot (born_ref A) (Ctx.Le.refl _) hB (bornComps A)
        (bornComps_ok A)).symm _).trans ?_
      refine (Term.mono_holeAt_sig _ _ _).symm.trans ?_
      refine (sig_mono _ (holeAt_compsSlot_arrT A)).trans ?_
      rw [Term.mono_mono]
      rfl

/-! ## The doubly witnessed child, born with the invariants -/

section BirthXDC

variable (hS : ModalSys.BStrong = true) {tp : NodeSt σ} {A Xe : VarType} {y z : ℕ}
  (hy : (ctxOf tp.l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
  (hz : (ctxOf tp.l).ref (.root (.free z)) = some Xe) {x : VarSymb} {X : VarType}
  (hX : (ctxOf tp.l).ref x = some (.VTypeDia X))

/-- ⭐The doubly witnessed child of the obligation `◇_x^{S_A × ◇Xe}[⟨u, e⟩ ↦ ⟨W, z⟩] Ξ` of
    `tp`. -/
noncomputable def retChildXDC
    (Ξ : WFF σ (((ctxOf tp.l).diaIn x).insert (.bnd 0) (RShape.wit (bornShape A) Xe).ty) 1) :
    NodeSt σ :=
  ⟨X :: rclD tp.l A Xe, complete (retSeedXDC hS hy hz hX tp.M Ξ)⟩

variable (hM : Theory.IsMCS tp.M)
  {Ξ : WFF σ (((ctxOf tp.l).diaIn x).insert (.bnd 0) (RShape.wit (bornShape A) Xe).ty) 1}
  (hΞ : WFF.retxS hS x ⟨X, hX⟩ (.wit (bornShape A) Xe) (unarrDT (σ := σ) hy hz).2 Ξ ∈ tp.M)

include hM hΞ

theorem retChildXDC_spec : retSeedXDC hS hy hz hX tp.M Ξ ⊆ (retChildXDC hS hy hz hX Ξ).M ∧
    Theory.IsMCS (retChildXDC hS hy hz hX Ξ).M :=
  complete_spec (retSeedXDC_consistent hS hy hz hX hM hΞ)

theorem retChildXDC_body : liftBodyXDR tp.l A Xe hX Ξ ∈ (retChildXDC hS hy hz hX Ξ).M :=
  (retChildXDC_spec hS hy hz hX hM hΞ).1 (Or.inl rfl)

/-- ⭐**The way home at birth, with companions**, along `x` and in `e`'s extent: through the
    padded tuple map along `x` (`ret_map`, P2, P3), contraposed. -/
theorem retChildXDC_back {o : ℕ} (ho : (ctxOf tp.l).ref (.root (.free o)) = some .VTypeOne) :
    RetInvWDB hS ModalSys.T rfl (retChildXDC hS hy hz hX Ξ) tp (bclD A Xe) (backImgD y o) tp.l
      (· + 2) (.root (.free 1)) Xe z x X (tp.l.length + 2) := by
  obtain ⟨hsub, hmcs⟩ := retChildXDC_spec hS hy hz hX hM hΞ
  refine ⟨rclXD_suffix tp.l A X Xe, backImgD_ok tp.l A Xe hy ho, List.suffix_refl _,
    rclXDImg tp.l A X Xe, bclD_e A Xe, hz, hX, rclXD_cx tp.l A X Xe, fun Φ hΦ => ?_⟩
  rw [WFF.mono_refl]
  by_contra hn
  have hn' : WFF.neg (WFF.retxS hS x ⟨X, hX⟩ (.wit (bornShape A) Xe) (unarrDT (σ := σ) hy hz).2
      (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
        (ShapeMap.liftObj (σ := σ) (.wit (bornShape A) Xe) (mapD A Xe)).2) Φ)) ∈ tp.M := by
    refine hM.neg_mem_iff.mpr fun hr => hn ?_
    refine hM.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hr, ⟨?_⟩⟩
    exact Proof.conv (WFF.retxS_congr hS x _ _
        (holeRead_unarrDT_mapD hy hz (backImgD_ok tp.l A Xe hy ho)) rfl)
      (Proof.ret_map hS (.pos x ⟨X, hX⟩) (S := .wit (bornShape A) Xe) (mapD A Xe) _ Φ
        (Proof.lookup List.mem_cons_self))
  have h₁ := hsub (Or.inr ⟨_, hn', rfl⟩)
  have e : liftBodyXDR tp.l A Xe hX (WFF.neg (WFF.bodyRepl
      (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
        (ShapeMap.liftObj (σ := σ) (.wit (bornShape A) Xe) (mapD A Xe)).2) Φ)) =
      WFF.neg (liftBodyWD (rclXD_suffix tp.l A X Xe) (rclXDImg tp.l A X Xe) (bclD_e A Xe) hX
        (rclXD_cx tp.l A X Xe) Φ) := by
    rw [← liftBodyXDR_mapD]
    rfl
  rw [e] at h₁
  refine hmcs.1 ⟨[_, _], fun x hx => ?_, ⟨Proof.imp_elim
    (φ := liftBodyWD (rclXD_suffix tp.l A X Xe) (rclXDImg tp.l A X Xe) (bclD_e A Xe) hX
      (rclXD_cx tp.l A X Xe) Φ)
    (Proof.lookup List.mem_cons_self)
    (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁
  · rw [List.mem_singleton.mp hx]; exact hΦ

/-- ⭐**The forward arrow at birth, with companions**: a doubly witnessed body true at the parent
    is the doubly witnessed companion unit's conjunct read at the child (F2); its negation at the
    far end would clash with the unit (`ret_unitWDC` with `u := x.dia`, `retxS_absurd`, F1). -/
theorem retChildXDC_fwd {o : ℕ} (ho : (ctxOf tp.l).ref (.root (.free o)) = some .VTypeOne) :
    RetInvWDB hS ModalSys.T rfl tp (retChildXDC hS hy hz hX Ξ) tp.l (· + 2) (bclD A Xe)
      (backImgD y o) x X (tp.l.length + 2) (.root (.free 1)) Xe z := by
  obtain ⟨hsub, hmcs⟩ := retChildXDC_spec hS hy hz hX hM hΞ
  have himg := backImgD_ok tp.l A Xe hy ho
  refine ⟨List.suffix_refl _, rclXDImg tp.l A X Xe, rclXD_suffix tp.l A X Xe, himg, hX,
    rclXD_cx tp.l A X Xe, bclD_e A Xe, hz, fun Ψ hΨ => ?_⟩
  refine (congrArg (· ∈ (retChildXDC hS hy hz hX Ξ).M) (liftBodyXDR_unitBodyWDC_thetaD hS tp.l A
    Xe hX Ψ _ (VarType.compOk_compsAllB _ rfl _))).mp ?_
  have hle := ctxOf_le_of_suffix (List.suffix_refl tp.l)
  have e : WFF.unitBodyWDC hS (bornComps A) (bornComps_ok A) (Term.mono hle.boxIn (tupT tp.l).2)
      (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) _
      (VarType.compOk_compsAllB _ rfl (bcT tp.l)) (thetaD A Xe Ψ) =
      WFF.unitBodyWDC hS (bornComps A) (bornComps_ok A) (tupT tp.l).2
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) _
        (VarType.compOk_compsAllB _ rfl (bcT tp.l)) (thetaD A Xe Ψ) := by
    rw [Term.mono_refl]
  have hU : WFF.neg (WFF.retxS hS x ⟨X, hX⟩ (.wit (bornShape A) Xe) (unarrDT (σ := σ) hy hz).2
      (WFF.neg (WFF.unitBodyWDC hS (bornComps A) (bornComps_ok A) (tupT tp.l).2
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) _
        (VarType.compOk_compsAllB _ rfl (bcT tp.l)) (thetaD A Xe Ψ)))) ∈ tp.M := by
    refine hM.neg_mem_iff.mpr fun hr => hM.1 ⟨[WFF.retxS hS x ⟨X, hX⟩ (.wit (bornShape A) Xe)
      (unarrDT (σ := σ) hy hz).2 (WFF.neg (WFF.unitBodyWDC hS (bornComps A) (bornComps_ok A)
        (tupT tp.l).2 (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) _
        (VarType.compOk_compsAllB _ rfl (bcT tp.l)) (thetaD A Xe Ψ))),
      liftBodyWD (List.suffix_refl tp.l) himg hX (bclD_e A Xe) hz Ψ], fun x hx => ?_, ⟨?_⟩⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hr
      · rw [List.mem_singleton.mp hx]; exact hΨ
    refine Proof.retxS_absurd hS ⟨X, hX⟩ _ _ _ (ctxOf_fresh (l := tp.l) le_rfl)
      (Proof.conv (by rw [e]) (Proof.ret_unitWDC hS ⟨X, hX⟩ (bornComps A) (bornComps_ok A) _ _
        (Term.mono hle.boxIn (tupT tp.l).2) (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) _
        (VarType.compOk_compsAllB _ rfl (bcT tp.l)) _ (Proof.lookup List.mem_cons_self) ?_))
    exact Proof.conv ((holeRead_thetaD hy hz himg (Term.pair
        (Term.boxtm (Term.mono hle.boxIn (tupT tp.l).2)) (Term.eta x (.VTypeDia X) (hle.ref hX)))
        Ψ).trans (holeRead_tupImgT_pack2WD (List.suffix_refl tp.l) himg hX (bclD_e A Xe) hz
          Ψ)).symm
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
  have h₁ := hsub (Or.inr ⟨_, hU, rfl⟩)
  exact hmcs.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact h₁,
    ⟨Proof.byContra (Proof.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.lookup List.mem_cons_self))⟩⟩

end BirthXDC

end BArrow

end V12M
