import QML.QML_v12m_GLocal

/-!
# QML v12m — the growing tree: the lift

The operation behind strong 4 (`docs/v12-modal-extensions.md` §3 4, "The growing tree: the three
paper checks", 1).  For an edge `w → v` of kind `k` whose source `w` is fully committed (item map
`f`), and an address `n : T` of the target with `T` liftable, the source gets a fresh root
`m : T` and the edge sends `m.keep ↦ n`.

* `m`'s **seed** is what `Proof.keep_lift` hands its subproof: `◇_k χ(m.keep)` for every
  `χ(e)` whose reading at `n` holds in the target (`liftSeed`).  It is consistent with the source
  by the rule (`glift_consistent`).
* `m`'s other items, its **residual** (`VarType.lr`: `m.box : A` for `m : □A`, under T + 4 the
  items of `m.here`, nothing for `m : ◇A`), get a fresh variable of the target, as a realisation
  does (`gliftRealise_consistent`).  The edge's item map for `m` is `gliftG f T c n (.free z)`.

The arguments are those of paper check 1, read through the rule: a formula `χ(e)` about the kept
object is a slot formula at `e`, so the seed needs no abstraction of its own.
-/

namespace V12M

variable [ModalSys]

/-- The residual type of a lifted root, for a value `b` of `ModalSys.keepOnly`: what its items
    other than the kept one fill — `A` for `□A` (`m.box`), under T + 4 `gc A` (the items of
    `m.here`), and `𝟙` otherwise. -/
def VarType.lrB (b : Bool) : VarType → VarType
  | .VTypeBox A => cond b (A.gcB b) A
  | .VTypeDia _ => .VTypeOne
  | .VTypeProd _ _ => .VTypeOne
  | .Var => .VTypeOne
  | .VTypeOne => .VTypeOne

/-- ⭐The residual type of a lifted root (`VarType.lrB` at `ModalSys.keepOnly`). -/
abbrev VarType.lr (T : VarType) : VarType := VarType.lrB ModalSys.keepOnly T

namespace GArrow

open BArrow

variable {σ : Signature}

/-! ## Where a lifted root's residual items land -/

/-- Where the residual item `u.s` (path `q` from a lifted root of type `T`) lands in a variable of
    `T.lr`: `m.box` at the variable itself, under T + 4 `m.here.q.s` where `gPath` sends it. -/
def lPath : VarType → List Step → Step → List Step
  | .VTypeBox A, .here :: q, s => gPath A q s
  | _, _, _ => []

theorem ppath_lPath (T : VarType) (q : List Step) (s : Step) : PPath (lPath T q s) := by
  unfold lPath
  split
  · exact ppath_gPath _ _ _
  · exact fun _ h => by cases h

/-- ⭐A residual item of a liftable root lands at its type. -/
theorem ref_lItem (hF : ModalSys.Four = true) {L : List VarType} {Δ : Ctx} {ρ : Root} {r : ℕ}
    {u : VarSymb} {s : Step} {T : VarType} (hT : (rootTy L r).keepable = true)
    (h : (ctxOf L).boxIn (.step u s) = some T) (hr : u.rt = .free r)
    (hnk : ¬ (u = .root (.free r) ∧ s = .keep)) (hz : Δ.ref (.root ρ) = some (rootTy L r).lr) :
    Δ.ref ((VarSymb.root ρ).ext (lPath (rootTy L r) u.path s)) = some T := by
  obtain ⟨U, hU, hs⟩ : ∃ U, (ctxOf L).ref u = some U ∧
      ((s = .box ∧ ModalSys.keepOnly = false ∧ U = .VTypeBox T) ∨
        (s = .keep ∧ U = T ∧ T.keepable = true)) := by
    cases s with
    | box =>
        obtain ⟨hk, hu⟩ := Ctx.boxIn_box h
        exact ⟨_, hu, Or.inl ⟨rfl, hk, rfl⟩⟩
    | keep =>
        obtain ⟨-, hu, hT⟩ := Ctx.boxIn_keep h
        exact ⟨_, hu, Or.inr ⟨rfl, rfl, hT⟩⟩
    | _ => cases h
  have hp := (reach_ppath hU).1
  obtain ⟨r', hr', -, hR⟩ := ref_rt hU
  rw [hr] at hr'
  cases hr'
  have hwalk : (rootTy L r).walk u.path = some U := by
    have e := Ctx.ref_ext_ppath (ctxOf L) u.path (.root u.rt) hp
    rw [← VarSymb.eq_root_ext u, hU, hR] at e
    exact e.symm
  generalize rootTy L r = R at hT hwalk hz ⊢
  match hq : u.path, hp, hwalk with
  | [], _, hwalk =>
      cases hwalk
      have hu : u = .root (.free r) := by rw [VarSymb.eq_root_ext u, hq, hr]; rfl
      rcases hs with ⟨rfl, hk, rfl⟩ | ⟨rfl, -, -⟩
      · change Δ.ref (.root ρ) = _
        rw [hz]
        simp [VarType.lr, VarType.lrB, hk]
      · exact absurd ⟨hu, rfl⟩ hnk
  | t :: q, hp, hwalk =>
      have hq' : PPath q := fun s' hs' => hp s' (by simp [hs'])
      cases t with
      | here =>
          cases R with
          | VTypeBox X =>
              have hT' : ModalSys.T = true := by
                cases hT' : ModalSys.T
                · simp [VarType.walk, VarType.step, hT'] at hwalk
                · rfl
              have hk : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT', hF]
              have hwalk' : X.walk q = some U := by
                simpa [VarType.walk, VarType.step, hT'] using hwalk
              have hz' : Δ.ref (.root ρ) = some X.gc := by
                rw [hz]
                simp [VarType.lr, VarType.lrB, VarType.gc, hk]
              exact ref_gPath hF X q (.root ρ) hq' hwalk' hz' fun w' hw' => ref_gPath_nil hw' hs
          | _ => simp [VarType.walk, VarType.step] at hwalk
      | fst => cases R <;> first | (simp [VarType.walk, VarType.step] at hwalk; done) | cases hT
      | snd => cases R <;> first | (simp [VarType.walk, VarType.step] at hwalk; done) | cases hT
      | box => exact absurd (hp .box (by simp)) (by decide)
      | dia => exact absurd (hp .dia (by simp)) (by decide)
      | keep => exact absurd (hp .keep (by simp)) (by decide)

/-! ## The item map of a lift -/

/-- ⭐The item map of an edge whose source's root `c : T` is lifted: `c.keep ↦ κ`, `c`'s residual
    items into the variable `ρ` (`lPath`), every other item by `f`.  The edge's own map takes
    `κ = n` and `ρ` the fresh variable; abstractions take slots. -/
def gliftG (f : VarSymb → VarSymb) (T : VarType) (c : ℕ) (κ : VarSymb) (ρ : Root)
    (v : VarSymb) : VarSymb :=
  match v with
  | .step u s =>
      if u.rt = .free c then
        (if u = .root (.free c) ∧ s = .keep then κ else (VarSymb.root ρ).ext (lPath T u.path s))
      else f v
  | .root _ => f v

theorem gliftG_keep (f : VarSymb → VarSymb) (T : VarType) (c : ℕ) (κ : VarSymb) (ρ : Root) :
    gliftG f T c κ ρ (.step (.root (.free c)) .keep) = κ := by
  dsimp only [gliftG]
  exact (if_pos rfl).trans (if_pos ⟨rfl, rfl⟩)

theorem gliftG_res {f : VarSymb → VarSymb} {T : VarType} {c : ℕ} {κ : VarSymb} {ρ : Root}
    {u : VarSymb} {s : Step} (hrt : u.rt = .free c) (hnk : ¬ (u = .root (.free c) ∧ s = .keep)) :
    gliftG f T c κ ρ (.step u s) = (VarSymb.root ρ).ext (lPath T u.path s) := by
  dsimp only [gliftG]
  rw [if_pos hrt, if_neg hnk]

theorem gliftG_old {f : VarSymb → VarSymb} {T : VarType} {c : ℕ} {κ : VarSymb} {ρ : Root}
    {u : VarSymb} {s : Step} (hrt : ¬ u.rt = .free c) :
    gliftG f T c κ ρ (.step u s) = f (.step u s) := by
  dsimp only [gliftG]
  rw [if_neg hrt]

/-- ⭐The item map of a lift types the new view. -/
theorem itemOk_gliftG (hF : ModalSys.Four = true) {k : Option VarSymb} {T : VarType}
    {ls : List VarType} {Δ : Ctx} (hT : T.keepable = true) (hk : KOld k ls.length)
    {f : VarSymb → VarSymb} (hf : ItemOk ((ctxOf ls).kView k) Δ f) {κ : VarSymb}
    (hκ : Δ.ref κ = some T) {ρ : Root} (hρ : Δ.ref (.root ρ) = some T.lr) :
    ItemOk ((ctxOf (T :: ls)).kView k) Δ (gliftG f T ls.length κ ρ) := by
  intro v T' hl hv
  obtain ⟨u, s, rfl, -, U, hU⟩ := kView_item hv
  by_cases hrt : u.rt = .free ls.length
  · have hb := kView_boxIn hk hrt hv
    by_cases hnk : u = .root (.free ls.length) ∧ s = .keep
    · obtain ⟨rfl, rfl⟩ := hnk
      rw [gliftG_keep]
      obtain ⟨-, hu', -⟩ := Ctx.boxIn_keep hb
      rw [ctxOf_ref_new] at hu'
      cases hu'
      exact hκ
    · rw [gliftG_res hrt hnk]
      have h := ref_lItem hF (by rw [rootTy_new]; exact hT) hb hrt hnk
        (Δ := Δ) (ρ := ρ) (by rw [rootTy_new]; exact hρ)
      rwa [rootTy_new] at h
  · rw [gliftG_old hrt]
    rw [kView_old hrt] at hv
    exact hf _ _ hl hv

/-! ## The residual tuple -/

/-- The annotation of `rtupB`. -/
def rtupAnnB : VarSymb → (T : VarType) → (b : Bool) → Ann (T.lrB b)
  | u, .VTypeBox A, true => gtupAnnB (.step u .here) A true
  | u, .VTypeBox A, false => Ann.eta (.step u .box) A
  | _, .VTypeDia _, _ => .one
  | _, .VTypeProd _ _, _ => .one
  | _, .Var, _ => .one
  | _, .VTypeOne, _ => .one

/-- The residual items of `u : T` as one term of the `□` view, for a value `b` of
    `ModalSys.keepOnly`: `u.box`, or under T + 4 the tuple of `u.here`'s items. -/
def rtupB (hF : ModalSys.Four = true) {Γ : Ctx} : (u : VarSymb) → (T : VarType) → (b : Bool) →
    ModalSys.keepOnly = b → Γ.ref u = some T → Term σ Γ.boxIn (T.lrB b) (rtupAnnB u T b)
  | u, .VTypeBox A, true, hb, h =>
      gtupB hF (.step u .here) A true hb (Ctx.ref_here_of (ModalSys.keepOnly_flags hb).1 h)
  | u, .VTypeBox A, false, hb, h => Term.eta (.step u .box) A (Ctx.ref_boxIn_of hb h)
  | _, .VTypeDia _, _, _, _ => .unit
  | _, .VTypeProd _ _, _, _, _ => .unit
  | _, .Var, _, _, _ => .unit
  | _, .VTypeOne, _, _, _ => .unit

/-- ⭐The residual items of `u : T`, as one term of the `□` view of type `T.lr`. -/
abbrev rtup (hF : ModalSys.Four = true) {Γ : Ctx} (u : VarSymb) (T : VarType)
    (h : Γ.ref u = some T) : Term σ Γ.boxIn T.lr (rtupAnnB u T ModalSys.keepOnly) :=
  rtupB hF u T ModalSys.keepOnly rfl h

/-- ⭐An entry holding the residual tuple of a liftable `u : T` (weakened), read where `lPath`
    sends a residual item `v.s` of `v = u.q`, is the item itself. -/
theorem at_lPath_rtupB (hF : ModalSys.Four = true) {Γ Δ : Ctx} (hle : Γ.boxIn.Le Δ)
    (θ : Subst σ Δ) (b : Bool) (hb : ModalSys.keepOnly = b) {s : Step} (hs : s.isProj = false)
    {T' : VarType} (T : VarType) (hT : T.keepable = true) (q : List Step) {U' : VarType}
    (u w : VarSymb) (hu : Γ.ref u = some T) (hq : PPath q) (hwk : T.walk q = some U')
    (hθ : θ.at w = .tm (Term.mono hle (rtupB hF u T b hb hu))) (hnk : ¬ (q = [] ∧ s = .keep))
    (v : VarSymb) (hv : v = u.ext q) (hit : Γ.boxIn.ref (.step v s) = some T') :
    θ.at (w.ext (lPath T q s)) = .tm (Term.mono hle (Term.eta (.step v s) T' hit)) := by
  match q, hq, hwk, hnk with
  | [], _, hwk, hnk =>
      subst v
      change Γ.boxIn.ref (.step u s) = some T' at hit
      have hit' := hit
      rw [Ctx.ref_nonproj _ (show (VarSymb.step u s).lastProj = false from hs)] at hit'
      cases s with
      | box =>
          obtain ⟨hk, hu'⟩ := Ctx.boxIn_box hit'
          rw [hu] at hu'
          cases hu'
          obtain rfl : b = false := hb.symm.trans hk
          exact hθ
      | keep => exact absurd ⟨rfl, rfl⟩ hnk
      | dia => cases hit'
      | _ => cases hs
  | t :: q, hq, hwk, _ =>
      have hq' : PPath q := fun s' hs' => hq s' (by simp [hs'])
      cases t with
      | here =>
          cases T with
          | VTypeBox X =>
              have hT' : ModalSys.T = true := by
                cases hT' : ModalSys.T
                · simp [VarType.walk, VarType.step, hT'] at hwk
                · rfl
              have hk : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT', hF]
              obtain rfl : b = true := hb.symm.trans hk
              have hwk' : X.walk q = some U' := by
                simpa [VarType.walk, VarType.step, hT'] using hwk
              exact at_gPath_gtupB hF hle θ true hb hs X q (.step u .here) w
                (Ctx.ref_here_of hT' hu) hq' hwk' hθ v hv hit
          | _ => simp [VarType.walk, VarType.step] at hwk
      | fst => cases T <;> first | (simp [VarType.walk, VarType.step] at hwk; done) | cases hT
      | snd => cases T <;> first | (simp [VarType.walk, VarType.step] at hwk; done) | cases hT
      | box => exact absurd (hq .box (by simp)) (by decide)
      | dia => exact absurd (hq .dia (by simp)) (by decide)
      | keep => exact absurd (hq .keep (by simp)) (by decide)

/-! ## Reading substitutions along paths -/

/-- Along a projection path, a renaming entry renames. -/
theorem at_ext_ren {Δ : Ctx} (θ : Subst σ Δ) :
    ∀ (p : List Step) {w w' : VarSymb}, PPath p → θ.at w = .ren w' →
      θ.at (w.ext p) = .ren (w'.ext p)
  | [], _, _, _, h => h
  | s :: p, w, w', hp, h => by
      have hs : s.isProj = true := hp s (by simp)
      refine at_ext_ren θ p (w := .step w s) (w' := .step w' s)
        (fun s' hs' => hp s' (by simp [hs'])) ?_
      rw [Subst.at_proj _ _ hs, h]
      rfl

/-- A substitution renaming every address with a given root renames along it. -/
theorem at_ren_of {Δ : Ctx} (θ : Subst σ Δ) :
    ∀ w : VarSymb, (∀ v : VarSymb, v.rt = w.rt → θ v = .ren v) → θ.at w = .ren w
  | .root r, h => h (.root r) rfl
  | .step w s, h => by
      by_cases hs : s.isProj = true
      · rw [Subst.at_proj _ _ hs, at_ren_of θ w h]
        rfl
      · rw [Subst.at_nonproj _ (Bool.eq_false_iff.mpr hs : (VarSymb.step w s).lastProj = false)]
        exact h _ rfl

theorem under_raw_ne {Δ : Ctx} (θ : Subst σ Δ) {d d' : ℕ} {T : VarType}
    (h : Δ (.root (.bnd d')) = none) {v : VarSymb} (hv : v ≠ .root (.bnd d)) :
    θ.under d d' T h v = (θ v).mono (Ctx.le_insert h T) :=
  if_neg hv

theorem under_raw_root {Δ : Ctx} (θ : Subst σ Δ) {d d' : ℕ} {T : VarType}
    (h : Δ (.root (.bnd d')) = none) :
    θ.under d d' T h (.root (.bnd d)) = .ren (.root (.bnd d')) :=
  if_pos rfl

theorem at_under_root {Δ : Ctx} (θ : Subst σ Δ) {d d' : ℕ} {T : VarType}
    (h : Δ (.root (.bnd d')) = none) :
    (θ.under d d' T h).at (.root (.bnd d)) = .ren (.root (.bnd d')) :=
  if_pos rfl

theorem at_under_root_ne {Δ : Ctx} (θ : Subst σ Δ) {d d' : ℕ} {T : VarType}
    (h : Δ (.root (.bnd d')) = none) {r : Root} (hr : r ≠ .bnd d) :
    (θ.under d d' T h).at (.root r) = (θ (.root r)).mono (Ctx.le_insert h T) :=
  if_neg fun e => hr (by cases e; rfl)

theorem at_toFree_root {Δ : Ctx} (θ : Subst σ Δ) (d u : ℕ) (T : VarType)
    (h : Δ (.root (.free u)) = none) :
    (θ.toFree d u T h).at (.root (.bnd d)) = .ren (.root (.free u)) :=
  if_pos rfl

theorem single_raw_ne {Δ : Ctx} {r : Root} {e : SubE σ Δ} {v : VarSymb} (hv : v ≠ .root r) :
    Subst.single r e v = .ren v :=
  if_neg hv

theorem single_raw_root {Δ : Ctx} (r : Root) (e : SubE σ Δ) : Subst.single r e (.root r) = e :=
  if_pos rfl

theorem itemOk_id {Γ Δ : Ctx} (hle : Γ.Le Δ) : ItemOk Γ Δ id := fun v _ hl hv =>
  hle.ref (show Γ.ref v = _ by rw [Ctx.ref_nonproj _ hl]; exact hv)

theorem ItemOk.le {Γ Δ Δ' : Ctx} {f : VarSymb → VarSymb} (hf : ItemOk Γ Δ f) (hle : Δ.Le Δ') :
    ItemOk Γ Δ' f := fun v T hl hv => hle.ref (hf v T hl hv)

/-- The address of a reachable item's image has a free root. -/
theorem rt_free_of_ref {l : List VarType} {w : VarSymb} {T : VarType}
    (h : (ctxOf l).ref w = some T) : ∃ r, w.rt = .free r :=
  (reach_ppath h).2

/-! ## The abstractions of a lift -/

/-- The lifted root's kept item. -/
abbrev mKeep (ls : List VarType) : VarSymb := .step (.root (.free ls.length)) .keep

/-- The context of `χ(e, y)`: the old view, the kept object `e`, the residual `y`. -/
abbrev lCtx2 (k : Option VarSymb) (T : VarType) (ls : List VarType) : Ctx :=
  (((ctxOf ls).kView k).insert (.bnd 0) T).insert (.bnd 1) T.lr

theorem lCtx2_slots (k : Option VarSymb) (T : VarType) (ls : List VarType) :
    (lCtx2 k T ls).SlotsFrom 2 :=
  ((Ctx.NoSlots.slots (Γ := (ctxOf ls).kView k)).insert T).insert T.lr

theorem lCtx2_le (k : Option VarSymb) (T : VarType) (ls : List VarType) :
    ((ctxOf ls).kView k).Le (lCtx2 k T ls) :=
  (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf ls).kView k)).root T).trans
    (Ctx.le_insert ((Ctx.NoSlots.slots (Γ := (ctxOf ls).kView k)).insert T).root T.lr)

theorem itemOk_liftAbs (hF : ModalSys.Four = true) (k : Option VarSymb) (T : VarType)
    (hT : T.keepable = true) (ls : List VarType) (hko : KOld k ls.length) :
    ItemOk ((ctxOf (T :: ls)).kView k) (lCtx2 k T ls)
      (gliftG id T ls.length (.root (.bnd 0)) (.bnd 1)) :=
  itemOk_gliftG hF hT hko (itemOk_id (lCtx2_le k T ls))
    (by rw [Ctx.ref_insert_ne _ (fun h => by cases h)]; exact Ctx.ref_insert_root _ _ _)
    (Ctx.ref_insert_root _ _ _)

/-- A formula of the new view with the lifted root's kept item at the slot `e` and its residual
    at the slot `y`. -/
def liftAbs (hF : ModalSys.Four = true) (k : Option VarSymb) (T : VarType)
    (hT : T.keepable = true) (ls : List VarType) (hko : KOld k ls.length)
    (ψ : WFF σ ((ctxOf (T :: ls)).kView k) 0) : WFF σ (lCtx2 k T ls) 2 :=
  WFF.subst (itemIdx (gliftG id T ls.length (.root (.bnd 0)) (.bnd 1)))
    (itemS σ (lCtx2 k T ls) (gliftG id T ls.length (.root (.bnd 0)) (.bnd 1)))
    (ok_itemS_kView (itemOk_liftAbs hF k T hT ls hko))
    (coh_itemS_kView (itemOk_liftAbs hF k T hT ls hko)) Ctx.NoSlots.slots (lCtx2_slots k T ls) ψ

/-- ⭐The seed formula refuting a realisation of `ψ`: `χ(e) := ¬∃y. ψ(e, y)`. -/
def liftChi (hF : ModalSys.Four = true) (k : Option VarSymb) (T : VarType)
    (hT : T.keepable = true) (ls : List VarType) (hko : KOld k ls.length)
    (ψ : WFF σ ((ctxOf (T :: ls)).kView k) 0) :
    WFF σ (((ctxOf ls).kView k).insert (.bnd 0) T) 1 :=
  (WFF.ex T.lr (liftAbs hF k T hT ls hko ψ)).neg

/-- The context of `ψ(m.keep, y)`: the new view and the residual `y`. -/
abbrev lCtx1 (k : Option VarSymb) (T : VarType) (ls : List VarType) : Ctx :=
  ((ctxOf (T :: ls)).kView k).insert (.bnd 0) T.lr

theorem itemOk_liftRes (hF : ModalSys.Four = true) (k : Option VarSymb) (T : VarType)
    (hT : T.keepable = true) (ls : List VarType) (hko : KOld k ls.length) :
    ItemOk ((ctxOf (T :: ls)).kView k) (lCtx1 k T ls)
      (gliftG id T ls.length (mKeep ls) (.bnd 0)) :=
  itemOk_gliftG hF hT hko
    (itemOk_id (((ctxOf_le_append [T] ls).kView k).trans
      (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf (T :: ls)).kView k)).root T.lr)))
    (by
      rw [Ctx.ref_insert_ne _ (fun h => by cases h)]
      exact (Ctx.le_boxIn_kView _ k).ref (Ctx.ref_keep_of' hF (ctxOf_ref_new T ls) hT))
    (Ctx.ref_insert_root _ _ _)

/-- A formula of the new view with the lifted root's residual at the slot `y`. -/
def liftRes (hF : ModalSys.Four = true) (k : Option VarSymb) (T : VarType)
    (hT : T.keepable = true) (ls : List VarType) (hko : KOld k ls.length)
    (ψ : WFF σ ((ctxOf (T :: ls)).kView k) 0) : WFF σ (lCtx1 k T ls) 1 :=
  WFF.subst (itemIdx (gliftG id T ls.length (mKeep ls) (.bnd 0)))
    (itemS σ (lCtx1 k T ls) (gliftG id T ls.length (mKeep ls) (.bnd 0)))
    (ok_itemS_kView (itemOk_liftRes hF k T hT ls hko))
    (coh_itemS_kView (itemOk_liftRes hF k T hT ls hko)) Ctx.NoSlots.slots
    ((Ctx.NoSlots.slots (Γ := (ctxOf (T :: ls)).kView k)).insert T.lr) ψ

/-- The kept item of the lifted root has its type. -/
theorem kView_mKeep {k : Option VarSymb} {T : VarType} {ls : List VarType}
    (hko : KOld k ls.length) {T' : VarType}
    (hv : (ctxOf (T :: ls)).kView k (mKeep ls) = some T') : T' = T := by
  obtain ⟨-, hu, -⟩ := Ctx.boxIn_keep (kView_boxIn hko rfl hv)
  rw [ctxOf_ref_new] at hu
  exact (Option.some.inj hu).symm

/-- ⭐**Reading the seed formula at the lifted root**: `χ(m.keep) = ¬∃y. ψ(y)`. -/
theorem instantiate_liftChi (hF : ModalSys.Four = true) (k : Option VarSymb) (T : VarType)
    (hT : T.keepable = true) (ls : List VarType) (hko : KOld k ls.length)
    (hs : ((ctxOf (T :: ls)).kView k).SlotsFrom 0)
    (hle : (((ctxOf ls).kView k).insert (.bnd 0) T).Le
      (((ctxOf (T :: ls)).kView k).insert (.bnd 0) T))
    (h : ((ctxOf (T :: ls)).kView k).ref (mKeep ls) = some T)
    (ψ : WFF σ ((ctxOf (T :: ls)).kView k) 0) :
    WFF.instantiate hs (Term.eta (mKeep ls) T h) (WFF.mono hle (liftChi hF k T hT ls hko ψ)) =
      (WFF.ex T.lr (liftRes hF k T hT ls hko ψ)).neg := by
  unfold liftChi WFF.instantiate WFF.substRoot
  simp only [WFF.mono, WFF.subst]
  congr 2
  unfold liftAbs liftRes
  rw [WFF.subst_mono _ _ _ _ (lCtx2_slots k T ls)]
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ ψ
  refine Subst.sim_of ?_
  intro v T' hl hv
  obtain ⟨u, s, rfl, -, U, hU⟩ := kView_item hv
  have hs' : s.isProj = false := hl
  change SubE.Sim T'
    (if s.isProj then SubE.hide else .ren (gliftG id T ls.length (mKeep ls) (.bnd 0) (.step u s)))
    ((if s.isProj then SubE.hide
      else .ren (gliftG id T ls.length (.root (.bnd 0)) (.bnd 1) (.step u s))).comp _ _ _)
  rw [if_neg (by simp [hs']), if_neg (by simp [hs'])]
  by_cases hrt : u.rt = .free ls.length
  · by_cases hnk : u = .root (.free ls.length) ∧ s = .keep
    · obtain ⟨rfl, rfl⟩ := hnk
      have e := kView_mKeep hko hv
      subst T'
      rw [gliftG_keep, gliftG_keep]
      change SubE.Sim T _ ((Subst.under _ _ _ T.lr _).at (.root (.bnd 0)))
      rw [at_under_root_ne _ _ (fun h => by cases h), single_raw_root]
      change SubE.Sim T _ (.tm (Term.mono _ (Term.eta _ T h)))
      rw [Term.mono_eta]
      exact .ren_eta _ _
    · rw [gliftG_res hrt hnk, gliftG_res hrt hnk]
      change SubE.Sim T' _ ((Subst.under _ _ _ T.lr _).at
        ((VarSymb.root (.bnd 1)).ext (lPath T u.path s)))
      rw [at_ext_ren _ _ (ppath_lPath _ _ _) (at_under_root _ _)]
      exact .refl _
  · rw [gliftG_old hrt, gliftG_old hrt]
    change SubE.Sim T' _ ((Subst.under _ _ _ T.lr _).at (.step u s))
    rw [Subst.at_nonproj _ hl, under_raw_ne _ _ (fun h => by cases h),
      single_raw_ne (fun h => by cases h)]
    exact .refl _

/-- ⭐**The residual tuple realises the residual slot**: `ψ(y)` at `y := m`'s residual is `ψ`. -/
theorem instantiate_rtup_liftRes (hF : ModalSys.Four = true) (k : Option VarSymb) (T : VarType)
    (hT : T.keepable = true) (ls : List VarType) (hko : KOld k ls.length)
    (ψ : WFF σ ((ctxOf (T :: ls)).kView k) 0) :
    WFF.instantiate Ctx.NoSlots.slots
      (Term.mono (Ctx.le_boxIn_kView _ k)
        (rtup hF (.root (.free ls.length)) T (ctxOf_ref_new T ls)))
      (liftRes hF k T hT ls hko ψ) = ψ := by
  unfold WFF.instantiate WFF.substRoot liftRes
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ Subst.ok_idS Subst.coh_idS _ _ _ ?_ ψ).trans
    (WFF.subst_id _ _ _ ψ)
  refine Subst.sim_of ?_
  intro v T' hl hv
  obtain ⟨u, s, rfl, hup, U, hU⟩ := kView_item hv
  have hs' : s.isProj = false := hl
  change SubE.Sim T' (.ren (.step u s))
    ((if s.isProj then SubE.hide
      else .ren (gliftG id T ls.length (mKeep ls) (.bnd 0) (.step u s))).comp _ _ _)
  rw [if_neg (by simp [hs'])]
  by_cases hrt : u.rt = .free ls.length
  · by_cases hnk : u = .root (.free ls.length) ∧ s = .keep
    · obtain ⟨rfl, rfl⟩ := hnk
      rw [gliftG_keep]
      change SubE.Sim T' _ ((Subst.single (.bnd 0) _).at (mKeep ls))
      rw [Subst.single_at_ne (fun h => by cases h)]
      exact .refl _
    · rw [gliftG_res hrt hnk]
      change SubE.Sim T' _ ((Subst.single (.bnd 0) _).at
        ((VarSymb.root (.bnd 0)).ext (lPath T u.path s)))
      have hwalk : T.walk u.path = some U := by
        have e := Ctx.ref_ext_ppath (ctxOf (T :: ls)) u.path (.root u.rt) hup
        rw [← VarSymb.eq_root_ext u, hU, hrt, ctxOf_ref_new] at e
        exact e.symm
      have hit : (ctxOf (T :: ls)).boxIn.ref (.step u s) = some T' := by
        rw [Ctx.ref_nonproj _ hl]
        exact kView_boxIn hko hrt hv
      have hnk' : ¬ (u.path = [] ∧ s = .keep) := fun ⟨hp, hk⟩ =>
        hnk ⟨by rw [VarSymb.eq_root_ext u, hp, hrt]; rfl, hk⟩
      rw [at_lPath_rtupB hF (Ctx.le_boxIn_kView _ k) _ ModalSys.keepOnly rfl hs' T hT u.path
        (.root (.free ls.length)) (.root (.bnd 0)) (ctxOf_ref_new T ls) hup hwalk
        (Subst.at_single_root _ _) hnk' u (by rw [← hrt]; exact VarSymb.eq_root_ext u) hit,
        Term.mono_eta]
      exact .ren_eta _ _
  · rw [gliftG_old hrt]
    change SubE.Sim T' _ ((Subst.single (.bnd 0) _).at (.step u s))
    rw [Subst.single_at_ne (by
      change u.rt ≠ _
      obtain ⟨r, hr⟩ := (reach_ppath hU).2
      rw [hr]
      exact fun h => by cases h)]
    exact .refl _

/-! ## The target's reading -/

/-- ⭐A slot formula `χ(e)` about the kept object, read in the target at `n`: the body of the
    edge's translation of `∃e. χ(e)`, instantiated at `n`. -/
def liftTgt {k : Option VarSymb} {T : VarType} {ls lt : List VarType} {f : VarSymb → VarSymb}
    (hf : ItemOk ((ctxOf ls).kView k) (ctxOf lt) f) {n : VarSymb}
    (hn : (ctxOf lt).ref n = some T) (χ : WFF σ (((ctxOf ls).kView k).insert (.bnd 0) T) 1) :
    WFF σ (ctxOf lt) 0 :=
  WFF.instantiate Ctx.NoSlots.slots (Term.eta n T hn)
    (WFF.subst (VarSymb.shiftSlot (itemIdx f) 0 0)
      ((itemS σ (ctxOf lt) f).under 0 0 T (Ctx.NoSlots.slots (Γ := ctxOf lt)).root)
      (Subst.ok_under (ok_itemS_kView hf) T _)
      (Subst.coh_under (ok_itemS_kView hf) (coh_itemS_kView hf) Ctx.NoSlots.slots T _)
      ((Ctx.NoSlots.slots (Γ := (ctxOf ls).kView k)).insert T)
      ((Ctx.NoSlots.slots (Γ := ctxOf lt)).insert T) χ)

/-- The target's reading of `χ(e)` at `n` gives the translation of `∃e. χ(e)`. -/
theorem provable_ex_liftTgt {k : Option VarSymb} {T : VarType} {ls lt : List VarType}
    {f : VarSymb → VarSymb} (hf : ItemOk ((ctxOf ls).kView k) (ctxOf lt) f) {n : VarSymb}
    (hn : (ctxOf lt).ref n = some T) (χ : WFF σ (((ctxOf ls).kView k).insert (.bnd 0) T) 1) :
    Provable [liftTgt hf hn χ]
      (WFF.subst (itemIdx f) (itemS σ (ctxOf lt) f) (ok_itemS_kView hf) (coh_itemS_kView hf)
        Ctx.NoSlots.slots Ctx.NoSlots.slots (WFF.ex T χ)) :=
  ⟨Proof.ex_intro T (Term.eta n T hn) (Proof.lookup List.mem_cons_self)⟩

theorem itemOk_liftTr (hF : ModalSys.Four = true) {k : Option VarSymb} {T : VarType}
    (hT : T.keepable = true) {ls lt : List VarType} (hko : KOld k ls.length)
    {f : VarSymb → VarSymb} (hf : ItemOk ((ctxOf ls).kView k) (ctxOf lt) f) {n : VarSymb}
    (hn : (ctxOf lt).ref n = some T) :
    ItemOk ((ctxOf (T :: ls)).kView k) ((ctxOf lt).insert (.bnd 0) T.lr)
      (gliftG f T ls.length n (.bnd 0)) :=
  itemOk_gliftG hF hT hko (hf.le (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf lt)).root T.lr))
    ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf lt)).root T.lr).ref hn)
    (Ctx.ref_insert_root _ _ _)

/-- `ψ` read in the target with the lifted root's kept item at `n` and its residual at the slot. -/
def liftTr (hF : ModalSys.Four = true) {k : Option VarSymb} {T : VarType}
    (hT : T.keepable = true) {ls lt : List VarType} (hko : KOld k ls.length)
    {f : VarSymb → VarSymb} (hf : ItemOk ((ctxOf ls).kView k) (ctxOf lt) f) {n : VarSymb}
    (hn : (ctxOf lt).ref n = some T) (ψ : WFF σ ((ctxOf (T :: ls)).kView k) 0) :
    WFF σ ((ctxOf lt).insert (.bnd 0) T.lr) 1 :=
  WFF.subst (itemIdx (gliftG f T ls.length n (.bnd 0)))
    (itemS σ ((ctxOf lt).insert (.bnd 0) T.lr) (gliftG f T ls.length n (.bnd 0)))
    (ok_itemS_kView (itemOk_liftTr hF hT hko hf hn))
    (coh_itemS_kView (itemOk_liftTr hF hT hko hf hn)) Ctx.NoSlots.slots
    ((Ctx.NoSlots.slots (Γ := ctxOf lt)).insert T.lr) ψ

/-- The intermediate item map: the old items translated, the lifted root's at the slots. -/
theorem itemOk_liftMid (hF : ModalSys.Four = true) {k : Option VarSymb} {T : VarType}
    (hT : T.keepable = true) {ls lt : List VarType} (hko : KOld k ls.length)
    {f : VarSymb → VarSymb} (hf : ItemOk ((ctxOf ls).kView k) (ctxOf lt) f) :
    ItemOk ((ctxOf (T :: ls)).kView k) (((ctxOf lt).insert (.bnd 0) T).insert (.bnd 1) T.lr)
      (gliftG f T ls.length (.root (.bnd 0)) (.bnd 1)) :=
  itemOk_gliftG hF hT hko
    (hf.le ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf lt)).root T).trans
      (Ctx.le_insert ((Ctx.NoSlots.slots (Γ := ctxOf lt)).insert T).root T.lr)))
    (by rw [Ctx.ref_insert_ne _ (fun h => by cases h)]; exact Ctx.ref_insert_root _ _ _)
    (Ctx.ref_insert_root _ _ _)

/-- ⭐**The target's reading of the seed formula**: `χ(n) = ¬∃y. ψ(n, y)`. -/
theorem liftTgt_liftChi (hF : ModalSys.Four = true) {k : Option VarSymb} {T : VarType}
    (hT : T.keepable = true) {ls lt : List VarType} (hko : KOld k ls.length)
    {f : VarSymb → VarSymb} (hf : ItemOk ((ctxOf ls).kView k) (ctxOf lt) f) {n : VarSymb}
    (hn : (ctxOf lt).ref n = some T) (ψ : WFF σ ((ctxOf (T :: ls)).kView k) 0) :
    liftTgt hf hn (liftChi hF k T hT ls hko ψ) =
      (WFF.ex T.lr (liftTr hF hT hko hf hn ψ)).neg := by
  have hM := itemOk_liftMid hF hT hko hf
  have hMs : (((ctxOf lt).insert (.bnd 0) T).insert (.bnd 1) T.lr).SlotsFrom 2 :=
    ((Ctx.NoSlots.slots (Γ := ctxOf lt)).insert T).insert T.lr
  unfold liftTgt liftChi WFF.instantiate WFF.substRoot
  simp only [WFF.subst]
  congr 2
  unfold liftAbs liftTr
  rw [WFF.subst_comp _ _ (itemS σ _ (gliftG f T ls.length (.root (.bnd 0)) (.bnd 1))) _ _ _ _
    (ok_itemS_kView hM) (coh_itemS_kView hM) _ _ hMs ?sim1 ψ]
  · refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?sim2 ψ
    refine Subst.sim_of ?_
    intro v T' hl hv
    obtain ⟨u, s, rfl, -, U, hU⟩ := kView_item hv
    have hs' : s.isProj = false := hl
    change SubE.Sim T'
      (if s.isProj then SubE.hide else .ren (gliftG f T ls.length n (.bnd 0) (.step u s)))
      ((if s.isProj then SubE.hide
        else .ren (gliftG f T ls.length (.root (.bnd 0)) (.bnd 1) (.step u s))).comp _ _ _)
    rw [if_neg (by simp [hs']), if_neg (by simp [hs'])]
    by_cases hrt : u.rt = .free ls.length
    · by_cases hnk : u = .root (.free ls.length) ∧ s = .keep
      · obtain ⟨rfl, rfl⟩ := hnk
        have e := kView_mKeep hko hv
        subst T'
        rw [gliftG_keep, gliftG_keep]
        change SubE.Sim T _ ((Subst.under _ _ _ T.lr _).at (.root (.bnd 0)))
        rw [at_under_root_ne _ _ (fun h => by cases h), single_raw_root]
        change SubE.Sim T _ (.tm (Term.mono _ (Term.eta _ T hn)))
        rw [Term.mono_eta]
        exact .ren_eta _ _
      · rw [gliftG_res hrt hnk, gliftG_res hrt hnk]
        change SubE.Sim T' _ ((Subst.under _ _ _ T.lr _).at
          ((VarSymb.root (.bnd 1)).ext (lPath T u.path s)))
        rw [at_ext_ren _ _ (ppath_lPath _ _ _) (at_under_root _ _)]
        exact .refl _
    · rw [gliftG_old hrt, gliftG_old hrt]
      rw [kView_old hrt] at hv
      obtain ⟨r, hr⟩ := rt_free_of_ref (hf _ T' hl hv)
      change SubE.Sim T' _ ((Subst.under _ _ _ T.lr _).at (f (.step u s)))
      rw [at_ren_of _ _ (fun w hw => by
        rw [under_raw_ne _ _ (fun h => by rw [h] at hw; rw [hr] at hw; cases hw),
          single_raw_ne (fun h => by rw [h] at hw; rw [hr] at hw; cases hw)]
        rfl)]
      exact .refl _
  case sim1 =>
    refine Subst.sim_of ?_
    intro v T' hl hv
    obtain ⟨u, s, rfl, -, U, hU⟩ := kView_item hv
    have hs' : s.isProj = false := hl
    change SubE.Sim T'
      (if s.isProj then SubE.hide
        else .ren (gliftG f T ls.length (.root (.bnd 0)) (.bnd 1) (.step u s)))
      ((if s.isProj then SubE.hide
        else .ren (gliftG id T ls.length (.root (.bnd 0)) (.bnd 1) (.step u s))).comp _ _ _)
    rw [if_neg (by simp [hs']), if_neg (by simp [hs'])]
    by_cases hrt : u.rt = .free ls.length
    · by_cases hnk : u = .root (.free ls.length) ∧ s = .keep
      · obtain ⟨rfl, rfl⟩ := hnk
        rw [gliftG_keep, gliftG_keep]
        change SubE.Sim T' _ ((Subst.under _ _ _ T.lr _).at (.root (.bnd 0)))
        rw [at_under_root_ne _ _ (fun h => by cases h), under_raw_root]
        exact .refl _
      · rw [gliftG_res hrt hnk, gliftG_res hrt hnk]
        change SubE.Sim T' _ ((Subst.under _ _ _ T.lr _).at
          ((VarSymb.root (.bnd 1)).ext (lPath T u.path s)))
        rw [at_ext_ren _ _ (ppath_lPath _ _ _) (at_under_root _ _)]
        exact .refl _
    · rw [gliftG_old hrt, gliftG_old hrt]
      change SubE.Sim T' _ ((Subst.under _ _ _ T.lr _).at (.step u s))
      rw [Subst.at_nonproj _ hl, under_raw_ne _ _ (fun h => by cases h),
        under_raw_ne _ _ (fun h => by cases h)]
      change SubE.Sim T' _ (SubE.mono _ (SubE.mono _
        (if s.isProj then SubE.hide else .ren (f (.step u s)))))
      rw [if_neg (by simp [hs'])]
      exact .refl _

/-! ## The edge's own map for a lifted root -/

theorem itemOk_gliftZ (hF : ModalSys.Four = true) {k : Option VarSymb} {T : VarType}
    (hT : T.keepable = true) {ls lt : List VarType} (hko : KOld k ls.length)
    {f : VarSymb → VarSymb} (hf : ItemOk ((ctxOf ls).kView k) (ctxOf lt) f) {n : VarSymb}
    (hn : (ctxOf lt).ref n = some T) :
    ItemOk ((ctxOf (T :: ls)).kView k) (ctxOf (T.lr :: lt))
      (gliftG f T ls.length n (.free lt.length)) :=
  itemOk_gliftG hF hT hko (hf.le (ctxOf_le_append [T.lr] lt))
    ((ctxOf_le_append [T.lr] lt).ref hn) (ctxOf_ref_new T.lr lt)

/-- ⭐The edge's item map for a lifted root, applied to a formula: `m.keep ↦ n`, the residual
    to the fresh variable `lt.length : T.lr`. -/
abbrev gliftArrow (hF : ModalSys.Four = true) {k : Option VarSymb} {T : VarType}
    (hT : T.keepable = true) {ls lt : List VarType} (hko : KOld k ls.length)
    {f : VarSymb → VarSymb} (hf : ItemOk ((ctxOf ls).kView k) (ctxOf lt) f) {n : VarSymb}
    (hn : (ctxOf lt).ref n = some T) (ψ : WFF σ ((ctxOf (T :: ls)).kView k) 0) :
    WFF σ (ctxOf (T.lr :: lt)) 0 :=
  WFF.subst (itemIdx (gliftG f T ls.length n (.free lt.length)))
    (itemS σ (ctxOf (T.lr :: lt)) (gliftG f T ls.length n (.free lt.length)))
    (ok_itemS_kView (itemOk_gliftZ hF hT hko hf hn))
    (coh_itemS_kView (itemOk_gliftZ hF hT hko hf hn)) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ

/-- ⭐The edge's translation for a lifted root is `liftTr` opened at the fresh variable. -/
theorem gliftArrow_openFree (hF : ModalSys.Four = true) {k : Option VarSymb} {T : VarType}
    (hT : T.keepable = true) {ls lt : List VarType} (hko : KOld k ls.length)
    {f : VarSymb → VarSymb} (hf : ItemOk ((ctxOf ls).kView k) (ctxOf lt) f) {n : VarSymb}
    (hn : (ctxOf lt).ref n = some T) (ψ : WFF σ ((ctxOf (T :: ls)).kView k) 0) :
    gliftArrow hF hT hko hf hn ψ =
      WFF.openFree lt.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots
        (liftTr hF hT hko hf hn ψ) := by
  unfold WFF.openFree liftTr
  refine (WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ ψ).symm
  refine Subst.sim_of ?_
  intro v T' hl hv
  obtain ⟨u, s, rfl, -, U, hU⟩ := kView_item hv
  have hs' : s.isProj = false := hl
  change SubE.Sim T'
    (if s.isProj then SubE.hide else .ren (gliftG f T ls.length n (.free lt.length) (.step u s)))
    ((if s.isProj then SubE.hide
      else .ren (gliftG f T ls.length n (.bnd 0) (.step u s))).comp _ _ _)
  rw [if_neg (by simp [hs']), if_neg (by simp [hs'])]
  have hren : ∀ w : VarSymb, (∃ r, w.rt = .free r) →
      ((Subst.idRen (σ := σ) (ctxOf lt)).toFree 0 lt.length T.lr
        (ctxOf_fresh le_rfl).root).at w = .ren w := fun w ⟨r, hr⟩ =>
    at_ren_of _ _ fun w' hw' => by
      rw [Subst.toFree_ne _ _ _ _ (fun h => by rw [h] at hw'; rw [hr] at hw'; cases hw')]
      rfl
  by_cases hrt : u.rt = .free ls.length
  · by_cases hnk : u = .root (.free ls.length) ∧ s = .keep
    · obtain ⟨rfl, rfl⟩ := hnk
      rw [gliftG_keep, gliftG_keep]
      change SubE.Sim T' _ ((Subst.toFree _ 0 lt.length T.lr _).at n)
      rw [hren n (rt_free_of_ref hn)]
      exact .refl _
    · rw [gliftG_res hrt hnk, gliftG_res hrt hnk]
      change SubE.Sim T' _ ((Subst.toFree _ 0 lt.length T.lr _).at
        ((VarSymb.root (.bnd 0)).ext (lPath T u.path s)))
      rw [at_ext_ren _ _ (ppath_lPath _ _ _) (at_toFree_root _ _ _ _ _)]
      exact .refl _
  · rw [gliftG_old hrt, gliftG_old hrt]
    rw [kView_old hrt] at hv
    change SubE.Sim T' _ ((Subst.toFree _ 0 lt.length T.lr _).at (f (.step u s)))
    rw [hren _ (rt_free_of_ref (hf _ T' hl hv))]
    exact .refl _

/-! ## The possibility of an edge, and the rule along it -/

/-- The possibility of an edge's kind: `◇`, or `◇_x` for a child made for `◇_x`. -/
def kDia {Γ : Ctx} {d : ℕ} : (k : Option VarSymb) → KDecl Γ k → WFF σ (Γ.kView k) d →
    WFF σ Γ d
  | none, _, φ => (WFF.box φ.neg).neg
  | some x, hk, φ => WFF.dia x (hk x rfl) φ

/-- ⭐What `Proof.keep_lift` hands its subproof along an edge's kind: `◇_k χ(c.keep)`. -/
def kLiftRead (hF : ModalSys.Four = true) {T : VarType} (hl : T.liftable = true) {Γ : Ctx}
    [Γ.NoSlots] : (k : Option VarSymb) → KDecl Γ k → {c : ℕ} → Γ.RootFresh (.free c) →
    WFF σ ((Γ.kView k).insert (.bnd 0) T) 1 → WFF σ (Γ.insert (.free c) T) 0
  | none, _, _, hc, χ => WFF.liftRead hF hl .nec hc χ
  | some x, hk, _, hc, χ => WFF.liftRead hF hl (.pos x (hk x rfl)) hc χ

theorem kLiftRead_eq (hF : ModalSys.Four = true) {T : VarType} (hl : T.liftable = true)
    {Γ : Ctx} [Γ.NoSlots] (k : Option VarSymb) (hk : KDecl Γ k) {c : ℕ}
    (hc : Γ.RootFresh (.free c)) (χ : WFF σ ((Γ.kView k).insert (.bnd 0) T) 1)
    (hs : ((Γ.insert (.free c) T).kView k).SlotsFrom 0)
    (h : ((Γ.insert (.free c) T).kView k).ref (.step (.root (.free c)) .keep) = some T)
    (hle : ((Γ.kView k).insert (.bnd 0) T).Le
      (((Γ.insert (.free c) T).kView k).insert (.bnd 0) T)) :
    kLiftRead hF hl k hk hc χ = kDia k (kDecl_mono (Ctx.le_insert hc.root T) hk)
      (WFF.instantiate hs (Term.eta (.step (.root (.free c)) .keep) T h) (WFF.mono hle χ)) := by
  cases k <;> rfl

/-- ⭐**Strong 4 along an edge's kind** (`Proof.keep_lift` at the leg `□` or `◇_x`). -/
def Proof.kKeepLift (hF : ModalSys.Four = true) {T : VarType} (hl : T.liftable = true)
    {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} :
    (k : Option VarSymb) → (hk : KDecl Γ k) → (χ : WFF σ ((Γ.kView k).insert (.bnd 0) T) 1) →
    (c : ℕ) → (hc : Γ.RootFresh (.free c)) → {ψ : WFF σ Γ 0} →
    Proof σ Γ Δ (kDia k hk (WFF.ex T χ)) →
    Proof σ (Γ.insert (.free c) T)
      (kLiftRead hF hl k hk hc χ :: Δ.map (WFF.weaken hc.root T)) (ψ.weaken hc.root T) →
    Proof σ Γ Δ ψ
  | none, _, χ, c, hc, _, p, q => Proof.keep_lift hF hl .nec χ c hc p q
  | some x, hk, χ, c, hc, _, p, q => Proof.keep_lift hF hl (.pos x (hk x rfl)) χ c hc p q

/-- `◇_k` is monotone. -/
theorem kDia_mono {Γ : Ctx} (k : Option VarSymb) (hk : KDecl Γ k)
    {φ φ' : WFF σ (Γ.kView k) 0} (p : Provable [φ] φ') :
    Provable [kDia k hk φ] (kDia k hk φ') := by
  obtain ⟨p⟩ := p
  cases k with
  | none =>
      have q : Provable [φ'.neg] φ.neg := Provable.imp_intro (Provable.mp
        (Provable.of_mem (List.mem_cons_of_mem _ List.mem_cons_self)) ⟨Proof.ofSubset
          (fun y hy => by rw [List.mem_singleton.mp hy]; exact List.mem_cons_self) p⟩)
      obtain ⟨q⟩ := q
      exact Provable.imp_intro (Provable.mp
        (Provable.of_mem (List.mem_cons_of_mem _ List.mem_cons_self))
        (Provable.mono (fun y hy => by
          rw [List.mem_singleton.mp hy]; exact List.mem_cons_self)
          ⟨Proof.K_box (Δ := [φ'.neg]) q⟩))
  | some x =>
      exact ⟨Proof.ofSubset (fun y hy => by simpa using hy)
        (Proof.K_dia x (hk x rfl) (Δ₁ := []) (Δ₂ := []) (ψ := φ) (φ := φ')
          (Proof.ofSubset (fun y hy => by simpa using hy) p))⟩

/-- `□_k ψ` and `◇_k χ` refute each other when `ψ` and `χ` do. -/
theorem kBox_kDia_bot {Γ : Ctx} (k : Option VarSymb) (hk : KDecl Γ k)
    {ψ χ : WFF σ (Γ.kView k) 0} (p : Provable [ψ, χ] .bot) :
    Provable [kBox k hk ψ, kDia k hk χ] .bot := by
  obtain ⟨p⟩ := p
  cases k with
  | none =>
      have q : Provable [ψ] χ.neg := Provable.imp_intro ⟨Proof.ofSubset (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · rw [List.mem_singleton.mp hy]; exact List.mem_cons_self) p⟩
      obtain ⟨q⟩ := q
      exact Provable.mp (Provable.of_mem (List.mem_cons_of_mem _ List.mem_cons_self))
        (Provable.mono (fun y hy => by
          rw [List.mem_singleton.mp hy]; exact List.mem_cons_self)
          ⟨Proof.K_box (Δ := [ψ]) q⟩)
  | some x =>
      refine ⟨Proof.ofSubset (fun y hy => ?_) (Proof.dia_bot x (hk x rfl)
        (Proof.K_dia x (hk x rfl) (Δ₁ := []) (Δ₂ := [ψ]) (ψ := χ) (φ := .bot)
          (Proof.ofSubset (fun y hy => ?_) p)))⟩
      · simp only [List.map_cons, List.map_nil, List.append_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_cons_self
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact List.mem_cons_of_mem _ (by simp)
        · simp only [List.mem_singleton] at hy
          rw [hy]
          exact List.mem_cons_self

/-- What is not `◇_k`-possible is `□_k`-refuted. -/
theorem not_kDia_mem {Γ : Ctx} {M : Set (WFF σ Γ 0)} (hM : Theory.IsMCS M)
    (k : Option VarSymb) (hk : KDecl Γ k) {φ : WFF σ (Γ.kView k) 0} (h : kDia k hk φ ∉ M) :
    kBox k hk φ.neg ∈ M := by
  cases k with
  | none =>
      by_contra hb
      exact h (hM.neg_mem_iff.mpr hb)
  | some x =>
      refine hM.neg_mem_iff.mpr fun hd => h (hM.closed ⟨[WFF.dia x (hk x rfl) φ.neg.neg],
        fun y hy => by rw [List.mem_singleton.mp hy]; exact hd, ?_⟩)
      exact kDia_mono (some x) hk (Provable.byContra (Provable.mp
        (Provable.of_mem (List.mem_cons_of_mem _ List.mem_cons_self))
        (Provable.of_mem List.mem_cons_self)))

/-- A list of formulas, each in `S` or the image of a `P`-formula, reduces to one image, given
    `P` is closed under `⊤` and `∧` and the image of a conjunction derives the images of its
    parts. -/
theorem list_reduce_d {α : Type} {Δ : Ctx} (P : α → Prop) (top : α) (cj : α → α → α)
    (htop : P top) (hand : ∀ {a b}, P a → P b → P (cj a b)) (g : α → WFF σ Δ 0)
    (hg₁ : ∀ a b, Provable [g (cj a b)] (g a)) (hg₂ : ∀ a b, Provable [g (cj a b)] (g b))
    (S : Set (WFF σ Δ 0)) :
    ∀ L : List (WFF σ Δ 0), (∀ δ ∈ L, δ ∈ S ∨ ∃ a, P a ∧ δ = g a) →
      ∃ a, P a ∧ ∀ δ ∈ L, Theory.Derives (S ∪ {g a}) δ
  | [], _ => ⟨top, htop, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨a₀, ha₀, hL⟩ := list_reduce_d P top cj htop hand g hg₁ hg₂ S L
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      rcases h δ List.mem_cons_self with hS | ⟨a₁, ha₁, rfl⟩
      · refine ⟨a₀, ha₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact Theory.Derives.of_mem (Or.inl hS)
        · exact hL d hd
      · have hg : ∀ {b}, Provable [g (cj a₀ a₁)] b → Theory.Derives (S ∪ {g (cj a₀ a₁)}) b :=
          fun p => ⟨[g (cj a₀ a₁)], fun x hx => by
            rw [List.mem_singleton.mp hx]; exact Or.inr rfl, p⟩
        refine ⟨cj a₀ a₁, hand ha₀ ha₁, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact hg (hg₂ a₀ a₁)
        · refine Derives.trans (fun x hx => ?_) (hL d hd)
          rcases hx with hx | hx
          · exact Theory.Derives.of_mem (Or.inl hx)
          · rw [Set.mem_singleton_iff.mp hx]
            exact hg (hg₁ a₀ a₁)

/-! ## The lift's seed -/

/-- ⭐The lifted root's **seed**: `◇_k χ(m.keep)` for every `χ(e)` whose reading at `n` the
    target holds. -/
def liftSeed (hF : ModalSys.Four = true) {T : VarType} (hl : T.liftable = true)
    {ls lt : List VarType} {k : Option VarSymb} (hk : KDecl (ctxOf ls) k)
    {f : VarSymb → VarSymb} (hf : ItemOk ((ctxOf ls).kView k) (ctxOf lt) f) {n : VarSymb}
    (hn : (ctxOf lt).ref n = some T) (N : Set (WFF σ (ctxOf lt) 0)) :
    Set (WFF σ ((ctxOf ls).insert (.free ls.length) T) 0) :=
  {φ | ∃ χ, liftTgt hf hn χ ∈ N ∧ φ = kLiftRead hF hl k hk (ctxOf_fresh le_rfl) χ}

/-- The seed of a conjunction gives the seeds of its parts. -/
theorem kLiftRead_and (hF : ModalSys.Four = true) {T : VarType} (hl : T.liftable = true)
    {Γ : Ctx} [Γ.NoSlots] (k : Option VarSymb) (hk : KDecl Γ k) {c : ℕ}
    (hc : Γ.RootFresh (.free c)) (χ₁ χ₂ : WFF σ ((Γ.kView k).insert (.bnd 0) T) 1) :
    Provable [kLiftRead hF hl k hk hc (χ₁.and χ₂)] (kLiftRead hF hl k hk hc χ₁) ∧
      Provable [kLiftRead hF hl k hk hc (χ₁.and χ₂)] (kLiftRead hF hl k hk hc χ₂) := by
  have h := (Ctx.le_boxIn_kView _ k).ref (Ctx.ref_keep_of' hF (Ctx.ref_insert_root Γ (.free c) T)
    (VarType.keepable_of_liftable hl))
  have hle := ((Ctx.le_insert hc.root T).kView k).insert (.bnd 0) T
  rw [kLiftRead_eq hF hl k hk hc _ Ctx.NoSlots.slots h hle,
    kLiftRead_eq hF hl k hk hc χ₁ Ctx.NoSlots.slots h hle,
    kLiftRead_eq hF hl k hk hc χ₂ Ctx.NoSlots.slots h hle]
  exact ⟨kDia_mono k _ (Provable.and_elim_l (Provable.of_mem List.mem_cons_self)),
    kDia_mono k _ (Provable.and_elim_r (Provable.of_mem List.mem_cons_self))⟩

/-- ⭐**The lift's seed is consistent with the source** (`Proof.keep_lift`): given the edge's
    transfer, every `χ(e)` true of `n` in the target is `◇_k`-true of a fresh `m.keep`. -/
theorem glift_consistent (hF : ModalSys.Four = true) {T : VarType} (hl : T.liftable = true)
    {ls lt : List VarType} {M : Set (WFF σ (ctxOf ls) 0)} (hM : Theory.IsMCS M)
    {N : Set (WFF σ (ctxOf lt) 0)} (hN : Theory.IsMCS N) {k : Option VarSymb}
    (hk : KDecl (ctxOf ls) k) {f : VarSymb → VarSymb}
    (hf : ItemOk ((ctxOf ls).kView k) (ctxOf lt) f)
    (htr : GTransfer M ls (Ctx.Le.refl _) k hk N f hf) {n : VarSymb}
    (hn : (ctxOf lt).ref n = some T) :
    Theory.Consistent (WFF.weaken (ctxOf_fresh (l := ls) le_rfl).root T '' M ∪
      liftSeed hF hl hk hf hn N) := by
  rintro ⟨L, hL, p⟩
  have hc := ctxOf_fresh (l := ls) le_rfl
  obtain ⟨χ, hχ, hder⟩ := list_reduce_d (fun χ => liftTgt hf hn χ ∈ N) .top WFF.and
    hN.top_mem (fun h₁ h₂ => hN.and_mem_iff.mpr ⟨h₁, h₂⟩) (kLiftRead hF hl k hk hc)
    (fun a b => (kLiftRead_and hF hl k hk hc a b).1)
    (fun a b => (kLiftRead_and hF hl k hk hc a b).2)
    (WFF.weaken hc.root T '' M) L (fun δ hδ => hL δ hδ)
  obtain ⟨Δ, hΔ, ⟨q⟩⟩ := derives_of_derives hder p
  obtain ⟨Δ₀, h₀, h₁⟩ := exists_hyps_cons_map (P := fun x => x ∈ M) (WFF.weaken hc.root T)
    (kLiftRead hF hl k hk hc χ) Δ (fun δ hδ => by
      rcases hΔ δ hδ with ⟨x, hx, rfl⟩ | h
      · exact Or.inr ⟨x, hx, rfl⟩
      · exact Or.inl (Set.mem_singleton_iff.mp h))
  -- The kept object's possibility is in the source: otherwise its refutation transfers.
  have hdia : kDia k hk (WFF.ex T χ) ∈ M := by
    by_contra hnd
    have hb := not_kDia_mem hM k hk hnd
    have ht := htr _ (by rw [WFF.mono_refl]; exact hb)
    have hex := hN.closed ⟨[liftTgt hf hn χ], fun x hx => by
      rw [List.mem_singleton.mp hx]; exact hχ, provable_ex_liftTgt hf hn χ⟩
    exact hN.neg_mem_iff.mp ht hex
  -- The rule turns the refutation of the seed into one of the source.
  apply hM.1
  refine ⟨kDia k hk (WFF.ex T χ) :: Δ₀, fun x hx => ?_,
    ⟨Proof.kKeepLift hF hl k hk χ ls.length hc (ψ := .bot) (Proof.lookup List.mem_cons_self)
      (Proof.ofSubset (fun y hy => ?_) q)⟩⟩
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact hdia
    · exact h₀ x hx
  · rcases List.mem_cons.mp (h₁ y hy) with rfl | hy'
    · exact List.mem_cons_self
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy'
      exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_cons_of_mem _ hz))

/-! ## The lifted root's residual -/

/-- The seed formula read at the lifted root. -/
theorem kLiftRead_liftChi (hF : ModalSys.Four = true) {T : VarType} (hl : T.liftable = true)
    {ls : List VarType} {k : Option VarSymb} (hk : KDecl (ctxOf ls) k)
    (ψ : WFF σ ((ctxOf (T :: ls)).kView k) 0) :
    kLiftRead hF hl k hk (ctxOf_fresh le_rfl)
        (liftChi hF k T (VarType.keepable_of_liftable hl) ls (kOld_of_kDecl hk) ψ) =
      kDia (Γ := ctxOf (T :: ls)) k (kDecl_mono (ctxOf_le_append [T] ls) hk)
        (WFF.ex T.lr (liftRes hF k T (VarType.keepable_of_liftable hl) ls
          (kOld_of_kDecl hk) ψ)).neg := by
  have h := (Ctx.le_boxIn_kView _ k).ref (Ctx.ref_keep_of' hF (ctxOf_ref_new T ls)
    (VarType.keepable_of_liftable hl))
  exact (kLiftRead_eq hF hl k hk (ctxOf_fresh le_rfl) _ Ctx.NoSlots.slots h
    (((ctxOf_le_append [T] ls).kView k).insert (.bnd 0) T)).trans
    (congrArg _ (instantiate_liftChi hF k T _ ls _ _ _ h ψ))

/-- ⭐**The lifted root's residual is realised** along the edge: in a source theory holding the
    seed, whatever is `□_k`-necessary of the lifted root is consistent with the target, `m.keep`
    read as `n` and the residual as a fresh variable. -/
theorem gliftRealise_consistent (hF : ModalSys.Four = true) {T : VarType}
    (hl : T.liftable = true) {ls lt : List VarType} {N : Set (WFF σ (ctxOf lt) 0)}
    (hN : Theory.IsMCS N) {k : Option VarSymb} (hk : KDecl (ctxOf ls) k)
    {f : VarSymb → VarSymb} (hf : ItemOk ((ctxOf ls).kView k) (ctxOf lt) f) {n : VarSymb}
    (hn : (ctxOf lt).ref n = some T) {M' : Set (WFF σ (ctxOf (T :: ls)) 0)}
    (hM' : Theory.IsMCS M') (hseed : liftSeed hF hl hk hf hn N ⊆ M') :
    Theory.Consistent (WFF.mono (ctxOf_le_append [T.lr] lt) '' N ∪
      {φ | ∃ ψ, kBox k (kDecl_mono (ctxOf_le_append [T] ls) hk) ψ ∈ M' ∧
        φ = gliftArrow hF (VarType.keepable_of_liftable hl) (kOld_of_kDecl hk) hf hn ψ}) := by
  have hT := VarType.keepable_of_liftable hl
  have hko := kOld_of_kDecl hk
  have hk' := kDecl_mono (ctxOf_le_append [T] ls) hk
  rintro ⟨L, hL, p⟩
  obtain ⟨ψ, hψ, hder⟩ := list_reduce (fun ψ => kBox k hk' ψ ∈ M')
    (by simpa only [WFF.mono_refl] using kBox_top_mem hM' (Ctx.Le.refl _) hk')
    (fun h₁ h₂ => by
      simpa only [WFF.mono_refl] using kBox_and_mem hM' (Ctx.Le.refl _) hk'
        (by rw [WFF.mono_refl]; exact h₁) (by rw [WFF.mono_refl]; exact h₂))
    (gliftArrow hF hT hko hf hn) (fun _ _ => rfl)
    (WFF.mono (ctxOf_le_append [T.lr] lt) '' N) L (fun δ hδ => (hL δ hδ).imp id id)
  have hbot := derives_of_derives hder p
  by_cases hex : WFF.ex T.lr (liftTr hF hT hko hf hn ψ) ∈ N
  · -- The residual has a Henkin witness: the fresh variable.
    have hc := henkin_consistent hN.1 (Theory.Derives.of_mem hex) (ctxOf_fresh (l := lt) le_rfl)
    rw [gliftArrow_openFree] at hbot
    exact hc hbot
  · -- Otherwise the seed refutes `ψ` at the lifted root.
    have hneg : liftTgt hf hn (liftChi hF k T hT ls hko ψ) ∈ N := by
      rw [liftTgt_liftChi]
      exact hN.neg_mem_iff.mpr hex
    have hlr := hseed ⟨_, hneg, rfl⟩
    rw [kLiftRead_liftChi] at hlr
    have hprov : Provable [ψ, (WFF.ex T.lr (liftRes hF k T hT ls hko ψ)).neg] .bot :=
      ⟨Proof.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
        (Proof.ex_intro T.lr (Term.mono (Ctx.le_boxIn_kView _ k)
          (rtup hF (.root (.free ls.length)) T (ctxOf_ref_new T ls)))
          (Proof.conv (instantiate_rtup_liftRes hF k T hT ls hko ψ).symm
            (Proof.lookup List.mem_cons_self)))⟩
    exact hM'.1 ⟨_, fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hψ
      · rw [List.mem_singleton.mp hx]; exact hlr, kBox_kDia_bot k hk' hprov⟩

end GArrow

end V12M
