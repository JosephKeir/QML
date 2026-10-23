import QML.QML_v12m_GSyntax

/-!
# QML v12m — the growing tree: the items of a root under 4

A **fresh realisation** commits a root `r : R` of a world along an edge by one fresh variable of
the target, which holds images for all of `r`'s items (`docs/v12-modal-extensions.md` §3 4, "The
growing tree: the three paper checks", 1).  Under 4 the items of the `□` view are `u.box : A` and
`u.keep : □A` for `u : □A`, and `u.keep : ◇A` for `u : ◇A`, with `u` a projection path from `r`
(`GArrow.boxIn_item`).  So the variable's type is `R.gc` (`VarType.gcB`): a `□A` component becomes
`A × □A` (contents, then the kept object), a `◇A` component stays `◇A` (the kept object), products
go componentwise, and every other leaf becomes `𝟙`.

Under T + 4 (`ModalSys.keepOnly`) a view shows no `box`, and a reachable address may pass through
`here`, so a `□A` component becomes `□A × gc A`: the kept object, then the items of `u.here`.

The item `u.s` lands at `gPath R u.path s` in the variable (`ref_gItem`), and the item map of a
family of fresh realisations is `gImg` (`itemOk_gImg`, `itemOk_gImgX` for a witness arrow).  This
is B's `VarType.bc` and `BArrow.itemAt` made for 4; B's files are untouched.
-/

namespace V12M

variable [ModalSys]

/-- The type of a fresh realisation under 4, for a given value `b` of `ModalSys.keepOnly` (taken as
    an argument so that terms of it can be built by matching, as `VarType.bcB`). -/
def VarType.gcB (b : Bool) : VarType → VarType
  | .VTypeProd A B => .VTypeProd (VarType.gcB b A) (VarType.gcB b B)
  | .VTypeBox A => cond b (.VTypeProd (.VTypeBox A) (VarType.gcB b A)) (.VTypeProd A (.VTypeBox A))
  | .VTypeDia A => .VTypeDia A
  | .Var => .VTypeOne
  | .VTypeOne => .VTypeOne

/-- ⭐What a fresh realisation under 4 gives a variable of type `T` at the target: each `□A`
    component becomes `A × □A` (its contents and its kept object), each `◇A` component its kept
    object `◇A`, every other leaf `𝟙`.  Under T + 4, `□A × gc A`: the kept object, then the items
    of the `here` value. -/
abbrev VarType.gc (T : VarType) : VarType := VarType.gcB ModalSys.keepOnly T

namespace Ctx

/-- Along a projection path, the type reached is the walk from the start's type. -/
theorem ref_ext_ppath (Γ : Ctx) :
    ∀ (q : List Step) (v : VarSymb), PPath q → Γ.ref (v.ext q) = (Γ.ref v).bind (·.walk q)
  | [], v, _ => by
      change Γ.ref v = _
      cases Γ.ref v <;> rfl
  | s :: q, v, h => by
      change Γ.ref ((VarSymb.step v s).ext q) = _
      rw [ref_ext_ppath Γ q _ (fun s' hs' => h s' (by simp [hs'])),
        ref_step_proj Γ v (h s (by simp))]
      cases Γ.ref v <;> rfl

end Ctx

namespace GArrow

open BArrow

/-! ## Where an item lands -/

/-- ⭐Where the item `u.s` of a root of type `R` lands in a variable of type `R.gc`, from `u`'s path
    `q`: products componentwise and, under T + 4, a `□` component's `here` value in the second
    component.  At `u` itself, `box` is the first component and `keep` the second (under T + 4 the
    first); a `◇` component's `keep` is the whole. -/
def gPath : VarType → List Step → Step → List Step
  | .VTypeProd A _, .fst :: q, s => .fst :: gPath A q s
  | .VTypeProd _ B, .snd :: q, s => .snd :: gPath B q s
  | .VTypeBox A, .here :: q, s => .snd :: gPath A q s
  | .VTypeBox _, [], .box => [.fst]
  | .VTypeBox _, [], .keep => cond ModalSys.keepOnly [.fst] [.snd]
  | _, _, _ => []

/-- An item at its own address: from a variable of `U.gc`, the item `u.s` of `u : U` is read at
    `gPath U [] s`. -/
theorem ref_gPath_nil {Δ : Ctx} {w : VarSymb} {U T : VarType} {s : Step}
    (hw : Δ.ref w = some U.gc)
    (hs : (s = .box ∧ ModalSys.keepOnly = false ∧ U = .VTypeBox T) ∨
      (s = .keep ∧ U = T ∧ T.keepable = true)) :
    Δ.ref (w.ext (gPath U [] s)) = some T := by
  rcases hs with ⟨rfl, hk, rfl⟩ | ⟨rfl, rfl, hT⟩
  · change Δ.ref (.step w .fst) = _
    rw [Ctx.ref_step_proj Δ w rfl, hw]
    simp [VarType.gc, VarType.gcB, hk, VarType.step]
  · cases U with
    | VTypeBox A =>
        cases hk : ModalSys.keepOnly
        · change Δ.ref (w.ext (cond ModalSys.keepOnly [.fst] [.snd])) = _
          rw [hk]
          change Δ.ref (.step w .snd) = _
          rw [Ctx.ref_step_proj Δ w rfl, hw]
          simp [VarType.gc, VarType.gcB, hk, VarType.step]
        · change Δ.ref (w.ext (cond ModalSys.keepOnly [.fst] [.snd])) = _
          rw [hk]
          change Δ.ref (.step w .fst) = _
          rw [Ctx.ref_step_proj Δ w rfl, hw]
          simp [VarType.gc, VarType.gcB, hk, VarType.step]
    | VTypeDia A => exact hw
    | _ => cases hT

/-- ⭐Along a projection path: the path's steps read in `R.gc` reach the `gc` type of where they
    lead, and the item there lands as at its own address. -/
theorem ref_gPath (hF : ModalSys.Four = true) {Δ : Ctx} {s : Step} {T : VarType} :
    ∀ (R : VarType) (q : List Step) {U : VarType} (w : VarSymb), PPath q → R.walk q = some U →
      Δ.ref w = some R.gc →
      (∀ w' : VarSymb, Δ.ref w' = some U.gc → Δ.ref (w'.ext (gPath U [] s)) = some T) →
      Δ.ref (w.ext (gPath R q s)) = some T
  | R, [], U, w, _, hq, hw, hb => by
      cases hq
      exact hb w hw
  | R, t :: q, U, w, hp, hq, hw, hb => by
      have hq' : PPath q := fun s' hs' => hp s' (by simp [hs'])
      cases t with
      | fst =>
          cases R with
          | VTypeProd A B =>
              have hw' : Δ.ref (.step w .fst) = some A.gc := by
                rw [Ctx.ref_step_proj Δ w rfl, hw]
                rfl
              exact ref_gPath hF A q (.step w .fst) hq' hq hw' hb
          | _ => cases hq
      | snd =>
          cases R with
          | VTypeProd A B =>
              have hw' : Δ.ref (.step w .snd) = some B.gc := by
                rw [Ctx.ref_step_proj Δ w rfl, hw]
                rfl
              exact ref_gPath hF B q (.step w .snd) hq' hq hw' hb
          | _ => cases hq
      | here =>
          cases R with
          | VTypeBox A =>
              have hT : ModalSys.T = true := by
                cases hT : ModalSys.T
                · simp [VarType.walk, VarType.step, hT] at hq
                · rfl
              have hk : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
              have hq'' : A.walk q = some U := by
                simpa [VarType.walk, VarType.step, hT] using hq
              have hw' : Δ.ref (.step w .snd) = some A.gc := by
                rw [Ctx.ref_step_proj Δ w rfl, hw]
                simp [VarType.gc, VarType.gcB, hk, VarType.step]
              exact ref_gPath hF A q (.step w .snd) hq' hq'' hw' hb
          | _ => cases hq
      | box => exact absurd (hp .box (by simp)) (by decide)
      | dia => exact absurd (hp .dia (by simp)) (by decide)
      | keep => exact absurd (hp .keep (by simp)) (by decide)

/-- ⭐An item of a world's `□` view, of a root `r`, lands at its type in a variable `z` of
    `r`'s `gc` type. -/
theorem ref_gItem (hF : ModalSys.Four = true) {l : List VarType} {Δ : Ctx} {z : Root} {r : ℕ}
    {u : VarSymb} {s : Step} {T : VarType} (h : (ctxOf l).boxIn (.step u s) = some T)
    (hr : u.rt = .free r) (hz : Δ.ref (.root z) = some (rootTy l r).gc) :
    Δ.ref ((VarSymb.root z).ext (gPath (rootTy l r) u.path s)) = some T := by
  obtain ⟨U, hU, hs⟩ : ∃ U, (ctxOf l).ref u = some U ∧
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
  have hwalk : (rootTy l r).walk u.path = some U := by
    have e := Ctx.ref_ext_ppath (ctxOf l) u.path (.root u.rt) hp
    rw [← VarSymb.eq_root_ext u, hU, hR] at e
    exact e.symm
  exact ref_gPath hF _ _ _ hp hwalk hz fun w' hw' => ref_gPath_nil hw' hs

/-! ## The item map of fresh realisations -/

/-- ⭐The item map of a family of fresh realisations, root `r` to the variable `img r`: the item
    `u.s` of `r` lands at `gPath` in `img r`. -/
def gImg (l : List VarType) (img : ℕ → ℕ) (v : VarSymb) : VarSymb :=
  match v with
  | .step u s =>
      match u.rt with
      | .free r => (VarSymb.root (.free (img r))).ext (gPath (rootTy l r) u.path s)
      | .bnd _ => v
  | .root _ => v

/-- The images of the roots are declared at the `gc` types. -/
def GImgOk (l : List VarType) (Δ : Ctx) (img : ℕ → ℕ) : Prop :=
  ∀ r, r < l.length → Δ.ref (.root (.free (img r))) = some (rootTy l r).gc

theorem gImg_item (l : List VarType) (img : ℕ → ℕ) {u : VarSymb} {r : ℕ} (hr : u.rt = .free r)
    (s : Step) :
    gImg l img (.step u s) = (VarSymb.root (.free (img r))).ext (gPath (rootTy l r) u.path s) := by
  dsimp only [gImg]
  rw [hr]

/-- ⭐Fresh realisations type the items of the `□` view. -/
theorem itemOk_gImg (hF : ModalSys.Four = true) {l : List VarType} {Δ : Ctx} {img : ℕ → ℕ}
    (himg : GImgOk l Δ img) : ItemOk (ctxOf l).boxIn Δ (gImg l img) := by
  intro v T _ hv
  obtain ⟨u, s, rfl, -, U, hU⟩ := boxIn_item hv
  obtain ⟨r, hr, hlt, -⟩ := ref_rt hU
  rw [gImg_item l img hr]
  exact ref_gItem hF hv hr (himg r hlt)

/-- The item map of a witness arrow: `x.dia` to the variable `cx` holding `x`'s content, the rest
    by fresh realisations. -/
def gImgX (l : List VarType) (img : ℕ → ℕ) (x : VarSymb) (cx : ℕ) (v : VarSymb) : VarSymb :=
  if v = .step x .dia then .root (.free cx) else gImg l img v

/-- ⭐A witness arrow's item map types the items of the `◇_x` view, given `cx` holds `x`'s
    content type. -/
theorem itemOk_gImgX (hF : ModalSys.Four = true) {l : List VarType} {Δ : Ctx} {img : ℕ → ℕ}
    {x : VarSymb} {cx : ℕ} {X : VarType} (himg : GImgOk l Δ img)
    (hx : (ctxOf l).ref x = some (.VTypeDia X)) (hcx : Δ.ref (.root (.free cx)) = some X) :
    ItemOk ((ctxOf l).diaIn x) Δ (gImgX l img x cx) := by
  intro v T hl hv
  by_cases hvx : v = .step x .dia
  · subst hvx
    change (if x = x then (match (ctxOf l).ref x with | some (.VTypeDia X) => some X | _ => none)
      else none) = some T at hv
    rw [if_pos rfl, hx] at hv
    cases hv
    unfold gImgX
    rw [if_pos rfl]
    exact hcx
  · unfold gImgX
    rw [if_neg hvx]
    have hb : (ctxOf l).boxIn v = some T := by
      match v, hvx with
      | .step u .dia, hvx =>
          change (if u = x then _ else none) = some T at hv
          rw [if_neg (fun e => hvx (by rw [e]))] at hv
          cases hv
      | .step u .box, _ => exact hv
      | .step u .keep, _ => exact hv
      | .root _, _ => exact hv
      | .step u .fst, _ => exact hv
      | .step u .snd, _ => exact hv
      | .step u .here, _ => exact hv
    exact itemOk_gImg hF himg v T hl hb

end GArrow

end V12M
