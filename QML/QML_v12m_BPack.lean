import QML.QML_v12m_BAbs

/-!
# QML v12m — B's arrow model: packing a world's roots into one slot

Strong B's network invariant (`docs/v12-modal-extensions.md` §11.17) speaks of all the roots
committed along an arrow at once, as one necessary object `d` whose content is the tuple of their
items.  So a formula of a world's `□` view must become a hole formula over that tuple:

* `bcT l`, `tupPath`: the type of the tuple of `l`'s roots' box contents (oldest innermost; by
  recursion on the list, so committing one more root pairs one more component), and the path from
  it to root `r`'s component.
* `packS`, `pack`: every item of root `r` goes to the matching component of a base address — the
  slot, for a hole formula.  `BAbs.absS` abstracts one root; this abstracts them all.
* ⭐`holeRead_tupT_pack`: instantiated at the tuple of the roots' items (`tupT`), the packed
  formula is the formula itself.
* ⭐`holeRead_tupImgT_pack`: instantiated at the tuple of the roots' images (`tupImgT`), it is the
  formula sent along the arrow.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## The tuple of the roots -/

/-- The type of the tuple of a list's roots' box contents, oldest innermost: committing one more
    root pairs one more component. -/
def bcT : List VarType → VarType
  | [] => .VTypeOne
  | A :: l => .VTypeProd (bcT l) A.bc

/-- The path from the tuple of `l`'s roots to root `r`'s component. -/
def tupPath : List VarType → ℕ → List Step
  | [], _ => []
  | _ :: l, r => if r = l.length then [.snd] else .fst :: tupPath l r

theorem ref_tupPath {Δ : Ctx} : ∀ (l : List VarType) {r : ℕ}, r < l.length → ∀ {b : VarSymb},
    Δ.ref b = some (bcT l) → Δ.ref (b.ext (tupPath l r)) = some (rootTy l r).bc
  | [], r, h, _, _ => absurd h (Nat.not_lt_zero r)
  | A :: l, r, h, b, hb => by
      unfold tupPath
      split_ifs with hr
      · subst hr
        rw [rootTy_new]
        change Δ.ref (.step b .snd) = _
        simp only [Ctx.ref, Step.isProj, if_true, hb, Option.bind_some]
        rfl
      · have hr' : r < l.length := by
          have : r < l.length + 1 := h
          omega
        rw [rootTy_old hr']
        change Δ.ref ((VarSymb.step b .fst).ext (tupPath l r)) = _
        exact ref_tupPath l hr' (by
          simp only [Ctx.ref, Step.isProj, if_true, hb, Option.bind_some]
          rfl)

/-- ⭐The items of `l`'s roots, as one term of the `□` view. -/
def tupT [ModalSys.NoFour] : (l : List VarType) →
    Σ a : Ann (bcT l), Term σ (ctxOf l).boxIn (bcT l) a
  | [] => ⟨_, .unit⟩
  | A :: l => ⟨_, .pair (Term.mono (ctxOf_le_append [A] l).boxIn (tupT l).2)
      (tup (.root (.free l.length)) A (ctxOf_ref_new A l))⟩

/-- Images of a list's roots are images of its older roots. -/
theorem ImgOk.tail {A : VarType} {l : List VarType} {Δ : Ctx} {img : ℕ → ℕ}
    (h : ImgOk (A :: l) Δ img) : ImgOk l Δ img := fun r hr => by
  rw [← rootTy_old hr]
  exact h r (Nat.lt_succ_of_lt hr)

/-- The image of a list's newest root is declared at its `bc` type. -/
theorem ImgOk.head {A : VarType} {l : List VarType} {Δ : Ctx} {img : ℕ → ℕ}
    (h : ImgOk (A :: l) Δ img) : Δ.ref (.root (.free (img l.length))) = some A.bc := by
  have := h l.length (Nat.lt_succ_self _)
  rwa [rootTy_new] at this

/-- ⭐The images of `l`'s roots along an index map, as one term of the target. -/
def tupImgT {Δ : Ctx} : (l : List VarType) → (img : ℕ → ℕ) → ImgOk l Δ img →
    Σ a : Ann (bcT l), Term σ Δ (bcT l) a
  | [], _, _ => ⟨_, .unit⟩
  | A :: l, img, himg => ⟨_, .pair (tupImgT l img (ImgOk.tail himg)).2
      (Term.eta (.root (.free (img l.length))) A.bc (ImgOk.head himg))⟩

/-- A substitution's entry at `b.box`'s weakened tuple read along `u`'s projections: the tuple of
    `u`, weakened (`mono_tupB`). -/
theorem mono_tupB [ModalSys.NoFour] {Γ Γ' : Ctx} (h : Γ.Le Γ') :
    ∀ (u : VarSymb) (R : VarType) (b : Bool) (hb : ModalSys.T = b) (hu : Γ.ref u = some R),
      Term.mono h.boxIn (tupB (σ := σ) u R b hb hu) = tupB u R b hb (h.ref hu)
  | _, .Var, _, _, _ => rfl
  | _, .VTypeOne, _, _, _ => rfl
  | u, .VTypeProd A B, b, hb, hu => by
      change Term.pair (Term.mono h.boxIn (tupB _ A b hb _))
        (Term.mono h.boxIn (tupB _ B b hb _)) = _
      rw [mono_tupB h _ A b hb, mono_tupB h _ B b hb]
      rfl
  | u, .VTypeBox A, true, hb, hu => by
      change Term.pair (Term.mono h.boxIn (Term.eta _ _ _))
        (Term.mono h.boxIn (tupB _ A true hb _)) = _
      rw [Term.mono_eta, mono_tupB h _ A true hb]
      rfl
  | u, .VTypeBox A, false, hb, hu => by
      change Term.mono h.boxIn (Term.eta _ _ _) = _
      rw [Term.mono_eta]
      rfl
  | _, .VTypeDia _, _, _, _ => rfl

/-! ## Packing -/

/-- Where root `r`'s items go: the `r`-th entry of the tuple at `b`. -/
def packBase (l : List VarType) (b : VarSymb) : Root → VarSymb
  | .free r => b.ext (tupPath l r)
  | .bnd _ => b

/-- ⭐Packing the roots: the item `u.box` goes to `u`'s projections encoded, read from its root's
    entry of the tuple at `b` (as `itemAt` reads them from a root). -/
def packS (σ : Signature) (Δ : Ctx) (l : List VarType) (b : VarSymb) : Subst σ Δ := fun v =>
  match v with
  | .step u .box => .ren ((packBase l b u.rt).ext (encPath u.path ++ itemTail))
  | _ => .hide

/-- Where packing sends annotation indices. -/
def packIdx (l : List VarType) (b : VarSymb) (a : VarSymb) : VarSymb :=
  (packBase l b a.rt).ext (itemPath a.path)

theorem ref_encB {l : List VarType} {Δ : Ctx} {b : VarSymb} {R : VarType} :
    ∀ {u : VarSymb} {T : VarType}, (ctxOf l).ref u = some T → (ctxOf l).ref (.root u.rt) = some R →
      Δ.ref b = some R.bc → Δ.ref (b.ext (encPath u.path)) = some T.bc
  | .root r, T, h, hR, hb => by
      change (ctxOf l).ref (.root r) = some R at hR
      rw [hR] at h
      cases h
      exact hb
  | .step u s, T, h, hR, hb => by
      have hproj : s.isProj = true := (reach_ppath h).1 s (by simp [VarSymb.path])
      simp only [Ctx.ref, if_pos hproj] at h
      cases hU : (ctxOf l).ref u with
      | none => rw [hU] at h; cases h
      | some U =>
          rw [hU] at h
          have ih := ref_encB hU hR hb
          change Δ.ref (b.ext (encPath (u.path ++ [s]))) = _
          rw [show encPath (u.path ++ [s]) = encPath u.path ++ [encStep s] from
            List.map_append, VarSymb.ext_step]
          simp only [Ctx.ref, if_pos (encStep_proj hproj), ih, Option.bind_some]
          exact bc_encStep hproj h

/-- An item lands at its type, read from any base holding its root's box contents. -/
theorem ref_itemB {l : List VarType} {Δ : Ctx} {b : VarSymb} {R : VarType} {u : VarSymb}
    {T : VarType} (hu : (ctxOf l).ref u = some (.VTypeBox T))
    (hR : (ctxOf l).ref (.root u.rt) = some R) (hb : Δ.ref b = some R.bc) :
    Δ.ref (b.ext (encPath u.path ++ itemTail)) = some T := by
  have h := ref_encB hu hR hb
  rw [VarSymb.ext_append]
  unfold itemTail
  by_cases hT : ModalSys.T = true
  · rw [if_pos hT]
    change Δ.ref (.step (b.ext (encPath u.path)) .fst) = _
    simp only [Ctx.ref, Step.isProj, if_true, h, Option.bind_some, VarType.bc, hT, VarType.bcB]
    rfl
  · rw [if_neg hT]
    simpa [VarType.bc, VarType.bcB, hT] using h

theorem ok_packS [ModalSys.NoFour] (l : List VarType) {Δ : Ctx} {b : VarSymb}
    (hb : Δ.ref b = some (bcT l)) :
    Subst.Ok (ctxOf l).boxIn (packS σ Δ l b) := by
  intro v T _ hv
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  obtain ⟨r, hr, hlt, hR⟩ := ref_rt hu
  change Δ.ref ((packBase l b u.rt).ext (encPath u.path ++ itemTail)) = some T
  have hz : Δ.ref (packBase l b u.rt) = some (rootTy l r).bc := by
    rw [hr]
    exact ref_tupPath l hlt hb
  exact ref_itemB hu hR hz

theorem coh_packS [ModalSys.NoFour] (l : List VarType) {Δ : Ctx} {b : VarSymb}
    (hb : Δ.ref b = some (bcT l)) :
    Subst.Coh (packIdx l b) (ctxOf l).boxIn (packS σ Δ l b) := by
  refine Subst.coh_of (ok_packS l hb) ?_
  intro v T _ hv p
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  change ((packBase l b u.rt).ext (encPath u.path ++ itemTail)).ext p =
    (packBase l b _).ext _
  rw [itemPath_item (reach_ppath hu).1 p, VarSymb.ext_rt,
    VarSymb.ext_append _ (encPath u.path ++ itemTail) p]
  rfl

/-- The slot holding the tuple, as a hole's context. -/
abbrev packCtx (l : List VarType) : Ctx := Ctx.empty.insert (.bnd 0) (bcT l)

theorem packCtx_ref (l : List VarType) :
    (packCtx l).ref (.root (.bnd 0)) = some (bcT l) :=
  Ctx.ref_insert_root _ _ _

/-- ⭐A formula of the `□` view of `ctxOf l`, packed into a hole formula over the tuple of all the
    roots' items. -/
def pack [ModalSys.NoFour] (l : List VarType) (ψ : WFF σ (ctxOf l).boxIn 0) :
    WFF σ (Ctx.empty.insert (.bnd 0) (bcT l)) 1 :=
  WFF.subst (packIdx l (.root (.bnd 0)))
    (packS σ (packCtx l) l (.root (.bnd 0)))
    (ok_packS l (packCtx_ref l)) (coh_packS l (packCtx_ref l)) Ctx.NoSlots.slots
    (Ctx.slotsFrom_empty.insert _) ψ

/-! ## Instantiating at the tuple of the items -/

/-- The weakened tuple's entry for root `r`, reached along its path: root `r`'s tuple, weakened. -/
theorem at_tupPath_tupT [ModalSys.NoFour] {Δ : Ctx} (θ : Subst σ Δ) :
    ∀ (l : List VarType) (hle : (ctxOf l).boxIn.Le Δ) {b : VarSymb},
      θ.at b = .tm (Term.mono hle (tupT l).2) → ∀ {r : ℕ}, r < l.length →
        ∃ (R : VarType) (hR : (ctxOf l).ref (.root (.free r)) = some R),
          θ.at (b.ext (tupPath l r)) = .tm (Term.mono hle (tup (σ := σ) (.root (.free r)) R hR))
  | [], _, _, _, r, hr => absurd hr (Nat.not_lt_zero r)
  | A :: l, hle, b, hb, r, hr => by
      unfold tupPath
      split_ifs with hrn
      · subst hrn
        refine ⟨A, ctxOf_ref_new A l, ?_⟩
        change θ.at (.step b .snd) = _
        rw [Subst.at_proj _ _ rfl, hb]
        rfl
      · have hr' : r < l.length := by
          have : r < l.length + 1 := hr
          omega
        have hb' : θ.at (.step b .fst) =
            .tm (Term.mono ((ctxOf_le_append [A] l).boxIn.trans hle) (tupT l).2) := by
          rw [Subst.at_proj _ _ rfl, hb]
          exact congrArg SubE.tm (Term.mono_mono (ctxOf_le_append [A] l).boxIn hle (tupT l).2)
        obtain ⟨R, hR, h⟩ := at_tupPath_tupT θ l _ hb' hr'
        refine ⟨R, (ctxOf_le_append [A] l).ref hR, ?_⟩
        change θ.at ((VarSymb.step b .fst).ext (tupPath l r)) = _
        rw [h, ← Term.mono_mono (ctxOf_le_append [A] l).boxIn hle,
          mono_tupB (ctxOf_le_append [A] l)]

/-- `at_single_tupB` from any base: a substitution whose entry at `b` is the tuple of root `r`
    reads, along `u`'s projections encoded, the tuple of `u`. -/
theorem at_enc_tupB [ModalSys.NoFour] {l : List VarType} (θ : Subst σ (ctxOf l).boxIn)
    {b : VarSymb} {r : ℕ} {R : VarType} (bb : Bool) (hbb : ModalSys.T = bb)
    (hR : (ctxOf l).ref (.root (.free r)) = some R)
    (hb : θ.at b = .tm (tupB (σ := σ) (.root (.free r)) R bb hbb hR)) :
    ∀ {u : VarSymb} {U : VarType} (hu : (ctxOf l).ref u = some U), u.rt = .free r →
      θ.at (b.ext (encPath u.path)) = .tm (tupB u U bb hbb hu)
  | .root r', U, hu, hrt => by
      change VarSymb.rt (.root r') = _ at hrt
      subst hrt
      obtain rfl : U = R := Option.some.inj (hu.symm.trans hR)
      exact hb
  | .step u s, U, hu, hrt => by
      have hproj : s.isProj = true := (reach_ppath hu).1 s (by simp [VarSymb.path])
      have hu' := hu
      simp only [Ctx.ref, if_pos hproj] at hu'
      cases hU : (ctxOf l).ref u with
      | none => rw [hU] at hu'; cases hu'
      | some U' =>
          rw [hU] at hu'
          have ih := at_enc_tupB θ bb hbb hR hb hU hrt
          change θ.at (b.ext (encPath (u.path ++ [s]))) = _
          rw [show encPath (u.path ++ [s]) = encPath u.path ++ [encStep s] from
            List.map_append, VarSymb.ext_step, Subst.at_proj _ _ (encStep_proj hproj), ih]
          cases s with
          | fst =>
              rw [encStep_fst]
              cases U' with
              | VTypeProd X Y => cases hu'; rfl
              | _ => cases hu'
          | snd =>
              rw [encStep_snd]
              cases U' with
              | VTypeProd X Y => cases hu'; rfl
              | _ => cases hu'
          | here =>
              cases U' with
              | VTypeBox X =>
                  obtain ⟨hT, rfl⟩ := VarType.step_here hu'
                  obtain rfl : bb = true := hbb.symm.trans hT
                  rw [encStep_here hT]
                  rfl
              | _ => cases hu'
          | _ => exact absurd hproj (by decide)

/-- `at_item_of_tupB` from any base. -/
theorem at_item_of_tupB_base [ModalSys.NoFour] {Γ : Ctx} (θ : Subst σ Γ.boxIn) (b : VarSymb)
    {u : VarSymb} {T : VarType} (hu : Γ.ref u = some (.VTypeBox T)) (bb : Bool)
    (hbb : ModalSys.T = bb)
    (h : θ.at (b.ext (encPath u.path)) = .tm (tupB u (.VTypeBox T) bb hbb hu)) :
    θ.at (b.ext (encPath u.path ++ itemTail)) =
      .tm (Term.eta (.step u .box) T (Ctx.ref_boxIn_of ModalSys.NoFour.keepOnly hu)) := by
  rw [VarSymb.ext_append]
  cases bb with
  | true =>
      rw [show itemTail = [Step.fst] by simp [itemTail, hbb]]
      change θ.at (.step (b.ext (encPath u.path)) .fst) = _
      rw [Subst.at_proj _ _ rfl, h]
      rfl
  | false =>
      rw [show itemTail = [] by simp [itemTail, hbb]]
      exact h

/-- ⭐A formula of the `□` view is its packing instantiated at the tuple of all the roots' items. -/
theorem holeRead_tupT_pack [ModalSys.NoFour] (l : List VarType) (ψ : WFF σ (ctxOf l).boxIn 0) :
    WFF.holeRead (tupT l).2 (pack l ψ) = ψ := by
  have hs : ((ctxOf l).boxIn.insert (.bnd 0) (bcT l)).SlotsFrom 1 :=
    (Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).insert _
  unfold WFF.holeRead WFF.instantiate WFF.substRoot pack
  rw [WFF.subst_mono ((Ctx.empty_le _).insert (.bnd 0) _) _ _ _ (Ctx.slotsFrom_empty.insert _) hs]
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ Subst.ok_idS Subst.coh_idS _ _ _ ?_ ψ).trans
    (WFF.subst_id _ _ _ ψ)
  refine Subst.sim_of ?_
  intro v T _ hv
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  obtain ⟨r, hr, hlt, _⟩ := ref_rt hu
  change SubE.Sim T (.ren (.step u .box))
    ((Subst.single (.bnd 0) (.tm (tupT l).2)).at
      ((packBase l (.root (.bnd 0)) u.rt).ext (encPath u.path ++ itemTail)))
  rw [hr]
  change SubE.Sim T _ ((Subst.single (.bnd 0) _).at
    (((VarSymb.root (.bnd 0)).ext (tupPath l r)).ext (encPath u.path ++ itemTail)))
  have h0 : (Subst.single (σ := σ) (Δ := (ctxOf l).boxIn) (.bnd 0)
      (.tm (tupT l).2)).at (.root (.bnd 0)) = .tm (Term.mono (Ctx.Le.refl _) (tupT l).2) := by
    rw [Term.mono_refl]
    change Subst.single (.bnd 0) _ (.root (.bnd 0)) = _
    exact if_pos rfl
  obtain ⟨R, hR, h1⟩ := at_tupPath_tupT _ l _ h0 hlt
  rw [Term.mono_refl] at h1
  have h2 := at_enc_tupB _ ModalSys.T rfl hR h1 hu hr
  rw [at_item_of_tupB_base _ _ hu ModalSys.T rfl h2]
  exact .ren_eta _ _

/-! ## Instantiating at the tuple of the images -/

/-- The images' tuple's entry for root `r`, reached along its path: an η-expansion of `r`'s
    image. -/
theorem at_tupPath_tupImgT {Δ : Ctx} (θ : Subst σ Δ) :
    ∀ (l : List VarType) {img : ℕ → ℕ} (himg : ImgOk l Δ img) {b : VarSymb},
      θ.at b = .tm (tupImgT l img himg).2 → ∀ {r : ℕ}, r < l.length →
        ∃ (T : VarType) (h : Δ.ref (.root (.free (img r))) = some T),
          θ.at (b.ext (tupPath l r)) = .tm (Term.eta (.root (.free (img r))) T h)
  | [], _, _, _, _, r, hr => absurd hr (Nat.not_lt_zero r)
  | A :: l, img, himg, b, hb, r, hr => by
      unfold tupPath
      split_ifs with hrn
      · subst hrn
        refine ⟨A.bc, ImgOk.head himg, ?_⟩
        change θ.at (.step b .snd) = _
        rw [Subst.at_proj _ _ rfl, hb]
        rfl
      · have hr' : r < l.length := by
          have : r < l.length + 1 := hr
          omega
        exact at_tupPath_tupImgT θ l (ImgOk.tail himg) (by rw [Subst.at_proj _ _ rfl, hb]; rfl) hr'

/-- An undeclared address stays undeclared along projections. -/
theorem ref_ext_none {Δ : Ctx} : ∀ (q : List Step), PPath q → ∀ {v : VarSymb},
    Δ.ref v = none → Δ.ref (v.ext q) = none
  | [], _, _, h => h
  | s :: q, hq, v, h => by
      have hs : s.isProj = true := hq s List.mem_cons_self
      refine ref_ext_none q (fun s' h' => hq s' (List.mem_cons_of_mem _ h')) ?_
      simp only [Ctx.ref, if_pos hs, h, Option.bind_none]

/-- A substitution `Sim` to a renaming at `b` stays so along a projection path. -/
theorem sim_ren_at_ext {Δ : Ctx} (θ : Subst σ Δ) : ∀ (q : List Step), PPath q →
    ∀ {b y : VarSymb} {U U' : VarType}, Δ.ref y = some U → Δ.ref (y.ext q) = some U' →
      SubE.Sim U (.ren y) (θ.at b) → SubE.Sim U' (.ren (y.ext q)) (θ.at (b.ext q))
  | [], _, _, _, _, _, hy, hy', h => by
      obtain rfl : _ = _ := Option.some.inj (hy.symm.trans hy')
      exact h
  | s :: q, hq, b, y, U, U', hy, hy', h => by
      have hs : s.isProj = true := hq s List.mem_cons_self
      have hq' : PPath q := fun s' h' => hq s' (List.mem_cons_of_mem _ h')
      have hys : Δ.ref (VarSymb.step y s) = U.step s := by
        simp only [Ctx.ref, if_pos hs, hy, Option.bind_some]
      cases hUs : U.step s with
      | none =>
          rw [hUs] at hys
          have := ref_ext_none q hq' hys
          change Δ.ref ((VarSymb.step y s).ext q) = _ at hy'
          rw [this] at hy'
          cases hy'
      | some Us =>
          rw [hUs] at hys
          have h' : SubE.Sim Us (.ren (VarSymb.step y s)) (θ.at (VarSymb.step b s)) := by
            rw [Subst.at_proj _ _ hs]
            exact SubE.Sim.proj_step h hs hUs
          exact sim_ren_at_ext θ q hq' hys hy' h'

/-- ⭐A formula of the `□` view, packed and instantiated at the tuple of the roots' images, is the
    formula sent along the arrow. -/
theorem holeRead_tupImgT_pack [ModalSys.NoFour] {l : List VarType} {Δ : Ctx} [Δ.NoSlots]
    {img : ℕ → ℕ} (himg : ImgOk l Δ img) (ψ : WFF σ (ctxOf l).boxIn 0) :
    WFF.holeRead (tupImgT l img himg).2 (pack l ψ) =
      WFF.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS himg) (coh_arrowS himg)
        Ctx.NoSlots.slots Ctx.NoSlots.slots ψ := by
  have hs : (Δ.insert (.bnd 0) (bcT l)).SlotsFrom 1 :=
    (Ctx.NoSlots.slots (Γ := Δ)).insert _
  unfold WFF.holeRead WFF.instantiate WFF.substRoot pack
  rw [WFF.subst_mono ((Ctx.empty_le _).insert (.bnd 0) _) _ _ _ (Ctx.slotsFrom_empty.insert _) hs]
  refine WFF.subst_comp _ _ (arrowS σ Δ img) _ _ _ _ (ok_arrowS himg) (coh_arrowS himg) _ _ _
    ?_ ψ
  refine Subst.sim_of ?_
  intro v T _ hv
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  obtain ⟨r, hr, hlt, hR⟩ := ref_rt hu
  change SubE.Sim T (.ren (itemAt (imgRoot img u.rt) u))
    ((Subst.single (.bnd 0) (.tm (tupImgT l img himg).2)).at
      ((packBase l (.root (.bnd 0)) u.rt).ext (encPath u.path ++ itemTail)))
  have hz : Δ.ref (.root (imgRoot img u.rt)) = some (rootTy l r).bc := by
    rw [hr]; exact himg r hlt
  have hT := ref_item hu hR hz
  rw [hr] at hz hT ⊢
  change SubE.Sim T (.ren ((VarSymb.root (.free (img r))).ext (encPath u.path ++ itemTail)))
    ((Subst.single (.bnd 0) _).at
      (((VarSymb.root (.bnd 0)).ext (tupPath l r)).ext (encPath u.path ++ itemTail)))
  have h0 : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0)
      (.tm (tupImgT l img himg).2)).at (.root (.bnd 0)) = .tm (tupImgT l img himg).2 := by
    change Subst.single (.bnd 0) _ (.root (.bnd 0)) = _
    exact if_pos rfl
  obtain ⟨T', hT', h1⟩ := at_tupPath_tupImgT _ l himg h0 hlt
  refine sim_ren_at_ext _ _ ((PPath.encPath (reach_ppath hu).1).append PPath.itemTail) hT' hT ?_
  rw [h1]
  exact .ren_eta _ _

end BArrow

end V12M
