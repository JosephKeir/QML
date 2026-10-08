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

/-! ## Weakened tuples -/

/-- `at_enc_tupB` for a tuple weakened into a larger context. -/
theorem at_enc_tupB_mono [ModalSys.NoFour] {l : List VarType} {Δ : Ctx}
    (hle : (ctxOf l).boxIn.Le Δ) (θ : Subst σ Δ) {b : VarSymb} {r : ℕ} {R : VarType} (bb : Bool)
    (hbb : ModalSys.T = bb) (hR : (ctxOf l).ref (.root (.free r)) = some R)
    (hb : θ.at b = .tm (Term.mono hle (tupB (σ := σ) (.root (.free r)) R bb hbb hR))) :
    ∀ {u : VarSymb} {U : VarType} (hu : (ctxOf l).ref u = some U), u.rt = .free r →
      θ.at (b.ext (encPath u.path)) = .tm (Term.mono hle (tupB u U bb hbb hu))
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
          have ih := at_enc_tupB_mono hle θ bb hbb hR hb hU hrt
          change θ.at (b.ext (encPath (u.path ++ [s]))) = _
          rw [show encPath (u.path ++ [s]) = encPath u.path ++ [encStep s] from
            List.map_append, VarSymb.ext_step, Subst.at_proj _ _ (encStep_proj hproj), ih]
          exact proj_tupB_mono hle hbb hU hproj hu' hu

/-- `at_item_of_tupB_base` for a tuple weakened into a larger context. -/
theorem at_item_of_tupB_base_mono [ModalSys.NoFour] {Γ Δ : Ctx} (hle : Γ.boxIn.Le Δ)
    (θ : Subst σ Δ) (b : VarSymb) {u : VarSymb} {T : VarType} (hu : Γ.ref u = some (.VTypeBox T))
    (bb : Bool) (hbb : ModalSys.T = bb)
    (h : θ.at (b.ext (encPath u.path)) = .tm (Term.mono hle (tupB u (.VTypeBox T) bb hbb hu))) :
    θ.at (b.ext (encPath u.path ++ itemTail)) = .tm (Term.mono hle
      (Term.eta (.step u .box) T (Ctx.ref_boxIn_of ModalSys.NoFour.keepOnly hu))) := by
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

/-! ## Packing a body: the roots and one slot -/

section Pack2

variable [ModalSys.NoFour] (l : List VarType) (U : VarType)

/-- The hole's context for a packed body: the roots' tuple, paired with the body's slot. -/
abbrev pack2Ctx : Ctx := Ctx.empty.insert (.bnd 0) (.VTypeProd (bcT l) U)

omit [ModalSys.NoFour] in
theorem pack2Ctx_fst : (pack2Ctx l U).ref (.step (.root (.bnd 0)) .fst) = some (bcT l) := by
  simp only [Ctx.ref, Step.isProj, if_true]
  rfl

omit [ModalSys.NoFour] in
theorem pack2Ctx_snd : (pack2Ctx l U).ref (.step (.root (.bnd 0)) .snd) = some U := by
  simp only [Ctx.ref, Step.isProj, if_true]
  rfl

/-- ⭐Packing a body over `l`'s `□` view and a slot `e : U`: the roots' items go to the first
    component of the hole, as `packS` sends them, and `e` to the second. -/
def pack2S : Subst σ (pack2Ctx l U) :=
  (packS σ _ l (.step (.root (.bnd 0)) .fst)).set (.bnd 0) (.ren (.step (.root (.bnd 0)) .snd))

/-- Where `pack2S` sends annotation indices. -/
def pack2Idx : VarSymb → VarSymb :=
  Subst.setIdx (packIdx l (.step (.root (.bnd 0)) .fst)) (.bnd 0)
    (.ren (.step (.root (.bnd 0)) .snd) : SubE σ (pack2Ctx l U))

theorem ok_pack2S : Subst.Ok ((ctxOf l).boxIn.insert (.bnd 0) U) (pack2S (σ := σ) l U) :=
  Subst.ok_set (ok_packS l (pack2Ctx_fst l U)) (pack2Ctx_snd l U)

theorem coh_pack2S : Subst.Coh (pack2Idx (σ := σ) l U) ((ctxOf l).boxIn.insert (.bnd 0) U)
    (pack2S (σ := σ) l U) :=
  Subst.coh_set (ok_packS l (pack2Ctx_fst l U)) (coh_packS l (pack2Ctx_fst l U))
    ((Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).rootFresh (le_refl 0)) (pack2Ctx_snd l U)

/-- ⭐A body packed into a hole formula over the pair of the roots' tuple and its slot. -/
def pack2 (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) U) 1) : WFF σ (pack2Ctx l U) 1 :=
  WFF.subst (pack2Idx (σ := σ) l U) (pack2S l U) (ok_pack2S l U) (coh_pack2S l U)
    ((Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).insert U) (Ctx.slotsFrom_empty.insert _) Φ

end Pack2

/-- ⭐A packed body read at the roots' items (weakened) and its slot's η-expansion: the body,
    weakened. -/
theorem holeAt_tupT_pack2 [ModalSys.NoFour] {l : List VarType} {U : VarType} {Δ : Ctx}
    [Δ.NoSlots] (h : (ctxOf l).boxIn.Le Δ) (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) U) 1) :
    WFF.holeAt ((Ctx.NoSlots.slots (Γ := Δ)).insert U)
      (Term.pair (Term.mono (h.trans (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Δ)).root U))
          (tupT l).2)
        (Term.eta (.root (.bnd 0)) U (Ctx.ref_insert_root Δ (.bnd 0) U)))
      (pack2 l U Φ) = WFF.mono (h.insert (.bnd 0) U) Φ := by
  have hle := h.trans (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Δ)).root U)
  unfold WFF.holeAt pack2
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ (Subst.ok_idS_le (h.insert (.bnd 0) U))
    (Subst.coh_idS_le (h.insert (.bnd 0) U)) _ _ _ ?_ Φ).trans
    (WFF.subst_ren (h.insert (.bnd 0) U) _ _ _ _ _ (fun v _ _ => Subst.at_idS v) Φ)
  refine Subst.sim_of fun v T hlp hv => ?_
  have h0 : (Subst.single (σ := σ) (Δ := Δ.insert (.bnd 0) U) (.bnd 0)
      (.tm (Term.pair (Term.mono hle (tupT l).2)
        (Term.eta (.root (.bnd 0)) U (Ctx.ref_insert_root Δ (.bnd 0) U))))).at
        (.root (.bnd 0)) = .tm (Term.pair (Term.mono hle (tupT l).2)
          (Term.eta (.root (.bnd 0)) U (Ctx.ref_insert_root Δ (.bnd 0) U))) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = U := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp, pack2S]
    rw [Subst.set_root]
    dsimp only [SubE.comp]
    rw [Subst.at_proj _ _ rfl, h0]
    exact .ren_eta _ _
  · have hv' : (ctxOf l).boxIn v = some T := by
      change (if v = VarSymb.root (.bnd 0) then _ else _) = _ at hv
      rwa [if_neg hvr] at hv
    obtain ⟨u, rfl, hu⟩ := boxIn_item hv'
    obtain ⟨r, hr, hlt, _⟩ := ref_rt hu
    dsimp only [Subst.comp, pack2S]
    rw [Subst.set_ne _ _ hvr]
    dsimp only [packS, SubE.comp]
    rw [hr]
    change SubE.Sim T _ (Subst.at _
      (((VarSymb.step (.root (.bnd 0)) .fst).ext (tupPath l r)).ext (encPath u.path ++ itemTail)))
    have hb : (Subst.single (σ := σ) (Δ := Δ.insert (.bnd 0) U) (.bnd 0)
        (.tm (Term.pair (Term.mono hle (tupT l).2)
          (Term.eta (.root (.bnd 0)) U (Ctx.ref_insert_root Δ (.bnd 0) U))))).at
          (.step (.root (.bnd 0)) .fst) = .tm (Term.mono hle (tupT l).2) := by
      rw [Subst.at_proj _ _ rfl, h0]
      rfl
    obtain ⟨R, hR, h1⟩ := at_tupPath_tupT _ l hle hb hlt
    have h2 := at_enc_tupB_mono hle _ ModalSys.T rfl hR h1 hu hr
    rw [at_item_of_tupB_base_mono hle _ _ hu ModalSys.T rfl h2, Term.mono_eta]
    exact .ren_eta _ _

/-- ⭐A packed body read at the roots' images and a term `X`: the body sent along the arrow, its
    slot set to `X`. -/
theorem holeRead_tupImgT_pack2 [ModalSys.NoFour] {l : List VarType} {U : VarType} {Δ : Ctx}
    [Δ.NoSlots] {img : ℕ → ℕ} (himg : ImgOk l Δ img) {x : Ann U} (X : Term σ Δ U x)
    (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) U) 1) :
    WFF.holeRead (Term.pair (tupImgT l img himg).2 X) (pack2 l U Φ) =
      WFF.subst (Subst.setIdx (arrowIdx img) (.bnd 0) (.tm X))
        ((arrowS σ Δ img).set (.bnd 0) (.tm X)) (Subst.ok_set (ok_arrowS himg) rfl)
        (Subst.coh_set (ok_arrowS himg) (coh_arrowS himg)
          ((Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).rootFresh (le_refl 0)) rfl)
        ((Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).insert U) Ctx.NoSlots.slots Φ := by
  have hs : (Δ.insert (.bnd 0) (.VTypeProd (bcT l) U)).SlotsFrom 1 :=
    (Ctx.NoSlots.slots (Γ := Δ)).insert _
  unfold WFF.holeRead WFF.instantiate WFF.substRoot pack2
  rw [WFF.subst_mono ((Ctx.empty_le _).insert (.bnd 0) _) _ _ _ (Ctx.slotsFrom_empty.insert _) hs]
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v T hlp hv => ?_
  have h0 : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0)
      (.tm (Term.pair (tupImgT l img himg).2 X))).at (.root (.bnd 0)) =
        .tm (Term.pair (tupImgT l img himg).2 X) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    dsimp only [Subst.comp, pack2S]
    rw [Subst.set_root, Subst.set_root]
    dsimp only [SubE.comp]
    rw [Subst.at_proj _ _ rfl, h0]
    exact .refl _
  · have hv' : (ctxOf l).boxIn v = some T := by
      change (if v = VarSymb.root (.bnd 0) then _ else _) = _ at hv
      rwa [if_neg hvr] at hv
    obtain ⟨u, rfl, hu⟩ := boxIn_item hv'
    obtain ⟨r, hr, hlt, hR⟩ := ref_rt hu
    dsimp only [Subst.comp, pack2S]
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    dsimp only [packS, SubE.comp]
    have hz : Δ.ref (.root (imgRoot img u.rt)) = some (rootTy l r).bc := by
      rw [hr]; exact himg r hlt
    have hT := ref_item hu hR hz
    change SubE.Sim T (.ren (itemAt (imgRoot img u.rt) u)) _
    rw [hr] at hz hT ⊢
    change SubE.Sim T (.ren ((VarSymb.root (.free (img r))).ext (encPath u.path ++ itemTail)))
      (Subst.at _
        (((VarSymb.step (.root (.bnd 0)) .fst).ext (tupPath l r)).ext (encPath u.path ++ itemTail)))
    have hb : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0)
        (.tm (Term.pair (tupImgT l img himg).2 X))).at (.step (.root (.bnd 0)) .fst) =
          .tm (tupImgT l img himg).2 := by
      rw [Subst.at_proj _ _ rfl, h0]
      rfl
    obtain ⟨T', hT', h1⟩ := at_tupPath_tupImgT _ l himg hb hlt
    refine sim_ren_at_ext _ _ ((PPath.encPath (reach_ppath hu).1).append PPath.itemTail) hT' hT ?_
    rw [h1]
    exact .ren_eta _ _

/-! ## The arrow sends the items' tuple to the images' tuple -/

/-- An η-expansion depends only on its address. -/
theorem eta_addr_congr {Δ : Ctx} {T : VarType} {x y : VarSymb} (h : x = y)
    (hx : Δ.ref x = some T) (hy : Δ.ref y = some T) :
    (⟨_, Term.eta (σ := σ) x T hx⟩ : Σ a, Term σ Δ T a) = ⟨_, Term.eta y T hy⟩ := by
  subst h
  rfl

theorem ext_enc_step (b u : VarSymb) (s : Step) :
    b.ext (encPath (VarSymb.step u s).path) = .step (b.ext (encPath u.path)) (encStep s) := by
  change b.ext (encPath (u.path ++ [s])) = _
  rw [show encPath (u.path ++ [s]) = encPath u.path ++ [encStep s] from List.map_append,
    VarSymb.ext_step]

/-- The arrow sends a root's tuple, read along `u`'s projections, to the η-expansion of the matching
    component of the root's image. -/
theorem subst_arrow_tupB [ModalSys.NoFour] {l : List VarType} {Δ : Ctx} {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) {n : ℕ} :
    ∀ (bb : Bool) (hbb : ModalSys.T = bb) (u : VarSymb) (U : VarType)
      (hu : (ctxOf l).ref u = some U), u.rt = .free n →
      ∀ (h : Δ.ref ((VarSymb.root (.free (img n))).ext (encPath u.path)) = some (U.bcB bb)),
        (⟨_, Term.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS himg) (coh_arrowS himg)
          (tupB u U bb hbb hu)⟩ : Σ a, Term σ Δ (U.bcB bb) a) =
          ⟨_, Term.eta ((VarSymb.root (.free (img n))).ext (encPath u.path)) _ h⟩
  | _, _, _, .Var, _, _, _ => rfl
  | _, _, _, .VTypeOne, _, _, _ => rfl
  | _, _, _, .VTypeDia _, _, _, _ => rfl
  | bb, hbb, u, .VTypeProd A B, hu, hrt, h => by
      have h₁ : Δ.ref ((VarSymb.root (.free (img n))).ext (encPath (VarSymb.step u .fst).path)) =
          some (A.bcB bb) := by
        rw [ext_enc_step, encStep_fst]
        simp only [Ctx.ref, Step.isProj, if_true, h, Option.bind_some]
        rfl
      have h₂ : Δ.ref ((VarSymb.root (.free (img n))).ext (encPath (VarSymb.step u .snd).path)) =
          some (B.bcB bb) := by
        rw [ext_enc_step, encStep_snd]
        simp only [Ctx.ref, Step.isProj, if_true, h, Option.bind_some]
        rfl
      exact sig_pair
        ((subst_arrow_tupB himg bb hbb _ A (Ctx.ref_fst_of hu) hrt h₁).trans
          (eta_addr_congr (by rw [ext_enc_step, encStep_fst]) _ _))
        ((subst_arrow_tupB himg bb hbb _ B (Ctx.ref_snd_of hu) hrt h₂).trans
          (eta_addr_congr (by rw [ext_enc_step, encStep_snd]) _ _))
  | true, hbb, u, .VTypeBox A, hu, hrt, h => by
      obtain ⟨r, hr, hlt, hR⟩ := ref_rt hu
      have hz : Δ.ref (.root (imgRoot img u.rt)) = some (rootTy l r).bc := by
        rw [hr]; exact himg r hlt
      have hw := ref_item hu hR hz
      have hat : (arrowS σ Δ img).at (.step u .box) = .ren (itemImg img u) := by
        rw [Subst.at_nonproj _ rfl]
        rfl
      have h₂ : Δ.ref ((VarSymb.root (.free (img n))).ext (encPath (VarSymb.step u .here).path)) =
          some (A.bcB true) := by
        rw [ext_enc_step, encStep_here hbb]
        simp only [Ctx.ref, Step.isProj, if_true, h, Option.bind_some]
        rfl
      refine sig_pair ((Term.subst_eta_renAt _ _ _ A _ _ _ hw hat).trans
        (eta_addr_congr ?_ _ _))
        ((subst_arrow_tupB himg true hbb _ A (Ctx.ref_here_of hbb hu) hrt h₂).trans
          (eta_addr_congr (by rw [ext_enc_step, encStep_here hbb]) _ _))
      rw [itemAt, hrt, VarSymb.ext_append, show itemTail = [Step.fst] by simp [itemTail, hbb]]
      rfl
  | false, hbb, u, .VTypeBox A, hu, hrt, h => by
      obtain ⟨r, hr, hlt, hR⟩ := ref_rt hu
      have hz : Δ.ref (.root (imgRoot img u.rt)) = some (rootTy l r).bc := by
        rw [hr]; exact himg r hlt
      have hw := ref_item hu hR hz
      have hat : (arrowS σ Δ img).at (.step u .box) = .ren (itemImg img u) := by
        rw [Subst.at_nonproj _ rfl]
        rfl
      refine (Term.subst_eta_renAt _ _ _ A _ _ _ hw hat).trans (eta_addr_congr ?_ _ _)
      rw [itemAt, hrt, show itemTail = [] by simp [itemTail, hbb], List.append_nil]
      rfl

/-- ⭐The arrow sends the tuple of a list's roots' items to the tuple of their images. -/
theorem subst_arrow_tupT [ModalSys.NoFour] {Δ : Ctx} {img : ℕ → ℕ} :
    ∀ (l : List VarType) (himg : ImgOk l Δ img),
      (⟨_, Term.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS himg) (coh_arrowS himg)
        (tupT l).2⟩ : Σ a, Term σ Δ (bcT l) a) = tupImgT l img himg
  | [], _ => rfl
  | A :: l, himg => by
      refine sig_pair ?_
        (subst_arrow_tupB himg ModalSys.T rfl _ A (ctxOf_ref_new A l) rfl (ImgOk.head himg))
      change (⟨_, Term.subst _ _ _ _ (Term.mono _ (tupT l).2)⟩ : Σ a, Term σ Δ (bcT l) a) = _
      rw [Term.subst_mono]
      exact subst_arrow_tupT l (ImgOk.tail himg)

end BArrow

end V12M
