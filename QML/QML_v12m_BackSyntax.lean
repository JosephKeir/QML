import QML.QML_v12m_SubstEta

/-!
# QML v12m — strong B: the syntax its rules are stated in

Roadmap milestone 2, step 4 (`docs/v12-modal-extensions.md` §11.2, §11.14).

* **Hole formulas and terms**, closed apart from one hole (§11.2): `WFF.holeRead`, `Term.holeRead`
  read them in a context with a term in the hole.  A round trip carries no addresses, so the two
  ends of a `Back` meet only through the hole.
* ⭐`OutLeg`: the out leg of a round trip — every arrow (`nec`, row 1) or a witness's extent
  (`pos y`, row 2) — with its view, its `◇` and `□`, and the `Back` atom of a carrier given by its
  body (`OutLeg.back`).  The rules are stated once over it; substitution sends a leg to a leg
  (`OutLeg.subst`) and acts on its pieces definitionally (`OutLeg.subst_dia`, `subst_box`,
  `subst_back`).
-/

namespace V12M

variable [ModalSys]

namespace Subst

variable {σ : Signature} {Δ : Ctx}

/-! ## Changing one root's entry -/

/-- `r ↦ e`, every other address as in `θ`. -/
def set (θ : Subst σ Δ) (r : Root) (e : SubE σ Δ) : Subst σ Δ :=
  fun v => if v = .root r then e else θ v

def setIdx (ι : VarSymb → VarSymb) (r : Root) (e : SubE σ Δ) : VarSymb → VarSymb :=
  fun i => if i.rt = r then e.idxAlong i.path else ι i

theorem set_root (θ : Subst σ Δ) (r : Root) (e : SubE σ Δ) : θ.set r e (.root r) = e :=
  if_pos rfl

theorem set_ne (θ : Subst σ Δ) {r : Root} (e : SubE σ Δ) {v : VarSymb} (h : v ≠ .root r) :
    θ.set r e v = θ v :=
  if_neg h

theorem ok_set {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) {r : Root} {T : VarType}
    {e : SubE σ Δ} (he : e.OkRef T) : Ok (Γ.insert r T) (θ.set r e) := by
  intro v U hlp hv
  by_cases hvr : v = .root r
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    rw [set_root]
    exact he
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    rw [set_ne _ _ hvr]
    exact hθ v U hlp hv'

theorem coh_set {ι : VarSymb → VarSymb} {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ)
    (hc : Coh ι Γ θ) {r : Root} {T : VarType} {e : SubE σ Δ} (hr : Γ.RootFresh r)
    (he : e.OkRef T) : Coh (setIdx ι r e) (Γ.insert r T) (θ.set r e) := by
  refine coh_of (ok_set hθ he) ?_
  intro v U hlp hv p
  by_cases hvr : v = .root r
  · subst hvr
    rw [set_root]
    change e.idxAlong p = if ((VarSymb.root r).ext p).rt = r then
      e.idxAlong ((VarSymb.root r).ext p).path else _
    simp only [VarSymb.ext_rt, VarSymb.ext_path, VarSymb.rt, VarSymb.path, List.nil_append,
      if_true]
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    have hrt : v.rt ≠ r := fun he' => by
      rw [hr v he'] at hv'
      cases hv'
    rw [set_ne _ _ hvr, ← at_nonproj θ hlp, hc v U ((Ctx.ref_nonproj Γ hlp).trans hv') p]
    change ι (v.ext p) = if (v.ext p).rt = r then _ else ι (v.ext p)
    rw [VarSymb.ext_rt, if_neg hrt]

end Subst

/-- A **hole formula** — closed apart from its hole — read in `Γ` with `t` in the hole. -/
def WFF.holeRead {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) : WFF σ Γ 0 :=
  WFF.instantiate Ctx.NoSlots.slots t (WFF.mono ((Ctx.empty_le Γ).insert (.bnd 0) A) ψ)

/-- A **hole term** — closed apart from its hole — read in `Γ` with `t` in the hole: what `Back`'s
    β-rule maps a carrier and its value by. -/
def Term.holeRead {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) {B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    Term σ Γ B (b.mapIdx (Subst.singleIdx (.bnd 0) (.tm t))) :=
  Term.subst (Subst.singleIdx (.bnd 0) (.tm t)) (Subst.single (.bnd 0) (.tm t))
    (Subst.ok_single (Ctx.Le.refl Γ) rfl)
    (Subst.coh_single ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) (Ctx.Le.refl Γ) rfl)
    (Term.mono ((Ctx.empty_le Γ).insert (.bnd 0) A) s)

/-! ## The returning possibility's syntax (§11.14)

`WFF.ret hS t Φ` binds one necessary object `d : □A` of the far world, at the slot of its body
`Φ`.  Several items are packed into one by pairing; the operations below move between the packed
and unpacked forms, by substitutions of the body's slots. -/

omit [ModalSys] in
theorem Ctx.slotsFrom_empty : Ctx.empty.SlotsFrom 0 := fun _ _ _ _ => rfl

/-- A hole formula read at **any** binder depth, with `t` in the hole: a substitution from the
    hole's own context, so no weakening and no slot bookkeeping.  Inside a returning
    possibility's body, which has a slot, this replaces `WFF.holeRead`. -/
def WFF.holeAt {σ : Signature} {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) : WFF σ Γ d :=
  WFF.subst (Subst.singleIdx (.bnd 0) (.tm t)) (Subst.single (.bnd 0) (.tm t))
    (Subst.ok_single (Ctx.empty_le Γ) rfl)
    (Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le Γ) rfl)
    (Ctx.slotsFrom_empty.insert A) hs ψ

/-- A hole term read with `t` in the hole, at any depth. -/
def Term.holeAt {σ : Signature} {Γ : Ctx} {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    {B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    Term σ Γ B (b.mapIdx (Subst.singleIdx (.bnd 0) (.tm t))) :=
  Term.subst (Subst.singleIdx (.bnd 0) (.tm t)) (Subst.single (.bnd 0) (.tm t))
    (Subst.ok_single (Ctx.empty_le Γ) rfl)
    (Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le Γ) rfl) s

/-! ## Companions -/

/-- Under T, a companion path into a value of type `A` at address `w` reaches the necessary object
    `w.ext p : □C`. -/
theorem Ctx.ref_compAt {Γ : Ctx} (hT : ModalSys.T = true) (p : List Step) :
    ∀ {w : VarSymb} {A C : VarType}, Γ.ref w = some A → A.compAt p = some C →
      Γ.ref (w.ext p) = some (.VTypeBox C) := by
  induction p with
  | nil =>
      intro w A C hw hp
      cases A <;> simp only [VarType.compAt, reduceCtorEq, Option.some.injEq] at hp
      subst hp
      exact hw
  | cons s p ih =>
      intro w A C hw hp
      cases A <;> cases s <;> simp only [VarType.compAt, reduceCtorEq] at hp
      · exact ih (Ctx.ref_fst_of hw) hp
      · exact ih (Ctx.ref_snd_of hw) hp
      · exact ih (Ctx.ref_here_of hT hw) hp

/-- A valid companion list stays valid without its head. -/
theorem VarType.CompOk.tail {A : VarType} {p : List Step} {ps : List (List Step)}
    (h : A.CompOk (p :: ps)) : A.CompOk ps :=
  Or.inr ⟨(h.resolve_left (List.cons_ne_nil _ _)).1,
    fun q hq => (h.resolve_left (List.cons_ne_nil _ _)).2.1 q (List.mem_cons_of_mem _ hq),
    (List.nodup_cons.mp (h.resolve_left (List.cons_ne_nil _ _)).2.2).2⟩

/-- The head companion of a valid list is a necessary object of the bound one. -/
theorem VarType.CompOk.ref_head {Γ : Ctx} {u : VarSymb} {A : VarType} {p : List Step}
    {ps : List (List Step)} (h : A.CompOk (p :: ps)) (hu : Γ.ref u = some (.VTypeBox A)) :
    Γ.ref ((VarSymb.step u .here).ext p) = some (.VTypeBox ((A.compAt p).getD .VTypeOne)) := by
  obtain ⟨hT, hall, -⟩ := h.resolve_left (List.cons_ne_nil _ _)
  obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp (hall p List.mem_cons_self)
  rw [hC]
  exact Ctx.ref_compAt hT p (Ctx.ref_here_of hT hu) hC

/-- The contents of a `□A` object and of its companions, as one term of its `□` view (the
    companions' contents last). -/
def compsBody {σ : Signature} (A : VarType) : (cs : List (List Step)) → A.CompOk cs →
    Σ b, Term σ (Ctx.empty.insert (.bnd 0) (.VTypeBox A)).boxIn (A.compsFlat cs) b
  | [], _ => ⟨_, Term.eta (VarSymb.root (.bnd 0)).inner A
      (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))⟩
  | p :: ps, h => ⟨_, Term.pair (compsBody A ps h.tail).2
      (Term.eta ((VarSymb.step (.root (.bnd 0)) .here).ext p).inner ((A.compAt p).getD .VTypeOne)
        (Ctx.ref_inner (h.ref_head (Ctx.ref_insert_root _ _ _))))⟩

/-- The path from a `□A` object's value with companions to its own value: the first component,
    once per companion. -/
def compsFst : List (List Step) → List Step
  | [] => []
  | _ :: ps => .fst :: compsFst ps

theorem Ctx.ref_compsFst {Γ : Ctx} {A : VarType} : ∀ (cs : List (List Step)) {u : VarSymb},
    Γ.ref u = some (A.compsFlat cs) → Γ.ref (u.ext (compsFst cs)) = some A
  | [], _, h => h
  | _ :: ps, _, h => Ctx.ref_compsFst ps (Ctx.ref_fst_of h)

/-- Under T, a companion in the full list is a necessary object of the bound one. -/
theorem Ctx.ref_compMem {Γ : Ctx} (hT : ModalSys.T = true) {u : VarSymb} {A : VarType}
    {q : List Step} (hq : q ∈ A.hereChains) (hu : Γ.ref u = some (.VTypeBox A)) :
    Γ.ref ((VarSymb.step u .here).ext q) = some (.VTypeBox ((A.compAt q).getD .VTypeOne)) := by
  obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp (VarType.compAt_hereChains A q hq)
  rw [hC]
  exact Ctx.ref_compAt hT q (Ctx.ref_here_of hT hu) hC

/-- Where the companion `q` sits in a value with companions `cs`: under the first components
    of the companions after it, the second component. -/
def compsIdx : List (List Step) → List Step → List Step
  | [], _ => []
  | p :: ps, q => if q = p then [.snd] else .fst :: compsIdx ps q

theorem Ctx.ref_compsIdx {Γ : Ctx} {A : VarType} : ∀ (cs : List (List Step)) {u : VarSymb}
    (q : List Step), q ∈ cs → Γ.ref u = some (A.compsFlat cs) →
      Γ.ref (u.ext (compsIdx cs q)) = some ((A.compAt q).getD .VTypeOne)
  | [], _, _, hq, _ => absurd hq List.not_mem_nil
  | p :: ps, u, q, hq, hu => by
      unfold compsIdx
      split_ifs with h
      · subst h
        exact Ctx.ref_snd_of hu
      · exact Ctx.ref_compsIdx ps q ((List.mem_cons.mp hq).resolve_left h) (Ctx.ref_fst_of hu)

/-- ⭐**The tree of a value's items** under T (`bcB true Z`), with its leaf at each companion path
    `q` given by `get`: the contents of a `□C` component, then its value's items; pairs for
    products; `()` elsewhere.  The network's tuple `tupB` is this tree with the items `u.q.box`
    as leaves; the map `ShapeMap.tupC` fills it with a born root's here-items, or with its
    companions' values (docs §11.21, stage 3). -/
def bcTree {σ : Signature} {Γ : Ctx} : (Z : VarType) →
    (∀ q, q ∈ Z.hereChains → Σ c, Term σ Γ ((Z.compAt q).getD .VTypeOne) c) →
    Σ c, Term σ Γ (Z.bcB true) c
  | .VTypeBox C, get => ⟨_, Term.pair (get [] List.mem_cons_self).2
      (bcTree C (fun q hq => get (.here :: q)
        (List.mem_cons_of_mem _ (List.mem_map_of_mem hq)))).2⟩
  | .VTypeProd X Y, get => ⟨_, Term.pair
      (bcTree X (fun q hq => get (.fst :: q) (List.mem_append_left _ (List.mem_map_of_mem hq)))).2
      (bcTree Y (fun q hq => get (.snd :: q)
        (List.mem_append_right _ (List.mem_map_of_mem hq)))).2⟩
  | .Var, _ => ⟨_, .unit⟩
  | .VTypeOne, _ => ⟨_, .unit⟩
  | .VTypeDia _, _ => ⟨_, .unit⟩

/-- Under T, the items of `u : R` as one tree of its `□` view: the leaf at each companion path
    `q` is the item `(u.q).inner`.  This is `tupB u R true`, with `inner` for `box`. -/
def itemsTree {σ : Signature} {Γ : Ctx} (hT : ModalSys.T = true) (u : VarSymb) (R : VarType)
    (hu : Γ.ref u = some R) : Σ c, Term σ Γ.boxIn (R.bcB true) c :=
  bcTree R fun q hq => ⟨_, Term.eta (u.ext q).inner _ (Ctx.ref_inner (by
    obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp (VarType.compAt_hereChains R q hq)
    rw [hC]
    exact Ctx.ref_compAt hT q hu hC))⟩

/-- The tuple of one born root `□A` under T, as a type: `𝟙 × (A × bc A)`. -/
abbrev tupOneTy (A : VarType) (b : Bool) : VarType :=
  .VTypeProd .VTypeOne ((VarType.VTypeBox A).bcB b)

/-- The born root's companion that a companion of its tuple is. -/
def tupCompOf (A : VarType) (p : List Step) : List Step :=
  ((VarType.VTypeBox A).bcDec p.tail).tail

omit [ModalSys] in
theorem tupCompOf_spec (A : VarType) (p : List Step) (hp : p ∈ (tupOneTy A true).hereChains) :
    tupCompOf A p ∈ A.hereChains ∧
      (tupOneTy A true).compAt p = A.compAt (tupCompOf A p) := by
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨_, hq, _⟩ := List.mem_map.mp hp
    cases hq
  · obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp
    have hbox := VarType.bcDec_box A p' hp'
    have hmem := VarType.bcDec_mem (.VTypeBox A) p' hp'
    rw [hbox] at hmem
    refine ⟨?_, ?_⟩
    · rcases List.mem_cons.mp hmem with h | h
      · cases h
      · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp h
        cases hqe
        exact hq
    · change ((VarType.VTypeBox A).bcB true).compAt p' = _
      rw [VarType.compAt_bcDec (.VTypeBox A) p' hp', hbox]
      rfl

/-- The value of the tuple of one born root and its companions, read off the root's value with
    companions `w` (`bnd 0`): `⟨(), ⟨w's own value, the tree of its companions' values⟩⟩`, then
    each companion of the tuple as the root's companion it is (`tupCompOf`). -/
def tupCVal {σ : Signature} (A : VarType) (hT : ModalSys.T = true) :
    (cs : List (List Step)) → (∀ p ∈ cs, p ∈ (tupOneTy A true).hereChains) →
    Σ c, Term σ (Ctx.empty.insert (.bnd 0) (A.compsFlat A.hereChains))
      ((tupOneTy A true).compsFlat cs) c
  | [], _ => ⟨_, Term.pair Term.unit (Term.pair
      (Term.eta ((VarSymb.root (.bnd 0)).ext (compsFst A.hereChains)) A
        (Ctx.ref_compsFst _ (Ctx.ref_insert_root _ _ _)))
      (bcTree A (fun q hq => ⟨_, Term.eta ((VarSymb.root (.bnd 0)).ext (compsIdx A.hereChains q)) _
        (Ctx.ref_compsIdx _ q hq (Ctx.ref_insert_root _ _ _))⟩)).2)⟩
  | p :: ps, h => ⟨_, Term.pair (tupCVal A hT ps fun p' hp' => h p' (List.mem_cons_of_mem _ hp')).2
      (Term.eta ((VarSymb.root (.bnd 0)).ext (compsIdx A.hereChains (tupCompOf A p)))
        (((tupOneTy A true).compAt p).getD .VTypeOne) (by
          rw [(tupCompOf_spec A p (h p List.mem_cons_self)).2]
          exact Ctx.ref_compsIdx _ _ (tupCompOf_spec A p (h p List.mem_cons_self)).1
            (Ctx.ref_insert_root _ _ _)))⟩

omit [ModalSys] in
/-- A companion of a value padded with `()` is a companion of the value, under `fst`. -/
theorem padC_mem {Z : VarType} {p : List Step}
    (hp : p ∈ (VarType.VTypeProd Z .VTypeOne).hereChains) :
    p = .fst :: p.tail ∧ p.tail ∈ Z.hereChains := by
  rcases List.mem_append.mp hp with hq | hq
  · obtain ⟨q, hq₀, rfl⟩ := List.mem_map.mp hq
    exact ⟨rfl, hq₀⟩
  · obtain ⟨_, hq₀, _⟩ := List.mem_map.mp hq
    cases hq₀

/-- The value of a padded object and its companions, read off the object's value with
    companions `w` (`bnd 0`): `⟨w's own value, ()⟩`, then each companion `fst :: q` as `w`'s
    companion `q`. -/
def padCVal {σ : Signature} (Z : VarType) :
    (cs : List (List Step)) → (∀ p ∈ cs, p ∈ (VarType.VTypeProd Z .VTypeOne).hereChains) →
    Σ c, Term σ (Ctx.empty.insert (.bnd 0) (Z.compsFlat Z.hereChains))
      ((VarType.VTypeProd Z .VTypeOne).compsFlat cs) c
  | [], _ => ⟨_, Term.pair
      (Term.eta ((VarSymb.root (.bnd 0)).ext (compsFst Z.hereChains)) Z
        (Ctx.ref_compsFst _ (Ctx.ref_insert_root _ _ _))) Term.unit⟩
  | p :: ps, h => ⟨_, Term.pair (padCVal Z ps fun p' hp' => h p' (List.mem_cons_of_mem _ hp')).2
      (Term.eta ((VarSymb.root (.bnd 0)).ext (compsIdx Z.hereChains p.tail))
        (((VarType.VTypeProd Z .VTypeOne).compAt p).getD .VTypeOne) (by
          obtain ⟨e, hq⟩ := padC_mem (h p List.mem_cons_self)
          rw [e]
          exact Ctx.ref_compsIdx _ _ hq (Ctx.ref_insert_root _ _ _)))⟩

/-- The companions of a pair: the first half's under `fst`, the second's under `snd`.  A pair's
    full companion list is this (`hereChains` of a product). -/
abbrev pairComps (csX csY : List (List Step)) : List (List Step) :=
  csX.map (Step.fst :: ·) ++ csY.map (Step.snd :: ·)

omit [ModalSys] in
theorem pairComps_mem {csX csY : List (List Step)} {p : List Step}
    (hp : p ∈ pairComps csX csY) :
    (p = .fst :: p.tail ∧ p.tail ∈ csX) ∨ (p = .snd :: p.tail ∧ p.tail ∈ csY) := by
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact Or.inl ⟨rfl, hq⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact Or.inr ⟨rfl, hq⟩

omit [ModalSys] in
/-- A pair's companions, from duplicate-free halves, are duplicate-free. -/
theorem pairComps_nodup {csX csY : List (List Step)} (hX : csX.Nodup) (hY : csY.Nodup) :
    (pairComps csX csY).Nodup :=
  List.Nodup.append (hX.map (fun _ _ h => (List.cons.inj h).2))
    (hY.map (fun _ _ h => (List.cons.inj h).2)) (by simp [List.Disjoint])

theorem VarType.compOk_pairComps {X Y : VarType} {csX csY : List (List Step)}
    (hX : X.CompOk csX) (hY : Y.CompOk csY) :
    (VarType.VTypeProd X Y).CompOk (pairComps csX csY) := by
  have hnd := pairComps_nodup hX.nodup hY.nodup
  rcases hX with rfl | ⟨hT, hx, -⟩
  · rcases hY with rfl | ⟨hT, hy, -⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨hT, fun p hp => ?_, hnd⟩
      rcases pairComps_mem hp with ⟨-, hq⟩ | ⟨e, hq⟩
      · cases hq
      · rw [e]
        exact hy _ hq
  · refine Or.inr ⟨hT, fun p hp => ?_, hnd⟩
    rcases pairComps_mem hp with ⟨e, hq⟩ | ⟨e, hq⟩
    · rw [e]
      exact hx _ hq
    · rcases hY with rfl | ⟨-, hy, -⟩
      · cases hq
      · rw [e]
        exact hy _ hq

/-- A value with companions built from its own value and each companion's. -/
def compsBuild {σ : Signature} {Γ : Ctx} (A : VarType) (main : Σ a, Term σ Γ A a) :
    (cs : List (List Step)) → (∀ p ∈ cs, Σ c, Term σ Γ ((A.compAt p).getD .VTypeOne) c) →
    Σ c, Term σ Γ (A.compsFlat cs) c
  | [], _ => main
  | p :: ps, get => ⟨_, Term.pair
      (compsBuild A main ps fun p' hp' => get p' (List.mem_cons_of_mem _ hp')).2
      (get p List.mem_cons_self).2⟩

/-- Where a pair's companion `p` sits in the two halves' values with companions. -/
def pairCompAddr (csX csY : List (List Step)) (p : List Step) : VarSymb :=
  if p.head? = some .fst then (VarSymb.step (.root (.bnd 0)) .fst).ext (compsIdx csX p.tail)
  else (VarSymb.step (.root (.bnd 0)) .snd).ext (compsIdx csY p.tail)

theorem pairCompAddr_ref {X Y : VarType} {csX csY : List (List Step)} {p : List Step}
    (hp : p ∈ pairComps csX csY) :
    (Ctx.empty.insert (.bnd 0) (.VTypeProd (X.compsFlat csX) (Y.compsFlat csY))).ref
      (pairCompAddr csX csY p) = some (((VarType.VTypeProd X Y).compAt p).getD .VTypeOne) := by
  rcases pairComps_mem hp with ⟨e, hq⟩ | ⟨e, hq⟩
  · generalize p.tail = q at e hq
    subst e
    exact Ctx.ref_compsIdx csX q hq (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))
  · generalize p.tail = q at e hq
    subst e
    exact Ctx.ref_compsIdx csY q hq (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))

/-! ## The companion renaming of a necessary object's view (`holeC`) -/

/-- The contents of a necessary term. -/
def Term.unboxtm {σ : Signature} {Γ : Ctx} {A : VarType} {a : Ann (.VTypeBox A)} :
    Term σ Γ (.VTypeBox A) a → Σ b, Term σ Γ.boxIn A b
  | .boxtm t => ⟨_, t⟩

/-- Under T, the contents of `□sb`'s companion at the path `p`: `□sb` put into the hole of the
    companion's contents address `d.here.p.box`, read by substitution (`SubE.proj` reads `here` of
    `□v` as `collapse v`, and projections of pairs as components). -/
def compVal {σ : Signature} {Γ : Ctx} {A : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀)
    (p : List Step) {ps : List (List Step)} (h : A.CompOk (p :: ps)) :
    Σ b, Term σ Γ.boxIn ((A.compAt p).getD .VTypeOne) b :=
  Term.unboxtm (Term.holeAt (Term.boxtm sb) (Term.boxtm
    (Term.eta ((VarSymb.step (.root (.bnd 0)) .here).ext p).inner ((A.compAt p).getD .VTypeOne)
      (Ctx.ref_inner (h.ref_head (Ctx.ref_insert_root _ _ _))))))

/-- The type reached from `T` along a path, if every step applies. -/
def VarType.walk : VarType → List Step → Option VarType
  | T, [] => some T
  | T, s :: p => (T.step s).bind fun U => U.walk p

theorem VarType.walk_append (T : VarType) (p q : List Step) :
    T.walk (p ++ q) = (T.walk p).bind fun U => U.walk q := by
  induction p generalizing T with
  | nil => rfl
  | cons s p ih =>
      simp only [List.cons_append, VarType.walk]
      cases T.step s with
      | none => rfl
      | some U => exact ih U

/-- The addresses of a context with one root: the root along projection steps, at the type the
    path walks to. -/
theorem Ctx.ref_insert_one {r : Root} {R : VarType} : ∀ (u : VarSymb) {U : VarType},
    (Ctx.empty.insert r R).ref u = some U →
      u.rt = r ∧ (∀ s ∈ u.path, s.isProj = true) ∧ R.walk u.path = some U
  | .root r', U, h => by
      change (if VarSymb.root r' = .root r then some R else Ctx.empty (.root r')) = some U at h
      split_ifs at h with he
      · cases he
        exact ⟨rfl, fun _ hs => absurd hs List.not_mem_nil, h⟩
      · cases h
  | .step v s, U, h => by
      simp only [Ctx.ref] at h
      split_ifs at h with hs
      · obtain ⟨V, hv, hst⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨hrt, hp, hw⟩ := Ctx.ref_insert_one v hv
        refine ⟨hrt, fun t ht => ?_, ?_⟩
        · rcases List.mem_append.mp ht with ht | ht
          · exact hp t ht
          · rw [List.mem_singleton.mp ht]; exact hs
        · change R.walk (v.path ++ [s]) = some U
          rw [VarType.walk_append, hw]
          simpa [VarType.walk] using hst
      · change (if VarSymb.step v s = .root r then some R else Ctx.empty (.step v s)) = some U at h
        rw [if_neg (by simp)] at h
        cases h

/-- A path walking a type to a necessary type reaches a companion there. -/
theorem VarType.compAt_of_walk : ∀ (A : VarType) (p : List Step) {C : VarType},
    (∀ s ∈ p, s.isProj = true) → A.walk p = some (.VTypeBox C) → A.compAt p = some C
  | A, [], C, _, h => by
      cases A <;> simp only [VarType.walk, Option.some.injEq, reduceCtorEq] at h
      rw [VarType.VTypeBox.inj h]
      rfl
  | A, s :: p, C, hp, h => by
      have hs := hp s List.mem_cons_self
      have hp' : ∀ t ∈ p, t.isProj = true := fun t ht => hp t (List.mem_cons_of_mem _ ht)
      cases A <;> cases s <;> simp only [Step.isProj, Bool.false_eq_true] at hs <;>
        simp only [VarType.walk, VarType.step, Option.bind_none, Option.bind_some,
          reduceCtorEq] at h
      · exact VarType.compAt_of_walk _ p hp' h
      · exact VarType.compAt_of_walk _ p hp' h
      · rename_i A'
        by_cases hT : ModalSys.T = true
        · rw [if_pos hT, Option.bind_some] at h
          exact VarType.compAt_of_walk A' p hp' h
        · rw [if_neg hT, Option.bind_none] at h
          cases h

omit [ModalSys] in
/-- Every path to a necessary component is one of the companions. -/
theorem VarType.mem_hereChains : ∀ (A : VarType) (p : List Step) {C : VarType},
    A.compAt p = some C → p ∈ A.hereChains
  | .VTypeBox C', [], _, _ => List.mem_cons_self
  | .VTypeBox C', .here :: q, C, h =>
      List.mem_cons_of_mem _ (List.mem_map_of_mem (VarType.mem_hereChains C' q h))
  | .VTypeProd X _, .fst :: q, C, h =>
      List.mem_append_left _ (List.mem_map_of_mem (VarType.mem_hereChains X q h))
  | .VTypeProd _ Y, .snd :: q, C, h =>
      List.mem_append_right _ (List.mem_map_of_mem (VarType.mem_hereChains Y q h))
  | .Var, _, _, h => by simp [VarType.compAt] at h
  | .VTypeOne, _, _, h => by simp [VarType.compAt] at h
  | .VTypeDia _, _, _, h => by simp [VarType.compAt] at h
  | .VTypeBox _, .fst :: _, _, h => by simp [VarType.compAt] at h
  | .VTypeBox _, .snd :: _, _, h => by simp [VarType.compAt] at h
  | .VTypeBox _, .box :: _, _, h => by simp [VarType.compAt] at h
  | .VTypeBox _, .dia :: _, _, h => by simp [VarType.compAt] at h
  | .VTypeBox _, .keep :: _, _, h => by simp [VarType.compAt] at h
  | .VTypeProd _ _, [], _, h => by simp [VarType.compAt] at h
  | .VTypeProd _ _, .box :: _, _, h => by simp [VarType.compAt] at h
  | .VTypeProd _ _, .dia :: _, _, h => by simp [VarType.compAt] at h
  | .VTypeProd _ _, .here :: _, _, h => by simp [VarType.compAt] at h
  | .VTypeProd _ _, .keep :: _, _, h => by simp [VarType.compAt] at h

/-- A necessary item of the one-root view of `d : □A`: `d` itself, or under T a companion
    `d.here.p` (`p` among all of `A`'s companions). -/
theorem Ctx.ref_insert_box {A : VarType} {u : VarSymb} {T : VarType}
    (hu : (Ctx.empty.insert (.bnd 0) (.VTypeBox A)).ref u = some (.VTypeBox T)) :
    u.rt = .bnd 0 ∧ (∀ s ∈ u.path, s.isProj = true) ∧
      ((u.path = [] ∧ T = A) ∨
        (ModalSys.T = true ∧ ∃ p, u.path = .here :: p ∧ A.compAt p = some T)) := by
  obtain ⟨hrt, hp, hw⟩ := Ctx.ref_insert_one u hu
  refine ⟨hrt, hp, ?_⟩
  revert hp hw
  cases u.path with
  | nil =>
      intro _ hw
      simp only [VarType.walk, Option.some.injEq] at hw
      exact Or.inl ⟨rfl, (VarType.VTypeBox.inj hw).symm⟩
  | cons s p =>
      intro hp hw
      have hs := hp s List.mem_cons_self
      have hp' : ∀ t ∈ p, t.isProj = true := fun t ht => hp t (List.mem_cons_of_mem _ ht)
      cases s <;> simp only [Step.isProj, Bool.false_eq_true] at hs <;>
        simp only [VarType.walk, VarType.step, Option.bind_none, reduceCtorEq] at hw
      by_cases hT : ModalSys.T = true
      · rw [if_pos hT, Option.bind_some] at hw
        exact Or.inr ⟨hT, p, rfl, VarType.compAt_of_walk A p hp' hw⟩
      · rw [if_neg hT, Option.bind_none] at hw
        cases hw

omit [ModalSys] in
omit [ModalSys] in
theorem VarSymb.ext_append_single : ∀ (v : VarSymb) (p : List Step) (s : Step),
    v.ext (p ++ [s]) = .step (v.ext p) s
  | _, [], _ => rfl
  | v, t :: p, s => VarSymb.ext_append_single (.step v t) p s

omit [ModalSys] in
/-- An address is its root along its path. -/
theorem VarSymb.root_ext_path : ∀ (u : VarSymb), (VarSymb.root u.rt).ext u.path = u
  | .root _ => rfl
  | .step u s => by
      change (VarSymb.root u.rt).ext (u.path ++ [s]) = _
      rw [VarSymb.ext_append_single, VarSymb.root_ext_path u]

/-- A path cut at its first `box`. -/
def cutBox : List Step → Option (List Step × List Step)
  | [] => none
  | .box :: q => some ([], q)
  | s :: q => (cutBox q).map fun pq => (s :: pq.1, pq.2)

omit [ModalSys] in
theorem cutBox_proj : ∀ (p : List Step) (q : List Step), (∀ s ∈ p, s.isProj = true) →
    cutBox (p ++ .box :: q) = some (p, q)
  | [], q, _ => rfl
  | s :: p, q, hp => by
      have hs := hp s List.mem_cons_self
      have ih := cutBox_proj p q (fun t ht => hp t (List.mem_cons_of_mem _ ht))
      cases s <;> simp [Step.isProj] at hs <;> simp [cutBox, ih]

/-- Where an item of `d`'s view lands in `d`'s value with companions `cs`: `d.box` at the
    contents, `d.here.p.box` at companion `p`. -/
def compsItemAddr (cs : List (List Step)) : List Step → VarSymb
  | [] => (VarSymb.root (.bnd 0)).ext (compsFst cs)
  | .here :: p => (VarSymb.root (.bnd 0)).ext (compsIdx cs p)
  | _ => .root (.bnd 0)

/-- ⭐**The companion renaming**: the view of a necessary object `d` (the slot `bnd 0`) read off
    its value with companions `cs`, each item to its component (`compsItemAddr`). -/
def compsRen (σ : Signature) (Δ : Ctx) (cs : List (List Step)) : Subst σ Δ := fun v =>
  match v with
  | .step u .box => if u.rt = .bnd 0 then .ren (compsItemAddr cs u.path) else .hide
  | _ => .hide

/-- Where the companion renaming sends annotation indices: below an item, below its image. -/
def compsRenIdx (cs : List (List Step)) (a : VarSymb) : VarSymb :=
  match cutBox a.path with
  | some (p, q) => (compsItemAddr cs p).ext q
  | none => a

theorem ok_compsRen {σ : Signature} (hF : ModalSys.Four = false) (A : VarType) (b : Bool)
    (hb : ModalSys.T = b) :
    Subst.Ok (Ctx.empty.insert (.bnd 0) (.VTypeBox A)).boxIn
      (compsRen σ (Ctx.empty.insert (.bnd 0) (A.compsFlat (A.compsAllB b))) (A.compsAllB b)) := by
  intro v T _ hv
  match v with
  | .step u .box =>
      obtain ⟨-, hu⟩ := Ctx.boxIn_box hv
      obtain ⟨hrt, -, hc⟩ := Ctx.ref_insert_box hu
      dsimp only [compsRen]
      rw [if_pos hrt]
      change Ctx.ref _ (compsItemAddr _ u.path) = some T
      rcases hc with ⟨hpath, rfl⟩ | ⟨hT, p, hpath, hp⟩
      · rw [hpath]
        exact Ctx.ref_compsFst _ (Ctx.ref_insert_root _ _ _)
      · rw [hpath]
        subst hb
        rw [hT] at *
        have hm : p ∈ A.compsAllB true := VarType.mem_hereChains A p hp
        have := Ctx.ref_compsIdx _ p hm (Ctx.ref_insert_root Ctx.empty (.bnd 0)
          (A.compsFlat (A.compsAllB true)))
        rw [hp] at this
        exact this
  | .step u .keep => exact absurd ((Ctx.boxIn_keep hv).1.symm.trans hF) (by decide)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem coh_compsRen {σ : Signature} (hF : ModalSys.Four = false) (A : VarType) (b : Bool)
    (hb : ModalSys.T = b) :
    Subst.Coh (compsRenIdx (A.compsAllB b)) (Ctx.empty.insert (.bnd 0) (.VTypeBox A)).boxIn
      (compsRen σ (Ctx.empty.insert (.bnd 0) (A.compsFlat (A.compsAllB b))) (A.compsAllB b)) := by
  refine Subst.coh_of (ok_compsRen hF A b hb) ?_
  intro v T _ hv q
  match v with
  | .step u .box =>
      obtain ⟨-, hu⟩ := Ctx.boxIn_box hv
      obtain ⟨hrt, hproj, -⟩ := Ctx.ref_insert_box hu
      dsimp only [compsRen]
      rw [if_pos hrt]
      change (compsItemAddr _ u.path).ext q = compsRenIdx _ ((VarSymb.step u .box).ext q)
      unfold compsRenIdx
      rw [VarSymb.ext_path, show (VarSymb.step u .box).path = u.path ++ [.box] from rfl,
        List.append_assoc, List.singleton_append, cutBox_proj u.path q hproj]
  | .step u .keep => exact absurd ((Ctx.boxIn_keep hv).1.symm.trans hF) (by decide)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem VarType.CompOk.single {A : VarType} {cs : List (List Step)} (h : A.CompOk cs)
    {p : List Step} (hp : p ∈ cs) : A.CompOk [p] := by
  rcases h with rfl | ⟨hT, hall, -⟩
  · exact absurd hp List.not_mem_nil
  · exact Or.inr ⟨hT, fun p' hp' => by rw [List.mem_singleton.mp hp']; exact hall p hp,
      List.nodup_singleton p⟩

/-- ⭐**`holeC`'s value**: the contents `s` of the source's contents, and each companion of
    `□s[d.inner]` as its contents (`compVal`) read off the source's value with **all** its
    companions (`compsRen`). -/
def holeCVal {σ : Signature} {A B : VarType} {bB : Ann B}
    (s : Term σ (Ctx.empty.insert (.bnd 0) A) B bB) (b : Bool) (hb : ModalSys.T = b)
    (hF : ModalSys.Four = false) (cs : List (List Step)) (h : B.CompOk cs) :
    Σ c, Term σ (Ctx.empty.insert (.bnd 0) (A.compsFlat (A.compsAllB b))) (B.compsFlat cs) c :=
  compsBuild B ⟨_, Term.holeAt (Term.eta ((VarSymb.root (.bnd 0)).ext (compsFst (A.compsAllB b)))
      A (Ctx.ref_compsFst _ (Ctx.ref_insert_root _ _ _))) s⟩ cs
    fun q hq => ⟨_, Term.subst (compsRenIdx (A.compsAllB b))
      (compsRen σ _ (A.compsAllB b)) (ok_compsRen hF A b hb) (coh_compsRen hF A b hb)
      (compVal (Γ := Ctx.empty.insert (.bnd 0) (.VTypeBox A))
        (Term.holeAt (Term.eta (VarSymb.root (.bnd 0)).inner A
          (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))) s) q (h.single hq)).2⟩

/-! ## Maps between returnable shapes -/

/-- ⭐A **structural map between shapes of necessary objects** (docs §11.17): identity,
    composition, projections and pairing, packing two necessary objects into one, and a hole term
    acting on a necessary object's item.  Each acts on the objects out there (`obj`) and on the
    values they come back as (`val`), compatibly, so a returning possibility can be moved along it
    (`ret_map`), its witness, if any, carried unchanged: this is β for every shape, and
    repacking. -/
inductive ShapeMap (σ : Signature) : NShape → NShape → Type where
  | id (S : NShape) : ShapeMap σ S S
  | comp {S T U : NShape} : ShapeMap σ S T → ShapeMap σ T U → ShapeMap σ S U
  | fst (S T : NShape) : ShapeMap σ (.prod S T) S
  | snd (S T : NShape) : ShapeMap σ (.prod S T) T
  | pair {S T U : NShape} : ShapeMap σ S T → ShapeMap σ S U → ShapeMap σ S (.prod T U)
  | pack (A B : VarType) : ShapeMap σ (.prod (.box A) (.box B)) (.box (.VTypeProd A B))
  | hole {A B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
      ShapeMap σ (.box A) (.box B)
  /-- Packing a `□A` object and its companions into one necessary object (docs §11.21). -/
  | packC (A : VarType) (cs : List (List Step)) (h : A.CompOk cs) :
      ShapeMap σ (.boxC A cs h) (.box (A.compsFlat cs))
  /-- Forgetting a `□A` object's companions (docs §11.21): the object kept, its own value
      taken from the value with companions. -/
  | forgetC (A : VarType) (cs : List (List Step)) (h : A.CompOk cs) :
      ShapeMap σ (.boxC A cs h) (.box A)
  /-- **Padding** a necessary object with `()` (docs §11.21, stage 3c): the object `□⟨d.inner, ()⟩`,
      whose companions are `d`'s own under `fst`. -/
  | padC (Z : VarType) (b : Bool) (hb : ModalSys.T = b) :
      ShapeMap σ (.boxC Z (Z.compsAllB b) (VarType.compOk_compsAllB b hb Z))
        (.boxC (.VTypeProd Z .VTypeOne) ((VarType.VTypeProd Z .VTypeOne).compsAllB b)
          (VarType.compOk_compsAllB b hb _))
  /-- **Packing with companions** (docs §11.21, stage 4): two necessary objects into one,
      `□⟨d₀.inner, d₁.inner⟩`, whose companions are theirs under `fst` and `snd`. -/
  | packCC (X Y : VarType) (csX csY : List (List Step)) (hX : X.CompOk csX)
      (hY : Y.CompOk csY) :
      ShapeMap σ (.prod (.boxC X csX hX) (.boxC Y csY hY))
        (.boxC (.VTypeProd X Y) (pairComps csX csY) (VarType.compOk_pairComps hX hY))
  /-- **The first half with its companions**: `□(d.inner.fst)`, whose companions are `d`'s under
      `fst`. -/
  | fstC (X Y : VarType) (csX csY : List (List Step)) (hX : X.CompOk csX)
      (hY : Y.CompOk csY) :
      ShapeMap σ (.boxC (.VTypeProd X Y) (pairComps csX csY) (VarType.compOk_pairComps hX hY))
        (.boxC X csX hX)
  /-- **The second half with its companions.** -/
  | sndC (X Y : VarType) (csX csY : List (List Step)) (hX : X.CompOk csX)
      (hY : Y.CompOk csY) :
      ShapeMap σ (.boxC (.VTypeProd X Y) (pairComps csX csY) (VarType.compOk_pairComps hX hY))
        (.boxC Y csY hY)
  /-- **Selecting companions**: the object kept, some of its companions (any order). -/
  | subC (A : VarType) (cs cs' : List (List Step)) (h : A.CompOk cs) (h' : A.CompOk cs')
      (hsub : ∀ p ∈ cs', p ∈ cs) :
      ShapeMap σ (.boxC A cs h) (.boxC A cs' h')
  /-- ⭐**A born root's tuple** (docs §11.21, stage 3): the necessary object `□⟨(), items u⟩` of
      a `□A` object `u`'s items (its contents and, under T, its value's items).  Its companions
      are `u`'s own, so they come back as `u`'s do: a sound map into a companion shape, because
      the object is coherent by construction. -/
  | tupC (A : VarType) (b : Bool) (hb : ModalSys.T = b) :
      ShapeMap σ (.boxC A (A.compsAllB b) (VarType.compOk_compsAllB b hb A))
        (.boxC (tupOneTy A b) ((tupOneTy A b).compsAllB b) (VarType.compOk_compsAllB b hb _))
  /-- ⭐**A hole map with companions** (docs §11.21, step 8): a `□A` object `d` with **all** its
      companions to `□s[d.inner]` with companions `cs`.  Each companion of `□s[d.inner]` has as
      contents a term of `d`'s view (`compVal`), and every item of that view, `d.box` or
      `d.here.p.box`, is named by the source (`compsRen`), so the map is sound with no side
      condition: the coherent instance of `holeH`.  With T off it is `hole s` up to `η`. -/
  | holeC {A B : VarType} {bB : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B bB)
      (b : Bool) (hb : ModalSys.T = b) (hF : ModalSys.Four = false) (cs : List (List Step))
      (h : B.CompOk cs) :
      ShapeMap σ (.boxC A (A.compsAllB b) (VarType.compOk_compsAllB b hb A)) (.boxC B cs h)

/-- The map on the object out there, as a hole term. -/
def ShapeMap.obj {σ : Signature} : {S T : NShape} → ShapeMap σ S T →
    Σ b, Term σ (Ctx.empty.insert (.bnd 0) S.ty) T.ty b
  | _, _, .id S => ⟨_, Term.eta (.root (.bnd 0)) S.ty (Ctx.ref_insert_root _ _ _)⟩
  | _, _, .comp F G => ⟨_, Term.holeAt F.obj.2 G.obj.2⟩
  | _, _, .fst S _ =>
      ⟨_, Term.eta (.step (.root (.bnd 0)) .fst) S.ty (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))⟩
  | _, _, .snd _ T =>
      ⟨_, Term.eta (.step (.root (.bnd 0)) .snd) T.ty (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))⟩
  | _, _, .pair F G => ⟨_, Term.pair F.obj.2 G.obj.2⟩
  | _, _, .pack A B => ⟨_, Term.boxtm (Term.pair
      (Term.eta (VarSymb.step (.root (.bnd 0)) .fst).inner A
        (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))
      (Term.eta (VarSymb.step (.root (.bnd 0)) .snd).inner B
        (Ctx.ref_inner (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)))))⟩
  | _, _, .hole (A := A) s => ⟨_, Term.boxtm (Term.holeAt
      (Term.eta (VarSymb.root (.bnd 0)).inner A (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))) s)⟩
  | _, _, .packC A cs h => ⟨_, Term.boxtm (compsBody A cs h).2⟩
  | _, _, .forgetC A _ _ => ⟨_, Term.eta (.root (.bnd 0)) (.VTypeBox A) (Ctx.ref_insert_root _ _ _)⟩
  | _, _, .padC Z _ _ => ⟨_, Term.boxtm (Term.pair
      (Term.eta (VarSymb.root (.bnd 0)).inner Z (Ctx.ref_inner (Ctx.ref_insert_root _ _ _)))
      Term.unit)⟩
  | _, _, .packCC X Y _ _ _ _ => ⟨_, Term.boxtm (Term.pair
      (Term.eta (VarSymb.step (.root (.bnd 0)) .fst).inner X
        (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))
      (Term.eta (VarSymb.step (.root (.bnd 0)) .snd).inner Y
        (Ctx.ref_inner (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)))))⟩
  | _, _, .fstC X _ _ _ _ _ => ⟨_, Term.boxtm (Term.eta
      (VarSymb.step (VarSymb.root (.bnd 0)).inner .fst) X
      (Ctx.ref_fst_of (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))))⟩
  | _, _, .sndC _ Y _ _ _ _ => ⟨_, Term.boxtm (Term.eta
      (VarSymb.step (VarSymb.root (.bnd 0)).inner .snd) Y
      (Ctx.ref_snd_of (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))))⟩
  | _, _, .subC A _ _ _ _ _ =>
      ⟨_, Term.eta (.root (.bnd 0)) (.VTypeBox A) (Ctx.ref_insert_root _ _ _)⟩
  | _, _, .tupC A false _ => ⟨_, Term.boxtm (Term.pair Term.unit
      (Term.eta (VarSymb.root (.bnd 0)).inner A (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))))⟩
  | _, _, .tupC A true hb => ⟨_, Term.boxtm (Term.pair Term.unit
      (itemsTree hb (.root (.bnd 0)) (.VTypeBox A) (Ctx.ref_insert_root _ _ _)).2)⟩
  | _, _, .holeC (A := A) s _ _ _ _ _ => ⟨_, Term.boxtm (Term.holeAt
      (Term.eta (VarSymb.root (.bnd 0)).inner A (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))) s)⟩

/-- The map on the value it comes back as, as a hole term. -/
def ShapeMap.val {σ : Signature} : {S T : NShape} → ShapeMap σ S T →
    Σ b, Term σ (Ctx.empty.insert (.bnd 0) S.flat) T.flat b
  | _, _, .id S => ⟨_, Term.eta (.root (.bnd 0)) S.flat (Ctx.ref_insert_root _ _ _)⟩
  | _, _, .comp F G => ⟨_, Term.holeAt F.val.2 G.val.2⟩
  | _, _, .fst S _ => ⟨_, Term.eta (.step (.root (.bnd 0)) .fst) S.flat
      (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))⟩
  | _, _, .snd _ T => ⟨_, Term.eta (.step (.root (.bnd 0)) .snd) T.flat
      (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))⟩
  | _, _, .pair F G => ⟨_, Term.pair F.val.2 G.val.2⟩
  | _, _, .pack A B => ⟨_, Term.eta (.root (.bnd 0)) (.VTypeProd A B) (Ctx.ref_insert_root _ _ _)⟩
  | _, _, .hole s => ⟨_, s⟩
  | _, _, .packC A cs _ =>
      ⟨_, Term.eta (.root (.bnd 0)) (A.compsFlat cs) (Ctx.ref_insert_root _ _ _)⟩
  | _, _, .forgetC A cs _ => ⟨_, Term.eta ((VarSymb.root (.bnd 0)).ext (compsFst cs)) A
      (Ctx.ref_compsFst cs (Ctx.ref_insert_root _ _ _))⟩
  | _, _, .padC Z false _ =>
      ⟨_, Term.pair (Term.eta (.root (.bnd 0)) Z (Ctx.ref_insert_root _ _ _)) Term.unit⟩
  | _, _, .padC Z true _ => padCVal Z _ fun _ hp => hp
  | _, _, .packCC X Y csX csY _ _ => compsBuild (.VTypeProd X Y)
      ⟨_, Term.pair
        (Term.eta ((VarSymb.step (.root (.bnd 0)) .fst).ext (compsFst csX)) X
          (Ctx.ref_compsFst csX (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))
        (Term.eta ((VarSymb.step (.root (.bnd 0)) .snd).ext (compsFst csY)) Y
          (Ctx.ref_compsFst csY (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))⟩
      (pairComps csX csY) fun p hp =>
        ⟨_, Term.eta (pairCompAddr csX csY p) _ (pairCompAddr_ref hp)⟩
  | _, _, .fstC X _ csX csY _ _ => compsBuild X
      ⟨_, Term.eta (VarSymb.step ((VarSymb.root (.bnd 0)).ext (compsFst (pairComps csX csY)))
        .fst) X (Ctx.ref_fst_of (Ctx.ref_compsFst _ (Ctx.ref_insert_root _ _ _)))⟩
      csX fun q hq => ⟨_, Term.eta ((VarSymb.root (.bnd 0)).ext
        (compsIdx (pairComps csX csY) (.fst :: q))) _
        (Ctx.ref_compsIdx _ (.fst :: q) (List.mem_append_left _ (List.mem_map_of_mem hq))
          (Ctx.ref_insert_root _ _ _))⟩
  | _, _, .sndC _ Y csX csY _ _ => compsBuild Y
      ⟨_, Term.eta (VarSymb.step ((VarSymb.root (.bnd 0)).ext (compsFst (pairComps csX csY)))
        .snd) Y (Ctx.ref_snd_of (Ctx.ref_compsFst _ (Ctx.ref_insert_root _ _ _)))⟩
      csY fun q hq => ⟨_, Term.eta ((VarSymb.root (.bnd 0)).ext
        (compsIdx (pairComps csX csY) (.snd :: q))) _
        (Ctx.ref_compsIdx _ (.snd :: q) (List.mem_append_right _ (List.mem_map_of_mem hq))
          (Ctx.ref_insert_root _ _ _))⟩
  | _, _, .subC A cs cs' _ _ hsub => compsBuild A
      ⟨_, Term.eta ((VarSymb.root (.bnd 0)).ext (compsFst cs)) A
        (Ctx.ref_compsFst cs (Ctx.ref_insert_root _ _ _))⟩
      cs' fun q hq => ⟨_, Term.eta ((VarSymb.root (.bnd 0)).ext (compsIdx cs q)) _
        (Ctx.ref_compsIdx cs q (hsub q hq) (Ctx.ref_insert_root _ _ _))⟩
  | _, _, .tupC A false _ =>
      ⟨_, Term.pair Term.unit (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root _ _ _))⟩
  | _, _, .tupC A true hb => tupCVal A hb _ fun _ hp => hp
  | _, _, .holeC s b hb hF cs h => holeCVal s b hb hF cs h

/-- The map on the object out there, at a returnable shape: on the necessary part, the witness
    carried along. -/
def ShapeMap.liftObj {σ : Signature} : (S : RShape) → {T : NShape} → ShapeMap σ S.necPart T →
    Σ b, Term σ (Ctx.empty.insert (.bnd 0) S.ty) (S.withNec T).ty b
  | .nec _, _, F => F.obj
  | .wit N X, _, F => ⟨_, Term.pair
      (Term.holeAt (Term.eta (.step (.root (.bnd 0)) .fst) N.ty
        (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))) F.obj.2)
      (Term.eta (.step (.root (.bnd 0)) .snd) (.VTypeDia X)
        (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)))⟩

/-- The map on the value it comes back as, at a returnable shape. -/
def ShapeMap.liftVal {σ : Signature} : (S : RShape) → {T : NShape} → ShapeMap σ S.necPart T →
    Σ b, Term σ (Ctx.empty.insert (.bnd 0) S.flat) (S.withNec T).flat b
  | .nec _, _, F => F.val
  | .wit N X, _, F => ⟨_, Term.pair
      (Term.holeAt (Term.eta (.step (.root (.bnd 0)) .fst) N.flat
        (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))) F.val.2)
      (Term.eta (.step (.root (.bnd 0)) .snd) X (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)))⟩

/-- ⭐**β on the possible part** (docs §11.20, the audit): the map on the object out there.  The
    necessary part `d` is kept; the possible part `e` becomes the possible object with `e`'s
    worlds whose content is `h` of `d`'s contents and `e`'s — `diatm e h(d.box, e.dia)`, any term
    with `e` as its witness. -/
def ShapeMap.possObj {σ : Signature} {C X Z : VarType} {b : Ann Z}
    (h : Term σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C X)) Z b) :
    Σ a, Term σ (Ctx.empty.insert (.bnd 0) (RShape.wit (.box C) X).ty)
      (RShape.wit (.box C) Z).ty a :=
  ⟨_, Term.pair
    (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox C)
      (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))
    (Term.diatm (.step (.root (.bnd 0)) .snd) ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩
      (Term.holeAt
        (Term.pair
          (Term.eta (VarSymb.step (.root (.bnd 0)) .fst).inner C
            ((Ctx.le_boxIn_diaIn _ _).ref
              (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))))
          (Term.eta (VarSymb.step (.step (.root (.bnd 0)) .snd) .dia) X
            (Ctx.ref_diaIn_of (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)))))
        h))⟩

/-- β on the possible part, on the value: the necessary part's value kept, the content's mapped
    by `h`. -/
def ShapeMap.possVal {σ : Signature} {C X Z : VarType} {b : Ann Z}
    (h : Term σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C X)) Z b) :
    Σ a, Term σ (Ctx.empty.insert (.bnd 0) (RShape.wit (.box C) X).flat)
      (RShape.wit (.box C) Z).flat a :=
  ⟨_, Term.pair
    (Term.eta (.step (.root (.bnd 0)) .fst) C (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))) h⟩

/-- β on the possible part, on the value, at a necessary part with companions (docs §11.21,
    step 8): the necessary part's value with companions kept, the content's mapped by `h` of its
    contents and the content; `possVal` itself when there are none. -/
def ShapeMap.possValC {σ : Signature} {C X Z : VarType} {b : Ann Z}
    (h : Term σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C X)) Z b) :
    (cs : List (List Step)) → (hcs : C.CompOk cs) →
    Σ a, Term σ (Ctx.empty.insert (.bnd 0) (RShape.wit (.boxC C cs hcs) X).flat)
      (RShape.wit (.boxC C cs hcs) Z).flat a
  | [], _ => ShapeMap.possVal h
  | p :: ps, _ => ⟨_, Term.pair
      (Term.eta (.step (.root (.bnd 0)) .fst) (C.compsFlat (p :: ps))
        (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))
      (Term.holeAt (Term.pair
          (Term.eta ((VarSymb.step (.root (.bnd 0)) .fst).ext (compsFst (p :: ps))) C
            (Ctx.ref_compsFst _ (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))
          (Term.eta (.step (.root (.bnd 0)) .snd) X (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))
        h)⟩

/-! ## A companion -/

/-- In `ret_extS`'s body, the object out there, read from the extended slot. -/
def RShape.extL {σ : Signature} (V : Ctx) : (S : RShape) → (B : VarType) →
    Σ a, Term σ (V.insert (.bnd 0) (S.ext B).ty) S.ty a
  | .nec N, B => ⟨_, Term.eta (.step (.root (.bnd 0)) .fst) N.ty
      (Ctx.ref_fst_of (Ctx.ref_insert_root V (.bnd 0) (RShape.ext (.nec N) B).ty))⟩
  | .wit N X, B => ⟨_, Term.pair
      (Term.eta (.step (.step (.root (.bnd 0)) .fst) .fst) N.ty
        (Ctx.ref_fst_of (Ctx.ref_fst_of (Ctx.ref_insert_root V (.bnd 0)
          (RShape.ext (.wit N X) B).ty))))
      (Term.eta (.step (.root (.bnd 0)) .snd) (.VTypeDia X)
        (Ctx.ref_snd_of (Ctx.ref_insert_root V (.bnd 0) (RShape.ext (.wit N X) B).ty)))⟩

/-- In `ret_extS`'s body, the companion, read from the extended slot. -/
def RShape.extR {σ : Signature} (V : Ctx) : (S : RShape) → (B : VarType) →
    Σ a, Term σ (V.insert (.bnd 0) (S.ext B).ty) (.VTypeBox B) a
  | .nec N, B => ⟨_, Term.eta (.step (.root (.bnd 0)) .snd) (.VTypeBox B)
      (Ctx.ref_snd_of (Ctx.ref_insert_root V (.bnd 0) (RShape.ext (.nec N) B).ty))⟩
  | .wit N X, B => ⟨_, Term.eta (.step (.step (.root (.bnd 0)) .fst) .snd) (.VTypeBox B)
      (Ctx.ref_snd_of (Ctx.ref_fst_of (Ctx.ref_insert_root V (.bnd 0)
        (RShape.ext (.wit N X) B).ty)))⟩

/-- In `ret_realise`'s body, the necessary part, read from the witnessed slot. -/
def RShape.realL {σ : Signature} (V : Ctx) (N : NShape) (X : VarType) :
    Σ a, Term σ (V.insert (.bnd 0) (RShape.wit N X).ty) N.ty a :=
  ⟨_, Term.eta (.step (.root (.bnd 0)) .fst) N.ty
    (Ctx.ref_fst_of (Ctx.ref_insert_root V (.bnd 0) (RShape.wit N X).ty))⟩

/-- In `ret_extS`'s conclusion, the value and the companion's value, arranged as the extended
    shape's value: the companion joins the necessary part. -/
def RShape.extTm {σ : Signature} {Γ : Ctx} [Γ.NoSlots] : (S : RShape) → {B : VarType} →
    {a : Ann S.flat} → Term σ Γ S.flat a → {b : Ann B} → Term σ Γ B b →
    Σ c, Term σ Γ (S.ext B).flat c
  | .nec _, _, _, t, _, u => ⟨_, Term.pair t u⟩
  | .wit N X, B, _, t, _, u => ⟨_, Term.holeRead (Term.pair t u) (Term.pair
      (Term.pair
        (Term.eta (.step (.step (.root (.bnd 0)) .fst) .fst) N.flat
          (Ctx.ref_fst_of (Ctx.ref_fst_of (Ctx.ref_insert_root Ctx.empty (.bnd 0)
            (.VTypeProd (RShape.wit N X).flat B)))))
        (Term.eta (.step (.root (.bnd 0)) .snd) B
          (Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0)
            (.VTypeProd (RShape.wit N X).flat B)))))
      (Term.eta (.step (.step (.root (.bnd 0)) .fst) .snd) X
        (Ctx.ref_snd_of (Ctx.ref_fst_of (Ctx.ref_insert_root Ctx.empty (.bnd 0)
          (.VTypeProd (RShape.wit N X).flat B))))))⟩

/-! ## A named companion -/

/-- In `ret_compS`'s body, the object out there, read from the shape with one more companion: the
    object itself (a companion leaves the object's type alone). -/
def RShape.compL {σ : Signature} (V : Ctx) (A : VarType) (cs : List (List Step))
    (h : A.CompOk cs) (p : List Step) (h' : A.CompOk (p :: cs)) : (S : RShape) →
    Σ a, Term σ (V.insert (.bnd 0) (S.withNec (.boxC A (p :: cs) h')).ty)
      (S.withNec (.boxC A cs h)).ty a
  | .nec _ => ⟨_, Term.eta (.root (.bnd 0)) (.VTypeBox A) (Ctx.ref_insert_root V (.bnd 0) _)⟩
  | .wit _ X => ⟨_, Term.eta (.root (.bnd 0)) (.VTypeProd (.VTypeBox A) (.VTypeDia X))
      (Ctx.ref_insert_root V (.bnd 0) _)⟩

/-- In `ret_compS`'s conclusion, the value and the new companion's value, arranged as the value of
    the shape with one more companion. -/
def RShape.compTm {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (A : VarType) (cs : List (List Step))
    (h : A.CompOk cs) (p : List Step) (h' : A.CompOk (p :: cs)) : (S : RShape) →
    {a : Ann (S.withNec (.boxC A cs h)).flat} → Term σ Γ (S.withNec (.boxC A cs h)).flat a →
    {b : Ann ((A.compAt p).getD .VTypeOne)} → Term σ Γ ((A.compAt p).getD .VTypeOne) b →
    Σ c, Term σ Γ (S.withNec (.boxC A (p :: cs) h')).flat c
  | .nec _, _, t, _, u => ⟨_, Term.pair t u⟩
  | .wit _ X, _, t, _, u => ⟨_, Term.holeRead (Term.pair t u) (Term.pair
      (Term.pair
        (Term.eta (.step (.step (.root (.bnd 0)) .fst) .fst) (A.compsFlat cs)
          (Ctx.ref_fst_of (Ctx.ref_fst_of (Ctx.ref_insert_root Ctx.empty (.bnd 0)
            (.VTypeProd (RShape.wit (.boxC A cs h) X).flat ((A.compAt p).getD .VTypeOne))))))
        (Term.eta (.step (.root (.bnd 0)) .snd) ((A.compAt p).getD .VTypeOne)
          (Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0)
            (.VTypeProd (RShape.wit (.boxC A cs h) X).flat ((A.compAt p).getD .VTypeOne))))))
      (Term.eta (.step (.step (.root (.bnd 0)) .fst) .snd) X
        (Ctx.ref_snd_of (Ctx.ref_fst_of (Ctx.ref_insert_root Ctx.empty (.bnd 0)
          (.VTypeProd (RShape.wit (.boxC A cs h) X).flat ((A.compAt p).getD .VTypeOne)))))))⟩

/-- The value `□sb` and its companions come back as along the arrow out: `sb`, then each
    companion's contents (`compVal`); `sb` itself when there are none. -/
def compsVal {σ : Signature} {Γ : Ctx} {A : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) :
    (cs : List (List Step)) → A.CompOk cs → Σ b, Term σ Γ.boxIn (A.compsFlat cs) b
  | [], _ => ⟨_, sb⟩
  | p :: ps, h => ⟨_, Term.pair (compsVal sb ps h.tail).2 (compVal sb p h).2⟩

/-- ⭐`ret_unit`'s new conjunct, in the body of `◇[d₁ ↦ y]` (`d₁ : □C` the slot `bnd 0`):
    `◇[d ↦ sb] θ(d₁.box, d)` — from the far world, back here, a necessary object `d` coming back
    as `sb` with `θ` of it and of `d₁`'s return (docs §11.17). -/
def WFF.unitBody {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    {C A : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox C)) 1 :=
  WFF.ret hS (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root (.VTypeBox C)) sb)
    (WFF.holeAt (((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert (.VTypeBox C)).boxIn.insert
        (.VTypeBox A))
      (Term.pair
        (Term.eta (VarSymb.root (.bnd 0)).inner C
          ((Ctx.le_insert ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert (.VTypeBox C)).boxIn.root
            (.VTypeBox A)).ref
            (Ctx.ref_inner (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox C)))))
        (Term.eta (.root (.bnd 1)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd 1) _)))
      θ)

/-- The value with companions `cs` of the necessary object at `u`, read in a view `Δ'` containing
    `u`'s `□` view: its contents, then each companion's contents.  At no companions it is
    `u.inner` (docs §11.21: the units at an outer object with companions). -/
def compsSlot {σ : Signature} {Δ Δ' : Ctx} {u : VarSymb} {C : VarType}
    (hu : Δ.ref u = some (.VTypeBox C)) (hle : Δ.boxIn.Le Δ') :
    (cs : List (List Step)) → C.CompOk cs → Σ c, Term σ Δ' (C.compsFlat cs) c
  | [], _ => ⟨_, Term.eta u.inner C (hle.ref (Ctx.ref_inner hu))⟩
  | p :: ps, h => ⟨_, Term.pair (compsSlot hu hle ps h.tail).2
      (Term.eta ((VarSymb.step u .here).ext p).inner ((C.compAt p).getD .VTypeOne)
        (hle.ref (Ctx.ref_inner (h.ref_head hu))))⟩

/-- `ret_unit`'s new conjunct at an inner object with companions `cs` (docs §11.21): the
    companions of `□sb` come back too, each as its contents read along the way (`compsVal`).  At no
    companions this is `WFF.unitBody`. -/
def WFF.unitBodyC {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    {C A : VarType} (co : List (List Step)) (ho : C.CompOk co) {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) (cs : List (List Step)) (h : A.CompOk cs)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (C.compsFlat co) (.VTypeBox A))) 1) :
    WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox C)) 1 :=
  WFF.retS hS (.nec (.boxC A cs h))
    (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root (.VTypeBox C))
      (compsVal sb cs h).2)
    (WFF.holeAt (((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert (.VTypeBox C)).boxIn.insert
        (.VTypeBox A))
      (Term.pair
        (compsSlot (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox C))
          (Ctx.le_insert ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert (.VTypeBox C)).boxIn.root
            (.VTypeBox A)) co ho).2
        (Term.eta (.root (.bnd 1)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd 1) _)))
      θ)

theorem WFF.unitBodyC_nil {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    {C A : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) (h : A.CompOk [])
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF.unitBodyC hS (C := C) [] (Or.inl rfl) sb [] h θ = WFF.unitBody hS sb θ := rfl

/-- ⭐The **witnessed unit's** new conjunct, in the body of `◇_x[d₁ ↦ y]` (docs §11.17):
    `◇[d ↦ sb, e ⇝ u] θ(d₁.box, ⟨d, e⟩)`.  Going home from the far end, a necessary object comes
    back as `sb` and a possible one (`x` itself) is realised along the way back with content `u`,
    the witness's content there — the witness's share of the round trip, as `K_dia` carries it. -/
def WFF.unitBodyW {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    {x : VarSymb} {C A X : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X}
    (u : Term σ (Γ.diaIn x) X b₀)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (RShape.wit (.box A) X).ty)) 1) :
    WFF σ ((Γ.diaIn x).insert (.bnd 0) (.VTypeBox C)) 1 :=
  WFF.retS hS (.wit (.box A) X)
    (Term.pair
      (Term.mono ((Ctx.le_boxIn_diaIn Γ x).trans
        (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root (.VTypeBox C))) sb)
      (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root (.VTypeBox C)) u))
    (WFF.holeAt (((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert (.VTypeBox C)).boxIn.insert _)
      (Term.pair
        (Term.eta (VarSymb.root (.bnd 0)).inner C
          ((Ctx.le_insert ((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert (.VTypeBox C)).boxIn.root
            (RShape.wit (.box A) X).ty).ref
            (Ctx.ref_inner (Ctx.ref_insert_root (Γ.diaIn x) (.bnd 0) (.VTypeBox C)))))
        (Term.eta (.root (.bnd 1)) _ (Ctx.ref_insert_root _ (.bnd 1) _)))
      θ)

/-- The witnessed unit's conjunct at an inner object with companions (`WFF.unitBodyW` at `cs`). -/
def WFF.unitBodyWC {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    {x : VarSymb} {C A X : VarType} (co : List (List Step)) (ho : C.CompOk co) {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X}
    (u : Term σ (Γ.diaIn x) X b₀) (cs : List (List Step)) (h : A.CompOk cs)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (C.compsFlat co) (RShape.wit (.box A) X).ty)) 1) :
    WFF σ ((Γ.diaIn x).insert (.bnd 0) (.VTypeBox C)) 1 :=
  WFF.retS hS (.wit (.boxC A cs h) X)
    (Term.pair
      (Term.mono ((Ctx.le_boxIn_diaIn Γ x).trans
        (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root (.VTypeBox C)))
        (compsVal sb cs h).2)
      (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root (.VTypeBox C)) u))
    (WFF.holeAt (((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert (.VTypeBox C)).boxIn.insert _)
      (Term.pair
        (compsSlot (Ctx.ref_insert_root (Γ.diaIn x) (.bnd 0) (.VTypeBox C))
          (Ctx.le_insert ((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert (.VTypeBox C)).boxIn.root
            (RShape.wit (.box A) X).ty) co ho).2
        (Term.eta (.root (.bnd 1)) _ (Ctx.ref_insert_root _ (.bnd 1) _)))
      θ)

theorem WFF.unitBodyWC_nil {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    {x : VarSymb} {C A X : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X}
    (u : Term σ (Γ.diaIn x) X b₀) (h : A.CompOk [])
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (RShape.wit (.box A) X).ty)) 1) :
    WFF.unitBodyWC hS (C := C) [] (Or.inl rfl) sb u [] h θ = WFF.unitBodyW hS sb u θ := rfl

/-- ⭐The **unit along a returned possible part**, in the body of `◇[⟨d₁, e₁⟩ ↦ y]` with
    `e₁ ⇝ y.2`: `◇_{e₁}[d ↦ sb] θ(⟨d₁.box, e₁.dia⟩, d)`.  The way back lies in `e₁`'s extent, so
    from the far end home is reached along `e₁`, where `e₁`'s content is readable. -/
def WFF.unitBodyD {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    {C X A : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd C X) (.VTypeBox A))) 1) :
    WFF σ (Γ.boxIn.insert (.bnd 0) (RShape.wit (.box C) X).ty) 1 :=
  WFF.retxS hS (.step (.root (.bnd 0)) .snd) ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩
    (.box A) (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root _) sb)
    (WFF.holeAt ((((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert _).diaIn _).insert (.VTypeBox A))
      (Term.pair
        (Term.pair
          (Term.eta (VarSymb.step (.root (.bnd 0)) .fst).inner C
            ((Ctx.le_insert ((((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert _).diaIn _).root)
              (.VTypeBox A)).ref ((Ctx.le_boxIn_diaIn _ _).ref
                (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))))
          (Term.eta (VarSymb.step (.step (.root (.bnd 0)) .snd) .dia) X
            ((Ctx.le_insert ((((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert _).diaIn _).root)
              (.VTypeBox A)).ref (Ctx.ref_diaIn_of (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))))
        (Term.eta (.root (.bnd 1)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd 1) _)))
      θ)

/-- `WFF.unitBodyD` at an inner object with companions `cs`. -/
def WFF.unitBodyDC {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    {C X A : VarType} (co : List (List Step)) (ho : C.CompOk co) {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) (cs : List (List Step)) (h : A.CompOk cs)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd (C.compsFlat co) X) (.VTypeBox A))) 1) :
    WFF σ (Γ.boxIn.insert (.bnd 0) (RShape.wit (.box C) X).ty) 1 :=
  WFF.retxS hS (.step (.root (.bnd 0)) .snd) ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩
    (.nec (.boxC A cs h))
    (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root _) (compsVal sb cs h).2)
    (WFF.holeAt ((((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert _).diaIn _).insert (.VTypeBox A))
      (Term.pair
        (Term.pair
          (compsSlot (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))
            ((Ctx.le_boxIn_diaIn _ _).trans
              (Ctx.le_insert ((((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert _).diaIn _).root)
                (.VTypeBox A))) co ho).2
          (Term.eta (VarSymb.step (.step (.root (.bnd 0)) .snd) .dia) X
            ((Ctx.le_insert ((((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert _).diaIn _).root)
              (.VTypeBox A)).ref (Ctx.ref_diaIn_of (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))))
        (Term.eta (.root (.bnd 1)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd 1) _)))
      θ)

/-- ⭐The **doubly witnessed unit's** new conjunct, in the body of `◇_x[⟨d₁, e₁⟩ ↦ y]` with
    `e₁ ⇝ y.2` (docs §11.20): `◇_{e₁}[d ↦ sb, e ⇝ u] θ(⟨d₁.box, e₁.dia⟩, ⟨d, e⟩)`.  The way
    back lies in `e₁`'s extent (`unitBodyD`), and along it a necessary object comes back as `sb`
    and `x` itself is realised with content `u` (`unitBodyW`). -/
def WFF.unitBodyWD {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    {x : VarSymb} {C Xe A X : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X}
    (u : Term σ (Γ.diaIn x) X b₀)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd C Xe) (RShape.wit (.box A) X).ty)) 1) :
    WFF σ ((Γ.diaIn x).insert (.bnd 0) (RShape.wit (.box C) Xe).ty) 1 :=
  WFF.retxS hS (.step (.root (.bnd 0)) .snd) ⟨Xe, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩
    (.wit (.box A) X)
    (Term.pair
      (Term.mono ((Ctx.le_boxIn_diaIn Γ x).trans
        (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root _)) sb)
      (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root _) u))
    (WFF.holeAt ((((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert _).diaIn _).insert _)
      (Term.pair
        (Term.pair
          (Term.eta (VarSymb.step (.root (.bnd 0)) .fst).inner C
            ((Ctx.le_insert ((((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert _).diaIn _).root)
              _).ref ((Ctx.le_boxIn_diaIn _ _).ref
                (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))))
          (Term.eta (VarSymb.step (.step (.root (.bnd 0)) .snd) .dia) Xe
            ((Ctx.le_insert ((((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert _).diaIn _).root)
              _).ref (Ctx.ref_diaIn_of (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))))
        (Term.eta (.root (.bnd 1)) _ (Ctx.ref_insert_root _ (.bnd 1) _)))
      θ)

/-- `WFF.unitBodyWD` at an inner object with companions `cs`. -/
def WFF.unitBodyWDC {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    {x : VarSymb} {C Xe A X : VarType} (co : List (List Step)) (ho : C.CompOk co) {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X}
    (u : Term σ (Γ.diaIn x) X b₀) (cs : List (List Step)) (h : A.CompOk cs)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd (C.compsFlat co) Xe) (RShape.wit (.box A) X).ty)) 1) :
    WFF σ ((Γ.diaIn x).insert (.bnd 0) (RShape.wit (.box C) Xe).ty) 1 :=
  WFF.retxS hS (.step (.root (.bnd 0)) .snd) ⟨Xe, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩
    (.wit (.boxC A cs h) X)
    (Term.pair
      (Term.mono ((Ctx.le_boxIn_diaIn Γ x).trans
        (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root _)) (compsVal sb cs h).2)
      (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root _) u))
    (WFF.holeAt ((((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert _).diaIn _).insert _)
      (Term.pair
        (Term.pair
          (compsSlot (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))
            ((Ctx.le_boxIn_diaIn _ _).trans
              (Ctx.le_insert ((((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert _).diaIn _).root)
                _)) co ho).2
          (Term.eta (VarSymb.step (.step (.root (.bnd 0)) .snd) .dia) Xe
            ((Ctx.le_insert ((((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert _).diaIn _).root)
              _).ref (Ctx.ref_diaIn_of (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))))
        (Term.eta (.root (.bnd 1)) _ (Ctx.ref_insert_root _ (.bnd 1) _)))
      θ)

/-- `back_ret`'s body (docs §11.18): in the body of `◇[e ↦ c]` along a leg with view `V`, the
    object out there is the carrier's, `e = □bd`. -/
def WFF.backRetBody {σ : Signature} {V : Ctx} (hs : V.SlotsFrom 0) {A : VarType}
    (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ V.boxIn A a₀) :
    WFF σ (V.insert (.bnd 0) (.VTypeBox A)) 1 :=
  eqRec (.VTypeBox A) (Term.eta (.root (.bnd 0)) (.VTypeBox A) (Ctx.ref_insert_root V (.bnd 0) _))
    (Term.castAnn (A := .VTypeBox A) hA (Term.mono (Ctx.le_insert hs.root _) (Term.boxtm bd)))

/-- The **counit of a possible part**'s body, for `◇[⟨d, e⟩ ↦ y]` with `e ⇝ y.2`:
    `□_e ψ(⟨d.box, e.dia⟩)` — what holds along all of `e`'s arrows, at its content there. -/
def WFF.counitBodyD {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {C X : VarType}
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C X)) 1) :
    WFF σ (Γ.boxIn.insert (.bnd 0) (RShape.wit (.box C) X).ty) 1 :=
  WFF.boxx (.step (.root (.bnd 0)) .snd) ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩
    (WFF.holeAt (((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert _).diaIn _)
      (Term.pair
        (Term.eta (VarSymb.step (.root (.bnd 0)) .fst).inner C
          ((Ctx.le_boxIn_diaIn _ _).ref
            (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))))
        (Term.eta (VarSymb.step (.step (.root (.bnd 0)) .snd) .dia) X
          (Ctx.ref_diaIn_of (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)))))
      ψ)

/-- The first component of a necessary pair, as a necessary object: `□(fst v.box)`. -/
def Term.boxFst {σ : Signature} {Γ : Ctx} {v : VarSymb} {A B : VarType}
    (h : Γ.ref v = some (.VTypeBox (.VTypeProd A B))) :
    Term σ Γ (.VTypeBox A) (.box (Ann.eta (.step v.inner .fst) A)) :=
  .boxtm (Term.eta (.step v.inner .fst) A (Ctx.ref_fst_of (Ctx.ref_inner h)))

/-- The second component of a necessary pair, as a necessary object. -/
def Term.boxSnd {σ : Signature} {Γ : Ctx} {v : VarSymb} {A B : VarType}
    (h : Γ.ref v = some (.VTypeBox (.VTypeProd A B))) :
    Term σ Γ (.VTypeBox B) (.box (Ann.eta (.step v.inner .snd) B)) :=
  .boxtm (Term.eta (.step v.inner .snd) B (Ctx.ref_snd_of (Ctx.ref_inner h)))

section Body

variable {σ : Signature} {V : Ctx} [V.NoSlots]

omit [ModalSys] in
theorem body_le (T : VarType) : V.Le (V.insert (.bnd 0) T) :=
  Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root T

/-- ⭐**Replacing the bound item** by a term over a new one: a body about `e : □B` becomes a body
    about `d : □A`, with `e := X(d)`.  What β moves a returning possibility by (`Proof.ret_beta`);
    at any types, interchangeability's congruence uses it too (`Canon.Interch.subst_slot`). -/
def WFF.bodyRepl {A B : VarType} {b : Ann B} (X : Term σ (V.insert (.bnd 0) A) B b)
    (Φ : WFF σ (V.insert (.bnd 0) B) 1) : WFF σ (V.insert (.bnd 0) A) 1 :=
  WFF.subst (Subst.setIdx id (.bnd 0) (.tm X)) ((Subst.idS σ _).set (.bnd 0) (.tm X))
    (Subst.ok_set (Subst.ok_idS_le (body_le _)) rfl)
    (Subst.coh_set (Subst.ok_idS_le (body_le _)) (Subst.coh_idS_le (body_le _))
      ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) rfl)
    ((Ctx.NoSlots.slots (Γ := V)).insert _) ((Ctx.NoSlots.slots (Γ := V)).insert _) Φ

/-- ⭐**Splitting a paired item**: a body about two items `d : □A`, `b : □B` becomes a body about
    one `e : □C`, with `d := X₀(e)`, `b := X₁(e)` — the components `Term.boxFst`, `Term.boxSnd` of
    `e : □(A×B)` in `Proof.ret_ext`.  One more item of the same child, packed with the others. -/
def WFF.bodySplit {A B C : VarType} {b₀ : Ann A} {b₁ : Ann B}
    (X₀ : Term σ (V.insert (.bnd 0) C) A b₀)
    (X₁ : Term σ (V.insert (.bnd 0) C) B b₁)
    (Φ : WFF σ ((V.insert (.bnd 0) A).insert (.bnd 1) B) 2) :
    WFF σ (V.insert (.bnd 0) C) 1 :=
  have h₀ := Subst.ok_set (r := .bnd 0) (T := A) (e := .tm X₀)
    (Subst.ok_idS_le (σ := σ) (body_le (V := V) C)) rfl
  have c₀ := Subst.coh_set (r := .bnd 0) (T := A) (e := .tm X₀)
    (Subst.ok_idS_le (σ := σ) (body_le (V := V) C))
    (Subst.coh_idS_le (body_le (V := V) C))
    ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) rfl
  WFF.subst (Subst.setIdx (Subst.setIdx id (.bnd 0) (.tm X₀)) (.bnd 1) (.tm X₁))
    (((Subst.idS σ _).set (.bnd 0) (.tm X₀)).set (.bnd 1) (.tm X₁))
    (Subst.ok_set (r := .bnd 1) (T := B) (e := .tm X₁) h₀ rfl)
    (Subst.coh_set (r := .bnd 1) (T := B) (e := .tm X₁) h₀ c₀
      (((Ctx.NoSlots.slots (Γ := V)).insert _).rootFresh (le_refl 1)) rfl)
    (((Ctx.NoSlots.slots (Γ := V)).insert _).insert _) ((Ctx.NoSlots.slots (Γ := V)).insert _) Φ

end Body

/-- ⭐The **out leg** of a round trip (§11.1): every arrow out of the world (`nec`, row 1, carrier
    `□□A`) or the extent of a witness `y` (`pos`, row 2, carrier `◇□A`). -/
inductive OutLeg (Γ : Ctx) where
  | nec
  | pos (y : VarSymb) (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y))

namespace OutLeg

variable {σ : Signature} {Γ : Ctx}

/-- The leg of the `Back` atom. -/
def leg : OutLeg Γ → BLeg
  | .nec => .nec
  | .pos _ _ => .pos

/-- The view at the far end of the out leg. -/
def view : OutLeg Γ → Ctx
  | .nec => Γ.boxIn
  | .pos y _ => Γ.diaIn y

instance instNoSlots [Γ.NoSlots] {O : OutLeg Γ} : O.view.NoSlots := by
  cases O <;> (dsimp only [view]; infer_instance)

theorem slotsFrom {d : ℕ} (h : Γ.SlotsFrom d) : (O : OutLeg Γ) → O.view.SlotsFrom d
  | .nec => h.boxIn
  | .pos y _ => h.diaIn y

/-- Some arrow of the leg: `◇` or `◇_y`. -/
def dia {d : ℕ} : (O : OutLeg Γ) → WFF σ O.view d → WFF σ Γ d
  | .nec, φ => (WFF.box φ.neg).neg
  | .pos y hy, φ => WFF.dia y hy φ

/-- Every arrow of the leg: `□` or `□_y`. -/
def box {d : ℕ} : (O : OutLeg Γ) → WFF σ O.view d → WFF σ Γ d
  | .nec, φ => WFF.box φ
  | .pos y hy, φ => WFF.boxx y hy φ

/-- ⭐The `Back` atom of the carrier with body `bd` — `boxtm (boxtm bd)` or `diatm y (boxtm bd)`:
    every term of type `□□A` or `◇□A` has this shape, so the rules are stated at the body and
    survive substitution (§10.11). -/
def back {d : ℕ} (hS : ModalSys.BStrong = true) : (O : OutLeg Γ) → {A : VarType} →
    {a₀ : Ann A} → Term σ O.view.boxIn A a₀ → {a : Ann A} → Term σ Γ A a →
    WFF σ Γ d
  | .nec, _, _, bd, _, t => WFF.back hS .nec (Term.boxtm (Term.boxtm bd)) t
  | .pos y hy, _, _, bd, _, t => WFF.back hS .pos (Term.diatm y hy (Term.boxtm bd)) t

/-- The atom depends on its terms only as dependent pairs. -/
theorem back_congr {d : ℕ} (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    {a₁ a₂ : Ann A} {bd₁ : Term σ O.view.boxIn A a₁}
    {bd₂ : Term σ O.view.boxIn A a₂}
    (hbd : (⟨a₁, bd₁⟩ : Σ b, Term σ O.view.boxIn A b) = ⟨a₂, bd₂⟩) {c₁ c₂ : Ann A}
    {t₁ : Term σ Γ A c₁} {t₂ : Term σ Γ A c₂} (ht : (⟨c₁, t₁⟩ : Σ b, Term σ Γ A b) = ⟨c₂, t₂⟩) :
    (O.back hS bd₁ t₁ : WFF σ Γ d) = O.back hS bd₂ t₂ := by
  cases hbd
  cases ht
  rfl

/-- The `□` view lies inside the leg's view. -/
theorem le_view : (O : OutLeg Γ) → Γ.boxIn.Le O.view
  | .nec => Ctx.Le.refl _
  | .pos y _ => Ctx.le_boxIn_diaIn Γ y

/-- A returning possibility's body read at the far end of the leg, with the carrier's image `c` in
    its slot: what the bridging rule asks to be possible (`Proof.ret_bridge`). -/
def bodyRead [Γ.NoSlots] (O : OutLeg Γ) {A : VarType} {b : Ann (.VTypeBox A)}
    (c : Term σ O.view (.VTypeBox A) b) (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1) :
    WFF σ O.view 0 :=
  WFF.instantiate Ctx.NoSlots.slots c (WFF.mono (O.le_view.insert (.bnd 0) _) Φ)

/-- ⭐The **returning possibility along the leg** (§11.17): `◇[e ↦ t] Φ` from any arrow, or
    `◇_y[e ↦ t] Φ` from an arrow of `y`'s extent, with `Φ` read in the leg's view. -/
def retS {d : ℕ} (hS : ModalSys.BStrong = true) : (O : OutLeg Γ) → (S : RShape) →
    {a : Ann S.flat} → Term σ Γ S.flat a → WFF σ (O.view.insert (.bnd d) S.ty) (d + 1) →
    WFF σ Γ d
  | .nec, S, _, t, Φ => WFF.retS hS S t Φ
  | .pos y hy, S, _, t, Φ => WFF.retxS hS y hy S t Φ

/-- The returning possibility of a necessary object along the leg. -/
abbrev ret {d : ℕ} (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) (Φ : WFF σ (O.view.insert (.bnd d) (.VTypeBox A)) (d + 1)) : WFF σ Γ d :=
  O.retS hS (.box A) t Φ

/-- Two returning possibilities of one shape along a leg agree when their values and bodies do. -/
theorem retS_congr {d : ℕ} (hS : ModalSys.BStrong = true) (O : OutLeg Γ) (S : RShape)
    {a a' : Ann S.flat} {t : Term σ Γ S.flat a} {t' : Term σ Γ S.flat a'}
    {Φ Φ' : WFF σ (O.view.insert (.bnd d) S.ty) (d + 1)}
    (ht : (⟨a, t⟩ : Σ a, Term σ Γ S.flat a) = ⟨a', t'⟩) (hΦ : Φ = Φ') :
    (O.retS hS S t Φ : WFF σ Γ d) = O.retS hS S t' Φ' := by
  cases ht
  cases hΦ
  rfl

theorem retS_congr' {d : ℕ} (hS : ModalSys.BStrong = true) (O : OutLeg Γ) (S : RShape)
    {a : Ann S.flat} {t t' : Term σ Γ S.flat a} {Φ Φ' : WFF σ (O.view.insert (.bnd d) S.ty) (d + 1)}
    (ht : t = t') (hΦ : Φ = Φ') : (O.retS hS S t Φ : WFF σ Γ d) = O.retS hS S t' Φ' := by
  rw [ht, hΦ]

/-- A body over the `□` view, read in the leg's view (literally itself for `nec`). -/
def lift {d : ℕ} {T : VarType} : (O : OutLeg Γ) → WFF σ (Γ.boxIn.insert (.bnd d) T) (d + 1) →
    WFF σ (O.view.insert (.bnd d) T) (d + 1)
  | .nec, φ => φ
  | .pos y _, φ => WFF.mono ((Ctx.le_boxIn_diaIn Γ y).insert _ _) φ

/-- The leg in a larger context. -/
def mono {Γ' : Ctx} (h : Γ.Le Γ') : OutLeg Γ → OutLeg Γ'
  | .nec => .nec
  | .pos y hy => .pos y (hy.imp fun _ hY => h.ref hY)

theorem le_view_mono {Γ' : Ctx} (h : Γ.Le Γ') : (O : OutLeg Γ) → O.view.Le (O.mono h).view
  | .nec => h.boxIn
  | .pos y _ => h.diaIn y

/-- Two returning possibilities along a leg agree when their values and bodies do. -/
theorem ret_congr {d : ℕ} (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    {a a' : Ann A} {t : Term σ Γ A a} {t' : Term σ Γ A a'}
    {Φ Φ' : WFF σ (O.view.insert (.bnd d) (.VTypeBox A)) (d + 1)}
    (ht : (⟨a, t⟩ : Σ a, Term σ Γ A a) = ⟨a', t'⟩) (hΦ : Φ = Φ') :
    (O.ret hS t Φ : WFF σ Γ d) = O.ret hS t' Φ' := by
  cases ht
  cases hΦ
  rfl

/-- Two returning possibilities along a leg agree when their values and bodies do, at one
    annotation. -/
theorem ret_congr' {d : ℕ} (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    {a : Ann A} {t t' : Term σ Γ A a} {Φ Φ' : WFF σ (O.view.insert (.bnd d) (.VTypeBox A)) (d + 1)}
    (ht : t = t') (hΦ : Φ = Φ') : (O.ret hS t Φ : WFF σ Γ d) = O.ret hS t' Φ' := by
  rw [ht, hΦ]

theorem mono_retS {Γ' : Ctx} {d : ℕ} (h : Γ.Le Γ') (hS : ModalSys.BStrong = true) :
    (O : OutLeg Γ) → (S : RShape) → {a : Ann S.flat} → (t : Term σ Γ S.flat a) →
    (Φ : WFF σ (O.view.insert (.bnd d) S.ty) (d + 1)) →
    WFF.mono h (O.retS hS S t Φ) =
      (O.mono h).retS hS S (Term.mono h t) (WFF.mono ((le_view_mono h O).insert _ _) Φ)
  | .nec, _, _, _, _ => rfl
  | .pos _ _, _, _, _, _ => rfl

theorem mono_ret {Γ' : Ctx} {d : ℕ} (h : Γ.Le Γ') (hS : ModalSys.BStrong = true) :
    (O : OutLeg Γ) → {A : VarType} → {a : Ann A} → (t : Term σ Γ A a) →
    (Φ : WFF σ (O.view.insert (.bnd d) (.VTypeBox A)) (d + 1)) →
    WFF.mono h (O.ret hS t Φ) =
      (O.mono h).ret hS (Term.mono h t) (WFF.mono ((le_view_mono h O).insert _ _) Φ)
  | .nec, _, _, _, _ => rfl
  | .pos _ _, _, _, _, _ => rfl

/-! ### Substitution -/

section Subst

variable {ι : VarSymb → VarSymb} {Δ : Ctx} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
  (hc : Subst.Coh ι Γ θ)

/-- The leg a substitution sends a leg to: the witness goes where `ι` sends it. -/
def subst : OutLeg Γ → OutLeg Δ
  | .nec => .nec
  | .pos y hy =>
      have hw : (θ.at y).idxAlong [] = ι y := hy.elim fun _ hY => hc y _ hY []
      .pos (ι y) (hy.elim fun _ hY => SubE.ref_witness (Subst.okRef_at hθ hY) hw)

/-- The substitution on the leg's view. -/
def viewSubst : (O : OutLeg Γ) → Subst σ (O.subst θ hθ hc).view
  | .nec => θ.box
  | .pos y _ => θ.dia y (ι y)

theorem viewOk : (O : OutLeg Γ) → Subst.Ok O.view (O.viewSubst θ hθ hc)
  | .nec => Subst.ok_box hθ
  | .pos y hy => Subst.ok_dia hθ hy (hy.elim fun _ hY => hc y _ hY [])

theorem viewCoh : (O : OutLeg Γ) → Subst.Coh ι O.view (O.viewSubst θ hθ hc)
  | .nec => Subst.coh_box hθ hc
  | .pos _ hy => Subst.coh_dia hθ hc hy

theorem subst_dia {d d' : ℕ} (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d') :
    (O : OutLeg Γ) → (φ : WFF σ O.view d) →
    WFF.subst ι θ hθ hc hΓ hΔ (O.dia φ) =
      (O.subst θ hθ hc).dia (WFF.subst ι (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc)
        (O.viewCoh θ hθ hc) (slotsFrom hΓ O) (slotsFrom hΔ _) φ)
  | .nec, _ => rfl
  | .pos _ _, _ => rfl

theorem subst_box {d d' : ℕ} (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d') :
    (O : OutLeg Γ) → (φ : WFF σ O.view d) →
    WFF.subst ι θ hθ hc hΓ hΔ (O.box φ) =
      (O.subst θ hθ hc).box (WFF.subst ι (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc)
        (O.viewCoh θ hθ hc) (slotsFrom hΓ O) (slotsFrom hΔ _) φ)
  | .nec, _ => rfl
  | .pos _ _, _ => rfl

theorem subst_back {d d' : ℕ} (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d')
    (hS : ModalSys.BStrong = true) :
    (O : OutLeg Γ) → {A : VarType} → {a₀ : Ann A} →
    (bd : Term σ O.view.boxIn A a₀) → {a : Ann A} → (t : Term σ Γ A a) →
    WFF.subst ι θ hθ hc hΓ hΔ (O.back hS bd t : WFF σ Γ d) =
      ((O.subst θ hθ hc).back hS
        (Term.subst ι (O.viewSubst θ hθ hc).box (Subst.ok_box (O.viewOk θ hθ hc))
          (Subst.coh_box (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)) bd)
        (Term.subst ι θ hθ hc t) : WFF σ Δ d')
  | .nec, _, _, _, _, _ => rfl
  | .pos _ _, _, _, _, _, _ => rfl

theorem subst_retS {d d' : ℕ} (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d')
    (hS : ModalSys.BStrong = true) :
    (O : OutLeg Γ) → (S : RShape) → {a : Ann S.flat} → (t : Term σ Γ S.flat a) →
    (Φ : WFF σ (O.view.insert (.bnd d) S.ty) (d + 1)) →
    WFF.subst ι θ hθ hc hΓ hΔ (O.retS hS S t Φ) =
      (O.subst θ hθ hc).retS hS S (Term.subst ι θ hθ hc t)
        (WFF.subst (VarSymb.shiftSlot ι d d')
          ((O.viewSubst θ hθ hc).under d d' _ (slotsFrom hΔ (O.subst θ hθ hc)).root)
          (Subst.ok_under (O.viewOk θ hθ hc) _ (slotsFrom hΔ (O.subst θ hθ hc)).root)
          (Subst.coh_under (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc) (slotsFrom hΓ O) _
            (slotsFrom hΔ (O.subst θ hθ hc)).root)
          ((slotsFrom hΓ O).insert _) ((slotsFrom hΔ (O.subst θ hθ hc)).insert _) Φ)
  | .nec, _, _, _, _ => rfl
  | .pos _ _, _, _, _, _ => rfl

theorem subst_ret {d d' : ℕ} (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d')
    (hS : ModalSys.BStrong = true) :
    (O : OutLeg Γ) → {A : VarType} → {a : Ann A} → (t : Term σ Γ A a) →
    (Φ : WFF σ (O.view.insert (.bnd d) (.VTypeBox A)) (d + 1)) →
    WFF.subst ι θ hθ hc hΓ hΔ (O.ret hS t Φ) =
      (O.subst θ hθ hc).ret hS (Term.subst ι θ hθ hc t)
        (WFF.subst (VarSymb.shiftSlot ι d d')
          ((O.viewSubst θ hθ hc).under d d' _ (slotsFrom hΔ (O.subst θ hθ hc)).root)
          (Subst.ok_under (O.viewOk θ hθ hc) _ (slotsFrom hΔ (O.subst θ hθ hc)).root)
          (Subst.coh_under (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc) (slotsFrom hΓ O) _
            (slotsFrom hΔ (O.subst θ hθ hc)).root)
          ((slotsFrom hΓ O).insert _) ((slotsFrom hΔ (O.subst θ hθ hc)).insert _) Φ)
  | .nec, _, _, _, _ => rfl
  | .pos _ _, _, _, _, _ => rfl

end Subst

end OutLeg

/-- ⭐A returning possibility's body along `◇_x`, given as a hole formula `χ` about `x`'s content
    and the bound object together, with the view term `bd` for the content: `χ⟨bd, e⟩`.  The
    leg's counterpart of `WFF.viewReadTm`, and the form in which the own-arrow rules along a
    witness state their body (`Proof.ret_hereXC`, §11.21). -/
def WFF.viewBody {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {X T : VarType} {a : Ann X}
    (bd : Term σ (Γ.diaIn x) X a) (χ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeProd X T)) 1) :
    WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1 :=
  WFF.bodyRepl
    (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root T) bd)
      (Term.eta (.root (.bnd 0)) T (Ctx.ref_insert_root (Γ.diaIn x) (.bnd 0) T)))
    ((OutLeg.pos x hx : OutLeg Γ).lift χ)

end V12M
