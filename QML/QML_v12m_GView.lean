import QML.QML_v12m_GAbs

/-!
# QML v12m — the growing tree: view tuples

Under T, a `◇`-lifted root keeps literally to its lifted term, so its labels carry the child's
paths; for a term that uses a kept content possibility (`z.dia.keep`) the path operations then merge
positions of the root that differ (`docs/v12-modal-extensions.md` §3 4, "⚠ Paper pass: `◇`-lifted
terms break …").  So strong 4's `◇`-lift lifts only the **generic** possible object of each view
(D-H1), and every other possible object is kept from a term pulled back to it:

* `keepItems`: the reachable keepable addresses of a world language; `boxItems`: the declared items
  of its `□` view — `boxItems_spec`, and ⭐`mem_boxItems`: every one is listed;
* `itemsTm`: the tuple of the items' η-expansions;
* ⭐`viewTuple`: `◇_z ⟨η(z.dia), η(item₁), …⟩`, the view tuple of a possible address `z`;
* `LiftAdm`: the terms the chain lifts — necessary terms and view tuples;
* ⭐`pullS`: `z`'s view pulled back to the view of a root `x` lifted to the view tuple
  (`z.dia ↦ x.dia.fst`, the `k`-th item `↦` the `k`-th component of `x.dia.snd`), with `ok_pullS`
  and `coh_pullS` (`pullIdx`).
-/

namespace V12M

variable [ModalSys]

open BArrow

/-! ## Reachable keepable addresses -/

/-- The projection paths out of a type, with where they lead. -/
def VarType.projPaths : VarType → List (List Step × VarType)
  | .VTypeProd A B => ([], .VTypeProd A B) ::
      ((VarType.projPaths A).map (fun q => (Step.fst :: q.1, q.2)) ++
        (VarType.projPaths B).map (fun q => (Step.snd :: q.1, q.2)))
  | .VTypeBox A => ([], .VTypeBox A) ::
      (if ModalSys.T then (VarType.projPaths A).map (fun q => (Step.here :: q.1, q.2)) else [])
  | .Var => [([], .Var)]
  | .VTypeOne => [([], .VTypeOne)]
  | .VTypeDia A => [([], .VTypeDia A)]

theorem VarType.projPaths_spec : ∀ (U : VarType) {q : List Step} {T : VarType},
    (q, T) ∈ U.projPaths → PPath q ∧ U.walk q = some T
  | .VTypeProd A B, q, T, h => by
      simp only [VarType.projPaths, List.mem_cons, List.mem_append, List.mem_map] at h
      rcases h with h | ⟨⟨q', T'⟩, hm, he⟩ | ⟨⟨q', T'⟩, hm, he⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨(fun _ h => nomatch h), rfl⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        obtain ⟨hp, hw⟩ := VarType.projPaths_spec A hm
        exact ⟨fun s hs => (List.mem_cons.mp hs).elim (fun e => e ▸ rfl) (hp s), hw⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        obtain ⟨hp, hw⟩ := VarType.projPaths_spec B hm
        exact ⟨fun s hs => (List.mem_cons.mp hs).elim (fun e => e ▸ rfl) (hp s), hw⟩
  | .VTypeBox A, q, T, h => by
      simp only [VarType.projPaths, List.mem_cons] at h
      rcases h with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨(fun _ h => nomatch h), rfl⟩
      · cases hT : ModalSys.T with
        | false => rw [hT] at h; simp at h
        | true =>
            rw [hT, if_pos rfl, List.mem_map] at h
            obtain ⟨⟨q', T'⟩, hm, he⟩ := h
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
            obtain ⟨hp, hw⟩ := VarType.projPaths_spec A hm
            refine ⟨fun s hs => (List.mem_cons.mp hs).elim (fun e => e ▸ rfl) (hp s), ?_⟩
            change ((VarType.VTypeBox A).step .here).bind _ = _
            simp only [VarType.step, hT, if_true, Option.bind_some]
            exact hw
  | .Var, q, T, h => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp h)
      exact ⟨(fun _ h => nomatch h), rfl⟩
  | .VTypeOne, q, T, h => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp h)
      exact ⟨(fun _ h => nomatch h), rfl⟩
  | .VTypeDia A, q, T, h => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp h)
      exact ⟨(fun _ h => nomatch h), rfl⟩

theorem VarType.mem_projPaths_self : ∀ U : VarType, ([], U) ∈ U.projPaths
  | .VTypeProd _ _ => List.mem_cons_self
  | .VTypeBox _ => List.mem_cons_self
  | .Var => List.mem_cons_self
  | .VTypeOne => List.mem_cons_self
  | .VTypeDia _ => List.mem_cons_self

theorem VarType.mem_projPaths : ∀ (q : List Step) (U : VarType) {T : VarType}, PPath q →
    U.walk q = some T → (q, T) ∈ U.projPaths
  | [], U, T, _, h => by
      cases Option.some.inj h
      exact VarType.mem_projPaths_self U
  | s :: q, U, T, hq, h => by
      have hq' : PPath q := fun s' h => hq s' (List.mem_cons_of_mem _ h)
      change (U.step s).bind (fun V => V.walk q) = some T at h
      cases hV : U.step s with
      | none => rw [hV] at h; cases h
      | some V =>
          rw [hV] at h
          have ih := VarType.mem_projPaths q V hq' h
          cases U <;> cases s <;> simp only [VarType.step] at hV <;> try cases hV
          · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, ih, rfl⟩))
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩))
          · exact absurd (hq _ List.mem_cons_self) (by decide)
          · rename_i A
            split_ifs at hV with hT
            cases hV
            refine List.mem_cons_of_mem _ ?_
            simp only [hT, if_true]
            exact List.mem_map.mpr ⟨_, ih, rfl⟩
          · exact absurd (hq _ List.mem_cons_self) (by decide)

/-- The reachable keepable addresses of a world language, with their types. -/
def keepItems (l : List VarType) : List (VarSymb × VarType) :=
  (List.range l.length).flatMap fun r =>
    ((rootTy l r).projPaths.filter fun q => q.2.keepable).map
      fun q => ((VarSymb.root (.free r)).ext q.1, q.2)

theorem ref_root_lt {l : List VarType} {r : ℕ} (h : r < l.length) :
    (ctxOf l).ref (.root (.free r)) = some (rootTy l r) :=
  (Ctx.ref_nonproj _ rfl).trans (ctxOf_root_lt h)

theorem keepItems_spec (l : List VarType) :
    ∀ e ∈ keepItems l, (ctxOf l).ref e.1 = some e.2 ∧ e.2.keepable = true := by
  intro e he
  simp only [keepItems, List.mem_flatMap, List.mem_range] at he
  obtain ⟨r, hr, he⟩ := he
  rw [List.mem_map] at he
  obtain ⟨q, hq, rfl⟩ := he
  rw [List.mem_filter] at hq
  obtain ⟨hq, hk⟩ := hq
  obtain ⟨q, T⟩ := q
  obtain ⟨hp, hw⟩ := VarType.projPaths_spec _ hq
  refine ⟨?_, by simpa using hk⟩
  rw [Ctx.ref_ext_ppath _ _ _ hp, ref_root_lt hr]
  exact hw

omit [ModalSys] in
theorem ext_append_step (v : VarSymb) (s : Step) :
    ∀ p : List Step, v.ext (p ++ [s]) = (v.ext p).step s := by
  intro p
  induction p generalizing v with
  | nil => rfl
  | cons t p ih => exact ih (.step v t)

omit [ModalSys] in
theorem eq_root_ext : ∀ y : VarSymb, y = (VarSymb.root y.rt).ext y.path
  | .root _ => rfl
  | .step v s => by
      change VarSymb.step v s = (VarSymb.root v.rt).ext (v.path ++ [s])
      rw [ext_append_step, ← eq_root_ext v]

/-- ⭐**Every reachable keepable address of a world language is listed.** -/
theorem mem_keepItems {l : List VarType} {w : VarSymb} {T : VarType}
    (h : (ctxOf l).ref w = some T) (hk : T.keepable = true) : (w, T) ∈ keepItems l := by
  obtain ⟨hp, r, hr⟩ := reach_ppath h
  have hw : w = (VarSymb.root (.free r)).ext w.path := by
    have := eq_root_ext w
    rwa [hr] at this
  rw [hw, Ctx.ref_ext_ppath _ _ _ hp] at h
  cases hU : (ctxOf l).ref (.root (.free r)) with
  | none => rw [hU] at h; cases h
  | some U =>
      rw [hU] at h
      have hlt : r < l.length := by
        by_contra hn
        rw [Ctx.ref_nonproj _ rfl, ctxOf_root, List.getElem?_eq_none (by simpa using hn)] at hU
        cases hU
      rw [ref_root_lt hlt] at hU
      cases Option.some.inj hU
      simp only [keepItems, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter]
      exact ⟨r, hlt, (w.path, T), ⟨VarType.mem_projPaths _ _ hp h, by simpa using hk⟩,
        by rw [← hw]⟩

/-- The declared items of a world language's `□` view, with their types: each reachable keepable
    address kept, and, unless only kept items are visible, each reachable necessary address's
    contents. -/
def boxItems (l : List VarType) : List (VarSymb × VarType) :=
  (keepItems l).flatMap fun e => (VarSymb.step e.1 .keep, e.2) ::
    (if ModalSys.keepOnly then [] else
      match e.2 with
      | .VTypeBox A => [(VarSymb.step e.1 .box, A)]
      | _ => [])

theorem boxItems_spec (hF : ModalSys.Four = true) (l : List VarType) :
    ∀ e ∈ boxItems l, (ctxOf l).boxIn e.1 = some e.2 := by
  intro e he
  simp only [boxItems, List.mem_flatMap, List.mem_cons] at he
  obtain ⟨⟨w, T⟩, hm, he⟩ := he
  obtain ⟨hw, hk⟩ := keepItems_spec l _ hm
  rcases he with rfl | he
  · exact Ctx.boxIn_keep_of' hF hw hk
  · cases hko : ModalSys.keepOnly with
    | true => simp [hko] at he
    | false =>
        simp only [hko, Bool.false_eq_true, if_false] at he
        cases T with
        | VTypeBox A =>
            obtain rfl := List.mem_singleton.mp he
            exact Ctx.boxIn_box_of hko hw
        | _ => simp at he

/-- ⭐**Every declared item of a world language's `□` view is listed.** -/
theorem mem_boxItems {l : List VarType} {v : VarSymb} {T : VarType}
    (h : (ctxOf l).boxIn v = some T) : (v, T) ∈ boxItems l := by
  match v, h with
  | .step u .keep, h =>
      obtain ⟨-, hu, hk⟩ := Ctx.boxIn_keep h
      simp only [boxItems, List.mem_flatMap]
      exact ⟨(u, T), mem_keepItems hu hk, List.mem_cons_self⟩
  | .step u .box, h =>
      obtain ⟨hko, hu⟩ := Ctx.boxIn_box h
      simp only [boxItems, List.mem_flatMap]
      refine ⟨(u, .VTypeBox T), mem_keepItems hu rfl, List.mem_cons_of_mem _ ?_⟩
      simp [hko]
  | .root _, h => cases h
  | .step _ .fst, h => cases h
  | .step _ .snd, h => cases h
  | .step _ .dia, h => cases h
  | .step _ .here, h => cases h

/-! ## View tuples -/

/-- The type of a tuple of items. -/
def itemsTy : List (VarSymb × VarType) → VarType
  | [] => .VTypeOne
  | e :: L => .VTypeProd e.2 (itemsTy L)

/-- The tuple of the items' η-expansions. -/
def itemsTm {σ : Signature} {Γ : Ctx} :
    (L : List (VarSymb × VarType)) → (∀ e ∈ L, Γ.ref e.1 = some e.2) →
      Σ a : Ann (itemsTy L), Term σ Γ (itemsTy L) a
  | [], _ => ⟨_, .unit⟩
  | e :: L, h =>
      ⟨_, .pair (Term.eta e.1 e.2 (h e List.mem_cons_self))
        (itemsTm L (fun e' he' => h e' (List.mem_cons_of_mem _ he'))).2⟩

theorem boxItems_lastProj (l : List VarType) : ∀ e ∈ boxItems l, e.1.lastProj = false := by
  intro e he
  simp only [boxItems, List.mem_flatMap, List.mem_cons] at he
  obtain ⟨⟨w, T⟩, -, he⟩ := he
  rcases he with rfl | he
  · rfl
  · split_ifs at he
    · simp at he
    · split at he
      · obtain rfl := List.mem_singleton.mp he
        rfl
      · simp at he

theorem boxItems_ref (hF : ModalSys.Four = true) (l : List VarType) :
    ∀ e ∈ boxItems l, (ctxOf l).boxIn.ref e.1 = some e.2 := fun e he =>
  (Ctx.ref_nonproj _ (boxItems_lastProj l e he)).trans (boxItems_spec hF l e he)

/-! ## Pulling a view back to a view tuple's root -/

/-- Where the `k`-th item sits in a tuple of items. -/
def itemPath : ℕ → List Step
  | 0 => [.fst]
  | k + 1 => .snd :: itemPath k

omit [ModalSys] in
theorem itemPath_ppath : ∀ k : ℕ, PPath (itemPath k)
  | 0 => fun s hs => by rw [List.mem_singleton.mp hs]; rfl
  | k + 1 => fun s hs => (List.mem_cons.mp hs).elim (fun e => e ▸ rfl) (itemPath_ppath k s)

theorem itemsTy_walk : ∀ (L : List (VarSymb × VarType)) (k : ℕ) (hk : k < L.length),
    (itemsTy L).walk (itemPath k) = some L[k].2
  | _ :: _, 0, _ => rfl
  | _ :: L, k + 1, hk => itemsTy_walk L k (by simpa using hk)

/-- Split a path at its first level step. -/
def Step.splitLvl : List Step → Option (List Step × Step × List Step)
  | [] => none
  | s :: p =>
      if s.isProj then (Step.splitLvl p).map fun q => (s :: q.1, q.2.1, q.2.2) else some ([], s, p)

omit [ModalSys] in
theorem Step.splitLvl_append : ∀ {pre : List Step} (_ : PPath pre) {s : Step} (_ : s.isProj = false)
    (q : List Step), Step.splitLvl (pre ++ s :: q) = some (pre, s, q)
  | [], _, s, hs, q => by simp [Step.splitLvl, hs]
  | t :: pre, hp, s, hs, q => by
      have ht : t.isProj = true := hp t List.mem_cons_self
      simp only [List.cons_append, Step.splitLvl, ht, if_true]
      rw [Step.splitLvl_append (fun s' h => hp s' (List.mem_cons_of_mem _ h)) hs q]
      rfl

/-- ⭐**The pull-back of `z`'s view** to the view of a root `x` whose content is `z`'s view tuple:
    `z.dia ↦ x.dia.fst`, the `k`-th item of the `□` view `↦` the `k`-th item of `x.dia.snd`. -/
def pullS {σ : Signature} {Δ : Ctx} (l : List VarType) (z x : VarSymb) : Subst σ Δ := fun v =>
  if v = .step z .dia then .ren (x.ext [.dia, .fst])
  else if (boxItems l).any (·.1 == v) then
    .ren (x.ext (.dia :: .snd :: itemPath ((boxItems l).findIdx (·.1 == v))))
  else .hide

/-- Where the pull-back sends annotation indices: by the address the index's first level step
    leaves from. -/
def pullIdx (l : List VarType) (z x : VarSymb) (y : VarSymb) : VarSymb :=
  match Step.splitLvl y.path with
  | some (pre, s, q) =>
      if s = .dia then
        (if (VarSymb.root y.rt).ext pre = z then x.ext (.dia :: .fst :: q) else y)
      else x.ext (.dia :: .snd ::
        (itemPath ((boxItems l).findIdx (·.1 == ((VarSymb.root y.rt).ext pre).step s)) ++ q))
  | none => y

theorem pullS_dia {σ : Signature} {Δ : Ctx} (l : List VarType) (z x : VarSymb) :
    pullS (σ := σ) (Δ := Δ) l z x (.step z .dia) = .ren (x.ext [.dia, .fst]) :=
  if_pos rfl

theorem pullS_item {σ : Signature} {Δ : Ctx} {l : List VarType} {z x v : VarSymb}
    (hvz : v ≠ .step z .dia) (hany : (boxItems l).any (·.1 == v) = true) :
    pullS (σ := σ) (Δ := Δ) l z x v =
      .ren (x.ext (.dia :: .snd :: itemPath ((boxItems l).findIdx (·.1 == v)))) :=
  (if_neg hvz).trans (if_pos hany)

theorem findIdx_lt_boxItems {l : List VarType} {v : VarSymb} {T : VarType}
    (h : (v, T) ∈ boxItems l) : (boxItems l).findIdx (·.1 == v) < (boxItems l).length :=
  List.findIdx_lt_length_of_exists ⟨_, h, by simp⟩

theorem getElem_findIdx_boxItems {l : List VarType} {v : VarSymb} {T : VarType}
    (h : (v, T) ∈ boxItems l) :
    ((boxItems l)[(boxItems l).findIdx (·.1 == v)]'(findIdx_lt_boxItems h)).1 = v := by
  have := List.findIdx_getElem (w := findIdx_lt_boxItems h)
  simpa using this

theorem ok_pullS (hF : ModalSys.Four = true) {σ : Signature} {Γ : Ctx} {l : List VarType}
    {z x : VarSymb} {Z : VarType} (hz : (ctxOf l).ref z = some (.VTypeDia Z))
    (hx : Γ.ref x = some (.VTypeDia (.VTypeProd Z (itemsTy (boxItems l))))) :
    Subst.Ok ((ctxOf l).diaIn z) (pullS (σ := σ) (Δ := Γ.diaIn x) l z x) := by
  have hxd : (Γ.diaIn x).ref (.step x .dia) = some (.VTypeProd Z (itemsTy (boxItems l))) :=
    Ctx.ref_diaIn_of hx
  intro v T _ hv
  by_cases hvz : v = .step z .dia
  · subst hvz
    have hZ : T = Z := by
      change (if z = z then (match (ctxOf l).ref z with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      rw [if_pos rfl, hz] at hv
      exact (Option.some.inj hv).symm
    subst hZ
    rw [pullS_dia]
    exact Ctx.ref_fst_of hxd
  · have hb : (ctxOf l).boxIn v = some T := by
      match v, hv with
      | .step u .dia, hv =>
          change (if u = z then _ else none) = some T at hv
          split_ifs at hv with h
          · exact absurd (congrArg (VarSymb.step · Step.dia) h) hvz
      | .root _, hv => exact hv
      | .step _ .fst, hv => exact hv
      | .step _ .snd, hv => exact hv
      | .step _ .box, hv => exact hv
      | .step _ .keep, hv => exact hv
      | .step _ .here, hv => exact hv
    have hm := mem_boxItems hb
    have hany : (boxItems l).any (·.1 == v) = true := List.any_eq_true.mpr ⟨_, hm, by simp⟩
    rw [pullS_item hvz hany]
    have hlt := findIdx_lt_boxItems hm
    have hT : ((boxItems l)[(boxItems l).findIdx (·.1 == v)]'hlt).2 = T := by
      have e := boxItems_spec hF l _ (List.getElem_mem hlt)
      rw [getElem_findIdx_boxItems hm, hb] at e
      exact (Option.some.inj e).symm
    change (Γ.diaIn x).ref ((VarSymb.step x .dia).ext (.snd :: itemPath _)) = some T
    rw [Ctx.ref_ext_ppath _ _ _ (fun s hs => (List.mem_cons.mp hs).elim (fun e => e ▸ rfl)
      (itemPath_ppath _ s)), hxd]
    change (itemsTy (boxItems l)).walk (itemPath _) = some T
    rw [itemsTy_walk _ _ hlt, hT]

omit [ModalSys] in
theorem ext_ext : ∀ (v : VarSymb) (p q : List Step), (v.ext p).ext q = v.ext (p ++ q)
  | _, [], _ => rfl
  | v, s :: p, q => ext_ext (.step v s) p q

theorem coh_pullS (hF : ModalSys.Four = true) {σ : Signature} {Γ : Ctx} {l : List VarType}
    {z x : VarSymb} {Z : VarType} (hz : (ctxOf l).ref z = some (.VTypeDia Z))
    (hx : Γ.ref x = some (.VTypeDia (.VTypeProd Z (itemsTy (boxItems l))))) :
    Subst.Coh (pullIdx l z x) ((ctxOf l).diaIn z) (pullS (σ := σ) (Δ := Γ.diaIn x) l z x) := by
  refine Subst.coh_of (ok_pullS hF hz hx) fun v T _ hv p => ?_
  by_cases hvz : v = .step z .dia
  · subst hvz
    rw [pullS_dia]
    change (x.ext [.dia, .fst]).ext p = pullIdx l z x ((VarSymb.step z .dia).ext p)
    have hzp := (reach_ppath hz).1
    unfold pullIdx
    rw [VarSymb.ext_path, VarSymb.ext_rt,
      show (VarSymb.step z .dia).path ++ p = z.path ++ .dia :: p by
        change (z.path ++ [.dia]) ++ p = _
        simp,
      Step.splitLvl_append hzp rfl p]
    simp only [VarSymb.rt, ← eq_root_ext, if_true]
    rfl
  · have hb : (ctxOf l).boxIn v = some T := by
      match v, hv with
      | .step u .dia, hv =>
          change (if u = z then _ else none) = some T at hv
          split_ifs at hv with h
          · exact absurd (congrArg (VarSymb.step · Step.dia) h) hvz
      | .root _, hv => exact hv
      | .step _ .fst, hv => exact hv
      | .step _ .snd, hv => exact hv
      | .step _ .box, hv => exact hv
      | .step _ .keep, hv => exact hv
      | .step _ .here, hv => exact hv
    have hm := mem_boxItems hb
    have hany : (boxItems l).any (·.1 == v) = true := List.any_eq_true.mpr ⟨_, hm, by simp⟩
    rw [pullS_item hvz hany]
    change (x.ext _).ext p = _
    rw [ext_ext]
    obtain ⟨u, s, rfl, hs, hsd, hu⟩ : ∃ u s, v = .step u s ∧ s.isProj = false ∧ s ≠ .dia ∧
        PPath u.path := by
      match v, hb with
      | .step u .keep, hb =>
          exact ⟨u, .keep, rfl, rfl, by decide, (reach_ppath (Ctx.boxIn_keep hb).2.1).1⟩
      | .step u .box, hb =>
          exact ⟨u, .box, rfl, rfl, by decide, (reach_ppath (Ctx.boxIn_box hb).2).1⟩
      | .root _, hb => cases hb
      | .step _ .fst, hb => cases hb
      | .step _ .snd, hb => cases hb
      | .step _ .dia, hb => cases hb
      | .step _ .here, hb => cases hb
    unfold pullIdx
    rw [VarSymb.ext_path, VarSymb.ext_rt,
      show (VarSymb.step u s).path ++ p = u.path ++ s :: p by
        change (u.path ++ [s]) ++ p = _
        simp,
      Step.splitLvl_append hu hs p]
    simp only [if_neg hsd, VarSymb.rt, ← eq_root_ext]
    simp

/-! ## Pulling the `□` view back to a `□` view tuple's root -/

/-- ⭐**The pull-back of the `□` view** to the `□` view of a root `r` whose value is the `□` view
    tuple: the `k`-th item `↦` the `k`-th component of `r`'s contents. -/
def pullBoxS {σ : Signature} {Δ : Ctx} (l : List VarType) (r : VarSymb) : Subst σ Δ := fun v =>
  if (boxItems l).any (·.1 == v) then
    .ren (r.inner.ext (itemPath ((boxItems l).findIdx (·.1 == v))))
  else .hide

/-- Where the `□` pull-back sends annotation indices. -/
def pullBoxIdx (l : List VarType) (r : VarSymb) (y : VarSymb) : VarSymb :=
  match Step.splitLvl y.path with
  | some (pre, s, q) =>
      r.inner.ext
        (itemPath ((boxItems l).findIdx (·.1 == ((VarSymb.root y.rt).ext pre).step s)) ++ q)
  | none => y

theorem pullBoxS_item {σ : Signature} {Δ : Ctx} {l : List VarType} {r v : VarSymb}
    (hany : (boxItems l).any (·.1 == v) = true) :
    pullBoxS (σ := σ) (Δ := Δ) l r v =
      .ren (r.inner.ext (itemPath ((boxItems l).findIdx (·.1 == v)))) :=
  if_pos hany

theorem ok_pullBoxS (hF : ModalSys.Four = true) {σ : Signature} {Γ : Ctx} {l : List VarType}
    {r : VarSymb} (hr : Γ.ref r = some (.VTypeBox (itemsTy (boxItems l)))) :
    Subst.Ok (ctxOf l).boxIn (pullBoxS (σ := σ) (Δ := Γ.boxIn) l r) := by
  intro v T _ hb
  have hm := mem_boxItems hb
  have hany : (boxItems l).any (·.1 == v) = true := List.any_eq_true.mpr ⟨_, hm, by simp⟩
  rw [pullBoxS_item hany]
  have hlt := findIdx_lt_boxItems hm
  have hT : ((boxItems l)[(boxItems l).findIdx (·.1 == v)]'hlt).2 = T := by
    have e := boxItems_spec hF l _ (List.getElem_mem hlt)
    rw [getElem_findIdx_boxItems hm, hb] at e
    exact (Option.some.inj e).symm
  change Γ.boxIn.ref (r.inner.ext (itemPath _)) = some T
  rw [Ctx.ref_ext_ppath _ _ _ (itemPath_ppath _), Ctx.ref_inner hr]
  change (itemsTy (boxItems l)).walk (itemPath _) = some T
  rw [itemsTy_walk _ _ hlt, hT]

theorem coh_pullBoxS (hF : ModalSys.Four = true) {σ : Signature} {Γ : Ctx} {l : List VarType}
    {r : VarSymb} (hr : Γ.ref r = some (.VTypeBox (itemsTy (boxItems l)))) :
    Subst.Coh (pullBoxIdx l r) (ctxOf l).boxIn (pullBoxS (σ := σ) (Δ := Γ.boxIn) l r) := by
  refine Subst.coh_of (ok_pullBoxS hF hr) fun v T _ hb p => ?_
  have hm := mem_boxItems hb
  have hany : (boxItems l).any (·.1 == v) = true := List.any_eq_true.mpr ⟨_, hm, by simp⟩
  rw [pullBoxS_item hany]
  change (r.inner.ext _).ext p = _
  rw [ext_ext]
  obtain ⟨u, s, rfl, hs, hu⟩ : ∃ u s, v = .step u s ∧ s.isProj = false ∧ PPath u.path := by
    match v, hb with
    | .step u .keep, hb => exact ⟨u, .keep, rfl, rfl, (reach_ppath (Ctx.boxIn_keep hb).2.1).1⟩
    | .step u .box, hb => exact ⟨u, .box, rfl, rfl, (reach_ppath (Ctx.boxIn_box hb).2).1⟩
    | .root _, hb => cases hb
    | .step _ .fst, hb => cases hb
    | .step _ .snd, hb => cases hb
    | .step _ .dia, hb => cases hb
    | .step _ .here, hb => cases hb
  unfold pullBoxIdx
  rw [VarSymb.ext_path, VarSymb.ext_rt,
    show (VarSymb.step u s).path ++ p = u.path ++ s :: p by
      change (u.path ++ [s]) ++ p = _
      simp,
    Step.splitLvl_append hu hs p]
  simp only [VarSymb.rt, ← eq_root_ext]

/-! ## Pulling a view back to a lifted possible address and the `□` view tuple (D-H3) -/

/-- ⭐**The pull-back of `z`'s view** to the view of a root `x` lifted to `η(z)`, the items of the
    `□` view read from a root `r` lifted to the `□` view tuple: `z.dia ↦ x.dia`, the `k`-th item
    `↦` the `k`-th component of `r`'s contents. -/
def pullD {σ : Signature} {Δ : Ctx} (l : List VarType) (z x r : VarSymb) : Subst σ Δ := fun v =>
  if v = .step z .dia then .ren (.step x .dia)
  else if (boxItems l).any (·.1 == v) then
    .ren (r.inner.ext (itemPath ((boxItems l).findIdx (·.1 == v))))
  else .hide

/-- Where the pull-back sends annotation indices. -/
def pullDIdx (l : List VarType) (z x r : VarSymb) (y : VarSymb) : VarSymb :=
  match Step.splitLvl y.path with
  | some (pre, s, q) =>
      if s = .dia then
        (if (VarSymb.root y.rt).ext pre = z then x.ext (.dia :: q) else y)
      else r.inner.ext
        (itemPath ((boxItems l).findIdx (·.1 == ((VarSymb.root y.rt).ext pre).step s)) ++ q)
  | none => y

theorem pullD_dia {σ : Signature} {Δ : Ctx} (l : List VarType) (z x r : VarSymb) :
    pullD (σ := σ) (Δ := Δ) l z x r (.step z .dia) = .ren (.step x .dia) :=
  if_pos rfl

theorem pullD_item {σ : Signature} {Δ : Ctx} {l : List VarType} {z x r v : VarSymb}
    (hvz : v ≠ .step z .dia) (hany : (boxItems l).any (·.1 == v) = true) :
    pullD (σ := σ) (Δ := Δ) l z x r v =
      .ren (r.inner.ext (itemPath ((boxItems l).findIdx (·.1 == v)))) :=
  (if_neg hvz).trans (if_pos hany)

/-- The declared addresses of a `◇` view other than its content are the `□` view's. -/
theorem diaIn_boxIn_of_ne' {Γ : Ctx} {z v : VarSymb} {T : VarType} (hv : Γ.diaIn z v = some T)
    (hvz : v ≠ .step z .dia) : Γ.boxIn v = some T := by
  match v, hv with
  | .step u .dia, hv =>
      change (if u = z then _ else none) = some T at hv
      split_ifs at hv with h
      · exact absurd (congrArg (VarSymb.step · Step.dia) h) hvz
  | .root _, hv => exact hv
  | .step _ .fst, hv => exact hv
  | .step _ .snd, hv => exact hv
  | .step _ .box, hv => exact hv
  | .step _ .keep, hv => exact hv
  | .step _ .here, hv => exact hv

theorem ok_pullD (hF : ModalSys.Four = true) {σ : Signature} {Γ : Ctx} {l : List VarType}
    {z x r : VarSymb} {Z : VarType} (hz : (ctxOf l).ref z = some (.VTypeDia Z))
    (hx : Γ.ref x = some (.VTypeDia Z))
    (hr : Γ.ref r = some (.VTypeBox (itemsTy (boxItems l)))) :
    Subst.Ok ((ctxOf l).diaIn z) (pullD (σ := σ) (Δ := Γ.diaIn x) l z x r) := by
  intro v T _ hv
  by_cases hvz : v = .step z .dia
  · subst hvz
    have hZ : T = Z := by
      change (if z = z then (match (ctxOf l).ref z with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      rw [if_pos rfl, hz] at hv
      exact (Option.some.inj hv).symm
    subst hZ
    rw [pullD_dia]
    exact Ctx.ref_diaIn_of hx
  · have hb := diaIn_boxIn_of_ne' hv hvz
    have hm := mem_boxItems hb
    have hany : (boxItems l).any (·.1 == v) = true := List.any_eq_true.mpr ⟨_, hm, by simp⟩
    rw [pullD_item hvz hany]
    have hlt := findIdx_lt_boxItems hm
    have hT : ((boxItems l)[(boxItems l).findIdx (·.1 == v)]'hlt).2 = T := by
      have e := boxItems_spec hF l _ (List.getElem_mem hlt)
      rw [getElem_findIdx_boxItems hm, hb] at e
      exact (Option.some.inj e).symm
    change (Γ.diaIn x).ref (r.inner.ext (itemPath _)) = some T
    rw [Ctx.ref_ext_ppath _ _ _ (itemPath_ppath _),
      (Ctx.le_boxIn_diaIn Γ x).ref (Ctx.ref_inner hr)]
    change (itemsTy (boxItems l)).walk (itemPath _) = some T
    rw [itemsTy_walk _ _ hlt, hT]

theorem coh_pullD (hF : ModalSys.Four = true) {σ : Signature} {Γ : Ctx} {l : List VarType}
    {z x r : VarSymb} {Z : VarType} (hz : (ctxOf l).ref z = some (.VTypeDia Z))
    (hx : Γ.ref x = some (.VTypeDia Z))
    (hr : Γ.ref r = some (.VTypeBox (itemsTy (boxItems l)))) :
    Subst.Coh (pullDIdx l z x r) ((ctxOf l).diaIn z)
      (pullD (σ := σ) (Δ := Γ.diaIn x) l z x r) := by
  refine Subst.coh_of (ok_pullD hF hz hx hr) fun v T _ hv p => ?_
  by_cases hvz : v = .step z .dia
  · subst hvz
    rw [pullD_dia]
    change (VarSymb.step x .dia).ext p = pullDIdx l z x r ((VarSymb.step z .dia).ext p)
    have hzp := (reach_ppath hz).1
    unfold pullDIdx
    rw [VarSymb.ext_path, VarSymb.ext_rt,
      show (VarSymb.step z .dia).path ++ p = z.path ++ .dia :: p by
        change (z.path ++ [.dia]) ++ p = _
        simp,
      Step.splitLvl_append hzp rfl p]
    simp only [VarSymb.rt, ← eq_root_ext, if_true]
    rfl
  · have hb := diaIn_boxIn_of_ne' hv hvz
    have hm := mem_boxItems hb
    have hany : (boxItems l).any (·.1 == v) = true := List.any_eq_true.mpr ⟨_, hm, by simp⟩
    rw [pullD_item hvz hany]
    change (r.inner.ext _).ext p = _
    rw [ext_ext]
    obtain ⟨u, s, rfl, hs, hsd, hu⟩ : ∃ u s, v = .step u s ∧ s.isProj = false ∧ s ≠ .dia ∧
        PPath u.path := by
      match v, hb with
      | .step u .keep, hb =>
          exact ⟨u, .keep, rfl, rfl, by decide, (reach_ppath (Ctx.boxIn_keep hb).2.1).1⟩
      | .step u .box, hb =>
          exact ⟨u, .box, rfl, rfl, by decide, (reach_ppath (Ctx.boxIn_box hb).2).1⟩
      | .root _, hb => cases hb
      | .step _ .fst, hb => cases hb
      | .step _ .snd, hb => cases hb
      | .step _ .dia, hb => cases hb
      | .step _ .here, hb => cases hb
    unfold pullDIdx
    rw [VarSymb.ext_path, VarSymb.ext_rt,
      show (VarSymb.step u s).path ++ p = u.path ++ s :: p by
        change (u.path ++ [s]) ++ p = _
        simp,
      Step.splitLvl_append hu hs p]
    simp only [if_neg hsd, VarSymb.rt, ← eq_root_ext]

namespace GArrow

/-- ⭐**The view tuple** of a possible address `z` of a world language: under `◇_z`, its content
    beside the language's kept items — the generic possible object of `z`'s view. -/
def viewTuple (hF : ModalSys.Four = true) {σ : Signature} (l : List VarType) (z : VarSymb)
    (Z : VarType) (hz : (ctxOf l).ref z = some (.VTypeDia Z)) : LTerm σ :=
  ⟨l, .VTypeDia (.VTypeProd Z (itemsTy (boxItems l))), _,
    .diatm z ⟨Z, hz⟩ (.pair (Term.eta (.step z .dia) Z (Ctx.ref_diaIn_of hz))
      (Term.mono (Ctx.le_boxIn_diaIn _ z) (itemsTm (boxItems l) (boxItems_ref hF l)).2))⟩

/-- ⭐**The `□` view tuple** of a world language: the tuple of its `□` view's items, under `□` —
    the generic necessary object of the `□` view. -/
def boxTuple (hF : ModalSys.Four = true) {σ : Signature} (l : List VarType) : LTerm σ :=
  ⟨l, .VTypeBox (itemsTy (boxItems l)), _, .boxtm (itemsTm (boxItems l) (boxItems_ref hF l)).2⟩

/-- The η-expansion of a possible address of a world language, as a lifted term. -/
def etaTerm {σ : Signature} (l : List VarType) (z : VarSymb) (Z : VarType)
    (hz : (ctxOf l).ref z = some (.VTypeDia Z)) : LTerm σ :=
  ⟨l, .VTypeDia Z, _, Term.eta z (.VTypeDia Z) hz⟩

/-- The η-expansion of a necessary address of a world language, as a lifted term. -/
def etaBox {σ : Signature} (l : List VarType) (z : VarSymb) (A : VarType)
    (hz : (ctxOf l).ref z = some (.VTypeBox A)) : LTerm σ :=
  ⟨l, .VTypeBox A, _, Term.eta z (.VTypeBox A) hz⟩

/-- ⭐**The terms strong 4 lifts: generators** (`docs/v12-modal-extensions.md` §3 4, D-H3) — the
    `□` view tuple, and the η-expansion of a possible address; and, only when the `□`-lift is off
    (the parent then cannot name the child's necessary data), view tuples (D-H1).  Under 5 (T off)
    also the η-expansion of a necessary address: there every object is named once, by its origin,
    so addresses are lifted one by one and terms not at all (docs §3 5, names by origin (N1)). -/
def LiftAdm (hF : ModalSys.Four = true) {σ : Signature} (e : LTerm σ) : Prop :=
  e = boxTuple hF e.1 ∨ (∃ z Z hz, e = etaTerm e.1 z Z hz) ∨
    (ModalSys.FourStrong = false ∧ ∃ z Z hz, e = viewTuple hF e.1 z Z hz) ∨
    (ModalSys.Five = true ∧ ModalSys.T = false ∧ ∃ z A hz, e = etaBox e.1 z A hz)

/-- Under T the generators are the three of D-H3. -/
theorem LiftAdm.of_T (hF : ModalSys.Four = true) {σ : Signature} {e : LTerm σ}
    (hT : ModalSys.T = true) (h : LiftAdm hF e) :
    e = boxTuple hF e.1 ∨ (∃ z Z hz, e = etaTerm e.1 z Z hz) ∨
      (ModalSys.FourStrong = false ∧ ∃ z Z hz, e = viewTuple hF e.1 z Z hz) :=
  h.imp_right (Or.imp_right fun h => h.resolve_right fun h' => by
    rw [hT] at h'
    exact Bool.noConfusion h'.2.1)

theorem liftAdm_boxTuple (hF : ModalSys.Four = true) {σ : Signature} (l : List VarType) :
    LiftAdm hF (boxTuple (σ := σ) hF l) :=
  .inl rfl

theorem liftAdm_etaTerm (hF : ModalSys.Four = true) {σ : Signature} (l : List VarType)
    (z : VarSymb) (Z : VarType) (hz : (ctxOf l).ref z = some (.VTypeDia Z)) :
    LiftAdm hF (etaTerm (σ := σ) l z Z hz) :=
  .inr (.inl ⟨z, Z, hz, rfl⟩)

theorem liftAdm_viewTuple (hF : ModalSys.Four = true) {σ : Signature}
    (hS : ModalSys.FourStrong = false) (l : List VarType) (z : VarSymb) (Z : VarType)
    (hz : (ctxOf l).ref z = some (.VTypeDia Z)) :
    LiftAdm hF (viewTuple (σ := σ) hF l z Z hz) :=
  .inr (.inr (.inl ⟨hS, z, Z, hz, rfl⟩))

theorem liftAdm_etaBox (hF : ModalSys.Four = true) {σ : Signature}
    (hV : ModalSys.Five = true) (hT : ModalSys.T = false) (l : List VarType) (z : VarSymb)
    (A : VarType) (hz : (ctxOf l).ref z = some (.VTypeBox A)) :
    LiftAdm hF (etaBox (σ := σ) l z A hz) :=
  .inr (.inr (.inr ⟨hV, hT, z, A, hz, rfl⟩))

end GArrow

end V12M
