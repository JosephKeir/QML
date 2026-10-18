import QML.QML_v12m_BStepC

/-!
# QML v12m — the born root's arrangements, as hole terms (strong B with T)

A born root `□A` comes home with all its companions as a root `y : bc(□A)` (the back arrow
`c ↦ y`), and the obligation's value is `unarrT y`, the value with companions read off `y`'s
components (docs §11.21, item 6).  To make an obligation out of a user's atom, a value `W` with
companions is aliased as its tuple `arr W` (`arrB`, from `arrT`) and moved to `unarrT y`.  The
move needs `unarr` at any term, not only at a root:

* `unarrAt w`: `unarrT` with its root replaced by `w`;
* ⭐`unarrAt_eta`: at a root's η-expansion it is `unarrT`;
* ⭐`unarrAt_arrB`: the **arrangement identity**, `unarr(arr W) = W` (read with `getP`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

omit [ModalSys.NoFour] in
/-- The root of `[bc(□A)]`. -/
theorem bc_root_ref (A : VarType) :
    (ctxOf [(VarType.VTypeBox A).bc]).ref (.root (.free 0)) = some (VarType.VTypeBox A).bc :=
  ctxOf_ref_new _ []

/-- ⭐**`unarr` at a term**: the value with companions read off `w`'s components — `unarrT` at the
    root of `[bc(□A)]`, with `w` put for the root. -/
def unarrAt {Γ : Ctx} (A : VarType) {a : Ann (VarType.VTypeBox A).bc}
    (w : Term σ Γ (VarType.VTypeBox A).bc a) :
    Σ c, Term σ Γ (A.compsFlat (bornComps A)) c :=
  ⟨_, Term.subst (Subst.singleIdx (.free 0) (.tm w)) (Subst.single (.free 0) (.tm w))
    (Subst.ok_single (Ctx.empty_le Γ) rfl)
    (Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le Γ) rfl)
    (unarrT (σ := σ) (bc_root_ref A)).2⟩

/-- ⭐**`arr` as a hole term**: a value with companions' tuple, as the root `y` it is aliased by
    (`arrT`'s second component). -/
def arrB (A : VarType) :
    Σ c, Term σ (Ctx.empty.insert (.bnd 0) (A.compsFlat (bornComps A))) (VarType.VTypeBox A).bc c :=
  ⟨_, Term.holeAt (arrT A).2 (Term.eta (.step (.root (.bnd 0)) .snd) _
    (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)))⟩

/-! ## `unarr` at a root -/

omit [ModalSys.NoFour] in
/-- The renaming of `[bc(□A)]`'s root to a root `y`. -/
theorem sim_single_eta {Δ : Ctx} {y : VarSymb} {T : VarType} (hy : Δ.ref y = some T) :
    Subst.Sim (Ctx.empty.insert (.free 0) T)
      (Subst.single (σ := σ) (Δ := Δ) (.free 0) (.tm (Term.eta y T hy)))
      (Subst.single (.free 0) (.ren y)) := by
  refine Subst.sim_of fun v U _ hv => ?_
  by_cases hvr : v = .root (.free 0)
  · subst hvr
    obtain rfl : T = U := by simpa [Ctx.insert] using hv
    rw [Subst.single_root, Subst.single_root]
    exact .eta_ren _ _
  · exact absurd hv (by simp [Ctx.insert, hvr, Ctx.empty])

/-- ⭐`unarr` at a root's η-expansion is `unarrT`: the root put for `[bc(□A)]`'s root, then the
    back arrow there, is the back arrow to the root. -/
theorem unarrAt_eta {l : List VarType} {A : VarType} {y : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) :
    (⟨_, (unarrAt (σ := σ) A (Term.eta (.root (.free y)) _ hy)).2⟩ :
      Σ c, Term σ (ctxOf l) (A.compsFlat (bornComps A)) c) = unarrT hy := by
  unfold unarrAt unarrT
  have hok : Subst.Ok (Ctx.empty.insert (.free 0) (VarType.VTypeBox A).bc)
      (Subst.single (σ := σ) (Δ := ctxOf l) (.free 0) (.ren (.root (.free y)))) :=
    Subst.ok_single (Ctx.empty_le _) hy
  have hcoh : Subst.Coh (Subst.singleIdx (.free 0) (.ren (.root (.free y))))
      (Ctx.empty.insert (.free 0) (VarType.VTypeBox A).bc)
      (Subst.single (σ := σ) (Δ := ctxOf l) (.free 0) (.ren (.root (.free y)))) :=
    Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le _) hy
  refine (Term.subst_congr _ _ _ hok _ hcoh (sim_single_eta hy) _).trans ?_
  refine Term.subst_comp_sig _ _ _ _ _ hok hcoh (ok_arrowS (retBackImg l A hy))
    (coh_arrowS (retBackImg l A hy)) (Subst.sim_of fun v T _ hv => ?_) _
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  obtain ⟨r, hr, hlt, -⟩ := ref_rt hu
  obtain rfl : r = 0 := by simpa using hlt
  change SubE.Sim T (.ren (itemImg (fun _ => y) u))
    ((Subst.single (.free 0) (.ren (.root (.free y)))).at (itemImg (fun _ => 0) u))
  rw [itemImg, itemImg, hr]
  change SubE.Sim T (.ren (itemAt (.free y) u)) ((Subst.single _ _).at (itemAt (.free 0) u))
  unfold itemAt
  rw [Subst.at_ext_ren _ _ (by rw [Subst.at_nonproj _ rfl, Subst.single_root])
    (fun s hs => ?_)]
  · exact .refl _
  · rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
      exact (reach_ppath hu).1 s' hs' |> fun h => by
        unfold encStep
        split
        · split <;> first | rfl | exact h
        · exact h
    · unfold itemTail at hs
      split at hs
      · rw [List.mem_singleton.mp hs]; rfl
      · exact absurd hs List.not_mem_nil

/-! ## Reading the arrangements -/

omit [ModalSys.NoFour] in
theorem itemTail_true (hT : ModalSys.T = true) : itemTail = [.fst] := by
  simp [itemTail, hT]

omit [ModalSys.NoFour] in
theorem itemTail_false (hT : ModalSys.T = false) : itemTail = [] := by
  simp [itemTail, hT]

omit [ModalSys.NoFour] in
/-- A tree of items read at a companion path (encoded), then its first component: that leaf. -/
theorem getP_bcTree (hT : ModalSys.T = true) {Γ : Ctx} : ∀ (Z : VarType)
    (get : ∀ q, q ∈ Z.hereChains → Σ c, Term σ Γ ((Z.compAt q).getD .VTypeOne) c)
    (q : List Step) (hq : q ∈ Z.hereChains),
    (bcTree Z get).2.getP (encPath q ++ [.fst]) = some ⟨_, _, (get q hq).2⟩
  | .VTypeBox C, get, q, hq => by
      rcases List.mem_cons.mp hq with rfl | hq'
      · change (Term.pair _ _).getP (.fst :: []) = _
        rw [getP_pair_fst, getP_nil]
        rfl
      · obtain ⟨q', hq'', rfl⟩ := List.mem_map.mp hq'
        change (Term.pair _ _).getP (encStep .here :: (encPath q' ++ [.fst])) = _
        rw [encStep_here hT, getP_pair_snd]
        exact getP_bcTree hT C _ q' hq''
  | .VTypeProd X Y, get, q, hq => by
      rcases List.mem_append.mp hq with hq' | hq'
      · obtain ⟨q', hq'', rfl⟩ := List.mem_map.mp hq'
        change (Term.pair _ _).getP (encStep .fst :: (encPath q' ++ [.fst])) = _
        rw [encStep_fst, getP_pair_fst]
        exact getP_bcTree hT X _ q' hq''
      · obtain ⟨q', hq'', rfl⟩ := List.mem_map.mp hq'
        change (Term.pair _ _).getP (encStep .snd :: (encPath q' ++ [.fst])) = _
        rw [encStep_snd, getP_pair_snd]
        exact getP_bcTree hT Y _ q' hq''
  | .Var, _, _, hq => absurd hq List.not_mem_nil
  | .VTypeOne, _, _, hq => absurd hq List.not_mem_nil
  | .VTypeDia _, _, _, hq => absurd hq List.not_mem_nil

omit [ModalSys.NoFour] in
/-- `tupC`'s value under T, read past its companions: its own value. -/
theorem getP_tupCVal_fst (hT : ModalSys.T = true) {Γ : Ctx} {A : VarType}
    {a : Ann (A.compsFlat A.hereChains)} (W : Term σ Γ (A.compsFlat A.hereChains) a) :
    ∀ (cs : List (List Step)) (hcs : ∀ p ∈ cs, p ∈ (tupOneTy A true).hereChains)
      (ρ : List Step),
      (Term.holeAt W (tupCVal (σ := σ) A hT cs hcs).2).getP (compsFst cs ++ ρ) =
        (Term.holeAt W (tupCVal (σ := σ) A hT [] fun _ h => absurd h List.not_mem_nil).2).getP ρ
  | [], _, _ => rfl
  | _ :: ps, hcs, ρ => by
      change (Term.pair _ _).getP (.fst :: (compsFst ps ++ ρ)) = _
      rw [getP_pair_fst]
      exact getP_tupCVal_fst hT W ps _ ρ

/-- `arrT` at a value `b` of the flag. -/
def arrTB (A : VarType) (b : Bool) (hb : ModalSys.T = b) :
    Σ c, Term σ (Ctx.empty.insert (.bnd 0) (A.compsFlat (A.compsAllB b))) (tupOneTy A b) c :=
  ⟨_, Term.holeAt (ShapeMap.tupC (σ := σ) A b hb).val.2
    (ShapeMap.forgetC (σ := σ) (tupOneTy A b) _ (VarType.compOk_compsAllB b hb _)).val.2⟩

omit [ModalSys.NoFour] in
theorem getP_holeAt_arrTB {Γ : Ctx} (A : VarType) (b : Bool) (hb : ModalSys.T = b)
    {a : Ann (A.compsFlat (A.compsAllB b))} (W : Term σ Γ (A.compsFlat (A.compsAllB b)) a)
    (ρ : List Step) :
    (Term.holeAt W (arrTB (σ := σ) A b hb).2).getP ρ =
      (Term.holeAt W (ShapeMap.tupC (σ := σ) A b hb).val.2).getP
        (compsFst ((tupOneTy A b).compsAllB b) ++ ρ) := by
  exact (getP_congr (Term.holeAt_holeAt_sig W _ _) ρ).trans
    (getP_holeAt_eta _ _ (FS_compsFst _) rfl (Ctx.ref_compsFst _ (Ctx.ref_insert_root _ _ _)) ρ)

omit [ModalSys.NoFour] in
/-- ⭐`arr`'s tuple read at its root's contents: the value's own value. -/
theorem getP_arrTB_main {Γ : Ctx} (A : VarType) (b : Bool) (hb : ModalSys.T = b)
    {a : Ann (A.compsFlat (A.compsAllB b))} (W : Term σ Γ (A.compsFlat (A.compsAllB b)) a) :
    (Term.holeAt W (arrTB (σ := σ) A b hb).2).getP (.snd :: itemTail) =
      W.getP (compsFst (A.compsAllB b)) := by
  rw [getP_holeAt_arrTB]
  cases b with
  | false =>
      rw [itemTail_false hb]
      change (Term.pair _ _).getP [.snd] = W.getP []
      rw [getP_pair_snd]
      exact getP_holeAt_eta W [] FS_nil rfl _ []
  | true =>
      rw [itemTail_true hb]
      dsimp only [ShapeMap.val]
      refine (getP_tupCVal_fst hb W _ _ _).trans ?_
      change (Term.pair _ (Term.pair _ _)).getP [.snd, .fst] = _
      rw [getP_pair_snd, getP_pair_fst]
      exact (getP_holeAt_eta W _ (FS_compsFst _) rfl _ []).trans
        (congrArg W.getP (List.append_nil _))

omit [ModalSys.NoFour] in
/-- ⭐`arr`'s tuple read at a companion's place: the value's companion. -/
theorem getP_arrTB_comp {Γ : Ctx} (A : VarType) (b : Bool) (hb : ModalSys.T = b)
    {a : Ann (A.compsFlat (A.compsAllB b))} (W : Term σ Γ (A.compsFlat (A.compsAllB b)) a)
    (q : List Step) (hq : q ∈ A.compsAllB b) :
    (Term.holeAt W (arrTB (σ := σ) A b hb).2).getP (.snd :: (encPath (.here :: q) ++ itemTail)) =
      W.getP (compsIdx (A.compsAllB b) q) := by
  rw [getP_holeAt_arrTB]
  cases b with
  | false => exact absurd hq List.not_mem_nil
  | true =>
      dsimp only [ShapeMap.val]
      refine (getP_tupCVal_fst hb W _ _ _).trans ?_
      rw [itemTail_true hb]
      change (Term.pair _ (Term.pair _ _)).getP
        (.snd :: encStep .here :: (encPath q ++ [.fst])) = _
      rw [encStep_here hb, getP_pair_snd, getP_pair_snd]
      refine (getP_congr (Term.subst_bcTree _ _ _ A _) _).trans ?_
      refine (getP_bcTree hb A _ q hq).trans ?_
      exact (getP_nil _).symm.trans ((getP_holeAt_eta W _ (FS_compsIdx _ q) rfl _ []).trans
        (congrArg W.getP (List.append_nil _)))

omit [ModalSys.NoFour] in
theorem FS_itemTail : FS itemTail := by
  unfold itemTail
  split
  · exact FS_cons (Or.inl rfl) FS_nil
  · exact FS_nil

omit [ModalSys.NoFour] in
theorem FS_encPath_hereChains (hT : ModalSys.T = true) : ∀ (A : VarType) (q : List Step),
    q ∈ A.hereChains → FS (encPath q)
  | .VTypeBox C, q, hq => by
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact FS_nil
      · obtain ⟨q', hq'', rfl⟩ := List.mem_map.mp hq'
        change FS (encStep .here :: encPath q')
        rw [encStep_here hT]
        exact FS_cons (Or.inr rfl) (FS_encPath_hereChains hT C q' hq'')
  | .VTypeProd X Y, q, hq => by
      rcases List.mem_append.mp hq with hq' | hq'
      · obtain ⟨q', hq'', rfl⟩ := List.mem_map.mp hq'
        change FS (encStep .fst :: encPath q')
        rw [encStep_fst]
        exact FS_cons (Or.inl rfl) (FS_encPath_hereChains hT X q' hq'')
      · obtain ⟨q', hq'', rfl⟩ := List.mem_map.mp hq'
        change FS (encStep .snd :: encPath q')
        rw [encStep_snd]
        exact FS_cons (Or.inr rfl) (FS_encPath_hereChains hT Y q' hq'')
  | .Var, _, hq => absurd hq List.not_mem_nil
  | .VTypeOne, _, hq => absurd hq List.not_mem_nil
  | .VTypeDia _, _, hq => absurd hq List.not_mem_nil

omit [ModalSys.NoFour] in
theorem FS_encPath_here (hT : ModalSys.T = true) (q : List Step) (hq : FS (encPath q)) :
    FS (encPath (.here :: q) ++ itemTail) := by
  change FS (encStep .here :: encPath q ++ itemTail)
  rw [encStep_here hT]
  exact FS_cons (Or.inr rfl) (FS_append hq FS_itemTail)

omit [ModalSys.NoFour] in
/-- A value with companions read off a slot, at its own value's place. -/
theorem getP_compsSlot_fst {Δ Δ' : Ctx} {u : VarSymb} {C : VarType}
    (hu : Δ.ref u = some (.VTypeBox C)) (hle : Δ.boxIn.Le Δ') :
    ∀ (cs : List (List Step)) (h : C.CompOk cs),
      (compsSlot (σ := σ) hu hle cs h).2.getP (compsFst cs) =
        some ⟨C, _, Term.eta u.inner C (hle.ref (Ctx.ref_inner hu))⟩
  | [], _ => getP_nil _
  | _ :: ps, h => by
      change (Term.pair _ _).getP (.fst :: compsFst ps) = _
      rw [getP_pair_fst]
      exact getP_compsSlot_fst hu hle ps h.tail

omit [ModalSys.NoFour] in
/-- … and at a companion's place. -/
theorem getP_compsSlot_idx {Δ Δ' : Ctx} {u : VarSymb} {C : VarType}
    (hu : Δ.ref u = some (.VTypeBox C)) (hle : Δ.boxIn.Le Δ') :
    ∀ (cs : List (List Step)) (h : C.CompOk cs) (q : List Step) (hq : q ∈ cs),
      (compsSlot (σ := σ) hu hle cs h).2.getP (compsIdx cs q) =
        some ⟨_, _, Term.eta ((VarSymb.step u .here).ext q).inner ((C.compAt q).getD .VTypeOne)
          (hle.ref (Ctx.ref_inner (VarType.CompOk.ref_mem h hq hu)))⟩
  | [], _, _, hq => absurd hq List.not_mem_nil
  | p :: ps, h, q, hq => by
      by_cases hqp : q = p
      · subst hqp
        change (Term.pair _ _).getP (if q = q then [.snd] else _) = _
        rw [if_pos rfl, getP_pair_snd, getP_nil]
      · have hq' : q ∈ ps := (List.mem_cons.mp hq).resolve_left hqp
        change (Term.pair _ _).getP (if q = p then [.snd] else .fst :: compsIdx ps q) = _
        rw [if_neg hqp, getP_pair_fst]
        exact getP_compsSlot_idx hu hle ps h.tail q hq'

/-- `unarr` at a term, read at an item of the born root: the term read at the item's image. -/
theorem getP_unarrAt_item {Γ : Ctx} (A : VarType) {a : Ann (VarType.VTypeBox A).bc}
    (w : Term σ Γ (VarType.VTypeBox A).bc a) {u : VarSymb} {T : VarType} {π : List Step}
    (hπ : FS (encPath u.path ++ itemTail))
    (hu : (ctxOf [VarType.VTypeBox A]).boxIn.ref u.inner = some T)
    (hrt : u.rt = .free 0)
    (hg : (unarrT (σ := σ) (bc_root_ref A)).2.getP π =
      some ⟨T, _, Term.subst (arrowIdx (fun _ => 0))
        (arrowS σ (ctxOf [(VarType.VTypeBox A).bc]) (fun _ => 0))
        (ok_arrowS (retBackImg [_] A (bc_root_ref A)))
        (coh_arrowS (retBackImg [_] A (bc_root_ref A))) (Term.eta u.inner T hu)⟩) :
    (unarrAt (σ := σ) A w).2.getP π = w.getP (encPath u.path ++ itemTail) := by
  have hok := ok_arrowS (σ := σ) (retBackImg [(VarType.VTypeBox A).bc] A (bc_root_ref A))
  have hw : (ctxOf [(VarType.VTypeBox A).bc]).ref (itemAt (.free 0) u) = some T := by
    have hu' : (ctxOf [VarType.VTypeBox A]).boxIn.ref (.step u .box) = some T := by
      rwa [VarSymb.inner_box ModalSys.NoFour.keepOnly] at hu
    have := hok (.step u .box) T rfl ((Ctx.ref_nonproj _ rfl).symm.trans hu')
    change (ctxOf _).ref (itemImg (fun _ => 0) u) = some T at this
    rwa [itemImg, hrt] at this
  obtain ⟨b, s, hs⟩ := getP_some_of_ref (Γ := Γ) _ hπ (bc_root_ref A) hw w
  rw [hs]
  refine (getP_subst _ _ _ _ _ hg).trans (some_of_sig ?_)
  refine (sig_subst _ _ _ (Term.subst_eta_renAt _ _ _ T _ _ hu hw ?_)).trans
    (Term.subst_eta_tm _ _ _ T _ hw s
      (Subst.at_ext_getP _ _ (Subst.at_single_root (σ := σ) _ _) hs))
  rw [VarSymb.inner_box ModalSys.NoFour.keepOnly, Subst.at_nonproj _ rfl]
  change SubE.ren (itemImg (fun _ => 0) u) = _
  rw [itemImg, hrt]
  rfl

/-- `unarr` at a term, read at its own value's place: the term read at its first component. -/
theorem getP_unarrAt_main {Γ : Ctx} (A : VarType) {a : Ann (VarType.VTypeBox A).bc}
    (w : Term σ Γ (VarType.VTypeBox A).bc a) :
    (unarrAt (σ := σ) A w).2.getP (compsFst (bornComps A)) = w.getP itemTail :=
  getP_unarrAt_item A w (u := .root (.free 0)) FS_itemTail (Ctx.ref_inner (born_ref A)) rfl
    (getP_subst _ _ _ _ _ (getP_compsSlot_fst _ _ _ _))

/-- `unarr` at a term, read at a companion's place: the term read at the companion's image. -/
theorem getP_unarrAt_comp {Γ : Ctx} (A : VarType) {a : Ann (VarType.VTypeBox A).bc}
    (w : Term σ Γ (VarType.VTypeBox A).bc a) (q : List Step) (hq : q ∈ bornComps A) :
    (unarrAt (σ := σ) A w).2.getP (compsIdx (bornComps A) q) =
      w.getP (encPath (.here :: q) ++ itemTail) := by
  have hT : ModalSys.T = true := by
    cases h : ModalSys.T
    · change q ∈ A.compsAllB ModalSys.T at hq
      rw [h] at hq
      exact absurd hq List.not_mem_nil
    · rfl
  have hq' : q ∈ A.hereChains := by
    change q ∈ A.compsAllB ModalSys.T at hq
    rwa [hT] at hq
  have hpath : ((VarSymb.step (VarSymb.root (.free 0)) .here).ext q).path = .here :: q := by
    rw [VarSymb.ext_path]
    rfl
  have h := getP_unarrAt_item (σ := σ) A w (u := (VarSymb.step (.root (.free 0)) .here).ext q)
    (by rw [hpath]; exact FS_encPath_here hT q (FS_encPath_hereChains hT A q hq'))
    (Ctx.ref_inner (VarType.CompOk.ref_mem (bornComps_ok A) hq (born_ref A))) (VarSymb.ext_rt _ _)
    (getP_subst _ _ _ _ _ (getP_compsSlot_idx _ _ _ _ q hq))
  rwa [hpath] at h

omit [ModalSys.NoFour] in
/-- `arrB` read past its hole: `arrT` read at the second component. -/
theorem getP_holeAt_arrB {Γ : Ctx} (A : VarType) {a : Ann (A.compsFlat (bornComps A))}
    (W : Term σ Γ (A.compsFlat (bornComps A)) a) (ρ : List Step) :
    (Term.holeAt W (arrB (σ := σ) A).2).getP ρ = (Term.holeAt W (arrT (σ := σ) A).2).getP
      (.snd :: ρ) :=
  (getP_congr (Term.holeAt_holeAt_sig W _ _) ρ).trans
    (getP_holeAt_eta _ [.snd] (FS_cons (Or.inr rfl) FS_nil) rfl _ ρ)

/-- ⭐⭐**The arrangement identity**: a value with companions, arranged as its tuple and read back,
    is itself (`unarr(arr W) = W`). -/
theorem unarrAt_arrB {Γ : Ctx} (A : VarType) {a : Ann (A.compsFlat (bornComps A))}
    (W : Term σ Γ (A.compsFlat (bornComps A)) a) :
    (⟨_, (unarrAt (σ := σ) A (Term.holeAt W (arrB (σ := σ) A).2)).2⟩ :
      Σ c, Term σ Γ (A.compsFlat (bornComps A)) c) = ⟨a, W⟩ :=
  compsFlat_ext A (bornComps A) (compsAllB_nodup _ A) _ W
    ((getP_unarrAt_main A _).trans ((getP_holeAt_arrB A W _).trans
      (getP_arrTB_main A ModalSys.T rfl W)))
    (fun p hp => (getP_unarrAt_comp A _ p hp).trans ((getP_holeAt_arrB A W _).trans
      (getP_arrTB_comp A ModalSys.T rfl W p hp)))

/-! ## `unarr` as a hole term, and the born root's readings home -/

theorem unarrAt_sig {Γ : Ctx} (A : VarType) {a a' : Ann (VarType.VTypeBox A).bc}
    {w : Term σ Γ (VarType.VTypeBox A).bc a} {w' : Term σ Γ (VarType.VTypeBox A).bc a'}
    (h : (⟨a, w⟩ : Σ c, Term σ Γ _ c) = ⟨a', w'⟩) : unarrAt A w = unarrAt A w' := by
  cases h
  rfl

/-- `unarr` at the slot. -/
def unarrHole (A : VarType) :
    Σ c, Term σ (Ctx.empty.insert (.bnd 0) (VarType.VTypeBox A).bc) (A.compsFlat (bornComps A)) c :=
  unarrAt A (Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root _ _ _))

/-- ⭐`unarr`'s hole term at a term is `unarr` at the term. -/
theorem holeAt_unarrHole {Γ : Ctx} (A : VarType) {a : Ann (VarType.VTypeBox A).bc}
    (w : Term σ Γ (VarType.VTypeBox A).bc a) :
    (⟨_, Term.holeAt w (unarrHole (σ := σ) A).2⟩ :
      Σ c, Term σ Γ (A.compsFlat (bornComps A)) c) = unarrAt A w := by
  unfold unarrHole unarrAt Term.holeAt
  refine Term.subst_comp_sig _ _ _ _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) _
  by_cases hvr : v = .root (.free 0)
  · subst hvr
    obtain rfl : (VarType.VTypeBox A).bc = T := by simpa [Ctx.insert] using hv
    dsimp only [Subst.comp]
    rw [Subst.single_root, Subst.single_root]
    exact SubE.sim_tm_sigma (Term.subst_eta_tm _ _ _ _ _ _ w (Subst.at_single_root _ _)).symm
  · exact absurd hv (by simp [Ctx.insert, hvr, Ctx.empty])

/-- A born-root item along an arrow: its image under the root's image. -/
theorem subst_arrow_eta_born {l : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) {u : VarSymb} (hrt : u.rt = .free 0) {T : VarType}
    (hu : (ctxOf l).boxIn.ref u.inner = some T) :
    ∃ hw : Δ.ref (itemAt (.free (img 0)) u) = some T,
      (⟨_, Term.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS himg) (coh_arrowS himg)
        (Term.eta u.inner T hu)⟩ : Σ c, Term σ Δ T c) =
        ⟨_, Term.eta (itemAt (.free (img 0)) u) T hw⟩ := by
  have hu' : (ctxOf l).boxIn.ref (.step u .box) = some T := by
    rwa [VarSymb.inner_box ModalSys.NoFour.keepOnly] at hu
  have hw : Δ.ref (itemAt (.free (img 0)) u) = some T := by
    have := ok_arrowS (σ := σ) himg (.step u .box) T rfl ((Ctx.ref_nonproj _ rfl).symm.trans hu')
    change Δ.ref (itemImg img u) = some T at this
    rwa [itemImg, hrt] at this
  refine ⟨hw, Term.subst_eta_renAt _ _ _ T _ _ hu hw ?_⟩
  rw [VarSymb.inner_box ModalSys.NoFour.keepOnly, Subst.at_nonproj _ rfl]
  change SubE.ren (itemImg img u) = _
  rw [itemImg, hrt]
  rfl

/-- ⭐**The born root's readings home**: its value with companions `cs`, sent along an arrow that
    takes it to `y`, is `unarrT y` with `cs` selected. -/
theorem subst_arrow_compsSlot_born {l ls : List VarType} {A : VarType}
    (hc : (ctxOf l).ref (.root (.free 0)) = some (.VTypeBox A)) {img : ℕ → ℕ}
    (himg : ImgOk l (ctxOf ls) img) {y : ℕ}
    (hy : (ctxOf ls).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) (hy0 : img 0 = y) :
    ∀ (cs : List (List Step)) (h : A.CompOk cs) (hsub : ∀ p ∈ cs, p ∈ bornComps A),
      (⟨_, Term.subst (arrowIdx img) (arrowS σ (ctxOf ls) img) (ok_arrowS himg)
          (coh_arrowS himg) (compsSlot (σ := σ) hc (Ctx.Le.refl _) cs h).2⟩ :
        Σ c, Term σ (ctxOf ls) (A.compsFlat cs) c) =
        ⟨_, Term.holeAt (unarrT (σ := σ) hy).2
          (ShapeMap.subC (σ := σ) A (bornComps A) cs (bornComps_ok A) h hsub).val.2⟩
  | [], h, hsub => by
      obtain ⟨hw, e⟩ := subst_arrow_eta_born (σ := σ) himg (u := .root (.free 0)) rfl
        (Ctx.ref_inner hc)
      refine e.trans ?_
      obtain ⟨hw', e'⟩ := subst_arrow_eta_born (σ := σ) (retBackImg ls A hy)
        (u := .root (.free 0)) rfl (Ctx.ref_inner (born_ref A))
      refine Eq.trans ?_ (holeAt_eta_getP _ _ rfl (getP_subst _ _ _ _ _
        (getP_compsSlot_fst _ _ _ _)) _).symm
      refine Eq.trans ?_ e'.symm
      exact eta_addr_congr (by rw [hy0]) _ _
  | p :: ps, h, hsub => by
      refine sig_pair (subst_arrow_compsSlot_born hc himg hy hy0 ps h.tail
        (fun q hq => hsub q (List.mem_cons_of_mem _ hq))) ?_
      have hp := hsub p List.mem_cons_self
      obtain ⟨hw, e⟩ := subst_arrow_eta_born (σ := σ) himg
        (u := (VarSymb.step (.root (.free 0)) .here).ext p) (VarSymb.ext_rt _ _)
        (Ctx.ref_inner (h.ref_head hc))
      refine e.trans ?_
      obtain ⟨hw', e'⟩ := subst_arrow_eta_born (σ := σ) (retBackImg ls A hy)
        (u := (VarSymb.step (.root (.free 0)) .here).ext p) (VarSymb.ext_rt _ _)
        (Ctx.ref_inner (VarType.CompOk.ref_mem (bornComps_ok A) hp (born_ref A)))
      refine Eq.trans ?_ (holeAt_eta_getP _ _ rfl (getP_subst _ _ _ _ _
        (getP_compsSlot_idx _ _ _ _ p hp)) _).symm
      refine Eq.trans ?_ e'.symm
      exact eta_addr_congr (by rw [hy0]) _ _

/-! ## Naming the missing companions, and selecting back -/

omit [ModalSys] [ModalSys.NoFour] in
theorem compsFst_append : ∀ (Q cs : List (List Step)),
    compsFst (Q ++ cs) = List.replicate Q.length .fst ++ compsFst cs
  | [], _ => rfl
  | _ :: Q, cs => congrArg (Step.fst :: ·) (compsFst_append Q cs)

omit [ModalSys] [ModalSys.NoFour] in
theorem compsIdx_append {q : List Step} : ∀ (Q cs : List (List Step)), q ∉ Q →
    compsIdx (Q ++ cs) q = List.replicate Q.length .fst ++ compsIdx cs q
  | [], _, _ => rfl
  | p :: Q, cs, hq => by
      have hqp : q ≠ p := fun e => hq (e ▸ List.mem_cons_self)
      change (if q = p then [.snd] else .fst :: compsIdx (Q ++ cs) q) = _
      rw [if_neg hqp, compsIdx_append Q cs (fun h => hq (List.mem_cons_of_mem _ h))]
      rfl

/-- The born root's companions not in `cs`. -/
def missComps (A : VarType) (cs : List (List Step)) : List (List Step) :=
  (bornComps A).filter (fun q => decide (q ∉ cs))

omit [ModalSys.NoFour] in
theorem missComps_ok {A : VarType} {cs : List (List Step)} (h : A.CompOk cs) :
    A.CompOk (missComps A cs ++ cs) := by
  rcases bornComps_ok A with hB | ⟨hT, hallB, hndB⟩
  · rw [missComps, hB]
    exact h
  · refine Or.inr ⟨hT, fun p hp => ?_, List.Nodup.append (hndB.filter _) h.nodup ?_⟩
    · rcases List.mem_append.mp hp with hp | hp
      · exact hallB p (List.mem_filter.mp hp).1
      · rcases h with rfl | ⟨-, hall, -⟩
        · exact absurd hp List.not_mem_nil
        · exact hall p hp
    · intro p hp hp'
      exact of_decide_eq_true (List.mem_filter.mp hp).2 hp'

omit [ModalSys.NoFour] in
theorem missComps_sub (A : VarType) (cs : List (List Step)) :
    ∀ p ∈ bornComps A, p ∈ missComps A cs ++ cs := by
  intro p hp
  by_cases hc : p ∈ cs
  · exact List.mem_append_right _ hc
  · exact List.mem_append_left _ (List.mem_filter.mpr ⟨hp, decide_eq_true hc⟩)

omit [ModalSys.NoFour] in
theorem missComps_disj {A : VarType} {cs : List (List Step)} {q : List Step} (hq : q ∈ cs) :
    q ∉ missComps A cs :=
  fun h => of_decide_eq_true (List.mem_filter.mp h).2 hq

omit [ModalSys.NoFour] in
/-- A valid companion list is among the born root's companions. -/
theorem compOk_sub_born {A : VarType} {cs : List (List Step)} (h : A.CompOk cs) :
    ∀ p ∈ cs, p ∈ bornComps A := by
  intro p hp
  rcases h with rfl | ⟨hT, hall, -⟩
  · exact absurd hp List.not_mem_nil
  · change p ∈ A.compsAllB ModalSys.T
    rw [hT]
    obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp (hall p hp)
    exact VarType.mem_hereChains A p hC

omit [ModalSys.NoFour] in
/-- ⭐**Selecting back**: a value with the missing companions named in front of `V`, reordered to
    the born order and then `cs` selected, is `V`. -/
theorem holeAt_subC_sel {Γ : Ctx} {A : VarType} {cs : List (List Step)} (h : A.CompOk cs)
    {a : Ann (A.compsFlat cs)} (V : Term σ Γ (A.compsFlat cs) a)
    {a₁ : Ann (A.compsFlat (missComps A cs ++ cs))}
    (V₁ : Term σ Γ (A.compsFlat (missComps A cs ++ cs)) a₁)
    (hV₁ : V₁.getP (List.replicate (missComps A cs).length .fst) = some ⟨_, _, V⟩) :
    (⟨_, Term.holeAt (Term.holeAt V₁ (ShapeMap.subC (σ := σ) A (missComps A cs ++ cs)
        (bornComps A) (missComps_ok h) (bornComps_ok A) (missComps_sub A cs)).val.2)
      (ShapeMap.subC (σ := σ) A (bornComps A) cs (bornComps_ok A) h
        (compOk_sub_born h)).val.2⟩ : Σ c, Term σ Γ (A.compsFlat cs) c) = ⟨a, V⟩ := by
  refine compsFlat_ext A cs h.nodup _ V ?_ (fun q hq => ?_)
  · have e₁ := subC_read_main (σ := σ) A (bornComps A) cs (bornComps_ok A) h
      (compOk_sub_born h) (Term.holeAt V₁ (ShapeMap.subC (σ := σ) A (missComps A cs ++ cs)
        (bornComps A) (missComps_ok h) (bornComps_ok A) (missComps_sub A cs)).val.2) []
    have e₂ := subC_read_main (σ := σ) A (missComps A cs ++ cs) (bornComps A) (missComps_ok h)
      (bornComps_ok A) (missComps_sub A cs) V₁ []
    rw [List.append_nil, List.append_nil] at e₁ e₂
    rw [e₁, e₂, compsFst_append, getP_append _ _ _ hV₁]
  · have e₁ := subC_read_idx (σ := σ) A (bornComps A) cs (bornComps_ok A) h
      (compOk_sub_born h) (Term.holeAt V₁ (ShapeMap.subC (σ := σ) A (missComps A cs ++ cs)
        (bornComps A) (missComps_ok h) (bornComps_ok A) (missComps_sub A cs)).val.2) q hq []
    have e₂ := subC_read_idx (σ := σ) A (missComps A cs ++ cs) (bornComps A) (missComps_ok h)
      (bornComps_ok A) (missComps_sub A cs) V₁ q (compOk_sub_born h q hq) []
    rw [List.append_nil, List.append_nil] at e₁ e₂
    rw [e₁, e₂, compsIdx_append _ _ (missComps_disj hq), getP_append _ _ _ hV₁]

end BArrow

end V12M
