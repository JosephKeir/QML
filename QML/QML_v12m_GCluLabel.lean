import QML.QML_v12m_GCluOrig

/-!
# QML v12m — 5 on the growing tree: the cluster's arrows and labels

The cluster model (`docs/v12-modal-extensions.md` §3 5, "S5 steps 3–4"), under T as without it.

* `carrows`: every world's arrows are the root's, `R s t :⇔ CR t`.  Under T the root reaches
  every world, itself included, so the frame is universal.
* `CLeaf`, `CLeaf.rean`: `Acc w` is one type at every world, so a leaf moves between anchors with
  no change; the root action is the identity (`instRootKeepC`), and `keepAlong` is that move.
* ⭐`cLab`: the label of a root's address.  Under 5 every entry names an address, so a label has a
  closed form with no walk along a path: the member of `u.keep.r` at a world `b` is the label of
  `(name of u at b).r`, read back at the root (`cNext`).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-! ## Paths from the root -/

/-- A world's path from the root. -/
def rpath (s : GW hF M₀) : List ℕ := s.1.reverse

theorem rpath_eq (s : GW hF M₀) : s.1 = nodeOf (groot hF M₀).1 (rpath s) := by
  rw [nodeOf_eq]
  simp [rpath, groot]

/-- The root's stage at which a world's stage has its preimage. -/
noncomputable abbrev rstg (s : GW hF M₀) (i : ℕ) : ℕ :=
  pstgO (rpath s) (groot hF M₀) s (rpath_eq s) i

/-- A world's origins at the root. -/
noncomputable abbrev rorig (s : GW hF M₀) : VarSymb → VarSymb :=
  porig (rpath s) (groot hF M₀) s (rpath_eq s)

/-- The root's addresses named at a world. -/
noncomputable abbrev rnm (s : GW hF M₀) : VarSymb → VarSymb :=
  pnm (rpath s) (groot hF M₀) s (rpath_eq s)

/-! ## The cluster arrows -/

variable (M₀) in
/-- The root's self-arrow: the empty path, when the root has a self-edge. -/
def RootLoop (P : List ℕ) : Prop := P = [] ∧ GNetSt.LoopOn M₀

/-- ⭐**A world the root reaches**: by a path that is an arrow, or the root by its self-arrow. -/
def CR (t : GW hF M₀) : Prop :=
  ∃ P : List ℕ, (PathOk P ∨ RootLoop M₀ P) ∧ t.1 = nodeOf (groot hF M₀).1 P

open Classical in
/-- The path of a cluster arrow. -/
noncomputable def cpath {t : GW hF M₀} (h : CR t) : List ℕ := Classical.choose h

open Classical in
theorem cpath_spec {t : GW hF M₀} (h : CR t) : PathOk (cpath h) ∨ RootLoop M₀ (cpath h) :=
  (Classical.choose_spec h).1

open Classical in
theorem cpath_eq {t : GW hF M₀} (h : CR t) : t.1 = nodeOf (groot hF M₀).1 (cpath h) :=
  (Classical.choose_spec h).2

/-- The chosen path is any path. -/
theorem cpath_of {t : GW hF M₀} (hR : CR t) {P : List ℕ} (h : t.1 = nodeOf (groot hF M₀).1 P) :
    cpath hR = P :=
  nodeOf_inj ((cpath_eq hR).symm.trans h)

theorem cpathOk (hT : ModalSys.T = true) {t : GW hF M₀} (h : CR t) : PathOk (cpath h) := .inr hT

/-- An arrow that is not a path is the self-arrow, which needs the self-edge. -/
theorem CR.loop {t : GW hF M₀} (h : CR t) (hn : ¬ PathOk (cpath h)) : GNetSt.LoopOn M₀ :=
  ((cpath_spec h).resolve_left hn).2

/-- …and it ends at the root. -/
theorem CR.loop_eq {t : GW hF M₀} (h : CR t) (hn : ¬ PathOk (cpath h)) :
    t.1 = (groot hF M₀).1 := by
  have e := cpath_eq h
  rwa [((cpath_spec h).resolve_left hn).1] at e

/-- The membership of an arrow in an extent reads any path to its end. -/
theorem cmem_path {hM₀ : Theory.IsMCS M₀} {t : GW hF M₀} (hR : CR t) {P : List ℕ}
    (h : t.1 = nodeOf (groot hF M₀).1 P) {x : VarSymb} :
    GMem hM₀ (groot hF M₀) t (cpath hR) (cpath_eq hR) x ↔ GMem hM₀ (groot hF M₀) t P h x := by
  obtain rfl := cpath_of hR h
  exact Iff.rfl

/-- A descendant of the root is reached. -/
theorem CR.of_GR {t : GW hF M₀} (h : GR (groot hF M₀) t) : CR t := by
  obtain ⟨P, hP, e⟩ := h
  exact ⟨P, .inl hP, e⟩

/-- A path in a witness's extent is a path that is an arrow. -/
theorem pathOk_of_inExt {s t : GW hF M₀} {P : List ℕ} {h : t.1 = nodeOf s.1 P} {x : VarSymb}
    (hm : InExt s t P h x) : PathOk P := by
  cases P with
  | nil => exact hm.elim
  | cons _ _ => exact pathOk_cons

/-- A path in a witness's extent is the arrow's path. -/
theorem inExt_cpath {t : GW hF M₀} (hR : CR t) {P : List ℕ}
    {h : t.1 = nodeOf (groot hF M₀).1 P} {x : VarSymb} (hm : InExt (groot hF M₀) t P h x) :
    InExt (groot hF M₀) t (cpath hR) (cpath_eq hR) x := by
  obtain rfl := cpath_of hR h
  exact hm

variable (hF M₀) in
/-- ⭐**The cluster arrows**: from every world to every world the root reaches. -/
abbrev carrows : Arrows.{0, 0} σ where
  W := GW hF M₀
  R := fun _ t => CR t
  refl := fun hT w => ⟨rpath w, .inl (.inr hT), rpath_eq w⟩
  trans := fun _ {_ _ _} _ h₂ => h₂
  refl_trans := fun _ _ _ _ _ => rfl
  trans_refl := fun _ _ _ _ _ => rfl
  trans_assoc := fun _ _ _ _ _ _ _ _ => rfl

variable (hF M₀) in
/-- Leaves over the cluster arrows. -/
abbrev CLeaf (s : GW hF M₀) : Type := (carrows hF M₀).Leaf (fun _ => VarSymb) s

variable (hF M₀) in
/-- Shapes over the cluster arrows. -/
abbrev CShape (s : GW hF M₀) (T : VarType) : Type :=
  Model.Shape (carrows hF M₀) (fun _ => VarSymb) s T

/-- ⭐**A leaf moved to another anchor**: `Acc` is one type, so nothing changes. -/
def CLeaf.rean {s : GW hF M₀} (t : GW hF M₀) : CLeaf hF M₀ s → CLeaf hF M₀ t
  | .root r p => .root r p
  | .fam f => .fam f

variable (hF M₀) in
/-- ⭐**The root action is the identity**: the cluster shares its possible objects. -/
noncomputable instance instRootKeepC : Arrows.RootKeep (carrows hF M₀) (fun _ => VarSymb) :=
  Arrows.RootKeep.ofRoot fun _ {_} r _ => r

variable (hF M₀) in
instance instRootKeepLawsC : Arrows.RootKeepLaws (carrows hF M₀) (fun _ => VarSymb) :=
  Arrows.RootKeepLaws.ofRoot _ (fun _ {_} _ _ _ => rfl) (fun _ _ {_} _ => rfl)

/-- A leaf kept along a cluster arrow is the leaf at the arrow's end. -/
theorem keepAlong_rean (hF' : ModalSys.Four = true) {s : GW hF M₀}
    (a : (carrows hF M₀).Acc s) (l : CLeaf hF M₀ s) :
    Arrows.Leaf.keepAlong hF' a l = CLeaf.rean a.1 l :=
  match s, l, a with
  | _, .root _ _, _ => rfl
  | _, .fam _, _ => rfl

/-! ## Reading a world's address at the root -/

/-- A world's address read at the root: its origin before its first level step, the rest kept. -/
noncomputable def preIx (s : GW hF M₀) (z : VarSymb) : VarSymb :=
  match splitLevel z.path with
  | some (q, st, r) => (VarSymb.step (rorig s ((VarSymb.root z.rt).ext q)) st).ext r
  | none => rorig s z

theorem preIx_ppath (s : GW hF M₀) {z : VarSymb} (hz : PPath z.path) :
    preIx s z = rorig s z := by
  unfold preIx
  rw [splitLevel_ppath_none hz]

theorem preIx_lvl (s : GW hF M₀) {z : VarSymb} (hz : PPath z.path) {st : Step}
    (hs : st.isProj = false) (r : List Step) :
    preIx s ((VarSymb.step z st).ext r) = (VarSymb.step (rorig s z) st).ext r := by
  unfold preIx
  rw [show ((VarSymb.step z st).ext r).path = z.path ++ st :: r by
      rw [VarSymb.ext_path]
      change (z.path ++ [st]) ++ r = _
      simp,
    splitLevel_ppath hz hs]
  simp only [VarSymb.ext_rt]
  rw [show (VarSymb.step z st).rt = z.rt from rfl, VarSymb.root_ext_path]

/-! ## Labels -/

/-- The address that `v.keep.r`'s member at `b` is the label of: the rest at `v`'s name at `b`,
    read back at the root. -/
noncomputable def cNext (b : GW hF M₀) (v : VarSymb) (r : List Step) : VarSymb :=
  preIx b ((rnm b v).ext r)

/-- ⭐**The label of a root's address**, at any anchor, by its first level step: none, the address
    itself; `dia`, a root path from the projection prefix; `keep`, the family of what it reads
    along each arrow.  The level guard holds for declared addresses (`cNext_cases`). -/
noncomputable def cLab (y : VarSymb) (w : GW hF M₀) : CLeaf hF M₀ w :=
  match splitLevel y.path with
  | none => .root y []
  | some (pre, .dia, r) => .root ((VarSymb.root y.rt).ext pre) (.dia :: r)
  | some (pre, .keep, r) => .fam fun b =>
      if _hl : Step.levels (cNext b.1 ((VarSymb.root y.rt).ext pre) r).path < Step.levels y.path
      then cLab (cNext b.1 ((VarSymb.root y.rt).ext pre) r) b.1
      else .root junkR []
  | some _ => .root junkR []
termination_by Step.levels y.path
decreasing_by exact ‹_›

theorem cLab_ppath {y : VarSymb} (hy : PPath y.path) (w : GW hF M₀) :
    cLab y w = .root y [] := by
  rw [cLab, splitLevel_ppath_none hy]

theorem cLab_dia {v : VarSymb} (hv : PPath v.path) (r : List Step) (w : GW hF M₀) :
    cLab ((VarSymb.step v .dia).ext r) w = .root v (.dia :: r) := by
  rw [cLab, show ((VarSymb.step v .dia).ext r).path = v.path ++ .dia :: r by
      rw [VarSymb.ext_path]
      change (v.path ++ [.dia]) ++ r = _
      simp,
    splitLevel_ppath hv (by decide)]
  simp only [VarSymb.ext_rt]
  rw [show (VarSymb.step v .dia).rt = v.rt from rfl, VarSymb.root_ext_path]

theorem cLab_keep {v : VarSymb} (hv : PPath v.path) (r : List Step) (w : GW hF M₀) :
    cLab ((VarSymb.step v .keep).ext r) w = .fam fun b =>
      if _hl : Step.levels (cNext b.1 v r).path <
          Step.levels ((VarSymb.step v .keep).ext r).path
      then cLab (cNext b.1 v r) b.1 else .root junkR [] := by
  rw [cLab, show ((VarSymb.step v .keep).ext r).path = v.path ++ .keep :: r by
      rw [VarSymb.ext_path]
      change (v.path ++ [.keep]) ++ r = _
      simp,
    splitLevel_ppath hv (by decide)]
  simp only [VarSymb.ext_rt]
  rw [show (VarSymb.step v .keep).rt = v.rt from rfl, VarSymb.root_ext_path]

/-- The label at one anchor, moved to another. -/
theorem cLab_rean (y : VarSymb) (g g' : GW hF M₀) : CLeaf.rean g' (cLab y g) = cLab y g' := by
  rw [cLab, cLab]
  split <;> rfl

/-! ## Declared addresses -/

section Decl

variable (hV : ModalSys.Five = true) (hS : ModalSys.FourStrong = true)
  (hW : ModalSys.FourStrongW = true) (hM₀ : Theory.IsMCS M₀)

include hV hM₀ in
/-- A root's keepable address is declared at its name. -/
theorem declAt_rnm (b : GW hF M₀) {v : VarSymb} {U : VarType}
    (hv : DeclAt (groot hF M₀) v U) (hk : U.keepable = true) : DeclAt b (rnm b v) U := by
  obtain ⟨i, hi⟩ := hv
  exact ⟨_, pnm_ref hV hM₀ (rpath b) (groot hF M₀) b (rpath_eq b) i v U hi hk⟩

include hV hS hW hM₀ in
/-- A world's keepable address has its origin declared at the root. -/
theorem declAt_rorig (b : GW hF M₀) {z : VarSymb} {U : VarType} (hz : DeclAt b z U)
    (hk : U.keepable = true) : DeclAt (groot hF M₀) (rorig b z) U := by
  obtain ⟨i, hi⟩ := hz
  exact ⟨_, pPreOk hV hS hW hM₀ (rpath b) (groot hF M₀) b (rpath_eq b) i z U hi hk⟩

include hF hV hS hW hM₀ in
/-- ⭐**What a keep-first address reads at a world is a root's address** with a position of the
    same type and levels, the level steps after the first unchanged. -/
theorem cNext_cases (hT : ModalSys.T = true) (b : GW hF M₀) {v : VarSymb} {U : VarType}
    (hv : DeclAt (groot hF M₀) v U) (hk : U.keepable = true) {r : List Step} {V : VarType}
    (hw : Step.walkTy U r = some V) (hkV : V.keepable = true) :
    ∃ (v' : VarSymb) (U' : VarType) (π' : List Step), DeclAt (groot hF M₀) v' U' ∧
      PPath v'.path ∧ Step.walkTy U' π' = some V ∧
      Step.levels π' = Step.levels r ∧ (∀ j, lvlStep j π' = lvlStep j r) ∧
      cNext b v r = v'.ext π' := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  have hz := declAt_rnm hV hM₀ b hv hk
  obtain ⟨j, hj⟩ := hz
  have hpz : PPath (rnm b v).path := (reach_ppath hj).1
  by_cases h0 : Step.levels r = 0
  · have hr := ppath_of_levels0 h0
    have hd : DeclAt b ((rnm b v).ext r) V := declAt_ext ⟨j, hj⟩ hr hw
    have hd' := declAt_rorig hV hS hW hM₀ b hd hkV
    obtain ⟨i, hi⟩ := id hd'
    refine ⟨_, _, [], hd', (reach_ppath hi).1, rfl, by rw [h0]; rfl, fun j' => ?_, ?_⟩
    · rw [lvlStep_ppath _ hr]
      rfl
    · unfold cNext
      rw [preIx_ppath _ (by
        rw [VarSymb.ext_path]
        exact fun x hx => (List.mem_append.mp hx).elim (hpz x) (hr x))]
      rfl
  · obtain ⟨π₀, st, r', rfl, hπ₀, hst⟩ := split_first r (by omega)
    rw [Step.walkTy_append, walkTy_ppath U hπ₀] at hw
    obtain ⟨U₀, hU₀, hw₀⟩ := Option.bind_eq_some_iff.mp hw
    have hd₀ : DeclAt b ((rnm b v).ext π₀) U₀ :=
      declAt_ext ⟨j, hj⟩ hπ₀ ((walkTy_ppath U hπ₀).trans hU₀)
    have hpz₀ : PPath ((rnm b v).ext π₀).path := by
      rw [VarSymb.ext_path]
      exact fun x hx => (List.mem_append.mp hx).elim (hpz x) (hπ₀ x)
    have hkU₀ : U₀.keepable = true := by
      obtain ⟨W, hW', -⟩ := Option.bind_eq_some_iff.mp hw₀
      cases st with
      | fst => cases hst
      | snd => cases hst
      | here => cases hst
      | box =>
          change (if ModalSys.keepOnly = true then none else U₀.step .box) = some W at hW'
          rw [if_pos hko] at hW'
          cases hW'
      | dia =>
          cases U₀ with
          | VTypeDia _ => rfl
          | _ => cases hW'
      | keep => exact Step.typeStep_level_keepable rfl hW'
    have hd' := declAt_rorig hV hS hW hM₀ b hd₀ hkU₀
    obtain ⟨i, hi⟩ := id hd'
    refine ⟨_, _, st :: r', hd', (reach_ppath hi).1, hw₀, ?_, fun j' => ?_, ?_⟩
    · rw [Step.levels_append, levels_pp hπ₀, Nat.zero_add]
    · rw [lvlStep_append, levels_pp hπ₀, if_neg (by omega), Nat.sub_zero]
    · unfold cNext
      rw [VarSymb.ext_append,
        show ((rnm b v).ext π₀).ext (st :: r') =
          (VarSymb.step ((rnm b v).ext π₀) st).ext r' from rfl,
        preIx_lvl _ hpz₀ hst]
      rfl

include hF hV hS hW hM₀ in
/-- ⭐**A position of a declared root address has a well-formed label**, at any anchor, when the
    `□` levels are spelled by `keep`s. -/
theorem cLab_wf (hT : ModalSys.T = true) : ∀ (n : ℕ) {v : VarSymb} {U : VarType} {π : List Step}
    {A : VarType} {lw : List Bool}, DeclAt (groot hF M₀) v U → PPath v.path →
    Step.walkTy U π = some (.VTypeDia A) → Step.levels π = n → Step.levels π = lw.length →
    (∀ j, lw[j]? = some true → lvlStep j π = some .keep) → ∀ w : GW hF M₀,
      Arrows.Leaf.WF lw (cLab (v.ext π) w) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro v U π A lw hd hv hw hn hl hk w
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  by_cases h0 : Step.levels π = 0
  · have hπ := ppath_of_levels0 h0
    have hpre : PPath (v.ext π).path := by
      rw [VarSymb.ext_path]
      exact fun x hx => (List.mem_append.mp hx).elim (hv x) (hπ x)
    rw [cLab_ppath hpre]
    obtain rfl : lw = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact (Arrows.Leaf.wf_root _ []).mpr ⟨rfl, by simp, trivial,
      ⟨.VTypeDia .VTypeOne, .VTypeOne, rfl⟩⟩
  · obtain ⟨π₀, st, r, rfl, hπ₀, hst⟩ := split_first π (by omega)
    have hpre : PPath (v.ext π₀).path := by
      rw [VarSymb.ext_path]
      exact fun x hx => (List.mem_append.mp hx).elim (hv x) (hπ₀ x)
    have hlv : ∀ j, lvlStep j (π₀ ++ st :: r) = lvlStep j (st :: r) := fun j => by
      rw [lvlStep_append, levels_pp hπ₀, if_neg (by omega), Nat.sub_zero]
    rw [Step.walkTy_append, walkTy_ppath U hπ₀] at hw
    obtain ⟨U₀, hU₀, hw₀⟩ := Option.bind_eq_some_iff.mp hw
    have hd₀ : DeclAt (groot hF M₀) (v.ext π₀) U₀ :=
      declAt_ext hd hπ₀ ((walkTy_ppath U hπ₀).trans hU₀)
    have hlr : Step.levels (π₀ ++ st :: r) = 1 + Step.levels r := by
      rw [Step.levels_append, levels_pp hπ₀, Step.levels_cons, if_neg (by simp [hst])]
      omega
    rw [VarSymb.ext_append]
    cases st with
    | fst => cases hst
    | snd => cases hst
    | here => cases hst
    | box =>
        obtain ⟨W, hW', -⟩ := Option.bind_eq_some_iff.mp hw₀
        change (if ModalSys.keepOnly = true then none else U₀.step .box) = some W at hW'
        rw [if_pos hko] at hW'
        cases hW'
    | dia =>
        rw [show (v.ext π₀).ext (Step.dia :: r) = (VarSymb.step (v.ext π₀) .dia).ext r from rfl,
          cLab_dia hpre]
        have hlev : Step.levels (Step.dia :: r) = lw.length := by
          rw [← hl, hlr, Step.levels_cons, if_neg (by decide)]
        have hhead : lw.head? ≠ some true := fun hh => by
          have := hk 0 (by
            cases lw with
            | nil => cases hh
            | cons c l => simpa using hh)
          rw [hlv, lvlStep_lvl_zero (by decide)] at this
          cases this
        have hbox : Step.BoxOK lw (Step.dia :: r) := boxOK_of_lvl _ lw fun j hj e => by
          have := hk j hj
          rw [hlv, e] at this
          cases this
        exact (Arrows.Leaf.wf_root _ _).mpr ⟨hlev, hhead, hbox, ⟨U₀, A, hw₀⟩⟩
    | keep =>
        rw [show (v.ext π₀).ext (Step.keep :: r) = (VarSymb.step (v.ext π₀) .keep).ext r from rfl,
          cLab_keep hpre]
        obtain ⟨W, hW', hw₁⟩ := Option.bind_eq_some_iff.mp hw₀
        have hkU₀ : U₀.keepable = true := Step.typeStep_level_keepable rfl hW'
        have hr : Step.walkTy U₀ r = some (.VTypeDia A) :=
          (walkTy_keep hkU₀ r).symm.trans (Option.bind_eq_some_iff.mpr ⟨W, hW', hw₁⟩)
        have hlvl : Step.levels ((VarSymb.step (v.ext π₀) .keep).ext r).path =
            1 + Step.levels r := by
          rw [VarSymb.ext_path,
            show (VarSymb.step (v.ext π₀) .keep).path = (v.ext π₀).path ++ [.keep] from rfl,
            List.append_assoc, Step.levels_append, levels_pp hpre, List.singleton_append,
            Step.levels_cons, if_neg (by decide)]
          omega
        cases lw with
        | nil =>
            rw [hlr] at hl
            simp at hl
        | cons c lw' =>
            have hl' : Step.levels r = lw'.length := by
              rw [hlr] at hl
              simp only [List.length_cons] at hl
              omega
            intro b
            obtain ⟨v', U', π', hd', hv', hw', hlπ, hlv', e⟩ :=
              cNext_cases hV hS hW hM₀ hT b.1 hd₀ hkU₀ hr rfl
            have hlt : Step.levels (cNext b.1 (v.ext π₀) r).path <
                Step.levels ((VarSymb.step (v.ext π₀) .keep).ext r).path := by
              rw [hlvl, e, VarSymb.ext_path, Step.levels_append, levels_pp hv', hlπ]
              omega
            change Arrows.Leaf.WF lw' (dite _ _ _)
            rw [dif_pos hlt, e]
            refine IH (Step.levels π') (by rw [hlπ]; omega) (lw := lw') hd' hv' hw' rfl
              (hlπ.trans hl') (fun j hj => ?_) b.1
            have := hk (j + 1) (by simpa using hj)
            rw [hlv, lvlStep_lvl_succ rfl] at this
            rw [hlv' j, this]

/-! ## Names and origins invert each other -/

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] hV hM₀ in
include hS hW in
theorem liftable_of_keepable {T : VarType} (h : T.keepable = true) : T.liftable = true := by
  cases T <;> simp_all [VarType.liftable, VarType.keepable]

include hV hS hW hM₀ in
/-- ⭐**The name of an address's origin is the address**, at η-faithful types. -/
theorem nm_orig {s t : GW hF M₀} (h : GCh hF M₀ s t) {j : ℕ} {z : VarSymb} {T : VarType}
    (hz : (ctxOf (glat t j)).ref z = some T) (hk : T.keepable = true) (he : T.etaInj = true) :
    nm t (orig s t z) = z := by
  obtain ⟨i, v, U, hv, hkU, hn⟩ :=
    glorigin hV hM₀ h j hz (liftable_of_keepable hS hW hk)
  obtain ⟨i', U', hv', hkU', hn'⟩ := orig_spec (s := s) (t := t) (z := z) ⟨i, v, U, hv, hkU, hn⟩
  obtain rfl := names_type hM₀ h hv' hkU' hn' hz
  have hn'' := nm_spec hV t (orig s t z)
  rcases hn' with e | ⟨L, T₁, hz₁, e⟩ <;> rcases hn'' with e' | ⟨L', T₂, hz₂, e'⟩
  · exact Sum.inl.inj (e'.symm.trans e)
  · rw [e] at e'
    cases e'
  · rw [e] at e'
    cases e'
  · obtain ⟨rfl, -, -⟩ := entOf_names_tm hM₀ h i' hv' hkU' hz₁ e
    have h1 := Sigma.mk.inj (Sum.inr.inj (e'.symm.trans e))
    obtain ⟨rfl, h2⟩ := h1
    obtain ⟨rfl, h4⟩ := Sigma.mk.inj (eq_of_heq h2)
    exact eta_inj _ he hz₂ hz₁ (eq_of_heq h4)

include hV hS hW hM₀ in
/-- The path name of an address's path origin is the address, at η-faithful types. -/
theorem pnm_porig : ∀ (P : List ℕ) (s t : GW hF M₀) (hP : t.1 = nodeOf s.1 P) (j : ℕ)
    (z : VarSymb) (T : VarType), (ctxOf (glat t j)).ref z = some T → T.keepable = true →
    T.etaInj = true → pnm P s t hP (porig P s t hP z) = z
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | c :: P, s, t, hP, j, z, T, hz, hk, he => by
      change pnm P (stepW s c (born_step hP)) t hP (nm (stepW s c (born_step hP))
        (orig s (stepW s c (born_step hP)) (porig P (stepW s c (born_step hP)) t hP z))) = z
      rw [nm_orig hV hS hW hM₀ ⟨c, rfl⟩
        (pPreOk hV hS hW hM₀ P (stepW s c (born_step hP)) t hP j z T hz hk) hk he]
      exact pnm_porig P (stepW s c (born_step hP)) t hP j z T hz hk he

include hV hS hW hM₀ in
theorem rnm_rorig (b : GW hF M₀) {z : VarSymb} {T : VarType} (hz : DeclAt b z T)
    (hk : T.keepable = true) (he : T.etaInj = true) : rnm b (rorig b z) = z := by
  obtain ⟨j, hj⟩ := hz
  exact pnm_porig hV hS hW hM₀ (rpath b) (groot hF M₀) b (rpath_eq b) j z T hj hk he

include hV hM₀ in
theorem rorig_rnm (b : GW hF M₀) {v : VarSymb} {U : VarType} (hv : DeclAt (groot hF M₀) v U)
    (hk : U.keepable = true) (he : U.etaInj = true) : rorig b (rnm b v) = v := by
  obtain ⟨i, hi⟩ := hv
  exact porig_pnm hV hM₀ (rpath b) (groot hF M₀) b (rpath_eq b) i v U hi hk he

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem etaInj_of_step {U W : VarType} {s : Step} (h : U.step s = some W)
    (hW : W.etaInj = true) : U.etaInj = true := by
  cases U with
  | Var => cases s <;> cases h
  | VTypeOne => cases s <;> cases h
  | VTypeProd A B =>
      cases s
      case fst => cases h; simp [VarType.etaInj, hW]
      case snd => cases h; simp [VarType.etaInj, hW]
      all_goals cases h
  | VTypeBox A =>
      cases s
      case box => cases h; exact hW
      case here =>
        obtain ⟨-, rfl⟩ := VarType.step_here h
        exact hW
      all_goals cases h
  | VTypeDia A => rfl

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A type with a possible position is η-faithful. -/
theorem etaInj_of_walkTy : ∀ (π : List Step) {U : VarType} {X : VarType},
    Step.walkTy U π = some (.VTypeDia X) → U.etaInj = true
  | [], U, X, h => by
      obtain rfl := Option.some.inj h
      rfl
  | s :: π, U, X, h => by
      obtain ⟨W, hW, hw⟩ := Option.bind_eq_some_iff.mp h
      have ih := etaInj_of_walkTy π hw
      cases s with
      | keep =>
          change (if U.keepable = true then some U else none) = some W at hW
          split_ifs at hW
          cases hW
          exact ih
      | box =>
          change (if ModalSys.keepOnly = true then none else U.step .box) = some W at hW
          split_ifs at hW
          exact etaInj_of_step hW ih
      | fst => exact etaInj_of_step hW ih
      | snd => exact etaInj_of_step hW ih
      | dia => exact etaInj_of_step hW ih
      | here => exact etaInj_of_step hW ih

/-! ## Reading along an arrow -/

omit [ModalSys] [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem ppath_ext {z : VarSymb} {r : List Step} (hz : PPath z.path) (hr : PPath r) :
    PPath (z.ext r).path := by
  rw [VarSymb.ext_path]
  exact fun x hx => (List.mem_append.mp hx).elim (hz x) (hr x)

/-- What follows the first level step is kept by `cNext`. -/
theorem cNext_append (b : GW hF M₀) (v : VarSymb) (hz : PPath (rnm b v).path) (r s : List Step)
    (h : 0 < Step.levels r ∨ ∃ st t, s = st :: t ∧ st.isProj = false) :
    cNext b v (r ++ s) = (cNext b v r).ext s := by
  unfold cNext
  rw [VarSymb.ext_append]
  by_cases h0 : Step.levels r = 0
  · obtain ⟨st, t, rfl, hst⟩ := h.resolve_left (by omega)
    have hz' := ppath_ext hz (ppath_of_levels0 h0)
    rw [show ((rnm b v).ext r).ext (st :: t) = (VarSymb.step ((rnm b v).ext r) st).ext t from rfl,
      preIx_lvl _ hz' hst, preIx_ppath _ hz']
    rfl
  · obtain ⟨π₀, st, r', rfl, hπ₀, hst⟩ := split_first r (by omega)
    have hz' := ppath_ext hz hπ₀
    rw [VarSymb.ext_append,
      show ((rnm b v).ext π₀).ext (st :: r') =
        (VarSymb.step ((rnm b v).ext π₀) st).ext r' from rfl,
      ← VarSymb.ext_append, preIx_lvl _ hz' hst, preIx_lvl _ hz' hst, VarSymb.ext_append]

theorem cNext_append' (b : GW hF M₀) (v : VarSymb) (hz : PPath (rnm b v).path) (r s : List Step)
    (h : s = [] ∨ ∃ st t, s = st :: t ∧ st.isProj = false) :
    cNext b v (r ++ s) = (cNext b v r).ext s := by
  rcases h with rfl | h
  · rw [List.append_nil]
    rfl
  · exact cNext_append b v hz r s (.inr h)

include hV hM₀ in
/-- Read back at the root, the address itself. -/
theorem cNext_nil (b : GW hF M₀) {v : VarSymb} {U : VarType} (hd : DeclAt (groot hF M₀) v U)
    (hk : U.keepable = true) (he : U.etaInj = true) : cNext b v [] = v := by
  obtain ⟨j, hj⟩ := id (declAt_rnm hV hM₀ b hd hk)
  unfold cNext
  rw [show (rnm b v).ext [] = rnm b v from rfl, preIx_ppath _ (reach_ppath hj).1,
    rorig_rnm hV hM₀ b hd hk he]

include hV hM₀ in
/-- Read back at the root, from a level step on, the address itself. -/
theorem cNext_lvl (b : GW hF M₀) {v : VarSymb} {U : VarType} (hd : DeclAt (groot hF M₀) v U)
    (hk : U.keepable = true) (he : U.etaInj = true) {st : Step} (hst : st.isProj = false)
    (t : List Step) : cNext b v (st :: t) = (VarSymb.step v st).ext t := by
  obtain ⟨j, hj⟩ := id (declAt_rnm hV hM₀ b hd hk)
  unfold cNext
  rw [show (rnm b v).ext (st :: t) = (VarSymb.step (rnm b v) st).ext t from rfl,
    preIx_lvl _ (reach_ppath hj).1 hst, rorig_rnm hV hM₀ b hd hk he]

include hF hV hS hW hM₀ in
/-- A keep-first position of a declared address is the family of what it reads. -/
theorem cLab_keep_of (hT : ModalSys.T = true) {v : VarSymb} {U : VarType}
    (hd : DeclAt (groot hF M₀) v U) (hv : PPath v.path) (hk : U.keepable = true) {r : List Step}
    {A : VarType} (hw : Step.walkTy U r = some (.VTypeDia A)) (g : GW hF M₀) :
    cLab ((VarSymb.step v .keep).ext r) g = .fam fun b => cLab (cNext b.1 v r) b.1 := by
  rw [cLab_keep hv]
  congr 1
  funext b
  obtain ⟨v', U', π', -, hv', -, hlπ, -, e⟩ := cNext_cases hV hS hW hM₀ hT b.1 hd hk hw rfl
  rw [dif_pos]
  rw [levels_kept hv, e, VarSymb.ext_path, Step.levels_append, levels_pp hv', hlπ]
  omega

/-! ## Labels under the path edits -/

include hF hV hS hW hM₀ in
/-- ⭐**A leaf operation that follows a path edit on labels**: it passes through families, edits
    root paths at their own level, and holds at level zero; so it holds at every level. -/
theorem cLab_edit (hT : ModalSys.T = true)
    (op : ℕ → ∀ {w : GW hF M₀}, CLeaf hF M₀ w → CLeaf hF M₀ w) {U : VarType}
    (hkU : U.keepable = true) {s₁ s₂ : List Step}
    (hs₁ : ∃ A, Step.walkTy U s₁ = some (.VTypeDia A))
    (hs₂ : ∃ A, Step.walkTy U s₂ = some (.VTypeDia A))
    (happ₁ : s₁ = [] ∨ ∃ st t, s₁ = st :: t ∧ st.isProj = false)
    (happ₂ : s₂ = [] ∨ ∃ st t, s₂ = st :: t ∧ st.isProj = false)
    (hfam : ∀ (i : ℕ) {w : GW hF M₀} (f : (a : (carrows hF M₀).Acc w) → CLeaf hF M₀ a.1),
      op (i + 1) (.fam f) = .fam fun a => op i (f a))
    (hroot : ∀ (i : ℕ) {w : GW hF M₀} (r : VarSymb) (p : List Step), Step.levels p = i + 1 →
      op (i + 1) (.root r (p ++ s₁) : CLeaf hF M₀ w) = .root r (p ++ s₂))
    (hbase : ∀ v, DeclAt (groot hF M₀) v U → PPath v.path → ∀ g : GW hF M₀,
      op 0 (cLab (v.ext s₁) g) = cLab (v.ext s₂) g) :
    ∀ (j : ℕ) {v : VarSymb} {U₀ : VarType} {π : List Step}, DeclAt (groot hF M₀) v U₀ →
      PPath v.path → Step.walkTy U₀ π = some U → Step.levels π = j → ∀ g : GW hF M₀,
      op j (cLab (v.ext (π ++ s₁)) g) = cLab (v.ext (π ++ s₂)) g := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  intro j
  induction j with
  | zero =>
      intro v U₀ π hd hv hw hn g
      have hπ := ppath_of_levels0 hn
      rw [VarSymb.ext_append, VarSymb.ext_append]
      exact hbase _ (declAt_ext hd hπ hw) (ppath_ext hv hπ) g
  | succ j IH =>
      intro v U₀ π hd hv hw hn g
      obtain ⟨π₀, st, r, rfl, hπ₀, hst⟩ := split_first π (by omega)
      have hpre := ppath_ext hv hπ₀
      rw [Step.walkTy_append, walkTy_ppath U₀ hπ₀] at hw
      obtain ⟨U₁, hU₁, hw₀⟩ := Option.bind_eq_some_iff.mp hw
      have hd₀ : DeclAt (groot hF M₀) (v.ext π₀) U₁ :=
        declAt_ext hd hπ₀ ((walkTy_ppath U₀ hπ₀).trans hU₁)
      have hlr : Step.levels r = j := by
        rw [Step.levels_append, levels_pp hπ₀, Step.levels_cons, if_neg (by simp [hst])] at hn
        omega
      have key : ∀ s : List Step, v.ext ((π₀ ++ st :: r) ++ s) =
          (VarSymb.step (v.ext π₀) st).ext (r ++ s) := fun s => by
        rw [List.append_assoc, VarSymb.ext_append]
        rfl
      rw [key, key]
      cases st with
      | fst => cases hst
      | snd => cases hst
      | here => cases hst
      | box =>
          obtain ⟨W, hW', -⟩ := Option.bind_eq_some_iff.mp hw₀
          change (if ModalSys.keepOnly = true then none else U₁.step .box) = some W at hW'
          rw [if_pos hko] at hW'
          cases hW'
      | dia =>
          rw [cLab_dia hpre, cLab_dia hpre]
          exact hroot j (v.ext π₀) (.dia :: r) (by
            rw [Step.levels_cons, if_neg (by decide)]
            omega)
      | keep =>
          obtain ⟨W, hW', -⟩ := Option.bind_eq_some_iff.mp hw₀
          have hkU₁ : U₁.keepable = true := Step.typeStep_level_keepable rfl hW'
          have hr : Step.walkTy U₁ r = some U := (walkTy_keep hkU₁ r).symm.trans hw₀
          obtain ⟨A₁, h₁⟩ := hs₁
          obtain ⟨A₂, h₂⟩ := hs₂
          have hr₁ : Step.walkTy U₁ (r ++ s₁) = some (.VTypeDia A₁) := by
            rw [Step.walkTy_append, hr]
            exact h₁
          have hr₂ : Step.walkTy U₁ (r ++ s₂) = some (.VTypeDia A₂) := by
            rw [Step.walkTy_append, hr]
            exact h₂
          rw [cLab_keep_of hV hS hW hM₀ hT hd₀ hpre hkU₁ hr₁ g,
            cLab_keep_of hV hS hW hM₀ hT hd₀ hpre hkU₁ hr₂ g, hfam]
          congr 1
          funext b
          obtain ⟨v', U', π', hd', hv', hw', hlπ, -, e⟩ :=
            cNext_cases hV hS hW hM₀ hT b.1 hd₀ hkU₁ hr hkU
          obtain ⟨jz, hjz⟩ := id (declAt_rnm hV hM₀ b.1 hd₀ hkU₁)
          have hzp := (reach_ppath hjz).1
          rw [cNext_append' b.1 _ hzp r s₁ happ₁, cNext_append' b.1 _ hzp r s₂ happ₂, e,
            ← VarSymb.ext_append, ← VarSymb.ext_append]
          exact IH hd' hv' hw' (hlπ.trans hlr) b.1

include hF hV hS hW hM₀ in
/-- ⭐**A possible address kept**: `dk` at its own level is the kept address's label. -/
theorem cLab_dk (hT : ModalSys.T = true) {A : VarType} (j : ℕ) {v : VarSymb} {U₀ : VarType}
    {π : List Step} (hd : DeclAt (groot hF M₀) v U₀) (hv : PPath v.path)
    (hw : Step.walkTy U₀ π = some (.VTypeDia A)) (hn : Step.levels π = j) (g : GW hF M₀) :
    Arrows.Leaf.dk hF j (cLab (v.ext π) g) = cLab (v.ext (π ++ [.keep])) g := by
  have h := cLab_edit hV hS hW hM₀ hT (fun i {_} l => Arrows.Leaf.dk hF i l)
    (U := .VTypeDia A) rfl (s₁ := []) (s₂ := [.keep]) ⟨A, rfl⟩ ⟨A, rfl⟩ (.inl rfl)
    (.inr ⟨.keep, [], rfl, rfl⟩) (fun _ {_} _ => rfl)
    (fun i {_} r p hp => by
      rw [List.append_nil]
      change (.root r (Step.keepAt (i + 1) p) : CLeaf hF M₀ _) = _
      rw [keepAt_own p _ hp])
    (fun v' hd' hv' g' => by
      rw [show v'.ext [] = v' from rfl, cLab_ppath hv',
        show v'.ext [.keep] = (VarSymb.step v' .keep).ext [] from rfl,
        cLab_keep_of hV hS hW hM₀ hT hd' hv' rfl (A := A) rfl g']
      change Arrows.Leaf.fam _ = _
      congr 1
      funext b
      rw [cNext_nil hV hM₀ b.1 hd' rfl rfl, cLab_ppath hv']
      rfl) j hd hv hw hn g
  simpa using h

include hF hV hS hW hM₀ in
/-- ⭐**The content of a possible address kept**: `dkB` at the address's level. -/
theorem cLab_dkB (hT : ModalSys.T = true) {A X : VarType} {ρ₁ : List Step}
    (hρ : Step.walkTy A ρ₁ = some (.VTypeDia X)) (j : ℕ) {v : VarSymb} {U₀ : VarType}
    {π : List Step} (hd : DeclAt (groot hF M₀) v U₀) (hv : PPath v.path)
    (hw : Step.walkTy U₀ π = some (.VTypeDia A)) (hn : Step.levels π = j) (g : GW hF M₀) :
    Arrows.Leaf.dkB hF j (cLab (v.ext (π ++ .dia :: ρ₁)) g) =
      cLab (v.ext (π ++ .keep :: .dia :: ρ₁)) g :=
  cLab_edit hV hS hW hM₀ hT (fun i {_} l => Arrows.Leaf.dkB hF i l)
    (U := .VTypeDia A) rfl (s₁ := .dia :: ρ₁) (s₂ := .keep :: .dia :: ρ₁) ⟨X, hρ⟩
    ⟨X, by rw [walkTy_keep rfl]; exact hρ⟩ (.inr ⟨.dia, ρ₁, rfl, rfl⟩)
    (.inr ⟨.keep, _, rfl, rfl⟩) (fun _ {_} _ => rfl)
    (fun i {_} r p hp => by
      change (.root r (Step.shiftAt (i + 1) (p ++ .dia :: ρ₁)) : CLeaf hF M₀ _) = _
      rw [shiftAt_own p _ ρ₁ hp rfl])
    (fun v' hd' hv' g' => by
      rw [show v'.ext (.dia :: ρ₁) = (VarSymb.step v' .dia).ext ρ₁ from rfl, cLab_dia hv',
        show v'.ext (.keep :: .dia :: ρ₁) = (VarSymb.step v' .keep).ext (.dia :: ρ₁) from rfl,
        cLab_keep_of hV hS hW hM₀ hT hd' hv' rfl (A := X) (by exact hρ) g']
      change Arrows.Leaf.fam _ = _
      congr 1
      funext b
      rw [cNext_lvl hV hM₀ b.1 hd' rfl rfl (by decide), cLab_dia hv']
      rfl) j hd hv hw hn g

include hF hV hS hW hM₀ in
/-- ⭐**The content of a necessary address kept**: `shift` at the address's level. -/
theorem cLab_shift (hT : ModalSys.T = true) {A X : VarType} {ρ₁ : List Step}
    (hρ : Step.walkTy A ρ₁ = some (.VTypeDia X)) (j : ℕ) {v : VarSymb} {U₀ : VarType}
    {π : List Step} (hd : DeclAt (groot hF M₀) v U₀) (hv : PPath v.path)
    (hw : Step.walkTy U₀ π = some (.VTypeBox A)) (hn : Step.levels π = j) (g : GW hF M₀) :
    Arrows.Leaf.shift hF j (cLab (v.ext (π ++ .keep :: .here :: ρ₁)) g) =
      cLab (v.ext (π ++ .keep :: .keep :: .here :: ρ₁)) g := by
  have hw₁ : Step.walkTy (.VTypeBox A) (.keep :: .here :: ρ₁) = some (.VTypeDia X) := by
    rw [walkTy_keep rfl, walkTy_here hT]
    exact hρ
  have hw₂ : Step.walkTy (.VTypeBox A) (.keep :: .keep :: .here :: ρ₁) = some (.VTypeDia X) := by
    rw [walkTy_keep rfl]
    exact hw₁
  refine cLab_edit hV hS hW hM₀ hT (fun i {_} l => Arrows.Leaf.shift hF i l)
    (U := .VTypeBox A) rfl ⟨X, hw₁⟩ ⟨X, hw₂⟩ (.inr ⟨.keep, _, rfl, rfl⟩)
    (.inr ⟨.keep, _, rfl, rfl⟩) (fun _ {_} _ => rfl) ?_ ?_ j hd hv hw hn g
  · intro i _ r p hp
    change (.root r (Step.shiftAt (i + 1) (p ++ .keep :: .here :: ρ₁)) : CLeaf hF M₀ _) = _
    rw [shiftAt_own p _ _ hp rfl]
  · intro v' hd' hv' g'
    have he : (VarType.VTypeBox A).etaInj = true := etaInj_of_walkTy _ hw₁
    have hr : Step.walkTy (.VTypeBox A) (.here :: ρ₁) = some (.VTypeDia X) := by
      rw [walkTy_here hT]
      exact hρ
    rw [show v'.ext (.keep :: .here :: ρ₁) = (VarSymb.step v' .keep).ext (.here :: ρ₁) from rfl,
      show v'.ext (.keep :: .keep :: .here :: ρ₁) =
        (VarSymb.step v' .keep).ext (.keep :: .here :: ρ₁) from rfl,
      cLab_keep_of hV hS hW hM₀ hT hd' hv' rfl hr g',
      cLab_keep_of hV hS hW hM₀ hT hd' hv' rfl hw₁ g']
    change Arrows.Leaf.fam _ = _
    congr 1
    funext b
    rw [cNext_lvl hV hM₀ b.1 hd' rfl he (by decide),
      cLab_keep_of hV hS hW hM₀ hT hd' hv' rfl hr b.1]

include hF hV hS hW hM₀ in
/-- Collapsing the top of a kept address's label reads it at the anchor. -/
theorem cLab_collapse_zero (hT : ModalSys.T = true) {A X : VarType} {ρ₁ : List Step}
    (hρ : Step.walkTy A ρ₁ = some (.VTypeDia X)) {v : VarSymb}
    (hd : DeclAt (groot hF M₀) v (.VTypeBox A)) (hv : PPath v.path) (g : GW hF M₀) :
    Arrows.Leaf.collapse hT 0 (cLab (v.ext (.keep :: .here :: ρ₁)) g) =
      cLab (cNext g v (.here :: ρ₁)) g := by
  have hr : Step.walkTy (.VTypeBox A) (.here :: ρ₁) = some (.VTypeDia X) := by
    rw [walkTy_here hT]
    exact hρ
  rw [show v.ext (.keep :: .here :: ρ₁) = (VarSymb.step v .keep).ext (.here :: ρ₁) from rfl,
    cLab_keep_of hV hS hW hM₀ hT hd hv rfl hr g]
  rfl

include hF hV hS hW hM₀ in
/-- ⭐**A kept address's content read at the world**: `collapse` below the top level. -/
theorem cLab_collapse (hT : ModalSys.T = true) {A X : VarType} {ρ₁ : List Step}
    (hρ : Step.walkTy A ρ₁ = some (.VTypeDia X)) (n : ℕ) : ∀ {v : VarSymb} {U₀ : VarType}
    {π : List Step}, DeclAt (groot hF M₀) v U₀ → PPath v.path →
    Step.walkTy U₀ π = some (.VTypeBox A) → Step.levels π = n + 1 → ∀ g : GW hF M₀,
    Arrows.Leaf.collapse hT (n + 1) (cLab (v.ext (π ++ .keep :: .here :: ρ₁)) g) =
      cLab (v.ext (π ++ .here :: ρ₁)) g := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  have hw₁ : Step.walkTy (.VTypeBox A) (.keep :: .here :: ρ₁) = some (.VTypeDia X) := by
    rw [walkTy_keep rfl, walkTy_here hT]
    exact hρ
  have hwh : Step.walkTy (.VTypeBox A) (.here :: ρ₁) = some (.VTypeDia X) := by
    rw [walkTy_here hT]
    exact hρ
  have he : (VarType.VTypeBox A).etaInj = true := etaInj_of_walkTy _ hw₁
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro v U₀ π hd hv hw hn g
  obtain ⟨π₀, st, r, rfl, hπ₀, hst⟩ := split_first π (by omega)
  have hpre := ppath_ext hv hπ₀
  rw [Step.walkTy_append, walkTy_ppath U₀ hπ₀] at hw
  obtain ⟨U₁, hU₁, hw₀⟩ := Option.bind_eq_some_iff.mp hw
  have hd₀ : DeclAt (groot hF M₀) (v.ext π₀) U₁ :=
    declAt_ext hd hπ₀ ((walkTy_ppath U₀ hπ₀).trans hU₁)
  have hlr : Step.levels r = n := by
    rw [Step.levels_append, levels_pp hπ₀, Step.levels_cons, if_neg (by simp [hst])] at hn
    omega
  have key : ∀ s : List Step, v.ext ((π₀ ++ st :: r) ++ s) =
      (VarSymb.step (v.ext π₀) st).ext (r ++ s) := fun s => by
    rw [List.append_assoc, VarSymb.ext_append]
    rfl
  rw [key, key]
  cases st with
  | fst => cases hst
  | snd => cases hst
  | here => cases hst
  | box =>
      obtain ⟨W, hW', -⟩ := Option.bind_eq_some_iff.mp hw₀
      change (if ModalSys.keepOnly = true then none else U₁.step .box) = some W at hW'
      rw [if_pos hko] at hW'
      cases hW'
  | dia =>
      rw [cLab_dia hpre, cLab_dia hpre]
      change (.root _ (Step.collapseAt (n + 1) ((Step.dia :: r) ++ .keep :: .here :: ρ₁)) :
        CLeaf hF M₀ _) = _
      rw [collapseAt_own (.dia :: r) (n + 1) ρ₁ (by
        rw [Step.levels_cons, if_neg (by decide)]
        omega)]
      rfl
  | keep =>
      obtain ⟨W, hW', -⟩ := Option.bind_eq_some_iff.mp hw₀
      have hkU₁ : U₁.keepable = true := Step.typeStep_level_keepable rfl hW'
      have hr : Step.walkTy U₁ r = some (.VTypeBox A) := (walkTy_keep hkU₁ r).symm.trans hw₀
      have hr₁ : Step.walkTy U₁ (r ++ .keep :: .here :: ρ₁) = some (.VTypeDia X) := by
        rw [Step.walkTy_append, hr]
        exact hw₁
      have hr₂ : Step.walkTy U₁ (r ++ .here :: ρ₁) = some (.VTypeDia X) := by
        rw [Step.walkTy_append, hr]
        exact hwh
      rw [cLab_keep_of hV hS hW hM₀ hT hd₀ hpre hkU₁ hr₁ g,
        cLab_keep_of hV hS hW hM₀ hT hd₀ hpre hkU₁ hr₂ g]
      change Arrows.Leaf.fam _ = _
      congr 1
      funext b
      obtain ⟨jz, hjz⟩ := id (declAt_rnm hV hM₀ b.1 hd₀ hkU₁)
      have hzp := (reach_ppath hjz).1
      obtain ⟨v', U', π', hd', hv', hw', hlπ, -, e⟩ :=
        cNext_cases hV hS hW hM₀ hT b.1 hd₀ hkU₁ hr rfl
      beta_reduce
      rw [cNext_append b.1 _ hzp r _ (.inr ⟨.keep, _, rfl, rfl⟩)]
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · -- no level left: read at the arrow's end
        subst h0
        have hr0 : PPath r := ppath_of_levels0 hlr
        have hπ' : PPath π' := ppath_of_levels0 (hlπ.trans hlr)
        have hdz : DeclAt b.1 ((rnm b.1 (v.ext π₀)).ext r) (.VTypeBox A) :=
          declAt_ext ⟨jz, hjz⟩ hr0 hr
        have hc : cNext b.1 (v.ext π₀) r = rorig b.1 ((rnm b.1 (v.ext π₀)).ext r) := by
          unfold cNext
          exact preIx_ppath _ (ppath_ext hzp hr0)
        have hdv : DeclAt (groot hF M₀) (cNext b.1 (v.ext π₀) r) (.VTypeBox A) := by
          rw [e]
          exact declAt_ext hd' hπ' hw'
        have hpv : PPath (cNext b.1 (v.ext π₀) r).path := by
          rw [e]
          exact ppath_ext hv' hπ'
        rw [cLab_collapse_zero hV hS hW hM₀ hT hρ hdv hpv b.1]
        congr 1
        rw [hc]
        unfold cNext
        rw [rnm_rorig hV hS hW hM₀ b.1 hdz rfl he, VarSymb.ext_append]
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [cNext_append b.1 _ hzp r _ (.inl (by omega)), e, ← VarSymb.ext_append,
          ← VarSymb.ext_append]
        exact IH m (by omega) hd' hv' hw' (hlπ.trans hlr) b.1

end Decl

end GArrow

end V12M
