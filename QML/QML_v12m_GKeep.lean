import QML.QML_v12m_GShape
import QML.QML_v12m_GLiftEnt

/-!
# QML v12m — the growing tree: the leaf-valued root action

Under T + 4 the canonical labels are computed from addresses (`docs/v12-modal-extensions.md` §3 4,
"Phase 2b: the definition, corrected"):

* ⭐`gMem t Y P`: the member at the path `P` of a **kept address** `Y` (an address whose top level
  is a `keep`, as `u.keep.q`): along the empty path, the label of `Y` read at the world itself
  (its top level collapsed); along `c :: P`, the address kept once more and translated by the
  edge's entries, along `P`.  This is `pTr` on addresses.
* ⭐`gLab t y`: the label of an address, by its first level step — a root with the address for
  none, a root path from the projection prefix for `dia`, the family of its members for `keep`.
* ⭐`gKeepP`, `gKeep`: the root action.  Along the identity a root path stays; along a nonempty
  path a path typed in the root's declared type is read as the kept address `r.keep.p`, and any
  other path is a junk root's.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-- An address declared at some stage of a world, at a type. -/
def DeclAt (s : GW hF M₀) (v : VarSymb) (T : VarType) : Prop :=
  ∃ i, (ctxOf (glat s i)).ref v = some T

/-- A declared address keeps its declaration at later stages. -/
theorem DeclAt.at_le (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {v : VarSymb} {T : VarType} {i i' : ℕ}
    (h : (ctxOf (glat s i)).ref v = some T) (hii : i ≤ i') : (ctxOf (glat s i')).ref v = some T :=
  (ctxOf_le_of_suffix (gnet_lang_suffix hF hM₀ (by omega)
    (live_gbirth hF hM₀ s.2 (Nat.le_add_right _ i)))).ref h

/-- An address is declared at one type. -/
theorem DeclAt.unique (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {v : VarSymb} {T T' : VarType}
    (h : DeclAt s v T) (h' : DeclAt s v T') : T = T' := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨i', hi'⟩ := h'
  have e₁ := DeclAt.at_le hM₀ hi (le_max_left i i')
  have e₂ := DeclAt.at_le hM₀ hi' (le_max_right i i')
  rw [e₁] at e₂
  exact Option.some.inj e₂

/-- A root no world declares: the root of the leaves nothing names. -/
abbrev junkR : VarSymb := .root (.bnd 0)

/-- The level of an address's first level step, counted from its end (`VarSymb.shift`). -/
abbrev topL (Y : VarSymb) : ℕ := Step.levels Y.path - 1

/-- The kept address one edge further: kept once more at its top level, then translated by the
    edge's entries. -/
noncomputable abbrev keptTr (t : GW hF M₀) (c : ℕ) (Y : VarSymb) : VarSymb :=
  eIdx (fmapL hF M₀ (c :: t.1)) (Y.shift (topL Y))

/-- ⭐**The member of a kept address along a path**: along the empty path the label of the
    address read at the world (its top level collapsed, `gLab`); along `c :: P`, the address kept
    and translated along the edge (`keptTr`), along `P`.  The level guards hold for the genuine
    translations; they make the recursion well-founded. -/
noncomputable def gMem : (t t' : GW hF M₀) → (P : List ℕ) → t'.1 = nodeOf t.1 P → VarSymb →
    GLeaf hF M₀ t'
  | _, t', [], _, Y =>
      if _hl : Step.levels (Y.collapse (topL Y)).path < Step.levels Y.path then
        match splitLevel (Y.collapse (topL Y)).path with
        | none => .root (Y.collapse (topL Y)) []
        | some (pre, .dia, r) =>
            .root ((VarSymb.root (Y.collapse (topL Y)).rt).ext pre) (.dia :: r)
        | some (_, .keep, _) =>
            .fam fun b => gMem t' b.1 (pathOf b.2.down) (pathOf_eq b.2.down) (Y.collapse (topL Y))
        | some _ => .root junkR []
      else .root junkR []
  | t, t', c :: P, h, Y =>
      if _hl : Step.levels (keptTr t c Y).path ≤ Step.levels Y.path then
        gMem (stepW t c (born_step h)) t' P h (keptTr t c Y)
      else .root junkR []
termination_by _ _ P _ Y => (Step.levels Y.path, P.length)
decreasing_by
  · exact Prod.Lex.left _ _ ‹_›
  · rcases Nat.lt_or_eq_of_le ‹_› with hl | hl
    · exact Prod.Lex.left _ _ hl
    · rw [hl]
      exact Prod.Lex.right _ (Nat.lt_succ_self _)

/-- ⭐**The label of an address** at a world, by its first level step: none, the address itself;
    `dia`, a root path from the projection prefix; `keep`, the family of its members. -/
noncomputable def gLab (t : GW hF M₀) (y : VarSymb) : GLeaf hF M₀ t :=
  match splitLevel y.path with
  | none => .root y []
  | some (pre, .dia, r) => .root ((VarSymb.root y.rt).ext pre) (.dia :: r)
  | some (_, .keep, _) => .fam fun b => gMem t b.1 (pathOf b.2.down) (pathOf_eq b.2.down) y
  | some _ => .root junkR []

theorem gMem_nil (t t' : GW hF M₀) (h : t'.1 = nodeOf t.1 []) (Y : VarSymb) :
    gMem t t' [] h Y =
      if Step.levels (Y.collapse (topL Y)).path < Step.levels Y.path then
        gLab t' (Y.collapse (topL Y))
      else .root junkR [] := by
  by_cases hl : Step.levels (Y.collapse (topL Y)).path < Step.levels Y.path
  · rw [if_pos hl, gMem, dif_pos hl]
    rfl
  · rw [if_neg hl, gMem, dif_neg hl]

theorem gMem_cons (t t' : GW hF M₀) (c : ℕ) (P : List ℕ) (h : t'.1 = nodeOf t.1 (c :: P))
    (Y : VarSymb) :
    gMem t t' (c :: P) h Y =
      if Step.levels (keptTr t c Y).path ≤ Step.levels Y.path then
        gMem (stepW t c (born_step h)) t' P h (keptTr t c Y)
      else .root junkR [] := by
  by_cases hl : Step.levels (keptTr t c Y).path ≤ Step.levels Y.path
  · rw [if_pos hl, gMem, dif_pos hl]
  · rw [if_neg hl, gMem, dif_neg hl]

/-- The member depends on the path, not on how the end is reached. -/
theorem gMem_path {t t' : GW hF M₀} {P P' : List ℕ} (e : P = P') (h : t'.1 = nodeOf t.1 P)
    (h' : t'.1 = nodeOf t.1 P') (Y : VarSymb) : gMem t t' P h Y = gMem t t' P' h' Y := by
  subst e
  rfl

/-- The member depends on the start world, not on how its proofs are reached. -/
theorem gMem_world {t₀ t₁ t' : GW hF M₀} (e : t₀ = t₁) (P : List ℕ) (h : t'.1 = nodeOf t₀.1 P)
    (h' : t'.1 = nodeOf t₁.1 P) (Y : VarSymb) : gMem t₀ t' P h Y = gMem t₁ t' P h' Y := by
  subst e
  rfl

/-- A path typed in an address's declared type, a possible type: a root possibility's position. -/
def TypedAt (s : GW hF M₀) (r : VarSymb) (p : List Step) : Prop :=
  ∃ A, DeclAt s r (.VTypeDia A) ∧ Step.Typed (.VTypeDia A) p

open Classical in
/-- ⭐**The root action along a path**: along the empty path the root path itself; along a
    nonempty path, a path typed in the root's declared type is read as the kept address
    `r.keep.p` (`gMem`), any other path as a junk root's. -/
noncomputable def gKeepP (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (r : VarSymb)
    (p : List Step) : GLeaf hF M₀ t :=
  match P, h with
  | [], _ => .root r p
  | c :: P, h =>
      if TypedAt s r p then gMem s t (c :: P) h ((VarSymb.step r .keep).ext p) else .root junkR p

theorem gKeepP_path {s t : GW hF M₀} {P P' : List ℕ} (e : P = P') (h : t.1 = nodeOf s.1 P)
    (h' : t.1 = nodeOf s.1 P') (r : VarSymb) (p : List Step) :
    gKeepP s t P h r p = gKeepP s t P' h' r p := by
  subst e
  rfl

/-- ⭐**The canonical root action**: along an arrow, along its path (`gKeepP`). -/
noncomputable def gKeep (s : GW hF M₀) (r : VarSymb) (a : (garrows hF M₀).Acc s)
    (p : List Step) : GLeaf hF M₀ a.1 :=
  gKeepP s a.1 (pathOf a.2.down) (pathOf_eq a.2.down) r p

/-! ## Path operations at a path's own level -/

omit [ModalSys] in
theorem keepAt_own : ∀ (p : List Step) (m : ℕ), Step.levels p = m → Step.keepAt m p = p ++ [.keep]
  | [], m, h => by
      change 0 = m at h
      subst h
      rfl
  | s :: p, m, h => by
      change (if s.isProj then 0 else 1) + Step.levels p = m at h
      by_cases hs : s.isProj = true
      · rw [if_pos hs, Nat.zero_add] at h
        cases m <;> simp only [Step.keepAt, hs, if_true, List.cons_append] <;>
          rw [keepAt_own p _ h]
      · rw [if_neg hs] at h
        obtain rfl : m = Step.levels p + 1 := by omega
        simp only [Step.keepAt, hs, Bool.false_eq_true, if_false, List.cons_append]
        rw [keepAt_own p _ rfl]

omit [ModalSys] in
theorem shiftAt_own : ∀ (p : List Step) (m : ℕ) {s : Step} (q : List Step), Step.levels p = m →
    s.isProj = false → Step.shiftAt m (p ++ s :: q) = p ++ .keep :: s :: q
  | [], m, s, q, h, hs => by
      change 0 = m at h
      subst h
      simp [Step.shiftAt, hs]
  | t :: p, m, s, q, h, hs => by
      change (if t.isProj then 0 else 1) + Step.levels p = m at h
      by_cases ht : t.isProj = true
      · rw [if_pos ht, Nat.zero_add] at h
        simp only [List.cons_append, Step.shiftAt, ht, if_true]
        rw [shiftAt_own p m q h hs]
      · rw [if_neg ht] at h
        obtain rfl : m = Step.levels p + 1 := by omega
        simp only [List.cons_append, Step.shiftAt, ht, Bool.false_eq_true, if_false]
        rw [shiftAt_own p _ q rfl hs]

omit [ModalSys] in
theorem collapseAt_own : ∀ (p : List Step) (m : ℕ) (q : List Step), Step.levels p = m →
    Step.collapseAt m (p ++ .keep :: .here :: q) = p ++ .here :: q
  | [], m, q, h => by
      change 0 = m at h
      subst h
      simp [Step.collapseAt, Step.isProj]
  | t :: p, m, q, h => by
      change (if t.isProj then 0 else 1) + Step.levels p = m at h
      by_cases ht : t.isProj = true
      · rw [if_pos ht, Nat.zero_add] at h
        simp only [List.cons_append, Step.collapseAt, ht, if_true]
        rw [collapseAt_own p m q h]
      · rw [if_neg ht] at h
        obtain rfl : m = Step.levels p + 1 := by omega
        simp only [List.cons_append, Step.collapseAt, ht, Bool.false_eq_true, if_false]
        by_cases hc : Step.levels p = 0 ∧ t = .keep ∧ Step.headLvl (p ++ .keep :: .here :: q) = true
        · rw [if_pos hc]
          obtain ⟨hl0, rfl, hh⟩ := hc
          cases p with
          | nil => rfl
          | cons u p' =>
              exfalso
              change (if u.isProj then 0 else 1) + Step.levels p' = 0 at hl0
              have hu : u.isProj = true := by
                by_contra hu
                rw [if_neg hu] at hl0
                omega
              simp [Step.headLvl, hu] at hh
        · rw [if_neg hc, collapseAt_own p _ q rfl]

omit [ModalSys] in
/-- ⭐Collapsing a `keep` level at a path's own level deletes the `keep` (the keep-absorbing
    case deletes the `keep` before it, the same list). -/
theorem collapseAt_keep_own : ∀ (p : List Step) (m : ℕ) (q : List Step), Step.levels p = m →
    Step.collapseAt m (p ++ .keep :: q) = p ++ q
  | [], m, q, h => by
      change 0 = m at h
      subst h
      simp [Step.collapseAt, Step.isProj]
  | t :: p, m, q, h => by
      change (if t.isProj then 0 else 1) + Step.levels p = m at h
      by_cases ht : t.isProj = true
      · rw [if_pos ht, Nat.zero_add] at h
        simp only [List.cons_append, Step.collapseAt, ht, if_true]
        rw [collapseAt_keep_own p m q h]
      · rw [if_neg ht] at h
        obtain rfl : m = Step.levels p + 1 := by omega
        simp only [List.cons_append, Step.collapseAt, ht, Bool.false_eq_true, if_false]
        by_cases hc : Step.levels p = 0 ∧ t = .keep ∧ Step.headLvl (p ++ .keep :: q) = true
        · rw [if_pos hc]
          obtain ⟨hl0, rfl, hh⟩ := hc
          cases p with
          | nil => rfl
          | cons u p' =>
              exfalso
              change (if u.isProj then 0 else 1) + Step.levels p' = 0 at hl0
              have hu : u.isProj = true := by
                by_contra hu
                rw [if_neg hu] at hl0
                omega
              simp [Step.headLvl, hu] at hh
        · rw [if_neg hc, collapseAt_keep_own p _ q rfl]

/-! ## Kept addresses -/

omit [ModalSys] in
theorem levels_pp : ∀ {p : List Step}, PPath p → Step.levels p = 0
  | [], _ => rfl
  | s :: p, h => by
      change (if s.isProj then 0 else 1) + Step.levels p = 0
      rw [if_pos (h s List.mem_cons_self),
        levels_pp (fun s' hs => h s' (List.mem_cons_of_mem _ hs))]

omit [ModalSys] in
theorem levels_kept {v : VarSymb} (hv : PPath v.path) (q : List Step) :
    Step.levels ((VarSymb.step v .keep).ext q).path = Step.levels q + 1 := by
  rw [VarSymb.ext_path]
  change Step.levels ((v.path ++ [.keep]) ++ q) = _
  rw [Step.levels_append, Step.levels_append, (levels_pp hv)]
  simp [Step.levels, Step.isProj]
  omega

omit [ModalSys] in
theorem topL_kept {v : VarSymb} (hv : PPath v.path) (q : List Step) :
    topL ((VarSymb.step v .keep).ext q) = Step.levels q := by
  unfold topL
  rw [levels_kept hv]
  omega

omit [ModalSys] in
/-- Keeping a kept address at its top level doubles its `keep`. -/
theorem shift_kept (v : VarSymb) (q : List Step) :
    ((VarSymb.step v .keep).ext q).shift (Step.levels q) =
      (VarSymb.step (.step v .keep) .keep).ext q := by
  have e := VarSymb.shift_ext (.step v .keep) q 0
  rw [Nat.zero_add] at e
  rw [e, VarSymb.shift_level_zero (by decide)]

omit [ModalSys] in
/-- Collapsing a kept address at its top level drops its `keep`. -/
theorem collapse_kept (v : VarSymb) (q : List Step) :
    ((VarSymb.step v .keep).ext q).collapse (Step.levels q) = v.ext q := by
  have e := VarSymb.collapse_ext (.step v .keep) q 0
  rw [Nat.zero_add] at e
  rw [e]
  rfl

omit [ModalSys] in
/-- A path with no level step does not split. -/
theorem splitLevel_ppath_none : ∀ {q : List Step}, PPath q → splitLevel q = none
  | [], _ => rfl
  | a :: q, h => by
      change (if a.isProj then _ else _) = _
      rw [if_pos (h a (by simp)), splitLevel_ppath_none (fun s' hs' => h s' (by simp [hs']))]
      rfl

omit [ModalSys] in
/-- What a split path is made of. -/
theorem splitLevel_spec : ∀ (q : List Step) {pre r : List Step} {s : Step},
    splitLevel q = some (pre, s, r) → q = pre ++ s :: r ∧ PPath pre ∧ s.isProj = false
  | [], _, _, _, h => by cases h
  | a :: q, pre, r, s, h => by
      change (if a.isProj then _ else _) = _ at h
      by_cases ha : a.isProj = true
      · rw [if_pos ha] at h
        obtain ⟨⟨pre', s', r'⟩, hq, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        obtain ⟨e, hp, hs⟩ := splitLevel_spec q hq
        refine ⟨by rw [e]; rfl, fun x hx => ?_, hs⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact hp x hx
      · rw [if_neg ha] at h
        cases h
        exact ⟨rfl, fun x hx => absurd hx List.not_mem_nil, Bool.eq_false_iff.mpr ha⟩

/-- ⭐**Where an edge sends a kept address kept once more**: to the entry of its item, read at the
    doubled path. -/
theorem keptTr_kept (t : GW hF M₀) (c : ℕ) {v : VarSymb} (hv : PPath v.path) (q : List Step) :
    keptTr t c ((VarSymb.step v .keep).ext q) =
      entIdx (fmapL hF M₀ (c :: t.1) (.step v .keep)) (.keep :: q) := by
  unfold keptTr eIdx
  rw [topL_kept hv, shift_kept, VarSymb.ext_path,
    show (VarSymb.step (.step v .keep) .keep).path = v.path ++ [.keep, .keep] by
      change (v.path ++ [.keep]) ++ [.keep] = _
      simp,
    List.append_assoc, show [Step.keep, .keep] ++ q = .keep :: .keep :: q from rfl,
    splitLevel_ppath hv (by decide)]
  simp only [VarSymb.ext_rt]
  change entIdx (fmapL hF M₀ (c :: t.1) (.step ((VarSymb.root v.rt).ext v.path) .keep)) _ = _
  rw [VarSymb.root_ext_path]

theorem gMem_kept_nil (t t' : GW hF M₀) (h : t'.1 = nodeOf t.1 []) {v : VarSymb}
    (hv : PPath v.path) (q : List Step) :
    gMem t t' [] h ((VarSymb.step v .keep).ext q) = gLab t' (v.ext q) := by
  rw [gMem_nil, topL_kept hv, collapse_kept, if_pos]
  rw [levels_kept hv, VarSymb.ext_path, Step.levels_append, (levels_pp hv)]
  omega

theorem gMem_kept_cons (t t' : GW hF M₀) (c : ℕ) (P : List ℕ) (h : t'.1 = nodeOf t.1 (c :: P))
    {v : VarSymb} (hv : PPath v.path) (q : List Step) :
    gMem t t' (c :: P) h ((VarSymb.step v .keep).ext q) =
      if Step.levels (entIdx (fmapL hF M₀ (c :: t.1) (.step v .keep)) (.keep :: q)).path ≤
          Step.levels q + 1 then
        gMem (stepW t c (born_step h)) t' P h
          (entIdx (fmapL hF M₀ (c :: t.1) (.step v .keep)) (.keep :: q))
      else .root junkR [] := by
  rw [gMem_cons, keptTr_kept t c hv, levels_kept hv]

/-! ## Labels by an address's first level step -/

theorem gLab_ppath (t : GW hF M₀) {y : VarSymb} (hy : PPath y.path) : gLab t y = .root y [] := by
  unfold gLab
  rw [splitLevel_ppath_none hy]

theorem gLab_dia (t : GW hF M₀) {v : VarSymb} (hv : PPath v.path) (r : List Step) :
    gLab t ((VarSymb.step v .dia).ext r) = .root v (.dia :: r) := by
  unfold gLab
  rw [show ((VarSymb.step v .dia).ext r).path = v.path ++ .dia :: r by
      rw [VarSymb.ext_path]
      change (v.path ++ [.dia]) ++ r = _
      simp,
    splitLevel_ppath hv (by decide)]
  simp only [VarSymb.ext_rt]
  rw [show (VarSymb.step v .dia).rt = v.rt from rfl, VarSymb.root_ext_path]

theorem gLab_keep (t : GW hF M₀) {v : VarSymb} (hv : PPath v.path) (r : List Step) :
    gLab t ((VarSymb.step v .keep).ext r) =
      .fam fun b => gMem t b.1 (pathOf b.2.down) (pathOf_eq b.2.down)
        ((VarSymb.step v .keep).ext r) := by
  unfold gLab
  rw [show ((VarSymb.step v .keep).ext r).path = v.path ++ .keep :: r by
      rw [VarSymb.ext_path]
      change (v.path ++ [.keep]) ++ r = _
      simp,
    splitLevel_ppath hv (by decide)]

/-! ## η-annotations -/

/-- Shifting an η-annotation is η-expanding the shifted address. -/
theorem Ann.eta_shift : ∀ (T : VarType) (v : VarSymb) (k : ℕ),
    (Ann.eta v T).shift k = Ann.eta (v.shift k) T
  | .Var, _, _ => rfl
  | .VTypeOne, _, _ => rfl
  | .VTypeProd A B, v, k => by
      change Ann.prod ((Ann.eta _ A).shift k) ((Ann.eta _ B).shift k) = _
      rw [Ann.eta_shift A, Ann.eta_shift B, VarSymb.shift_proj (s := .fst) rfl,
        VarSymb.shift_proj (s := .snd) rfl]
      rfl
  | .VTypeBox A, v, k => by
      change Ann.box ((Ann.eta v.inner A).shift (k + 1)) = _
      rw [Ann.eta_shift A, VarSymb.inner_shift_succ]
      rfl
  | .VTypeDia A, v, k => by
      change Ann.dia (v.shift k) ((Ann.eta (.step v .dia) A).shift (k + 1)) = _
      rw [Ann.eta_shift A, VarSymb.shift_level_succ (by decide)]
      rfl

/-- What a type step that applies is. -/
theorem typeStep_some {T U : VarType} {s : Step} (h : Step.typeStep T s = some U) :
    (∃ A B, T = .VTypeProd A B ∧ ((s = .fst ∧ U = A) ∨ (s = .snd ∧ U = B))) ∨
    (∃ A, T = .VTypeBox A ∧ ((s = .box ∧ ModalSys.keepOnly = false ∧ U = A) ∨
      (s = .here ∧ ModalSys.T = true ∧ U = A) ∨ (s = .keep ∧ U = .VTypeBox A))) ∨
    (∃ A, T = .VTypeDia A ∧ ((s = .dia ∧ U = A) ∨ (s = .keep ∧ U = .VTypeDia A))) := by
  cases T <;> cases s
  all_goals first
    | (simp [Step.typeStep, VarType.step, VarType.keepable] at h; done)
    | skip
  · exact .inl ⟨_, _, rfl, .inl ⟨rfl, (Option.some.inj h).symm⟩⟩
  · exact .inl ⟨_, _, rfl, .inr ⟨rfl, (Option.some.inj h).symm⟩⟩
  · change (if ModalSys.keepOnly = true then none else some _) = some U at h
    split at h
    · cases h
    · rename_i hk
      exact .inr (.inl ⟨_, rfl, .inl ⟨rfl, Bool.eq_false_iff.mpr hk, (Option.some.inj h).symm⟩⟩)
  · change (if ModalSys.T = true then some _ else none) = some U at h
    split at h
    · rename_i hT
      exact .inr (.inl ⟨_, rfl, .inr (.inl ⟨rfl, hT, (Option.some.inj h).symm⟩)⟩)
    · cases h
  · exact .inr (.inl ⟨_, rfl, .inr (.inr ⟨rfl, (Option.some.inj h).symm⟩)⟩)
  · exact .inr (.inr ⟨_, rfl, .inl ⟨rfl, (Option.some.inj h).symm⟩⟩)
  · exact .inr (.inr ⟨_, rfl, .inr ⟨rfl, (Option.some.inj h).symm⟩⟩)

/-- ⭐**An η-annotation names the address's own positions**: along a path typed in its type, it
    reaches the address extended by the path — a `keep` keeps the address, a `here` reads it. -/
theorem Ann.idxAt_eta : ∀ (q : List Step) (w : VarSymb) (T X : VarType),
    Step.walkTy T q = some (.VTypeDia X) → (Ann.eta w T).idxAt q = w.ext q
  | [], w, T, X, h => by
      change some T = some _ at h
      cases h
      rfl
  | s :: q, w, T, X, h => by
      obtain ⟨U, hU, hq⟩ := Option.bind_eq_some_iff.mp h
      rcases typeStep_some hU with ⟨A, B, rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
        ⟨A, rfl, ⟨rfl, hk, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨A, rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact Ann.idxAt_eta q _ _ X hq
      · exact Ann.idxAt_eta q _ _ X hq
      · -- `box`, when views show contents
        change (Ann.eta w.inner _).idxAt q = _
        rw [Ann.idxAt_eta q _ _ X hq, VarSymb.inner_box hk]
        rfl
      · -- `here`, under T
        change ((Ann.eta w.inner _).idxAt q).collapse (Step.levels q) = _
        rw [Ann.idxAt_eta q _ _ X hq]
        have e := VarSymb.collapse_ext w.inner q 0
        rw [Nat.zero_add] at e
        rw [e, VarSymb.inner_collapse_zero]
        rfl
      · -- `keep` of a necessary object
        change (Ann.box ((Ann.eta w.inner A).shift 0)).idxAt q = _
        rw [Ann.eta_shift, VarSymb.inner_shift_zero]
        exact Ann.idxAt_eta q (.step w .keep) (.VTypeBox A) X hq
      · exact Ann.idxAt_eta q _ _ X hq
      · -- `keep` of a possible object
        change (Ann.dia (.step w .keep) ((Ann.eta (.step w .dia) A).shift 0)).idxAt q = _
        rw [Ann.eta_shift, VarSymb.shift_level_zero (by decide)]
        exact Ann.idxAt_eta q (.step w .keep) (.VTypeDia A) X hq

/-! ## Leading keeps -/

/-- An address kept `n` times. -/
def keepN : ℕ → VarSymb → VarSymb
  | 0, v => v
  | n + 1, v => keepN n (.step v .keep)

/-- An address shifted at its innermost level `n` times. -/
def shiftN : ℕ → VarSymb → VarSymb
  | 0, v => v
  | n + 1, v => shiftN n (v.shift 0)

omit [ModalSys] in
theorem keepN_ext : ∀ (n : ℕ) (v : VarSymb), keepN n v = v.ext (List.replicate n .keep)
  | 0, _ => rfl
  | n + 1, v => keepN_ext n (.step v .keep)

omit [ModalSys] in
/-- A kept item shifted is kept once more. -/
theorem shiftN_keep : ∀ (n : ℕ) (w : VarSymb),
    shiftN n (.step w .keep) = VarSymb.step (keepN n w) .keep
  | 0, _ => rfl
  | n + 1, w => by
      change shiftN n ((VarSymb.step w .keep).shift 0) = _
      rw [VarSymb.shift_level_zero (by decide)]
      exact shiftN_keep n (.step w .keep)

omit [ModalSys] in
theorem shiftN_dia : ∀ (n : ℕ) (z : VarSymb),
    shiftN n (.step z .dia) = VarSymb.step (keepN n z) .dia
  | 0, _ => rfl
  | n + 1, z => by
      change shiftN n ((VarSymb.step z .dia).shift 0) = _
      rw [VarSymb.shift_level_zero (by decide)]
      exact shiftN_dia n (.step z .keep)

/-! ## The items of a view -/

/-- The annotation of a tuple of items' η-expansions, each item's address read through `f`. -/
def itemsAnnF : (L : List (VarSymb × VarType)) → (VarSymb → VarSymb) → Ann (itemsTy L)
  | [], _ => .one
  | e :: L, f => .prod (Ann.eta (f e.1) e.2) (itemsAnnF L f)

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem itemsTm_ann {Γ : Ctx} :
    ∀ (L : List (VarSymb × VarType)) (h : ∀ e ∈ L, Γ.ref e.1 = some e.2),
    (itemsTm (σ := σ) L h).1 = itemsAnnF L id
  | [], _ => rfl
  | e :: L, h => by
      change Ann.prod (Ann.eta e.1 e.2) (itemsTm (σ := σ) L _).1 = _
      rw [itemsTm_ann L]
      rfl

theorem itemsAnnF_shift : ∀ (L : List (VarSymb × VarType)) (f : VarSymb → VarSymb) (k : ℕ),
    (itemsAnnF L f).shift k = itemsAnnF L fun v => (f v).shift k
  | [], _, _ => rfl
  | e :: L, f, k => by
      change Ann.prod ((Ann.eta (f e.1) e.2).shift k) ((itemsAnnF L f).shift k) = _
      rw [Ann.eta_shift, itemsAnnF_shift L]
      rfl

/-- A typed path into a tuple of items enters one item. -/
theorem items_walk : ∀ (L : List (VarSymb × VarType)) (q : List Step) (X : VarType),
    Step.walkTy (itemsTy L) q = some (.VTypeDia X) →
      ∃ (k : ℕ) (hk : k < L.length) (r : List Step), q = itemPath k ++ r ∧
        Step.walkTy L[k].2 r = some (.VTypeDia X)
  | [], [], _, h => by cases h
  | [], s :: q, _, h => by
      obtain ⟨U, hU, -⟩ := Option.bind_eq_some_iff.mp h
      rcases typeStep_some hU with ⟨_, _, he, -⟩ | ⟨_, he, -⟩ | ⟨_, he, -⟩ <;> cases he
  | e :: L, [], _, h => by cases h
  | e :: L, s :: q, X, h => by
      obtain ⟨U, hU, hq⟩ := Option.bind_eq_some_iff.mp h
      rcases typeStep_some hU with ⟨A, B, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨_, he, -⟩ | ⟨_, he, -⟩
      · cases he
        exact ⟨0, by simp, q, rfl, hq⟩
      · cases he
        obtain ⟨k, hk, r, rfl, hr⟩ := items_walk L q X hq
        exact ⟨k + 1, by simpa using hk, r, rfl, hr⟩
      · cases he
      · cases he

theorem items_idxAt : ∀ (L : List (VarSymb × VarType)) (f : VarSymb → VarSymb) (k : ℕ)
    (hk : k < L.length) (r : List Step),
    (itemsAnnF L f).idxAt (itemPath k ++ r) = (Ann.eta (f L[k].1) L[k].2).idxAt r
  | _ :: _, _, 0, _, _ => rfl
  | _ :: L, f, k + 1, hk, r => items_idxAt L f k (by simpa using hk) r

/-! ## The view tuples' annotations -/

/-- The annotation of a view tuple `◇_z⟨z.dia, items⟩`, the items read through `f`. -/
def VTann (z : VarSymb) (f : VarSymb → VarSymb) (L : List (VarSymb × VarType)) (Z : VarType) :
    Ann (.VTypeDia (.VTypeProd Z (itemsTy L))) :=
  .dia z (.prod (Ann.eta (.step z .dia) Z) (itemsAnnF L f))

/-- The annotation of a `□` view tuple `□⟨items⟩`, the items read through `f`. -/
def BTann (f : VarSymb → VarSymb) (L : List (VarSymb × VarType)) :
    Ann (.VTypeBox (itemsTy L)) :=
  .box (itemsAnnF L f)

theorem vt_keep (z : VarSymb) (f : VarSymb → VarSymb) (L : List (VarSymb × VarType))
    (Z : VarType) (q : List Step) :
    (VTann z f L Z).idxAt (.keep :: q) =
      (VTann (.step z .keep) (fun v => (f v).shift 0) L Z).idxAt q := by
  change (Ann.dia (.step z .keep) (Ann.prod ((Ann.eta (.step z .dia) Z).shift 0)
    ((itemsAnnF L f).shift 0))).idxAt q = _
  rw [Ann.eta_shift, itemsAnnF_shift, VarSymb.shift_level_zero (by decide)]
  rfl

theorem bt_keep (f : VarSymb → VarSymb) (L : List (VarSymb × VarType)) (q : List Step) :
    (BTann f L).idxAt (.keep :: q) = (BTann (fun v => (f v).shift 0) L).idxAt q := by
  change (Ann.box ((itemsAnnF L f).shift 0)).idxAt q = _
  rw [itemsAnnF_shift]
  rfl

theorem vt_keeps (z : VarSymb) (f : VarSymb → VarSymb) (L : List (VarSymb × VarType))
    (Z : VarType) : ∀ (n : ℕ) (q : List Step),
    (VTann z f L Z).idxAt (List.replicate n .keep ++ q) =
      (VTann (keepN n z) (fun v => shiftN n (f v)) L Z).idxAt q
  | 0, _ => rfl
  | n + 1, q => by
      change (VTann z f L Z).idxAt (.keep :: (List.replicate n .keep ++ q)) = _
      rw [vt_keep]
      exact vt_keeps (.step z .keep) (fun v => (f v).shift 0) L Z n q

theorem bt_keeps (f : VarSymb → VarSymb) (L : List (VarSymb × VarType)) :
    ∀ (n : ℕ) (q : List Step),
    (BTann f L).idxAt (List.replicate n .keep ++ q) =
      (BTann (fun v => shiftN n (f v)) L).idxAt q
  | 0, _ => rfl
  | n + 1, q => by
      change (BTann f L).idxAt (.keep :: (List.replicate n .keep ++ q)) = _
      rw [bt_keep]
      exact bt_keeps (fun v => (f v).shift 0) L n q

/-- ⭐**Where a view tuple's annotation leads**, along a typed path not starting with a `keep`:
    to the witness, into its content, or into an item. -/
theorem vt_base (L : List (VarSymb × VarType)) (Z : VarType) (q : List Step) (X : VarType)
    (hq0 : q.head? ≠ some .keep)
    (h : Step.walkTy (.VTypeDia (.VTypeProd Z (itemsTy L))) q = some (.VTypeDia X)) :
    (q = [] ∧ ∀ z f, (VTann z f L Z).idxAt q = z) ∨
    (∃ p, q = .dia :: .fst :: p ∧ Step.walkTy Z p = some (.VTypeDia X) ∧
      ∀ z f, (VTann z f L Z).idxAt q = (VarSymb.step z .dia).ext p) ∨
    (∃ k, ∃ hk : k < L.length, ∃ r, q = .dia :: .snd :: (itemPath k ++ r) ∧
      Step.walkTy L[k].2 r = some (.VTypeDia X) ∧
      ∀ z f, (VTann z f L Z).idxAt q = (f L[k].1).ext r) := by
  match q, hq0, h with
  | [], _, _ => exact .inl ⟨rfl, fun _ _ => rfl⟩
  | s :: q, hq0, h =>
      obtain ⟨U, hU, hq⟩ := Option.bind_eq_some_iff.mp h
      rcases typeStep_some hU with ⟨_, _, he, -⟩ | ⟨_, he, -⟩ | ⟨A, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · cases he
      · cases he
      · cases he
        cases q with
        | nil => cases hq
        | cons s' q' =>
            obtain ⟨U', hU', hq'⟩ := Option.bind_eq_some_iff.mp hq
            rcases typeStep_some hU' with ⟨A', B', he', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
              ⟨_, he', -⟩ | ⟨_, he', -⟩
            · cases he'
              exact .inr (.inl ⟨q', rfl, hq', fun _ _ => Ann.idxAt_eta q' _ _ X hq'⟩)
            · cases he'
              obtain ⟨k, hk, r, rfl, hr⟩ := items_walk L _ X hq'
              refine .inr (.inr ⟨k, hk, r, rfl, hr, fun z f => ?_⟩)
              change (itemsAnnF L f).idxAt (itemPath k ++ r) = _
              rw [items_idxAt]
              exact Ann.idxAt_eta r _ _ X hr
            · cases he'
            · cases he'
      · exact absurd rfl hq0

/-- ⭐**Where a `□` view tuple's annotation leads**, along a typed path not starting with a
    `keep` (T + 4): after a `here`, into an item read at the world. -/
theorem bt_base (hk : ModalSys.keepOnly = true) (L : List (VarSymb × VarType)) (q : List Step)
    (X : VarType) (hq0 : q.head? ≠ some .keep)
    (h : Step.walkTy (.VTypeBox (itemsTy L)) q = some (.VTypeDia X)) :
    ∃ k, ∃ hk : k < L.length, ∃ r, q = .here :: (itemPath k ++ r) ∧
      Step.walkTy L[k].2 r = some (.VTypeDia X) ∧
      ∀ f, (BTann f L).idxAt q = ((f L[k].1).ext r).collapse (Step.levels r) := by
  match q, hq0, h with
  | [], _, h => cases h
  | s :: q, hq0, h =>
      obtain ⟨U, hU, hq⟩ := Option.bind_eq_some_iff.mp h
      rcases typeStep_some hU with ⟨_, _, he, -⟩ |
        ⟨A, he, ⟨rfl, hk', rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨_, he, -⟩
      · cases he
      · rw [hk] at hk'
        cases hk'
      · cases he
        obtain ⟨k, hk, r, rfl, hr⟩ := items_walk L _ X hq
        refine ⟨k, hk, r, rfl, hr, fun f => ?_⟩
        change ((itemsAnnF L f).idxAt (itemPath k ++ r)).collapse
          (Step.levels (itemPath k ++ r)) = _
        rw [items_idxAt, Ann.idxAt_eta r _ _ X hr, Step.levels_append,
          levels_pp (itemPath_ppath k), Nat.zero_add]
      · exact absurd rfl hq0
      · cases he

/-! ## Every edge translates kept addresses faithfully -/

theorem walkTy_keep {U : VarType} (hU : U.keepable = true) (q : List Step) :
    Step.walkTy U (.keep :: q) = Step.walkTy U q := by
  change (if U.keepable = true then some U else none).bind _ = _
  rw [if_pos hU]
  rfl

theorem walkTy_keeps {U : VarType} (hU : U.keepable = true) :
    ∀ (n : ℕ) (q : List Step), Step.walkTy U (List.replicate n .keep ++ q) = Step.walkTy U q
  | 0, _ => rfl
  | n + 1, q => (walkTy_keep hU _).trans (walkTy_keeps hU n q)

omit [ModalSys] in
theorem levels_keeps : ∀ (n : ℕ) (q : List Step),
    Step.levels (List.replicate n .keep ++ q) = n + Step.levels q
  | 0, _ => by simp
  | n + 1, q => by
      change 1 + Step.levels (List.replicate n .keep ++ q) = _
      rw [levels_keeps n q]
      omega

omit [ModalSys] in
/-- An item kept `n + 1` times is a kept address with `n` keeps after its own. -/
theorem keepN_succ_kept (n : ℕ) (w : VarSymb) (r : List Step) :
    (keepN (n + 1) w).ext r = (VarSymb.step w .keep).ext (List.replicate n .keep ++ r) := by
  rw [keepN_ext, ← VarSymb.ext_append]
  rfl

omit [ModalSys] in
/-- A path's leading keeps. -/
theorem keeps_decomp : ∀ q : List Step,
    ∃ m q₀, q = List.replicate m .keep ++ q₀ ∧ q₀.head? ≠ some .keep
  | [] => ⟨0, [], rfl, by simp⟩
  | .keep :: q => by
      obtain ⟨m, q₀, rfl, h⟩ := keeps_decomp q
      exact ⟨m + 1, q₀, rfl, h⟩
  | .fst :: q => ⟨0, _, rfl, by simp⟩
  | .snd :: q => ⟨0, _, rfl, by simp⟩
  | .box :: q => ⟨0, _, rfl, by simp⟩
  | .dia :: q => ⟨0, _, rfl, by simp⟩
  | .here :: q => ⟨0, _, rfl, by simp⟩

omit [ModalSys] in
theorem keeps_assoc (n m : ℕ) (q : List Step) :
    Step.keep :: (List.replicate n .keep ++ (List.replicate m .keep ++ q)) =
      List.replicate (n + m + 1) .keep ++ q := by
  rw [← List.append_assoc, ← List.replicate_add]
  rfl

/-- A path that does not start with a projection: a possible object's position. -/
def NoProjHead (q : List Step) : Prop := ∀ s, q.head? = some s → s.isProj = false

omit [ModalSys] in
theorem noProjHead_cons {s : Step} (hs : s.isProj = false) (r : List Step) :
    NoProjHead (s :: r) := fun _ h => by
  cases h
  exact hs

omit [ModalSys] in
theorem noProjHead_keeps : ∀ (m : ℕ) {r : List Step}, NoProjHead r →
    NoProjHead (List.replicate m .keep ++ r)
  | 0, _, h => h
  | _ + 1, _, _ => noProjHead_cons rfl _

omit [ModalSys] in
theorem noProjHead_rep (m : ℕ) : NoProjHead (List.replicate m .keep) := by
  have := noProjHead_keeps m (r := []) (fun _ h => by cases h)
  rwa [List.append_nil] at this

/-- Under T + 4 a view's items are its kept items. -/
theorem boxItems_kept (hk : ModalSys.keepOnly = true) (l : List VarType) :
    ∀ e ∈ boxItems l, ∃ w, e.1 = .step w .keep ∧ (ctxOf l).ref w = some e.2 ∧
      e.2.keepable = true := by
  intro e he
  simp only [boxItems, hk, if_true, List.mem_flatMap, List.mem_singleton] at he
  obtain ⟨⟨w, T⟩, hm, rfl⟩ := he
  obtain ⟨hw, hk'⟩ := keepItems_spec l _ hm
  exact ⟨w, rfl, hw, hk'⟩

/-- ⭐**Every edge sends a typed kept address to a typed kept address with as many levels**
    (T + 4), and keeping first is keeping after: an image keeps the path; an η-lift renames the
    witness; a view tuple sends its witness's part to the witness and an item's part to the item,
    kept once more; a `□` view tuple sends an item's part to the item. -/
theorem keptTr_ok (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) (t : GW hF M₀) (c : ℕ)
    (hb : GBorn hF M₀ (c :: t.1)) {v : VarSymb} {U : VarType} (hd : DeclAt t v U)
    {q : List Step} {X : VarType} (hq : Step.walkTy U (.keep :: q) = some (.VTypeDia X)) :
    ∃ w q', (∀ n, entIdx (fmapL hF M₀ (c :: t.1) (.step v .keep))
          (.keep :: (List.replicate n .keep ++ q)) =
        (VarSymb.step w .keep).ext (List.replicate n .keep ++ q')) ∧ PPath w.path ∧
      (∃ U' X', DeclAt (stepW t c hb) w U' ∧
        Step.walkTy U' (.keep :: q') = some (.VTypeDia X')) ∧
      Step.levels q' = Step.levels q ∧ (NoProjHead q → NoProjHead q') := by
  have hk : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  obtain ⟨i, hi⟩ := hd
  obtain ⟨U₁, hU₁, -⟩ := Option.bind_eq_some_iff.mp hq
  have hUk : U.keepable = true := Step.typeStep_level_keepable rfl hU₁
  have hq' : Step.walkTy U q = some (.VTypeDia X) := (walkTy_keep hUk q).symm.trans hq
  have hok := gentOk_box hM₀ (t := stepW t c hb) ⟨c, rfl⟩ i (.step v .keep) U rfl
    (Ctx.boxIn_keep_of' hF hi hUk)
  set Δ := ctxOf (glat (stepW t c hb) (glstg t (stepW t c hb) i)) with hΔ
  change (entOf Δ (fmapL hF M₀ (c :: t.1) (.step v .keep))).OkRef U at hok
  obtain ⟨m, q₀, rfl, hq0⟩ := keeps_decomp q
  have hq₀ : Step.walkTy U q₀ = some (.VTypeDia X) := (walkTy_keeps hUk m q₀).symm.trans hq'
  cases he : fmapL hF M₀ (c :: t.1) (.step v .keep) with
  | inl w =>
      rw [he] at hok
      exact ⟨w, _, fun _ => rfl, (reach_ppath hok).1, ⟨U, X, ⟨_, hok⟩, hq⟩, rfl, id⟩
  | inr τ =>
      rw [he] at hok
      obtain ⟨e₀, hsuf, hadm, -, hτ⟩ := fmapL_adm he
      obtain ⟨L, T₀, a₀, t₀⟩ := τ
      have hle : (ctxOf L).Le Δ := by
        by_contra hn
        rw [show entOf Δ (.inr ⟨L, T₀, a₀, t₀⟩) = .hide from dif_neg hn] at hok
        exact hok
      rw [entOf_tm hle] at hok
      cases hok
      obtain ⟨l', T', a', t'⟩ := e₀
      have h₂ := eq_of_heq (Sigma.mk.inj hτ).2
      obtain ⟨rfl, h₃⟩ := Sigma.mk.inj h₂
      obtain ⟨rfl, -⟩ := Sigma.mk.inj (eq_of_heq h₃)
      have hl' : (ctxOf l').Le Δ := (ctxOf_le_of_suffix hsuf).trans hle
      simp only [entIdx]
      rcases hadm with hbt | ⟨z, Z, hz, he₀⟩ | ⟨-, z, Z, hz, he₀⟩
      · -- the `□` view tuple
        change (⟨l', _, _, t'⟩ : LTerm σ) = boxTuple hF l' at hbt
        unfold boxTuple at hbt
        cases hbt
        rw [show Ann.box (itemsTm (σ := σ) (boxItems l') (boxItems_ref hF l')).1 =
          BTann id (boxItems l') by rw [itemsTm_ann]; rfl]
        obtain ⟨k, hkl, r, rfl, hr, hidx⟩ := bt_base hk (boxItems l') _ X hq0 hq₀
        obtain ⟨w, hw₁, hw₂, hw₃⟩ := boxItems_kept hk l' _ (List.getElem_mem hkl)
        refine ⟨w, List.replicate m .keep ++ r, fun n => ?_, (reach_ppath hw₂).1,
          ⟨_, X, ⟨_, hl'.ref hw₂⟩, ?_⟩, ?_, fun hnp => ?_⟩
        · rw [keeps_assoc, bt_keeps, hidx]
          change ((shiftN (n + m + 1) (boxItems l')[k].1).ext r).collapse _ = _
          rw [hw₁, shiftN_keep, collapse_kept, keepN_succ_kept, List.replicate_add,
            List.append_assoc]
        · rw [walkTy_keep hw₃, walkTy_keeps hw₃]
          exact hr
        · rw [levels_keeps, levels_keeps, Step.levels_cons,
            if_pos (show Step.here.isProj = true from rfl), Step.levels_append,
            levels_pp (itemPath_ppath k)]
          omega
        · cases m with
          | zero => exact absurd (hnp .here rfl) (by decide)
          | succ m => exact noProjHead_cons rfl _
      · -- an η-lift
        change (⟨l', _, _, t'⟩ : LTerm σ) = etaTerm l' z Z hz at he₀
        unfold etaTerm at he₀
        obtain ⟨rfl, h₄⟩ := Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he₀).2)
        obtain ⟨rfl, -⟩ := Sigma.mk.inj (eq_of_heq h₄)
        refine ⟨z, _, fun n => Ann.idxAt_eta _ z _ X ?_, (reach_ppath hz).1,
          ⟨_, X, ⟨_, hl'.ref hz⟩, hq⟩, rfl, id⟩
        rw [walkTy_keep rfl, walkTy_keeps rfl]
        exact hq'
      · -- a view tuple
        change (⟨l', _, _, t'⟩ : LTerm σ) = viewTuple hF l' z Z hz at he₀
        unfold viewTuple at he₀
        obtain ⟨rfl, h₄⟩ := Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he₀).2)
        obtain ⟨rfl, -⟩ := Sigma.mk.inj (eq_of_heq h₄)
        rw [show Ann.dia z (Ann.prod (Ann.eta (.step z .dia) Z)
            (itemsTm (σ := σ) (boxItems l') (boxItems_ref hF l')).1) =
          VTann z id (boxItems l') Z by rw [itemsTm_ann]; rfl]
        have hzk : (VarType.VTypeDia Z).keepable = true := rfl
        rcases vt_base (boxItems l') Z q₀ X hq0 hq₀ with
          ⟨rfl, hidx⟩ | ⟨p, rfl, hp, hidx⟩ | ⟨k, hkl, r, rfl, hr, hidx⟩
        · -- the witness
          refine ⟨z, List.replicate m .keep, fun n => ?_, (reach_ppath hz).1,
            ⟨_, Z, ⟨_, hl'.ref hz⟩, ?_⟩, by rw [List.append_nil],
            fun _ => noProjHead_rep m⟩
          · rw [keeps_assoc, vt_keeps, hidx]
            have e := keepN_succ_kept (n + m) z []
            rw [List.append_nil, List.replicate_add] at e
            exact e
          · rw [walkTy_keep hzk, ← List.append_nil (List.replicate m Step.keep),
              walkTy_keeps hzk]
            rfl
        · -- the witness's content
          refine ⟨z, List.replicate m .keep ++ .dia :: p, fun n => ?_, (reach_ppath hz).1,
            ⟨_, X, ⟨_, hl'.ref hz⟩, ?_⟩, ?_,
            fun _ => noProjHead_keeps m (noProjHead_cons (by decide) _)⟩
          · rw [keeps_assoc, vt_keeps, hidx]
            rw [show (VarSymb.step (keepN (n + m + 1) z) .dia).ext p =
              (keepN (n + m + 1) z).ext (.dia :: p) from rfl, keepN_succ_kept,
              List.replicate_add, List.append_assoc]
          · rw [walkTy_keep hzk, walkTy_keeps hzk]
            exact hp
          · rw [levels_keeps, levels_keeps]
            simp [Step.levels_cons, Step.isProj]
        · -- an item
          obtain ⟨w, hw₁, hw₂, hw₃⟩ := boxItems_kept hk l' _ (List.getElem_mem hkl)
          refine ⟨w, List.replicate m .keep ++ .keep :: r, fun n => ?_, (reach_ppath hw₂).1,
            ⟨_, X, ⟨_, hl'.ref hw₂⟩, ?_⟩, ?_, fun _ => noProjHead_keeps m (noProjHead_cons rfl _)⟩
          · rw [keeps_assoc, vt_keeps, hidx]
            change (shiftN (n + m + 1) (boxItems l')[k].1).ext r = _
            rw [hw₁, shiftN_keep,
              show (VarSymb.step (keepN (n + m + 1) w) .keep).ext r =
                (keepN (n + m + 1) w).ext (.keep :: r) from rfl, keepN_succ_kept,
              List.replicate_add, List.append_assoc]
          · rw [walkTy_keep hw₃, walkTy_keeps hw₃, walkTy_keep hw₃]
            exact hr
          · rw [levels_keeps, levels_keeps, Step.levels_cons, Step.levels_cons, Step.levels_cons,
              if_neg (show ¬ Step.dia.isProj = true by decide),
              if_pos (show Step.snd.isProj = true from rfl), if_neg (by decide),
              Step.levels_append, levels_pp (itemPath_ppath k)]
            omega


/-! ## The translation's form: a middle piece rewritten -/

/-- Walking into an item. -/
theorem items_walk_eq : ∀ (L : List (VarSymb × VarType)) (k : ℕ) (hk : k < L.length)
    (r : List Step), Step.walkTy (itemsTy L) (itemPath k ++ r) = Step.walkTy L[k].2 r
  | _ :: _, 0, _, _ => rfl
  | _ :: L, k + 1, hk, r => items_walk_eq L k (by simpa using hk) r

theorem vt_content (L : List (VarSymb × VarType)) (Z : VarType) (z : VarSymb)
    (f : VarSymb → VarSymb) (r : List Step) {X : VarType}
    (hr : Step.walkTy Z r = some (.VTypeDia X)) :
    (VTann z f L Z).idxAt (.dia :: .fst :: r) = (VarSymb.step z .dia).ext r :=
  Ann.idxAt_eta r _ _ X hr

theorem vt_item (L : List (VarSymb × VarType)) (Z : VarType) (z : VarSymb)
    (f : VarSymb → VarSymb) (k : ℕ) (hk : k < L.length) (r : List Step) {X : VarType}
    (hr : Step.walkTy L[k].2 r = some (.VTypeDia X)) :
    (VTann z f L Z).idxAt (.dia :: .snd :: (itemPath k ++ r)) = (f L[k].1).ext r := by
  change (itemsAnnF L f).idxAt (itemPath k ++ r) = _
  rw [items_idxAt]
  exact Ann.idxAt_eta r _ _ X hr

theorem bt_item (L : List (VarSymb × VarType)) (f : VarSymb → VarSymb) (k : ℕ)
    (hk : k < L.length) (r : List Step) {X : VarType}
    (hr : Step.walkTy L[k].2 r = some (.VTypeDia X)) :
    (BTann f L).idxAt (.here :: (itemPath k ++ r)) =
      ((f L[k].1).ext r).collapse (Step.levels r) := by
  change ((itemsAnnF L f).idxAt (itemPath k ++ r)).collapse
    (Step.levels (itemPath k ++ r)) = _
  rw [items_idxAt, Ann.idxAt_eta r _ _ X hr, Step.levels_append,
    levels_pp (itemPath_ppath k), Nat.zero_add]

/-- The two pieces a translation exchanges: projections for projections, or a `dia` with
    projections after it for a level step with projections after it. -/
def ShapeOK (X X' : List Step) : Prop :=
  (PPath X ∧ PPath X') ∨
    ∃ Xp s' X'p, X = .dia :: Xp ∧ PPath Xp ∧ X' = s' :: X'p ∧ s'.isProj = false ∧ PPath X'p

theorem walkTy_here (hT : ModalSys.T = true) (A : VarType) (p : List Step) :
    Step.walkTy (.VTypeBox A) (.here :: p) = Step.walkTy A p := by
  change ((VarType.VTypeBox A).step .here).bind _ = _
  simp [VarType.step, hT]

omit [ModalSys] in
theorem ppath_nil : PPath [] := fun _ h => absurd h List.not_mem_nil

omit [ModalSys] in
theorem keeps_cons_append (n : ℕ) (Y : List Step) :
    Step.keep :: (List.replicate n .keep ++ Y) = List.replicate (n + 1) .keep ++ Y := rfl

/-- ⭐**The form of an edge's translation of typed kept addresses** (T + 4): it rewrites a middle
    piece `X ↦ X'` after the leading keeps and leaves the rest, uniformly in the number of keeps
    and (unless the address is a witness's, all keeps) in the rest. -/
theorem keptTr_form (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) (t : GW hF M₀) (c : ℕ)
    (hb : GBorn hF M₀ (c :: t.1)) {v : VarSymb} {U : VarType} (hd : DeclAt t v U)
    {q : List Step} {X₀ : VarType} (hq : Step.walkTy U (.keep :: q) = some (.VTypeDia X₀)) :
    ∃ (w : VarSymb) (n : ℕ) (X X' R : List Step) (tl : Bool),
      q = List.replicate n .keep ++ X ++ R ∧ Step.levels X = Step.levels X' ∧ ShapeOK X X' ∧
      PPath w.path ∧ (tl = false → X = [] ∧ X' = [] ∧ R = []) ∧
      ∀ (n' : ℕ) (R' : List Step), (tl = false → R' = []) → ∀ Y : VarType,
        Step.walkTy U (.keep :: (List.replicate n' .keep ++ X ++ R')) = some (.VTypeDia Y) →
        entIdx (fmapL hF M₀ (c :: t.1) (.step v .keep)) (List.replicate n' .keep ++ X ++ R') =
          w.ext (List.replicate n' .keep ++ X' ++ R') ∧
        entIdx (fmapL hF M₀ (c :: t.1) (.step v .keep))
            (.keep :: (List.replicate n' .keep ++ X ++ R')) =
          (VarSymb.step w .keep).ext (List.replicate n' .keep ++ X' ++ R') ∧
        ∃ U' Y', DeclAt (stepW t c hb) w U' ∧
          Step.walkTy U' (.keep :: (List.replicate n' .keep ++ X' ++ R')) =
            some (.VTypeDia Y') := by
  have hk : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  obtain ⟨i, hi⟩ := hd
  obtain ⟨U₁, hU₁, -⟩ := Option.bind_eq_some_iff.mp hq
  have hUk : U.keepable = true := Step.typeStep_level_keepable rfl hU₁
  have hq' : Step.walkTy U q = some (.VTypeDia X₀) := (walkTy_keep hUk q).symm.trans hq
  have hok := gentOk_box hM₀ (t := stepW t c hb) ⟨c, rfl⟩ i (.step v .keep) U rfl
    (Ctx.boxIn_keep_of' hF hi hUk)
  set Δ := ctxOf (glat (stepW t c hb) (glstg t (stepW t c hb) i)) with hΔ
  change (entOf Δ (fmapL hF M₀ (c :: t.1) (.step v .keep))).OkRef U at hok
  cases he : fmapL hF M₀ (c :: t.1) (.step v .keep) with
  | inl w =>
      rw [he] at hok
      exact ⟨w, 0, [], [], q, true, rfl, rfl, .inl ⟨ppath_nil, ppath_nil⟩, (reach_ppath hok).1,
        (fun h => by cases h), fun n' R' _ Y hY => ⟨rfl, rfl, U, Y, ⟨_, hok⟩, hY⟩⟩
  | inr τ =>
      rw [he] at hok
      obtain ⟨e₀, hsuf, hadm, -, hτ⟩ := fmapL_adm he
      obtain ⟨L, T₀, a₀, t₀⟩ := τ
      have hle : (ctxOf L).Le Δ := by
        by_contra hn
        rw [show entOf Δ (.inr ⟨L, T₀, a₀, t₀⟩) = .hide from dif_neg hn] at hok
        exact hok
      rw [entOf_tm hle] at hok
      cases hok
      obtain ⟨l', T', a', t'⟩ := e₀
      have h₂ := eq_of_heq (Sigma.mk.inj hτ).2
      obtain ⟨rfl, h₃⟩ := Sigma.mk.inj h₂
      obtain ⟨rfl, -⟩ := Sigma.mk.inj (eq_of_heq h₃)
      have hl' : (ctxOf l').Le Δ := (ctxOf_le_of_suffix hsuf).trans hle
      simp only [entIdx]
      obtain ⟨m, q₀, rfl, hq0⟩ := keeps_decomp q
      have hq₀ : Step.walkTy _ q₀ = some (.VTypeDia X₀) := (walkTy_keeps hUk m q₀).symm.trans hq'
      rcases hadm with hbt | ⟨z, Z, hz, he₀⟩ | ⟨-, z, Z, hz, he₀⟩
      · -- the `□` view tuple: `here` into an item, read at the world
        change (⟨l', _, _, t'⟩ : LTerm σ) = boxTuple hF l' at hbt
        unfold boxTuple at hbt
        cases hbt
        rw [show Ann.box (itemsTm (σ := σ) (boxItems l') (boxItems_ref hF l')).1 =
          BTann id (boxItems l') by rw [itemsTm_ann]; rfl]
        obtain ⟨k, hkl, r, rfl, -, -⟩ := bt_base hk (boxItems l') _ X₀ hq0 hq₀
        obtain ⟨w, hw₁, hw₂, hw₃⟩ := boxItems_kept hk l' _ (List.getElem_mem hkl)
        refine ⟨w, m, .here :: itemPath k, [], r, true, by simp, ?_,
          .inl ⟨fun x hx => ?_, ppath_nil⟩, (reach_ppath hw₂).1, (fun h => by cases h),
          fun n' R' _ Y hY => ?_⟩
        · rw [Step.levels_cons, if_pos (show Step.here.isProj = true from rfl),
            levels_pp (itemPath_ppath k)]
          rfl
        · rcases List.mem_cons.mp hx with rfl | hx
          · rfl
          · exact itemPath_ppath k x hx
        · have hR : Step.walkTy (boxItems l')[k].2 R' = some (.VTypeDia Y) := by
            rw [walkTy_keep hUk, List.append_assoc, walkTy_keeps hUk,
              show Step.here :: itemPath k ++ R' = .here :: (itemPath k ++ R') from rfl,
              walkTy_here hT, items_walk_eq] at hY
            exact hY
          refine ⟨?_, ?_, _, Y, ⟨_, hl'.ref hw₂⟩, ?_⟩
          · rw [List.append_assoc, bt_keeps,
              show Step.here :: itemPath k ++ R' = .here :: (itemPath k ++ R') from rfl,
              bt_item _ _ k hkl R' hR]
            change ((shiftN n' (boxItems l')[k].1).ext R').collapse _ = _
            rw [hw₁, shiftN_keep, collapse_kept, keepN_ext, ← VarSymb.ext_append]
            simp
          · rw [List.append_assoc, keeps_cons_append, bt_keeps,
              show Step.here :: itemPath k ++ R' = .here :: (itemPath k ++ R') from rfl,
              bt_item _ _ k hkl R' hR]
            change ((shiftN (n' + 1) (boxItems l')[k].1).ext R').collapse _ = _
            rw [hw₁, shiftN_keep, collapse_kept, keepN_succ_kept, List.append_nil]
          · rw [List.append_nil, walkTy_keep hw₃, walkTy_keeps hw₃]
            exact hR
      · -- an η-lift: the witness renamed
        change (⟨l', _, _, t'⟩ : LTerm σ) = etaTerm l' z Z hz at he₀
        unfold etaTerm at he₀
        obtain ⟨rfl, h₄⟩ := Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he₀).2)
        obtain ⟨rfl, -⟩ := Sigma.mk.inj (eq_of_heq h₄)
        refine ⟨z, 0, [], [], _, true, rfl, rfl, .inl ⟨ppath_nil, ppath_nil⟩,
          (reach_ppath hz).1, (fun h => by cases h), fun n' R' _ Y hY =>
            ⟨Ann.idxAt_eta _ z _ Y ((walkTy_keep rfl _).symm.trans hY), Ann.idxAt_eta _ z _ Y hY,
              _, Y, ⟨_, hl'.ref hz⟩, hY⟩⟩
      · -- a view tuple
        change (⟨l', _, _, t'⟩ : LTerm σ) = viewTuple hF l' z Z hz at he₀
        unfold viewTuple at he₀
        obtain ⟨rfl, h₄⟩ := Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he₀).2)
        obtain ⟨rfl, -⟩ := Sigma.mk.inj (eq_of_heq h₄)
        rw [show Ann.dia z (Ann.prod (Ann.eta (.step z .dia) Z)
            (itemsTm (σ := σ) (boxItems l') (boxItems_ref hF l')).1) =
          VTann z id (boxItems l') Z by rw [itemsTm_ann]; rfl]
        have hzk : (VarType.VTypeDia Z).keepable = true := rfl
        rcases vt_base (boxItems l') Z q₀ X₀ hq0 hq₀ with
          ⟨rfl, -⟩ | ⟨p, rfl, -, -⟩ | ⟨k, hkl, r, rfl, -, -⟩
        · -- the witness: all keeps
          refine ⟨z, m, [], [], [], false, by simp, rfl, .inl ⟨ppath_nil, ppath_nil⟩,
            (reach_ppath hz).1, fun _ => ⟨rfl, rfl, rfl⟩, fun n' R' hR' Y _ => ?_⟩
          obtain rfl := hR' rfl
          simp only [List.append_nil]
          refine ⟨?_, ?_, _, Z, ⟨_, hl'.ref hz⟩, ?_⟩
          · have e := vt_keeps z id (boxItems l') Z n' []
            rw [List.append_nil] at e
            rw [e]
            exact keepN_ext n' z
          · have e := keepN_succ_kept n' z []
            rw [List.append_nil] at e
            rw [show Step.keep :: List.replicate n' Step.keep =
              List.replicate (n' + 1) .keep ++ [] by simp [List.replicate_succ], vt_keeps]
            exact e
          · rw [walkTy_keep hzk, ← List.append_nil (List.replicate n' Step.keep),
              walkTy_keeps hzk]
            rfl
        · -- the witness's content
          refine ⟨z, m, [.dia, .fst], [.dia], p, true, by simp, rfl,
            .inr ⟨[.fst], .dia, [], rfl, fun x hx => by
              rw [List.mem_singleton.mp hx]; rfl, rfl, rfl, ppath_nil⟩,
            (reach_ppath hz).1, (fun h => by cases h), fun n' R' _ Y hY => ?_⟩
          have hR : Step.walkTy Z R' = some (.VTypeDia Y) := by
            rw [walkTy_keep hUk, List.append_assoc, walkTy_keeps hUk] at hY
            exact hY
          refine ⟨?_, ?_, _, Y, ⟨_, hl'.ref hz⟩, ?_⟩
          · rw [List.append_assoc, vt_keeps,
              show [Step.dia, .fst] ++ R' = .dia :: .fst :: R' from rfl, vt_content _ _ _ _ R' hR,
              show (VarSymb.step (keepN n' z) .dia).ext R' = (keepN n' z).ext (.dia :: R') from rfl,
              keepN_ext, ← VarSymb.ext_append]
            simp
          · rw [List.append_assoc, keeps_cons_append, vt_keeps,
              show [Step.dia, .fst] ++ R' = .dia :: .fst :: R' from rfl, vt_content _ _ _ _ R' hR,
              show (VarSymb.step (keepN (n' + 1) z) .dia).ext R' =
                (keepN (n' + 1) z).ext (.dia :: R') from rfl, keepN_succ_kept,
              List.append_assoc]
            rfl
          · rw [walkTy_keep hzk, List.append_assoc, walkTy_keeps hzk]
            exact hR
        · -- an item
          obtain ⟨w, hw₁, hw₂, hw₃⟩ := boxItems_kept hk l' _ (List.getElem_mem hkl)
          refine ⟨w, m, .dia :: .snd :: itemPath k, [.keep], r, true, by simp, ?_,
            .inr ⟨.snd :: itemPath k, .keep, [], rfl, fun x hx => ?_, rfl, rfl, ppath_nil⟩,
            (reach_ppath hw₂).1, (fun h => by cases h), fun n' R' _ Y hY => ?_⟩
          · simp [Step.levels, Step.isProj, levels_pp (itemPath_ppath k)]
          · rcases List.mem_cons.mp hx with rfl | hx
            · rfl
            · exact itemPath_ppath k x hx
          · have hR : Step.walkTy (boxItems l')[k].2 R' = some (.VTypeDia Y) := by
              rw [walkTy_keep hUk, List.append_assoc, walkTy_keeps hUk] at hY
              change Step.walkTy (itemsTy (boxItems l')) (itemPath k ++ R') = _ at hY
              rwa [items_walk_eq] at hY
            refine ⟨?_, ?_, _, Y, ⟨_, hl'.ref hw₂⟩, ?_⟩
            · rw [List.append_assoc, vt_keeps,
                show (Step.dia :: Step.snd :: itemPath k) ++ R' =
                  .dia :: .snd :: (itemPath k ++ R') from rfl, vt_item _ _ _ _ k hkl R' hR]
              change (shiftN n' (boxItems l')[k].1).ext R' = _
              rw [hw₁, shiftN_keep,
                show (VarSymb.step (keepN n' w) .keep).ext R' = (keepN n' w).ext (.keep :: R')
                  from rfl, keepN_ext, ← VarSymb.ext_append]
              simp
            · rw [List.append_assoc, keeps_cons_append, vt_keeps,
                show (Step.dia :: Step.snd :: itemPath k) ++ R' =
                  .dia :: .snd :: (itemPath k ++ R') from rfl, vt_item _ _ _ _ k hkl R' hR]
              change (shiftN (n' + 1) (boxItems l')[k].1).ext R' = _
              rw [hw₁, shiftN_keep,
                show (VarSymb.step (keepN (n' + 1) w) .keep).ext R' =
                  (keepN (n' + 1) w).ext (.keep :: R') from rfl, keepN_succ_kept,
                List.append_assoc]
              rfl
            · rw [walkTy_keep hw₃, List.append_assoc, walkTy_keeps hw₃, List.singleton_append,
                walkTy_keep hw₃]
              exact hR


/-! ## Path edits on shaped paths -/

/-- Delete the level step `i` levels from the front. -/
def delLvl : ℕ → List Step → List Step
  | _, [] => []
  | i, s :: p =>
      if s.isProj then s :: delLvl i p
      else match i with
        | 0 => p
        | i + 1 => s :: delLvl i p

/-- The level step `i` levels from the front. -/
def lvlStep : ℕ → List Step → Option Step
  | _, [] => none
  | i, s :: p =>
      if s.isProj then lvlStep i p
      else match i with
        | 0 => some s
        | i + 1 => lvlStep i p

omit [ModalSys] in
theorem delLvl_proj {s : Step} (hs : s.isProj = true) (i : ℕ) (p : List Step) :
    delLvl i (s :: p) = s :: delLvl i p := by
  simp [delLvl, hs]

omit [ModalSys] in
theorem lvlStep_proj {s : Step} (hs : s.isProj = true) (i : ℕ) (p : List Step) :
    lvlStep i (s :: p) = lvlStep i p := by
  simp [lvlStep, hs]

omit [ModalSys] in
theorem delLvl_lvl_zero {s : Step} (hs : s.isProj = false) (p : List Step) :
    delLvl 0 (s :: p) = p := by
  simp [delLvl, hs]

omit [ModalSys] in
theorem delLvl_lvl_succ {s : Step} (hs : s.isProj = false) (i : ℕ) (p : List Step) :
    delLvl (i + 1) (s :: p) = s :: delLvl i p := by
  simp [delLvl, hs]

omit [ModalSys] in
theorem lvlStep_lvl_zero {s : Step} (hs : s.isProj = false) (p : List Step) :
    lvlStep 0 (s :: p) = some s := by
  simp [lvlStep, hs]

omit [ModalSys] in
theorem lvlStep_lvl_succ {s : Step} (hs : s.isProj = false) (i : ℕ) (p : List Step) :
    lvlStep (i + 1) (s :: p) = lvlStep i p := by
  simp [lvlStep, hs]

omit [ModalSys] in
/-- ⭐**Collapsing a `keep` level deletes it** (the keep-absorbing case deletes the `keep` before
    it, the same list). -/
theorem collapseAt_eq_delLvl : ∀ (i : ℕ) (p : List Step), lvlStep i p = some .keep →
    Step.collapseAt i p = delLvl i p
  | _, [], h => by cases h
  | i, s :: p, h => by
      by_cases hs : s.isProj = true
      · rw [Step.collapseAt_proj hs, delLvl_proj hs]
        rw [lvlStep_proj hs] at h
        rw [collapseAt_eq_delLvl i p h]
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        cases i with
        | zero =>
            rw [lvlStep_lvl_zero hs'] at h
            cases h
            rw [Step.collapseAt_zero hs', if_pos rfl, delLvl_lvl_zero hs']
        | succ i =>
            rw [lvlStep_lvl_succ hs'] at h
            rw [Step.collapseAt_succ hs', delLvl_lvl_succ hs']
            split
            · rename_i hc
              obtain ⟨rfl, rfl, hh⟩ := hc
              cases p with
              | nil => cases h
              | cons u p =>
                  have hu : u.isProj = false := by simpa [Step.headLvl] using hh
                  rw [lvlStep_lvl_zero hu] at h
                  cases h
                  rw [delLvl_lvl_zero hu]
            · rw [collapseAt_eq_delLvl i p h]

omit [ModalSys] in
theorem shiftAt_ppath : ∀ (i : ℕ) {p : List Step}, PPath p → Step.shiftAt i p = p
  | _, [], _ => rfl
  | i, s :: p, h => by
      rw [Step.shiftAt_proj (h s List.mem_cons_self),
        shiftAt_ppath i (fun x hx => h x (List.mem_cons_of_mem _ hx))]

omit [ModalSys] in
theorem delLvl_ppath : ∀ (i : ℕ) {p : List Step}, PPath p → delLvl i p = p
  | _, [], _ => rfl
  | i, s :: p, h => by
      rw [delLvl_proj (h s List.mem_cons_self),
        delLvl_ppath i (fun x hx => h x (List.mem_cons_of_mem _ hx))]

omit [ModalSys] in
theorem lvlStep_ppath : ∀ (i : ℕ) {p : List Step}, PPath p → lvlStep i p = none
  | _, [], _ => rfl
  | i, s :: p, h => by
      rw [lvlStep_proj (h s List.mem_cons_self),
        lvlStep_ppath i (fun x hx => h x (List.mem_cons_of_mem _ hx))]

omit [ModalSys] in
/-- Inserting a `keep` in a concatenation: in the first part if its level is there. -/
theorem shiftAt_append : ∀ (i : ℕ) (Y Z : List Step),
    Step.shiftAt i (Y ++ Z) =
      if i < Step.levels Y then Step.shiftAt i Y ++ Z else Y ++ Step.shiftAt (i - Step.levels Y) Z
  | i, [], Z => by simp [Step.levels]
  | i, s :: Y, Z => by
      by_cases hs : s.isProj = true
      · rw [List.cons_append, Step.shiftAt_proj hs, Step.shiftAt_proj hs, shiftAt_append i Y Z,
          Step.levels_cons, if_pos hs, Nat.zero_add]
        split <;> rfl
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        rw [List.cons_append, Step.levels_cons, if_neg hs]
        cases i with
        | zero =>
            rw [Step.shiftAt_zero hs', Step.shiftAt_zero hs', if_pos (by omega)]
            rfl
        | succ i =>
            rw [Step.shiftAt_succ hs', Step.shiftAt_succ hs', shiftAt_append i Y Z]
            by_cases hl : i < Step.levels Y
            · rw [if_pos hl, if_pos (by omega)]
              rfl
            · rw [if_neg hl, if_neg (by omega), show i + 1 - (1 + Step.levels Y) =
                i - Step.levels Y by omega]
              rfl

omit [ModalSys] in
theorem delLvl_append : ∀ (i : ℕ) (Y Z : List Step),
    delLvl i (Y ++ Z) =
      if i < Step.levels Y then delLvl i Y ++ Z else Y ++ delLvl (i - Step.levels Y) Z
  | i, [], Z => by simp [Step.levels]
  | i, s :: Y, Z => by
      by_cases hs : s.isProj = true
      · rw [List.cons_append, delLvl_proj hs, delLvl_proj hs, delLvl_append i Y Z,
          Step.levels_cons, if_pos hs, Nat.zero_add]
        split <;> rfl
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        rw [List.cons_append, Step.levels_cons, if_neg hs]
        cases i with
        | zero =>
            rw [delLvl_lvl_zero hs', delLvl_lvl_zero hs', if_pos (by omega)]
        | succ i =>
            rw [delLvl_lvl_succ hs', delLvl_lvl_succ hs', delLvl_append i Y Z]
            by_cases hl : i < Step.levels Y
            · rw [if_pos hl, if_pos (by omega)]
              rfl
            · rw [if_neg hl, if_neg (by omega), show i + 1 - (1 + Step.levels Y) =
                i - Step.levels Y by omega]
              rfl

omit [ModalSys] in
theorem lvlStep_append : ∀ (i : ℕ) (Y Z : List Step),
    lvlStep i (Y ++ Z) =
      if i < Step.levels Y then lvlStep i Y else lvlStep (i - Step.levels Y) Z
  | i, [], Z => by simp [Step.levels]
  | i, s :: Y, Z => by
      by_cases hs : s.isProj = true
      · rw [List.cons_append, lvlStep_proj hs, lvlStep_proj hs, lvlStep_append i Y Z,
          Step.levels_cons, if_pos hs, Nat.zero_add]
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        rw [List.cons_append, Step.levels_cons, if_neg hs]
        cases i with
        | zero =>
            rw [lvlStep_lvl_zero hs', lvlStep_lvl_zero hs', if_pos (by omega)]
        | succ i =>
            rw [lvlStep_lvl_succ hs', lvlStep_lvl_succ hs', lvlStep_append i Y Z]
            by_cases hl : i < Step.levels Y
            · rw [if_pos hl, if_pos (by omega)]
            · rw [if_neg hl, if_neg (by omega), show i + 1 - (1 + Step.levels Y) =
                i - Step.levels Y by omega]

omit [ModalSys] in
theorem shiftAt_rep : ∀ (i n : ℕ), i < n →
    Step.shiftAt i (List.replicate n .keep) = List.replicate (n + 1) .keep
  | _, 0, h => absurd h (by omega)
  | 0, n + 1, _ => by
      rw [List.replicate_succ, Step.shiftAt_zero rfl]
      rfl
  | i + 1, n + 1, h => by
      rw [List.replicate_succ, Step.shiftAt_succ rfl, shiftAt_rep i n (by omega)]
      rfl

omit [ModalSys] in
theorem delLvl_rep : ∀ (i n : ℕ), i < n →
    delLvl i (List.replicate n .keep) = List.replicate (n - 1) .keep
  | _, 0, h => absurd h (by omega)
  | 0, n + 1, _ => by
      rw [List.replicate_succ, delLvl_lvl_zero rfl]
      rfl
  | i + 1, n + 1, h => by
      rw [List.replicate_succ, delLvl_lvl_succ rfl, delLvl_rep i n (by omega)]
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rfl

omit [ModalSys] in
theorem lvlStep_rep : ∀ (i n : ℕ), i < n → lvlStep i (List.replicate n .keep) = some .keep
  | _, 0, h => absurd h (by omega)
  | 0, n + 1, _ => by
      rw [List.replicate_succ, lvlStep_lvl_zero rfl]
  | i + 1, n + 1, h => by
      rw [List.replicate_succ, lvlStep_lvl_succ rfl, lvlStep_rep i n (by omega)]

omit [ModalSys] in
theorem levels_rep (n : ℕ) : Step.levels (List.replicate n .keep) = n := by
  have := levels_keeps n []
  rwa [List.append_nil, Step.levels, Nat.add_zero] at this

/-! ## Members along composite paths -/

/-- ⭐**A typed kept address**: `v.keep.q`, `v` a declared address of keepable type, `q` typed in
    it from the `keep`. -/
def KOk (t : GW hF M₀) (v : VarSymb) (q : List Step) : Prop :=
  PPath v.path ∧ ∃ U X, DeclAt t v U ∧ Step.walkTy U (.keep :: q) = some (.VTypeDia X)

/-- ⭐**A typed kept address's members along `c :: P` are its translation's members along
    `P`**, whatever keeps come first. -/
theorem gMem_step (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {t : GW hF M₀} {v : VarSymb}
    {q : List Step} (hk : KOk t v q) (c : ℕ) (hb : GBorn hF M₀ (c :: t.1)) :
    ∃ w q', KOk (stepW t c hb) w q' ∧ Step.levels q' = Step.levels q ∧
      (NoProjHead q → NoProjHead q') ∧
      ∀ (n : ℕ) (t' : GW hF M₀) (P : List ℕ) (h : t'.1 = nodeOf t.1 (c :: P)),
        gMem t t' (c :: P) h ((VarSymb.step v .keep).ext (List.replicate n .keep ++ q)) =
          gMem (stepW t c hb) t' P h ((VarSymb.step w .keep).ext (List.replicate n .keep ++ q'))
  := by
  obtain ⟨hv, U, X, hd, hq⟩ := hk
  obtain ⟨w, q', he, hw, ⟨U', X', hd', hq'⟩, hl, hnp⟩ := keptTr_ok hT hM₀ t c hb hd hq
  refine ⟨w, q', ⟨hw, U', X', hd', hq'⟩, hl, hnp, fun n t' P h => ?_⟩
  rw [gMem_kept_cons t t' c P h hv, he n, if_pos]
  rw [levels_kept hw, levels_keeps, levels_keeps, hl]

/-- ⭐**A kept address kept once more has the family of its members**, along any path. -/
theorem gMem_dk (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) :
    ∀ (Q : List ℕ) {t t'' : GW hF M₀} (h : t''.1 = nodeOf t.1 Q) {v : VarSymb} {q : List Step},
      KOk t v q →
      gMem t t'' Q h ((VarSymb.step v .keep).ext (.keep :: q)) =
        .fam fun b => gMem t b.1 (Q ++ pathOf b.2.down)
          (by rw [nodeOf_append, ← h]; exact pathOf_eq b.2.down)
          ((VarSymb.step v .keep).ext q)
  | [], t, t'', h, v, q, hk => by
      obtain rfl : t'' = t := gw_eq h
      rw [gMem_kept_nil _ _ _ hk.1]
      exact gLab_keep _ hk.1 q
  | c :: Q, t, t'', h, v, q, hk => by
      obtain ⟨w, q', hk', -, -, he⟩ := gMem_step hT hM₀ hk c (born_step h)
      have e₁ := he 1 t'' Q h
      simp only [List.replicate_one, List.singleton_append] at e₁
      rw [e₁, gMem_dk hT hM₀ Q h hk']
      congr 1
      funext b
      exact (he 0 b.1 (Q ++ pathOf b.2.down) _).symm

theorem not_declAt_junk (t : GW hF M₀) (T : VarType) : ¬ DeclAt t junkR T := fun ⟨_, h⟩ => by
  obtain ⟨r, hr⟩ := (reach_ppath h).2
  cases hr

theorem not_typedAt_junk (t : GW hF M₀) (p : List Step) : ¬ TypedAt t junkR p :=
  fun ⟨_, hd, _⟩ => not_declAt_junk t _ hd

/-- ⭐**Leaves kept along an arrow by the canonical action**: a root by `gKeep`, a family
    reindexed. -/
noncomputable def gKA {s : GW hF M₀} (a : (garrows hF M₀).Acc s) :
    GLeaf hF M₀ s → GLeaf hF M₀ a.1
  | .root r p => gKeep s r a p
  | .fam f => .fam fun t => f ⟨t.1, ⟨gtrans a.2.down t.2.down⟩⟩

/-- The arrow of a path. -/
abbrev pathAcc {s t : GW hF M₀} {P : List ℕ} (hP : PathOk P) (h : t.1 = nodeOf s.1 P) :
    (garrows hF M₀).Acc s :=
  ⟨t, ⟨⟨P, hP, h⟩⟩⟩

/-- ⭐**The root possibility at a position of a typed kept address, kept along an arrow, is the
    kept address's member there** (the base case of composition): a root path `r` or `r.dia…` is
    kept by `gKeep`; a family `r.keep…` by reindexing, the doubled keep (`gMem_dk`). -/
theorem gKA_gLab (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {t : GW hF M₀} {w : VarSymb}
    {q : List Step} (hk : KOk t w q) (hnp : NoProjHead q) (b : (garrows hF M₀).Acc t) :
    gKA b (gLab t (w.ext q)) = gMem t b.1 (pathOf b.2.down) (pathOf_eq b.2.down)
      ((VarSymb.step w .keep).ext q) := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  obtain ⟨hw, U, X, hd, hq⟩ := hk
  obtain ⟨U₁, hU₁, -⟩ := Option.bind_eq_some_iff.mp hq
  have hUk : U.keepable = true := Step.typeStep_level_keepable rfl hU₁
  have hq₂ : Step.walkTy U q = some (.VTypeDia X) := (walkTy_keep hUk q).symm.trans hq
  -- a root path typed for `w`, labelling `w.q`, is kept as the member
  have hroot : TypedAt t w q → (∀ t' : GW hF M₀, gLab t' (w.ext q) = .root w q) →
      gKA b (.root w q) = gMem t b.1 (pathOf b.2.down) (pathOf_eq b.2.down)
        ((VarSymb.step w .keep).ext q) := by
    intro hty hlab
    change gKeepP t b.1 (pathOf b.2.down) (pathOf_eq b.2.down) w q = _
    generalize pathOf b.2.down = P, pathOf_eq b.2.down = hP
    cases P with
    | nil =>
        rw [gMem_kept_nil _ _ _ hw]
        exact (hlab _).symm
    | cons c P => exact if_pos hty
  -- a kept possibility or necessary object: the family of its members
  have hfam : ∀ r, q = .keep :: r →
      gKA b (gLab t (w.ext q)) = gMem t b.1 (pathOf b.2.down) (pathOf_eq b.2.down)
        ((VarSymb.step w .keep).ext q) := by
    rintro r rfl
    change gKA b (gLab t ((VarSymb.step w .keep).ext r)) = _
    rw [gLab_keep _ hw, gMem_dk hT hM₀ _ _ ⟨hw, U, X, hd, ?_⟩]
    · change Arrows.Leaf.fam _ = Arrows.Leaf.fam _
      congr 1
      funext t''
      exact gMem_path (pathOf_trans b.2.down t''.2.down) _ _ _
    · exact hq₂
  cases q with
  | nil =>
      change some U = some _ at hq₂
      cases hq₂
      change gKA b (gLab t w) = _
      rw [gLab_ppath _ hw]
      exact hroot ⟨X, hd, X, rfl⟩ fun _ => gLab_ppath _ hw
  | cons s r =>
      obtain ⟨U₂, hU₂, -⟩ := Option.bind_eq_some_iff.mp hq₂
      rcases typeStep_some hU₂ with ⟨_, _, -, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ |
        ⟨_, -, ⟨rfl, hk', -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ | ⟨A, he, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
      · exact absurd (hnp .fst rfl) (by decide)
      · exact absurd (hnp .snd rfl) (by decide)
      · rw [hko] at hk'
        cases hk'
      · exact absurd (hnp .here rfl) (by decide)
      · exact hfam r rfl
      · -- a possibility's content: a root path
        subst he
        change gKA b (gLab t ((VarSymb.step w .dia).ext r)) = _
        rw [gLab_dia _ hw]
        exact hroot ⟨A, hd, X, hq₂⟩ fun _ => gLab_dia _ hw r
      · exact hfam r rfl

/-- ⭐**Keeping a member along an arrow is the member along the composite**, for a typed kept
    address not starting with a projection (a root possibility's), along a nonempty path. -/
theorem gKA_gMem (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) :
    ∀ (P : List ℕ) {t t' : GW hF M₀} (h : t'.1 = nodeOf t.1 P) {v : VarSymb} {q : List Step},
      P ≠ [] → KOk t v q → NoProjHead q → ∀ b : (garrows hF M₀).Acc t',
      gKA b (gMem t t' P h ((VarSymb.step v .keep).ext q)) =
        gMem t b.1 (P ++ pathOf b.2.down) (by rw [nodeOf_append, ← h]; exact pathOf_eq b.2.down)
          ((VarSymb.step v .keep).ext q)
  | [], _, _, _, _, _, hP, _, _, _ => absurd rfl hP
  | c :: P, t, t', h, v, q, _, hk, hnp, b => by
      obtain ⟨w, q', hk', -, hnp', he⟩ := gMem_step hT hM₀ hk c (born_step h)
      have e₁ := he 0 t' P h
      have e₂ := he 0 b.1 (P ++ pathOf b.2.down)
        (by
          rw [show c :: (P ++ pathOf b.2.down) = (c :: P) ++ pathOf b.2.down from rfl,
            nodeOf_append, ← h]
          exact pathOf_eq b.2.down)
      simp only [List.replicate_zero, List.nil_append] at e₁ e₂
      rw [e₁, show gMem t b.1 (c :: P ++ pathOf b.2.down) _ ((VarSymb.step v .keep).ext q) =
        gMem (stepW t c (born_step h)) b.1 (P ++ pathOf b.2.down) _
          ((VarSymb.step w .keep).ext q') from e₂]
      cases P with
      | nil =>
          have e : t' = stepW t c (born_step h) := gw_eq h
          have hk'' : KOk t' w q' := by rw [e]; exact hk'
          rw [gMem_kept_nil _ _ _ hk'.1, gKA_gLab hT hM₀ hk'' (hnp' hnp) b]
          exact gMem_world e _ _ _ _
      | cons c' P =>
          exact gKA_gMem hT hM₀ (c' :: P) h (List.cons_ne_nil _ _) hk' (hnp' hnp) b

/-- A possible object's positions do not start with a projection. -/
theorem noProjHead_of_dia {A X : VarType} {p : List Step}
    (h : Step.walkTy (.VTypeDia A) p = some (.VTypeDia X)) : NoProjHead p := by
  cases p with
  | nil => exact fun _ h' => by cases h'
  | cons s p =>
      obtain ⟨U, hU, -⟩ := Option.bind_eq_some_iff.mp h
      rcases typeStep_some hU with ⟨_, _, he, -⟩ | ⟨_, he, -⟩ | ⟨_, -, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
      · cases he
      · cases he
      · exact noProjHead_cons rfl _
      · exact noProjHead_cons rfl _

theorem kOk_of_typedAt {s : GW hF M₀} {r : VarSymb} {p : List Step} (h : TypedAt s r p) :
    KOk s r p ∧ NoProjHead p := by
  obtain ⟨A, ⟨i, hd⟩, X, hp⟩ := h
  exact ⟨⟨(reach_ppath hd).1, _, X, ⟨i, hd⟩, (walkTy_keep rfl p).trans hp⟩,
    noProjHead_of_dia hp⟩

open Classical in
/-- ⭐**Composition along paths**: the root action along `P`, kept along an arrow, is the root
    action along the composite path. -/
theorem gKA_gKeepP (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀}
    (P : List ℕ) (h : t.1 = nodeOf s.1 P) (r : VarSymb) (p : List Step)
    (b : (garrows hF M₀).Acc t) :
    gKA b (gKeepP s t P h r p) =
      gKeepP s b.1 (P ++ pathOf b.2.down) (by rw [nodeOf_append, ← h]; exact pathOf_eq b.2.down)
        r p := by
  cases P with
  | nil =>
      obtain rfl : t = s := gw_eq h
      rfl
  | cons c P =>
      by_cases hty : TypedAt s r p
      · obtain ⟨hk, hnp⟩ := kOk_of_typedAt hty
        change gKA b (if TypedAt s r p then _ else _) = if TypedAt s r p then _ else _
        rw [if_pos hty, if_pos hty]
        exact gKA_gMem hT hM₀ (c :: P) h (List.cons_ne_nil _ _) hk hnp b
      · change gKA b (if TypedAt s r p then _ else _) = if TypedAt s r p then _ else _
        rw [if_neg hty, if_neg hty]
        change gKeepP t b.1 (pathOf b.2.down) (pathOf_eq b.2.down) junkR p = _
        generalize pathOf b.2.down = Q, pathOf_eq b.2.down = hQ
        cases Q with
        | nil => rfl
        | cons c' Q => exact if_neg (not_typedAt_junk t p)

/-- ⭐**The canonical action composes**: kept along `a` then `b` is kept along `a ≫ b`. -/
theorem gKeep_trans (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀}
    (r : VarSymb) (a : (garrows hF M₀).Acc s) (b : (garrows hF M₀).Acc a.1) (p : List Step) :
    gKA b (gKeep s r a p) = gKeep s r ⟨b.1, ⟨gtrans a.2.down b.2.down⟩⟩ p := by
  change gKA b (gKeepP s a.1 (pathOf a.2.down) (pathOf_eq a.2.down) r p) =
    gKeepP s b.1 (pathOf (gtrans a.2.down b.2.down)) (pathOf_eq _) r p
  rw [gKA_gKeepP hT hM₀]
  exact gKeepP_path (pathOf_trans a.2.down b.2.down).symm _ _ r p

/-- ⭐**Along the identity, a root path stays.** -/
theorem gKeep_refl (hT : ModalSys.T = true) {s : GW hF M₀} (r : VarSymb) (p : List Step) :
    gKeep s r ⟨s, ⟨grefl hT s⟩⟩ p = .root r p := by
  change gKeepP s s (pathOf (grefl hT s)) (pathOf_eq _) r p = _
  rw [gKeepP_path (pathOf_refl hT s) _ rfl]
  rfl

/-! ## Naturality: the edits through a translation -/

omit [ModalSys] in
theorem levels_form {n : ℕ} {X X' R : List Step} (h : Step.levels X = Step.levels X') :
    Step.levels (List.replicate n .keep ++ X ++ R) =
      Step.levels (List.replicate n .keep ++ X' ++ R) := by
  rw [Step.levels_append, Step.levels_append, Step.levels_append, Step.levels_append, h]

omit [ModalSys] in
/-- ⭐**A shift goes through a translation's form**: before a leading keep or the piece's level
    step, one more leading keep; after them, in the rest. -/
theorem form_shift {n i : ℕ} {X X' R : List Step} (hsh : ShapeOK X X')
    (hi : i < Step.levels (List.replicate n .keep ++ X ++ R)) :
    ∃ n' R', Step.shiftAt i (List.replicate n .keep ++ X ++ R) =
        List.replicate n' .keep ++ X ++ R' ∧
      Step.shiftAt i (List.replicate n .keep ++ X' ++ R) = List.replicate n' .keep ++ X' ++ R' ∧
      (R = [] → R' = []) := by
  simp only [List.append_assoc] at hi ⊢
  rw [shiftAt_append i (List.replicate n .keep) (X ++ R),
    shiftAt_append i (List.replicate n .keep) (X' ++ R), levels_rep]
  by_cases hin : i < n
  · rw [if_pos hin, if_pos hin, shiftAt_rep i n hin]
    exact ⟨n + 1, R, by simp, by simp, id⟩
  · rw [if_neg hin, if_neg hin, shiftAt_append (i - n) X R, shiftAt_append (i - n) X' R]
    rcases hsh with ⟨hX, hX'⟩ | ⟨Xp, s', X'p, rfl, hXp, rfl, hs', hX'p⟩
    · rw [levels_pp hX, levels_pp hX', if_neg (by omega), if_neg (by omega)]
      exact ⟨n, Step.shiftAt (i - n - 0) R, rfl, rfl, fun h => by subst h; rfl⟩
    · have hl : Step.levels (Step.dia :: Xp) = 1 := by
        rw [Step.levels_cons, if_neg (by decide), levels_pp hXp]
      have hl' : Step.levels (s' :: X'p) = 1 := by
        rw [Step.levels_cons, if_neg (by simp [hs']), levels_pp hX'p]
      rw [hl, hl']
      by_cases h0 : i - n < 1
      · rw [if_pos h0, if_pos h0, show i - n = 0 by omega, Step.shiftAt_zero (by decide),
          Step.shiftAt_zero hs']
        exact ⟨n + 1, R, by simp [List.replicate_succ'], by simp [List.replicate_succ'], id⟩
      · rw [if_neg h0, if_neg h0]
        exact ⟨n, Step.shiftAt (i - n - 1) R, rfl, rfl, fun h => by subst h; rfl⟩

omit [ModalSys] in
/-- ⭐**Deleting a `keep` level goes through a translation's form**: a leading keep, or in the
    rest (the piece's level step is not a `keep`'s to delete). -/
theorem form_del {n i : ℕ} {X X' R : List Step} (hsh : ShapeOK X X')
    (hi : lvlStep i (List.replicate n .keep ++ X ++ R) = some .keep) :
    ∃ n' R', delLvl i (List.replicate n .keep ++ X ++ R) = List.replicate n' .keep ++ X ++ R' ∧
      delLvl i (List.replicate n .keep ++ X' ++ R) = List.replicate n' .keep ++ X' ++ R' ∧
      lvlStep i (List.replicate n .keep ++ X' ++ R) = some .keep ∧ (R = [] → R' = []) := by
  simp only [List.append_assoc] at hi ⊢
  rw [lvlStep_append i (List.replicate n .keep) (X ++ R), levels_rep] at hi
  rw [delLvl_append i (List.replicate n .keep) (X ++ R),
    delLvl_append i (List.replicate n .keep) (X' ++ R),
    lvlStep_append i (List.replicate n .keep) (X' ++ R), levels_rep]
  by_cases hin : i < n
  · rw [if_pos hin, if_pos hin, if_pos hin, delLvl_rep i n hin, lvlStep_rep i n hin]
    exact ⟨n - 1, R, by simp, by simp, rfl, id⟩
  · rw [if_neg hin] at hi
    rw [if_neg hin, if_neg hin, if_neg hin, delLvl_append (i - n) X R, delLvl_append (i - n) X' R,
      lvlStep_append (i - n) X' R]
    rw [lvlStep_append (i - n) X R] at hi
    rcases hsh with ⟨hX, hX'⟩ | ⟨Xp, s', X'p, rfl, hXp, rfl, hs', hX'p⟩
    · rw [levels_pp hX] at hi
      rw [levels_pp hX, levels_pp hX', if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [if_neg (by omega)] at hi
      refine ⟨n, delLvl (i - n - 0) R, rfl, rfl, hi, fun h => ?_⟩
      subst h
      cases hi
    · have hl : Step.levels (Step.dia :: Xp) = 1 := by
        rw [Step.levels_cons, if_neg (by decide), levels_pp hXp]
      have hl' : Step.levels (s' :: X'p) = 1 := by
        rw [Step.levels_cons, if_neg (by simp [hs']), levels_pp hX'p]
      rw [hl] at hi
      rw [hl, hl']
      by_cases h0 : i - n < 1
      · rw [if_pos h0, show i - n = 0 by omega, lvlStep_lvl_zero (by decide)] at hi
        cases hi
      · rw [if_neg h0] at hi
        rw [if_neg h0, if_neg h0, if_neg h0]
        refine ⟨n, delLvl (i - n - 1) R, rfl, rfl, hi, fun h => ?_⟩
        subst h
        cases hi

/-- A path typed from a type walks on projections as the type does. -/
theorem walkTy_ppath : ∀ (T : VarType) {q : List Step}, PPath q → Step.walkTy T q = T.walk q
  | _, [], _ => rfl
  | T, s :: q, h => by
      have hs := h s List.mem_cons_self
      change (Step.typeStep T s).bind _ = (T.step s).bind _
      have e : Step.typeStep T s = T.step s := by
        cases s <;> first | rfl | cases hs
      rw [e]
      cases T.step s with
      | none => rfl
      | some U => exact walkTy_ppath U (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- A typed kept address split at a projection prefix: its prefix's own kept address. -/
theorem kOk_proj {t : GW hF M₀} {v : VarSymb} {q₀ q₁ : List Step} (hk : KOk t v (q₀ ++ q₁))
    (hq₀ : PPath q₀) (hq₁ : Step.headLvl q₁ = true) : KOk t (v.ext q₀) q₁ := by
  obtain ⟨hv, U, X, ⟨i, hi⟩, hq⟩ := hk
  obtain ⟨U₁, hU₁, -⟩ := Option.bind_eq_some_iff.mp hq
  have hUk : U.keepable = true := Step.typeStep_level_keepable rfl hU₁
  rw [walkTy_keep hUk, Step.walkTy_append, walkTy_ppath U hq₀] at hq
  obtain ⟨U', hU', hq'⟩ := Option.bind_eq_some_iff.mp hq
  refine ⟨?_, U', X, ⟨i, ?_⟩, ?_⟩
  · rw [VarSymb.ext_path]
    exact fun x hx => (List.mem_append.mp hx).elim (hv x) (hq₀ x)
  · rw [Ctx.ref_ext_ppath _ q₀ v hq₀, hi]
    exact hU'
  · cases q₁ with
    | nil => cases hq₁
    | cons s r =>
        have hs : s.isProj = false := by simpa [Step.headLvl] using hq₁
        obtain ⟨U₂, hU₂, -⟩ := Option.bind_eq_some_iff.mp hq'
        rw [walkTy_keep (Step.typeStep_level_keepable hs hU₂)]
        exact hq'

/-- A typed kept address split before a `keep`: the prefix's own kept address. -/
theorem kOk_proj_keep {t : GW hF M₀} {v : VarSymb} {q₀ r : List Step}
    (hk : KOk t v (q₀ ++ .keep :: r)) (hq₀ : PPath q₀) : KOk t (v.ext q₀) r := by
  obtain ⟨hv, U', X, hd, hq⟩ := kOk_proj hk hq₀ rfl
  obtain ⟨U₁, hU₁, -⟩ := Option.bind_eq_some_iff.mp hq
  exact ⟨hv, U', X, hd, (walkTy_keep (Step.typeStep_level_keepable rfl hU₁) _).symm.trans hq⟩

/-- One edge of a member, given where the edge sends the kept address. -/
theorem gMem_tr (t t' : GW hF M₀) (c : ℕ) (P : List ℕ) (h : t'.1 = nodeOf t.1 (c :: P))
    {v w : VarSymb} (hv : PPath v.path) (hw : PPath w.path) {q q' : List Step}
    (he : entIdx (fmapL hF M₀ (c :: t.1) (.step v .keep)) (.keep :: q) =
      (VarSymb.step w .keep).ext q')
    (hl : Step.levels q' = Step.levels q) :
    gMem t t' (c :: P) h ((VarSymb.step v .keep).ext q) =
      gMem (stepW t c (born_step h)) t' P h ((VarSymb.step w .keep).ext q') := by
  rw [gMem_kept_cons t t' c P h hv, he, if_pos]
  rw [levels_kept hw, hl]

/-- The canonical root action, as a root action. -/
noncomputable def gRK : Arrows.RootKeep (garrows hF M₀) (fun _ => VarSymb) :=
  ⟨fun _ {s} r a p => gKeep s r a p⟩

theorem keepAlong_gRK {s : GW hF M₀} (a : (garrows hF M₀).Acc s) (ℓ : GLeaf hF M₀ s) :
    @Arrows.Leaf.keepAlong _ _ (garrows hF M₀) (fun _ => VarSymb) gRK hF s a ℓ = gKA a ℓ := by
  match ℓ with
  | .root _ _ => rfl
  | .fam _ => rfl

/-- `dk` for the canonical action. -/
noncomputable abbrev gdk (j : ℕ) {s : GW hF M₀} (ℓ : GLeaf hF M₀ s) : GLeaf hF M₀ s :=
  @Arrows.Leaf.dk _ _ (garrows hF M₀) (fun _ => VarSymb) gRK hF j s ℓ

/-- `dkB` for the canonical action. -/
noncomputable abbrev gdkB (j : ℕ) {s : GW hF M₀} (ℓ : GLeaf hF M₀ s) : GLeaf hF M₀ s :=
  @Arrows.Leaf.dkB _ _ (garrows hF M₀) (fun _ => VarSymb) gRK hF j s ℓ

omit [ModalSys] in
/-- A path with a level step splits at its first one. -/
theorem split_first : ∀ q : List Step, 0 < Step.levels q →
    ∃ q₀ s r, q = q₀ ++ s :: r ∧ PPath q₀ ∧ s.isProj = false
  | [], h => absurd h (by simp [Step.levels])
  | s :: q, h => by
      by_cases hs : s.isProj = true
      · rw [Step.levels_cons, if_pos hs, Nat.zero_add] at h
        obtain ⟨q₀, s', r, rfl, hq₀, hs'⟩ := split_first q h
        refine ⟨s :: q₀, s', r, rfl, fun x hx => ?_, hs'⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hs
        · exact hq₀ x hx
      · exact ⟨[], s, q, rfl, ppath_nil, Bool.eq_false_iff.mpr hs⟩

/-- A typed kept address has no `box` step (T + 4). -/
theorem kOk_no_box (hT : ModalSys.T = true) {t : GW hF M₀} {v : VarSymb} {q₀ r : List Step}
    (hk : KOk t v (q₀ ++ .box :: r)) : False := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  obtain ⟨-, U, X, -, hq⟩ := hk
  rw [show Step.keep :: (q₀ ++ .box :: r) = (.keep :: q₀) ++ .box :: r from rfl,
    Step.walkTy_append] at hq
  obtain ⟨V, -, hV⟩ := Option.bind_eq_some_iff.mp hq
  obtain ⟨W, hW, -⟩ := Option.bind_eq_some_iff.mp hV
  change (if ModalSys.keepOnly = true then none else V.step .box) = some W at hW
  rw [if_pos hko] at hW
  cases hW

/-- ⭐**(B) for shifts**: a member of a kept address shifted at level `i` is the member `dkB`'d
    there.  By induction on the level (a family passes the shift one level down to its members)
    and on the path (each edge's translation commutes with the shift, `form_shift`). -/
theorem gMem_shift (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) (i : ℕ) :
    ∀ (P : List ℕ) {t t' : GW hF M₀} (h : t'.1 = nodeOf t.1 P) {v : VarSymb} {q : List Step},
      KOk t v q → i < Step.levels q →
      gMem t t' P h ((VarSymb.step v .keep).ext (Step.shiftAt i q)) =
        gdkB i (gMem t t' P h ((VarSymb.step v .keep).ext q)) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro P
  induction P with
  | nil =>
      intro t t' h v q hk hi
      obtain rfl : t' = t := gw_eq h
      rw [gMem_kept_nil _ _ _ hk.1, gMem_kept_nil _ _ _ hk.1]
      obtain ⟨q₀, s, r, rfl, hq₀, hs⟩ := split_first q (by omega)
      rw [shiftAt_append, levels_pp hq₀, if_neg (by omega), Nat.sub_zero]
      have hpre : PPath (v.ext q₀).path := by
        rw [VarSymb.ext_path]
        exact fun x hx => (List.mem_append.mp hx).elim (hk.1 x) (hq₀ x)
      cases i with
      | zero =>
          rw [Step.shiftAt_zero hs, VarSymb.ext_append, VarSymb.ext_append,
            show (v.ext q₀).ext (Step.keep :: s :: r) =
              (VarSymb.step (v.ext q₀) .keep).ext (s :: r) from rfl, gLab_keep _ hpre]
          change _ = Arrows.Leaf.fam fun b => @Arrows.Leaf.keepAlong _ _ (garrows hF M₀)
            (fun _ => VarSymb) gRK hF _ b _
          congr 1
          funext b
          rw [keepAlong_gRK]
          exact (gKA_gLab hT hM₀ (kOk_proj hk hq₀ (by simp [Step.headLvl, hs]))
            (noProjHead_cons hs r) b).symm
      | succ i =>
          rw [Step.shiftAt_succ hs, VarSymb.ext_append, VarSymb.ext_append]
          cases s with
          | fst => cases hs
          | snd => cases hs
          | here => cases hs
          | box => exact (kOk_no_box hT hk).elim
          | dia =>
              rw [show (v.ext q₀).ext (Step.dia :: Step.shiftAt i r) =
                  (VarSymb.step (v.ext q₀) .dia).ext (Step.shiftAt i r) from rfl,
                show (v.ext q₀).ext (Step.dia :: r) = (VarSymb.step (v.ext q₀) .dia).ext r from rfl,
                gLab_dia _ hpre, gLab_dia _ hpre]
              rfl
          | keep =>
              rw [show (v.ext q₀).ext (Step.keep :: Step.shiftAt i r) =
                  (VarSymb.step (v.ext q₀) .keep).ext (Step.shiftAt i r) from rfl,
                show (v.ext q₀).ext (Step.keep :: r) =
                  (VarSymb.step (v.ext q₀) .keep).ext r from rfl,
                gLab_keep _ hpre, gLab_keep _ hpre]
              change _ = Arrows.Leaf.fam fun b => gdkB i _
              congr 1
              funext b
              have hl : i < Step.levels r := by
                rw [Step.levels_append, levels_pp hq₀, Step.levels_cons, if_neg (by decide)] at hi
                omega
              exact ih i (Nat.lt_succ_self i) _ _ (kOk_proj_keep hk hq₀) hl
  | cons c P ihP =>
      intro t t' h v q hk hi
      obtain ⟨hv, U, X₀, hd, hq⟩ := hk
      obtain ⟨w, n, X, X', R, tl, rfl, hlX, hsh, hw, htl, hform⟩ :=
        keptTr_form hT hM₀ t c (born_step h) hd hq
      obtain ⟨n', R', e₁, e₂, hR⟩ := form_shift hsh hi
      have htR : tl = false → R = [] := fun h => (htl h).2.2
      obtain ⟨-, he₀, U', Y', hd', hY'⟩ := hform n R htR X₀ hq
      have hq₁ : Step.walkTy U (.keep :: Step.shiftAt i (List.replicate n .keep ++ X ++ R)) =
          some (.VTypeDia X₀) := by
        obtain ⟨U₁, hU₁, -⟩ := Option.bind_eq_some_iff.mp hq
        have hUk : U.keepable = true := Step.typeStep_level_keepable rfl hU₁
        rw [walkTy_keep hUk, Step.walkTy_shiftAt, ← walkTy_keep hUk]
        exact hq
      rw [e₁] at hq₁ ⊢
      obtain ⟨-, he₁, -⟩ := hform n' R' (fun h => hR (htR h)) X₀ hq₁
      rw [gMem_tr t t' c P h hv hw he₁ (levels_form hlX).symm,
        gMem_tr t t' c P h hv hw he₀ (levels_form hlX).symm, ← e₂]
      exact ihP h ⟨hw, U', Y', hd', hY'⟩ (by rw [← levels_form hlX]; exact hi)

omit [ModalSys] in
theorem lvlStep_lt : ∀ (i : ℕ) (q : List Step) {s : Step}, lvlStep i q = some s →
    i < Step.levels q
  | _, [], _, h => by cases h
  | i, t :: q, s, h => by
      by_cases ht : t.isProj = true
      · rw [lvlStep_proj ht] at h
        rw [Step.levels_cons, if_pos ht]
        have := lvlStep_lt i q h
        omega
      · have ht' : t.isProj = false := Bool.eq_false_iff.mpr ht
        rw [Step.levels_cons, if_neg ht]
        cases i with
        | zero => omega
        | succ i =>
            rw [lvlStep_lvl_succ ht'] at h
            have := lvlStep_lt i q h
            omega

/-- Deleting a `keep` keeps a walk. -/
theorem walkTy_delLvl : ∀ (i : ℕ) (q : List Step) (T Y : VarType), lvlStep i q = some .keep →
    Step.walkTy T q = some Y → Step.walkTy T (delLvl i q) = some Y
  | _, [], _, _, h, _ => by cases h
  | i, s :: q, T, Y, h, hw => by
      by_cases hs : s.isProj = true
      · rw [lvlStep_proj hs] at h
        rw [delLvl_proj hs]
        obtain ⟨V, hV, hq⟩ := Option.bind_eq_some_iff.mp hw
        exact Option.bind_eq_some_iff.mpr ⟨V, hV, walkTy_delLvl i q V Y h hq⟩
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        cases i with
        | zero =>
            rw [lvlStep_lvl_zero hs'] at h
            cases h
            rw [delLvl_lvl_zero hs']
            obtain ⟨V, hV, hq⟩ := Option.bind_eq_some_iff.mp hw
            obtain rfl : V = T := by
              change (if T.keepable = true then some T else none) = some V at hV
              split at hV
              · exact (Option.some.inj hV).symm
              · cases hV
            exact hq
        | succ i =>
            rw [lvlStep_lvl_succ hs'] at h
            rw [delLvl_lvl_succ hs']
            obtain ⟨V, hV, hq⟩ := Option.bind_eq_some_iff.mp hw
            exact Option.bind_eq_some_iff.mpr ⟨V, hV, walkTy_delLvl i q V Y h hq⟩

omit [ModalSys] in
theorem ppath_of_levels0 : ∀ {p : List Step}, Step.levels p = 0 → PPath p
  | [], _ => ppath_nil
  | s :: p, h => by
      rw [Step.levels_cons] at h
      have hs : s.isProj = true := by
        by_contra hs
        rw [if_neg hs] at h
        omega
      rw [if_pos hs, Nat.zero_add] at h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hs
      · exact ppath_of_levels0 h x hx

/-- A typed kept address with no level step after its `keep`: the address itself is a possible
    root, kept. -/
theorem kOk_end {t : GW hF M₀} {v : VarSymb} {q : List Step} (hk : KOk t v q) (hq : PPath q) :
    KOk t (v.ext q) [] := by
  obtain ⟨hv, U, X, ⟨i, hi⟩, hw⟩ := hk
  obtain ⟨U₁, hU₁, -⟩ := Option.bind_eq_some_iff.mp hw
  have hUk : U.keepable = true := Step.typeStep_level_keepable rfl hU₁
  rw [walkTy_keep hUk, walkTy_ppath U hq] at hw
  refine ⟨?_, .VTypeDia X, X, ⟨i, ?_⟩, rfl⟩
  · rw [VarSymb.ext_path]
    exact fun x hx => (List.mem_append.mp hx).elim (hv x) (hq x)
  · rw [Ctx.ref_ext_ppath _ q v hq, hi]
    exact hw

/-- ⭐**(B) for collapses**: a member of a kept address with a `keep` level deleted is the member
    collapsed there. -/
theorem gMem_del (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) (i : ℕ) :
    ∀ (P : List ℕ) {t t' : GW hF M₀} (h : t'.1 = nodeOf t.1 P) {v : VarSymb} {q : List Step},
      KOk t v q → lvlStep i q = some .keep →
      gMem t t' P h ((VarSymb.step v .keep).ext (delLvl i q)) =
        Arrows.Leaf.collapse hT i (gMem t t' P h ((VarSymb.step v .keep).ext q)) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro P
  induction P with
  | nil =>
      intro t t' h v q hk hi
      obtain rfl : t' = t := gw_eq h
      rw [gMem_kept_nil _ _ _ hk.1, gMem_kept_nil _ _ _ hk.1]
      obtain ⟨q₀, s, r, rfl, hq₀, hs⟩ := split_first q (by have := lvlStep_lt i q hi; omega)
      rw [delLvl_append, levels_pp hq₀, if_neg (by omega), Nat.sub_zero]
      rw [lvlStep_append, levels_pp hq₀, if_neg (by omega), Nat.sub_zero] at hi
      have hpre : PPath (v.ext q₀).path := by
        rw [VarSymb.ext_path]
        exact fun x hx => (List.mem_append.mp hx).elim (hk.1 x) (hq₀ x)
      rw [VarSymb.ext_append, VarSymb.ext_append]
      cases i with
      | zero =>
          rw [lvlStep_lvl_zero hs] at hi
          cases hi
          rw [delLvl_lvl_zero hs,
            show (v.ext q₀).ext (Step.keep :: r) = (VarSymb.step (v.ext q₀) .keep).ext r from rfl,
            gLab_keep _ hpre]
          change _ = gMem _ _ (pathOf (grefl hT _)) (pathOf_eq _) _
          rw [gMem_path (pathOf_refl hT _) _ rfl, gMem_kept_nil _ _ _ hpre]
      | succ i =>
          rw [lvlStep_lvl_succ hs] at hi
          rw [delLvl_lvl_succ hs]
          cases s with
          | fst => cases hs
          | snd => cases hs
          | here => cases hs
          | box => exact (kOk_no_box hT hk).elim
          | dia =>
              rw [show (v.ext q₀).ext (Step.dia :: delLvl i r) =
                  (VarSymb.step (v.ext q₀) .dia).ext (delLvl i r) from rfl,
                show (v.ext q₀).ext (Step.dia :: r) = (VarSymb.step (v.ext q₀) .dia).ext r from rfl,
                gLab_dia _ hpre, gLab_dia _ hpre]
              change _ = Arrows.Leaf.root _ (Step.collapseAt (i + 1) (Step.dia :: r))
              rw [collapseAt_eq_delLvl (i + 1) _ (by rw [lvlStep_lvl_succ (by decide)]; exact hi),
                delLvl_lvl_succ (by decide)]
          | keep =>
              rw [show (v.ext q₀).ext (Step.keep :: delLvl i r) =
                  (VarSymb.step (v.ext q₀) .keep).ext (delLvl i r) from rfl,
                show (v.ext q₀).ext (Step.keep :: r) =
                  (VarSymb.step (v.ext q₀) .keep).ext r from rfl,
                gLab_keep _ hpre, gLab_keep _ hpre]
              change _ = Arrows.Leaf.fam fun b => Arrows.Leaf.collapse hT i _
              congr 1
              funext b
              exact ih i (Nat.lt_succ_self i) _ _ (kOk_proj_keep hk hq₀) hi
  | cons c P ihP =>
      intro t t' h v q hk hi
      obtain ⟨hv, U, X₀, hd, hq⟩ := hk
      obtain ⟨w, n, X, X', R, tl, rfl, hlX, hsh, hw, htl, hform⟩ :=
        keptTr_form hT hM₀ t c (born_step h) hd hq
      obtain ⟨n', R', e₁, e₂, hi', hR⟩ := form_del hsh hi
      have htR : tl = false → R = [] := fun h => (htl h).2.2
      obtain ⟨-, he₀, U', Y', hd', hY'⟩ := hform n R htR X₀ hq
      have hq₁ : Step.walkTy U (.keep :: delLvl i (List.replicate n .keep ++ X ++ R)) =
          some (.VTypeDia X₀) := by
        obtain ⟨U₁, hU₁, -⟩ := Option.bind_eq_some_iff.mp hq
        have hUk : U.keepable = true := Step.typeStep_level_keepable rfl hU₁
        rw [walkTy_keep hUk] at hq ⊢
        exact walkTy_delLvl i _ U _ hi hq
      rw [e₁] at hq₁ ⊢
      obtain ⟨-, he₁, -⟩ := hform n' R' (fun h => hR (htR h)) X₀ hq₁
      rw [gMem_tr t t' c P h hv hw he₁ (levels_form hlX).symm,
        gMem_tr t t' c P h hv hw he₀ (levels_form hlX).symm, ← e₂]
      exact ihP h ⟨hw, U', Y', hd', hY'⟩ hi'

/-- ⭐**(B) for keeping at the end**: a member of a kept address with a `keep` appended is the
    member `dk`'d at its last level. -/
theorem gMem_app (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) (m : ℕ) :
    ∀ (P : List ℕ) {t t' : GW hF M₀} (h : t'.1 = nodeOf t.1 P) {v : VarSymb} {q : List Step},
      KOk t v q → Step.levels q = m →
      gMem t t' P h ((VarSymb.step v .keep).ext (q ++ [.keep])) =
        gdk m (gMem t t' P h ((VarSymb.step v .keep).ext q)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro P
  induction P with
  | nil =>
      intro t t' h v q hk hm
      obtain rfl : t' = t := gw_eq h
      rw [gMem_kept_nil _ _ _ hk.1, gMem_kept_nil _ _ _ hk.1]
      cases m with
      | zero =>
          have hq := ppath_of_levels0 hm
          have hpre : PPath (v.ext q).path := by
            rw [VarSymb.ext_path]
            exact fun x hx => (List.mem_append.mp hx).elim (hk.1 x) (hq x)
          rw [VarSymb.ext_append_single, show VarSymb.step (v.ext q) .keep =
            (VarSymb.step (v.ext q) .keep).ext [] from rfl, gLab_keep _ hpre, gLab_ppath _ hpre]
          change _ = Arrows.Leaf.fam fun b => @Arrows.Leaf.keepAlong _ _ (garrows hF M₀)
            (fun _ => VarSymb) gRK hF _ b _
          congr 1
          funext b
          rw [keepAlong_gRK, ← gLab_ppath _ hpre]
          exact (gKA_gLab hT hM₀ (kOk_end hk hq) (fun _ h => by cases h) b).symm
      | succ m =>
          obtain ⟨q₀, s, r, rfl, hq₀, hs⟩ := split_first q (by omega)
          have hpre : PPath (v.ext q₀).path := by
            rw [VarSymb.ext_path]
            exact fun x hx => (List.mem_append.mp hx).elim (hk.1 x) (hq₀ x)
          have hr : Step.levels r = m := by
            rw [Step.levels_append, levels_pp hq₀, Step.levels_cons, if_neg (by simp [hs])] at hm
            omega
          rw [List.append_assoc, List.cons_append, VarSymb.ext_append, VarSymb.ext_append]
          cases s with
          | fst => cases hs
          | snd => cases hs
          | here => cases hs
          | box => exact (kOk_no_box hT hk).elim
          | dia =>
              rw [show (v.ext q₀).ext (Step.dia :: (r ++ [.keep])) =
                  (VarSymb.step (v.ext q₀) .dia).ext (r ++ [.keep]) from rfl,
                show (v.ext q₀).ext (Step.dia :: r) = (VarSymb.step (v.ext q₀) .dia).ext r from rfl,
                gLab_dia _ hpre, gLab_dia _ hpre]
              change _ = Arrows.Leaf.root _ (Step.keepAt (m + 1) (Step.dia :: r))
              rw [Step.keepAt_own (Step.dia :: r) (m + 1)
                (by rw [Step.levels_cons, if_neg (by decide), hr]; omega)]
              rfl
          | keep =>
              rw [show (v.ext q₀).ext (Step.keep :: (r ++ [.keep])) =
                  (VarSymb.step (v.ext q₀) .keep).ext (r ++ [.keep]) from rfl,
                show (v.ext q₀).ext (Step.keep :: r) =
                  (VarSymb.step (v.ext q₀) .keep).ext r from rfl,
                gLab_keep _ hpre, gLab_keep _ hpre]
              change _ = Arrows.Leaf.fam fun b => gdk m _
              congr 1
              funext b
              exact ih m (Nat.lt_succ_self m) _ _ (kOk_proj_keep hk hq₀) hr
  | cons c P ihP =>
      intro t t' h v q hk hm
      obtain ⟨hv, U, X₀, hd, hq⟩ := hk
      obtain ⟨w, n, X, X', R, tl, rfl, hlX, hsh, hw, htl, hform⟩ :=
        keptTr_form hT hM₀ t c (born_step h) hd hq
      have htR : tl = false → R = [] := fun h => (htl h).2.2
      obtain ⟨-, he₀, U', Y', hd', hY'⟩ := hform n R htR X₀ hq
      have hq₁ : Step.walkTy U (.keep :: (List.replicate n .keep ++ X ++ R ++ [.keep])) =
          some (.VTypeDia X₀) := by
        rw [show Step.keep :: (List.replicate n .keep ++ X ++ R ++ [.keep]) =
          (.keep :: (List.replicate n .keep ++ X ++ R)) ++ [.keep] from rfl, Step.walkTy_append,
          hq]
        rfl
      -- the appended keep: in the rest, or (a witness) one more leading keep
      obtain ⟨n', R', e₁, e₂, hR'⟩ : ∃ n' R',
          List.replicate n .keep ++ X ++ R ++ [.keep] = List.replicate n' .keep ++ X ++ R' ∧
          List.replicate n .keep ++ X' ++ R ++ [.keep] = List.replicate n' .keep ++ X' ++ R' ∧
          (tl = false → R' = []) := by
        cases tl with
        | true => exact ⟨n, R ++ [.keep], by simp, by simp, fun h => by cases h⟩
        | false =>
            obtain ⟨rfl, rfl, rfl⟩ := htl rfl
            exact ⟨n + 1, [], by simp [List.replicate_succ'], by simp [List.replicate_succ'],
              fun _ => rfl⟩
      rw [e₁] at hq₁ ⊢
      obtain ⟨-, he₁, -⟩ := hform n' R' hR' X₀ hq₁
      rw [gMem_tr t t' c P h hv hw he₁ (levels_form hlX).symm,
        gMem_tr t t' c P h hv hw he₀ (levels_form hlX).symm, ← e₂]
      exact ihP h ⟨hw, U', Y', hd', hY'⟩ (by rw [← levels_form hlX]; exact hm)

/-! ## Naturality of the root action -/

omit [ModalSys] in
theorem lvl_split : ∀ (i : ℕ) (p : List Step) {s : Step}, lvlStep i p = some s →
    ∃ A B, p = A ++ s :: B ∧ Step.levels A = i
  | _, [], _, h => by cases h
  | i, t :: p, s, h => by
      by_cases ht : t.isProj = true
      · rw [lvlStep_proj ht] at h
        obtain ⟨A, B, rfl, hA⟩ := lvl_split i p h
        exact ⟨t :: A, B, rfl, by rw [Step.levels_cons, if_pos ht, hA, Nat.zero_add]⟩
      · have ht' : t.isProj = false := Bool.eq_false_iff.mpr ht
        cases i with
        | zero =>
            rw [lvlStep_lvl_zero ht'] at h
            cases h
            exact ⟨[], p, rfl, rfl⟩
        | succ i =>
            rw [lvlStep_lvl_succ ht'] at h
            obtain ⟨A, B, rfl, hA⟩ := lvl_split i p h
            exact ⟨t :: A, B, rfl, by rw [Step.levels_cons, if_neg ht, hA]; omega⟩

omit [ModalSys] in
theorem boxOK_lvl : ∀ (p : List Step) (lw : List Bool) (i : ℕ), Step.BoxOK lw p →
    lw[i]? = some true → lvlStep i p ≠ some .dia
  | [], _, _, _, _ => by simp [lvlStep]
  | s :: p, lw, i, h, hi => by
      by_cases hs : s.isProj = true
      · rw [lvlStep_proj hs]
        unfold Step.BoxOK at h
        rw [if_pos hs] at h
        exact boxOK_lvl p lw i h hi
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        unfold Step.BoxOK at h
        rw [if_neg hs] at h
        cases i with
        | zero =>
            rw [lvlStep_lvl_zero hs']
            intro e
            cases e
            exact h.1 (by cases lw <;> simp_all) rfl
        | succ i =>
            rw [lvlStep_lvl_succ hs']
            exact boxOK_lvl p lw.tail i h.2 (by cases lw <;> simp_all)

/-- Under T + 4 a typed path has no `box` step. -/
theorem walkTy_no_box (hko : ModalSys.keepOnly = true) : ∀ (p : List Step) (T U : VarType),
    Step.walkTy T p = some U → Step.box ∉ p
  | [], _, _, _ => List.not_mem_nil
  | s :: p, T, U, h => by
      obtain ⟨V, hV, hp⟩ := Option.bind_eq_some_iff.mp h
      intro hm
      rcases List.mem_cons.mp hm with rfl | hm
      · change (if ModalSys.keepOnly = true then none else T.step .box) = some V at hV
        rw [if_pos hko] at hV
        cases hV
      · exact walkTy_no_box hko p V U hp hm

theorem typedAt_app_iff {s : GW hF M₀} {r : VarSymb} {p : List Step} :
    TypedAt s r (p ++ [.keep]) ↔ TypedAt s r p := by
  constructor
  · rintro ⟨A, hd, X, hw⟩
    rw [Step.walkTy_append] at hw
    obtain ⟨V, hV, hk⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨W, hW, hk'⟩ := Option.bind_eq_some_iff.mp hk
    change some W = some _ at hk'
    cases hk'
    change (if V.keepable = true then some V else none) = some _ at hW
    split at hW
    · cases hW
      exact ⟨A, hd, X, hV⟩
    · cases hW
  · rintro ⟨A, hd, X, hw⟩
    refine ⟨A, hd, X, ?_⟩
    rw [Step.walkTy_append, hw]
    rfl

theorem typedAt_shift_iff {s : GW hF M₀} {r : VarSymb} {p : List Step} (i : ℕ) :
    TypedAt s r (Step.shiftAt i p) ↔ TypedAt s r p := by
  simp only [TypedAt, Step.Typed, Step.walkTy_shiftAt]

theorem typedAt_del_iff {s : GW hF M₀} {r : VarSymb} {p : List Step}
    {i : ℕ} (hty : Step.Typable p) (hi : lvlStep i p = some .keep) :
    TypedAt s r (delLvl i p) ↔ TypedAt s r p := by
  obtain ⟨A, B, rfl, hA⟩ := lvl_split i p hi
  have hdel : delLvl i (A ++ .keep :: B) = A ++ B := by
    rw [delLvl_append, if_neg (by omega), hA, Nat.sub_self, delLvl_lvl_zero rfl]
  rw [hdel]
  constructor
  · rintro ⟨A₀, hd, X, hw⟩
    refine ⟨A₀, hd, X, ?_⟩
    rw [Step.walkTy_append] at hw ⊢
    obtain ⟨V, hV, hB⟩ := Option.bind_eq_some_iff.mp hw
    rw [hV]
    by_cases hVk : V.keepable = true
    · exact (walkTy_keep hVk B).trans hB
    · exfalso
      cases B with
      | nil =>
          change some V = some _ at hB
          cases hB
          exact hVk rfl
      | cons b B' =>
          obtain ⟨W, hW, -⟩ := Option.bind_eq_some_iff.mp hB
          rcases typeStep_some hW with ⟨_, _, rfl, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ | ⟨_, rfl, -⟩ | ⟨_, rfl, -⟩
          · -- `keep` then `fst`: no type has both
            obtain ⟨T', X', hw'⟩ := hty
            rw [Step.walkTy_append] at hw'
            obtain ⟨V', -, hk⟩ := Option.bind_eq_some_iff.mp hw'
            obtain ⟨V'', hV'', hk'⟩ := Option.bind_eq_some_iff.mp hk
            obtain ⟨W', hW', -⟩ := Option.bind_eq_some_iff.mp hk'
            have hV'k : V'.keepable = true := Step.typeStep_level_keepable rfl hV''
            obtain rfl : V'' = V' := by
              change (if V'.keepable = true then some V' else none) = some V'' at hV''
              rw [if_pos hV'k] at hV''
              exact (Option.some.inj hV'').symm
            rcases typeStep_some hW' with ⟨_, _, rfl, -⟩ | ⟨_, rfl, h'⟩ | ⟨_, rfl, h'⟩
            · cases hV'k
            · rcases h' with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> cases e
            · rcases h' with ⟨e, -⟩ | ⟨e, -⟩ <;> cases e
          · obtain ⟨T', X', hw'⟩ := hty
            rw [Step.walkTy_append] at hw'
            obtain ⟨V', -, hk⟩ := Option.bind_eq_some_iff.mp hw'
            obtain ⟨V'', hV'', hk'⟩ := Option.bind_eq_some_iff.mp hk
            obtain ⟨W', hW', -⟩ := Option.bind_eq_some_iff.mp hk'
            have hV'k : V'.keepable = true := Step.typeStep_level_keepable rfl hV''
            obtain rfl : V'' = V' := by
              change (if V'.keepable = true then some V' else none) = some V'' at hV''
              rw [if_pos hV'k] at hV''
              exact (Option.some.inj hV'').symm
            rcases typeStep_some hW' with ⟨_, _, rfl, -⟩ | ⟨_, rfl, h'⟩ | ⟨_, rfl, h'⟩
            · cases hV'k
            · rcases h' with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> cases e
            · rcases h' with ⟨e, -⟩ | ⟨e, -⟩ <;> cases e
          · exact hVk rfl
          · exact hVk rfl
  · rintro ⟨A₀, hd, X, hw⟩
    refine ⟨A₀, hd, X, ?_⟩
    rw [← hdel]
    exact walkTy_delLvl i _ _ _ (by rw [lvlStep_append, if_neg (by omega), hA, Nat.sub_self,
      lvlStep_lvl_zero rfl]) hw

open Classical in
theorem gKeepP_cons (s t : GW hF M₀) (c : ℕ) (P : List ℕ) (h : t.1 = nodeOf s.1 (c :: P))
    (r : VarSymb) (p : List Step) :
    gKeepP s t (c :: P) h r p =
      if TypedAt s r p then gMem s t (c :: P) h ((VarSymb.step r .keep).ext p)
      else .root junkR p := rfl

/-- ⭐**Naturality: keeping at the end.** -/
theorem gKeep_keepAt (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀}
    (r : VarSymb) (a : (garrows hF M₀).Acc s) (c : Bool) (lw : List Bool) (p : List Step)
    (hwf : Arrows.Leaf.WF (c :: lw) (Arrows.Leaf.root (F := garrows hF M₀)
      (Root := fun _ => VarSymb) (w := s) r p)) :
    gKeep s r a (Step.keepAt (lw.length + 1) p) = gdk (lw.length + 1) (gKeep s r a p) := by
  obtain ⟨hl, -, -, -⟩ :=
    (Arrows.Leaf.wf_root (F := garrows hF M₀) (Root := fun _ => VarSymb) (w := s) r p).mp hwf
  have hk : Step.keepAt (lw.length + 1) p = p ++ [.keep] :=
    Step.keepAt_own p _ (by simpa using hl)
  change gKeepP s a.1 (pathOf a.2.down) (pathOf_eq a.2.down) r _ =
    gdk _ (gKeepP s a.1 (pathOf a.2.down) (pathOf_eq a.2.down) r p)
  generalize pathOf a.2.down = P, pathOf_eq a.2.down = hP
  cases P with
  | nil => rfl
  | cons c' P =>
      rw [hk, gKeepP_cons, gKeepP_cons]
      by_cases ht : TypedAt s r p
      · rw [if_pos (typedAt_app_iff.mpr ht), if_pos ht]
        exact gMem_app hT hM₀ _ _ _ (kOk_of_typedAt ht).1 (by simpa using hl)
      · rw [if_neg (mt typedAt_app_iff.mp ht), if_neg ht, ← hk]
        rfl

/-- ⭐**Naturality: shifting.** -/
theorem gKeep_shiftAt (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀}
    (r : VarSymb) (a : (garrows hF M₀).Acc s) (c : Bool) (lw q : List Bool) (p : List Step)
    (hwf : Arrows.Leaf.WF (c :: lw ++ false :: q) (Arrows.Leaf.root (F := garrows hF M₀)
      (Root := fun _ => VarSymb) (w := s) r p)) :
    gKeep s r a (Step.shiftAt (lw.length + 1) p) = gdkB (lw.length + 1) (gKeep s r a p) := by
  obtain ⟨hl, -, -, -⟩ :=
    (Arrows.Leaf.wf_root (F := garrows hF M₀) (Root := fun _ => VarSymb) (w := s) r p).mp hwf
  change gKeepP s a.1 (pathOf a.2.down) (pathOf_eq a.2.down) r _ =
    gdkB _ (gKeepP s a.1 (pathOf a.2.down) (pathOf_eq a.2.down) r p)
  generalize pathOf a.2.down = P, pathOf_eq a.2.down = hP
  cases P with
  | nil => rfl
  | cons c' P =>
      rw [gKeepP_cons, gKeepP_cons]
      by_cases ht : TypedAt s r p
      · rw [if_pos ((typedAt_shift_iff _).mpr ht), if_pos ht]
        exact gMem_shift hT hM₀ _ _ _ (kOk_of_typedAt ht).1 (by simp at hl; omega)
      · rw [if_neg (mt (typedAt_shift_iff _).mp ht), if_neg ht]
        rfl

/-- At a `□` level of a well-formed position, a root path's level step is a `keep` (T + 4). -/
theorem lvlStep_keep_of_wf (hko : ModalSys.keepOnly = true) {lw : List Bool} {p : List Step}
    (hl : Step.levels p = lw.length) (hb : Step.BoxOK lw p) (hty : Step.Typable p) {i : ℕ}
    (hi : lw[i]? = some true) : lvlStep i p = some .keep := by
  have hil : i < Step.levels p := by
    rw [hl]
    exact (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨A, s, B, rfl, hA, hs⟩ : ∃ A s B, p = A ++ s :: B ∧ Step.levels A = i ∧
      s.isProj = false := by
    clear hl hb hty hi
    induction p generalizing i with
    | nil => exact absurd hil (by simp [Step.levels])
    | cons t p ih =>
        by_cases ht : t.isProj = true
        · rw [Step.levels_cons, if_pos ht, Nat.zero_add] at hil
          obtain ⟨A, s, B, rfl, hA, hs⟩ := ih hil
          exact ⟨t :: A, s, B, rfl, by rw [Step.levels_cons, if_pos ht, hA, Nat.zero_add], hs⟩
        · rw [Step.levels_cons, if_neg ht] at hil
          cases i with
          | zero => exact ⟨[], t, p, rfl, rfl, Bool.eq_false_iff.mpr ht⟩
          | succ i =>
              obtain ⟨A, s, B, rfl, hA, hs⟩ := ih (i := i) (by omega)
              exact ⟨t :: A, s, B, rfl, by rw [Step.levels_cons, if_neg ht, hA]; omega, hs⟩
  have hlv : lvlStep i (A ++ s :: B) = some s := by
    rw [lvlStep_append, if_neg (by omega), hA, Nat.sub_self, lvlStep_lvl_zero hs]
  rw [hlv]
  have hd := boxOK_lvl _ lw i hb hi
  rw [hlv] at hd
  obtain ⟨T', X', hw⟩ := hty
  have hnb := walkTy_no_box hko _ T' _ hw
  cases s with
  | fst => cases hs
  | snd => cases hs
  | here => cases hs
  | box => exact absurd (List.mem_append_right A List.mem_cons_self) hnb
  | dia => exact absurd rfl hd
  | keep => rfl

/-- ⭐**Naturality: collapsing a `□` level.** -/
theorem gKeep_collapseAt (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀}
    (r : VarSymb) (a : (garrows hF M₀).Acc s) (c : Bool) (lw q : List Bool) (p : List Step)
    (hwf : Arrows.Leaf.WF (c :: lw ++ true :: q) (Arrows.Leaf.root (F := garrows hF M₀)
      (Root := fun _ => VarSymb) (w := s) r p)) :
    gKeep s r a (Step.collapseAt (lw.length + 1) p) =
      Arrows.Leaf.collapse hT (lw.length + 1) (gKeep s r a p) := by
  obtain ⟨hl, -, hb, hty⟩ :=
    (Arrows.Leaf.wf_root (F := garrows hF M₀) (Root := fun _ => VarSymb) (w := s) r p).mp hwf
  have hi : lvlStep (lw.length + 1) p = some .keep :=
    lvlStep_keep_of_wf (by simp [ModalSys.keepOnly, hT, hF]) hl hb hty (by simp)
  change gKeepP s a.1 (pathOf a.2.down) (pathOf_eq a.2.down) r _ =
    Arrows.Leaf.collapse hT _ (gKeepP s a.1 (pathOf a.2.down) (pathOf_eq a.2.down) r p)
  generalize pathOf a.2.down = P, pathOf_eq a.2.down = hP
  cases P with
  | nil => rfl
  | cons c' P =>
      rw [collapseAt_eq_delLvl _ _ hi, gKeepP_cons, gKeepP_cons]
      by_cases ht : TypedAt s r p
      · rw [if_pos ((typedAt_del_iff hty hi).mpr ht), if_pos ht]
        exact gMem_del hT hM₀ _ _ _ (kOk_of_typedAt ht).1 hi
      · rw [if_neg (mt (typedAt_del_iff hty hi).mp ht), if_neg ht]
        change _ = Arrows.Leaf.root _ (Step.collapseAt _ p)
        rw [collapseAt_eq_delLvl _ _ hi]

/-! ## Well-formedness of the root action -/

omit [ModalSys] in
theorem boxOK_of_lvl : ∀ (p : List Step) (lw : List Bool),
    (∀ i, lw[i]? = some true → lvlStep i p ≠ some .dia) → Step.BoxOK lw p
  | [], _, _ => trivial
  | s :: p, lw, h => by
      by_cases hs : s.isProj = true
      · unfold Step.BoxOK
        rw [if_pos hs]
        exact boxOK_of_lvl p lw fun i hi => by rw [← lvlStep_proj hs]; exact h i hi
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        unfold Step.BoxOK
        rw [if_neg hs]
        refine ⟨fun hh e => ?_, boxOK_of_lvl p lw.tail fun i hi => ?_⟩
        · subst e
          exact h 0 (by cases lw <;> simp_all) (lvlStep_lvl_zero hs' p)
        · rw [← lvlStep_lvl_succ hs']
          exact h (i + 1) (by cases lw <;> simp_all)

omit [ModalSys] in
/-- A translation creates no `dia` step. -/
theorem form_lvl_dia {n j : ℕ} {X X' R : List Step} (hsh : ShapeOK X X')
    (h : lvlStep j (List.replicate n .keep ++ X' ++ R) = some .dia) :
    lvlStep j (List.replicate n .keep ++ X ++ R) = some .dia := by
  simp only [List.append_assoc] at h ⊢
  rw [lvlStep_append, levels_rep] at h ⊢
  by_cases hj : j < n
  · rw [if_pos hj, lvlStep_rep j n hj] at h
    cases h
  · rw [if_neg hj] at h ⊢
    rw [lvlStep_append] at h ⊢
    rcases hsh with ⟨hX, hX'⟩ | ⟨Xp, s', X'p, rfl, hXp, rfl, hs', hX'p⟩
    · rw [levels_pp hX'] at h
      rw [levels_pp hX, if_neg (by omega)]
      rw [if_neg (by omega)] at h
      exact h
    · have hl : Step.levels (Step.dia :: Xp) = 1 := by
        rw [Step.levels_cons, if_neg (by decide), levels_pp hXp]
      have hl' : Step.levels (s' :: X'p) = 1 := by
        rw [Step.levels_cons, if_neg (by simp [hs']), levels_pp hX'p]
      rw [hl'] at h
      rw [hl]
      by_cases h0 : j - n < 1
      · rw [if_pos h0, show j - n = 0 by omega, lvlStep_lvl_zero (by decide)]
      · rw [if_neg h0] at h ⊢
        exact h

/-- ⭐**A member of a typed kept address is well-formed at its position**, when the address's
    path has the position's levels and does not enter a possibility at a `□` level. -/
theorem gMem_wf (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) (m : ℕ) :
    ∀ (P : List ℕ) {t t' : GW hF M₀} (h : t'.1 = nodeOf t.1 P) {v : VarSymb} {q : List Step}
      {lw : List Bool}, KOk t v q → Step.levels q = m → lw.length = m → Step.BoxOK lw q →
      Arrows.Leaf.WF lw (gMem t t' P h ((VarSymb.step v .keep).ext q)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro P
  induction P with
  | nil =>
      intro t t' h v q lw hk hm hlw hb
      obtain rfl : t' = t := gw_eq h
      rw [gMem_kept_nil _ _ _ hk.1]
      by_cases h0 : Step.levels q = 0
      · have hq := ppath_of_levels0 h0
        have hpre : PPath (v.ext q).path := by
          rw [VarSymb.ext_path]
          exact fun x hx => (List.mem_append.mp hx).elim (hk.1 x) (hq x)
        rw [gLab_ppath _ hpre]
        obtain rfl : lw = [] := List.eq_nil_of_length_eq_zero (by omega)
        exact (Arrows.Leaf.wf_root _ []).mpr ⟨rfl, by simp, trivial,
          ⟨.VTypeDia .VTypeOne, .VTypeOne, rfl⟩⟩
      · obtain ⟨q₀, s, r, rfl, hq₀, hs⟩ := split_first q (by omega)
        have hpre : PPath (v.ext q₀).path := by
          rw [VarSymb.ext_path]
          exact fun x hx => (List.mem_append.mp hx).elim (hk.1 x) (hq₀ x)
        have hlv : ∀ j, lvlStep j (q₀ ++ s :: r) = lvlStep j (s :: r) := fun j => by
          rw [lvlStep_append, levels_pp hq₀, if_neg (by omega), Nat.sub_zero]
        have hlr : Step.levels (q₀ ++ s :: r) = 1 + Step.levels r := by
          rw [Step.levels_append, levels_pp hq₀, Step.levels_cons, if_neg (by simp [hs])]
          omega
        rw [VarSymb.ext_append]
        cases s with
        | fst => cases hs
        | snd => cases hs
        | here => cases hs
        | box => exact (kOk_no_box hT hk).elim
        | dia =>
            rw [show (v.ext q₀).ext (Step.dia :: r) = (VarSymb.step (v.ext q₀) .dia).ext r
              from rfl, gLab_dia _ hpre]
            obtain ⟨-, U', X', -, hw⟩ := kOk_proj hk hq₀ rfl
            obtain ⟨U₁, hU₁, -⟩ := Option.bind_eq_some_iff.mp hw
            have hlev : Step.levels (Step.dia :: r) = lw.length := by
              rw [hlw, ← hm, hlr, Step.levels_cons, if_neg (by decide)]
            have hhead : lw.head? ≠ some true := fun hh => by
              have := boxOK_lvl _ lw 0 hb (by
                cases lw with
                | nil => cases hh
                | cons c l => simpa using hh)
              rw [hlv, lvlStep_lvl_zero (by decide)] at this
              exact this rfl
            have hbox : Step.BoxOK lw (Step.dia :: r) := boxOK_of_lvl _ lw fun j hj => by
              rw [← hlv]
              exact boxOK_lvl _ lw j hb hj
            exact (Arrows.Leaf.wf_root _ _).mpr ⟨hlev, hhead, hbox,
              ⟨U', X', (walkTy_keep (Step.typeStep_level_keepable rfl hU₁) _).symm.trans hw⟩⟩
        | keep =>
            rw [show (v.ext q₀).ext (Step.keep :: r) = (VarSymb.step (v.ext q₀) .keep).ext r
              from rfl, gLab_keep _ hpre]
            cases lw with
            | nil => simp at hlw; omega
            | cons c lw' =>
                intro b
                refine ih (Step.levels r) (by omega) _ _ (kOk_proj_keep hk hq₀) rfl
                  (by simp at hlw; omega) (boxOK_of_lvl _ lw' fun j hj => ?_)
                rw [← lvlStep_lvl_succ (s := .keep) rfl, ← hlv]
                exact boxOK_lvl _ (c :: lw') (j + 1) hb (by simpa using hj)
  | cons c P ihP =>
      intro t t' h v q lw hk hm hlw hb
      obtain ⟨hv, U, X₀, hd, hq⟩ := hk
      obtain ⟨w, n, X, X', R, tl, rfl, hlX, hsh, hw, htl, hform⟩ :=
        keptTr_form hT hM₀ t c (born_step h) hd hq
      have htR : tl = false → R = [] := fun h => (htl h).2.2
      obtain ⟨-, he₀, U', Y', hd', hY'⟩ := hform n R htR X₀ hq
      rw [gMem_tr t t' c P h hv hw he₀ (levels_form hlX).symm]
      exact ihP h ⟨hw, U', Y', hd', hY'⟩ (by rw [← levels_form hlX]; exact hm) hlw
        (boxOK_of_lvl _ lw fun j hj e => boxOK_lvl _ lw j hb hj (form_lvl_dia hsh e))

/-- ⭐**The canonical action keeps leaves well-formed.** -/
theorem gKeep_wf (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀}
    (r : VarSymb) (a : (garrows hF M₀).Acc s) (lw : List Bool) (p : List Step)
    (hwf : Arrows.Leaf.WF lw (Arrows.Leaf.root (F := garrows hF M₀)
      (Root := fun _ => VarSymb) (w := s) r p)) :
    Arrows.Leaf.WF lw (gKeep s r a p) := by
  have h₀ :=
    (Arrows.Leaf.wf_root (F := garrows hF M₀) (Root := fun _ => VarSymb) (w := s) r p).mp hwf
  change Arrows.Leaf.WF lw (gKeepP s a.1 (pathOf a.2.down) (pathOf_eq a.2.down) r p)
  generalize pathOf a.2.down = P, pathOf_eq a.2.down = hP
  cases P with
  | nil => exact (Arrows.Leaf.wf_root _ _).mpr h₀
  | cons c P =>
      rw [gKeepP_cons]
      by_cases ht : TypedAt s r p
      · rw [if_pos ht]
        exact gMem_wf hT hM₀ _ _ _ (kOk_of_typedAt ht).1 rfl h₀.1.symm h₀.2.2.1
      · rw [if_neg ht]
        exact (Arrows.Leaf.wf_root _ _).mpr h₀

/-! ## The growing tree's root action -/

open Classical in
/-- ⭐**The growing tree's root action**: the canonical leaf-valued action (`gKeep`) under T over
    a maximal theory; otherwise, where nothing is shaped, a root path stays. -/
noncomputable instance instRootKeepG : Arrows.RootKeep (garrows hF M₀) (fun _ => VarSymb) :=
  if ModalSys.T = true ∧ Theory.IsMCS M₀ then gRK
  else Arrows.RootKeep.ofRoot fun _ {_} r _ => r

theorem instRootKeepG_eq (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) :
    (instRootKeepG : Arrows.RootKeep (garrows hF M₀) (fun _ => VarSymb)) = gRK :=
  if_pos ⟨hT, hM₀⟩

/-- Under T, leaves are kept by the canonical action. -/
theorem keepAlong_eq (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀}
    (a : (garrows hF M₀).Acc s) (ℓ : GLeaf hF M₀ s) :
    Arrows.Leaf.keepAlong hF a ℓ = gKA a ℓ := by
  rw [← keepAlong_gRK]
  congr 1
  exact instRootKeepG_eq hT hM₀

/-- ⭐**Its laws**: under T those of the canonical action, else path arithmetic. -/
instance instRootKeepLawsG : Arrows.RootKeepLaws (garrows hF M₀) (fun _ => VarSymb) := by
  by_cases h : ModalSys.T = true ∧ Theory.IsMCS M₀
  · obtain ⟨hT, hM₀⟩ := h
    rw [instRootKeepG_eq hT hM₀]
    exact @Arrows.RootKeepLaws.mk _ _ (garrows hF M₀) (fun _ => VarSymb) gRK
      (fun _ {_} r a b p => (keepAlong_gRK b _).trans (gKeep_trans hT hM₀ r a b p))
      (fun hT' _ {_} r p => gKeep_refl hT' r p)
      (fun _ {_} r a lw p h => gKeep_wf hT hM₀ r a lw p h)
      (fun _ {_} r a c lw p h => gKeep_keepAt hT hM₀ r a c lw p h)
      (fun _ {_} r a c lw q p h => gKeep_shiftAt hT hM₀ r a c lw q p h)
      (fun hT' _ {_} r a c lw q p h => gKeep_collapseAt hT' hM₀ r a c lw q p h)
  · have e : (instRootKeepG : Arrows.RootKeep (garrows hF M₀) (fun _ => VarSymb)) =
        Arrows.RootKeep.ofRoot fun _ {_} r _ => r := if_neg h
    rw [e]
    exact Arrows.RootKeepLaws.ofRoot (F := garrows hF M₀) (Root := fun _ => VarSymb) _
      (fun _ {_} _ _ _ => rfl) (fun _ _ {_} _ => rfl)

end GArrow

end V12M
