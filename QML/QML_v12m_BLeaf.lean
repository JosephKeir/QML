import QML.QML_v12m_BCanonTerm
import QML.QML_v12m_CanonLeaf

/-!
# QML v12m — B's canonical model: the leaf calculus

The tree's leaf calculus (`QML_v12m_CanonLeaf`, docs §10.39) on the network.  A label at depth `j`
(views entered from the anchor) is read as a leaf: cut where it leaves the anchor's level, a `dia`
keeps the rest as a path, a `□` step is a family over the arrows, each entry the leaf of the label
read there (`succAddrK`).  Only the arrows differ from the tree's: along a network arrow a label is
read through the arrow's index map (`arrowIdx`), along the world's own arrow it is collapsed.

The network's languages declare only roots, so a label at depth `j` has **exactly** `j` levels
(`Ctx.Exact`): its cut is its first level step, a `box`, which is where `arrowIdx` cuts too.

* ⭐`canonSh_eq`: a canonical shape is its η-annotation read canonically.
* ⭐`leafOf_collapse` / `annShp_eta_collapse`: collapsing a leaf collapses its label.
* ⭐⭐`termShp_canonical`: in a canonical environment a term's shape is its annotation read
  canonically.
* ⭐⭐`ann_eq_of_rden`: under T, tags determine annotations.  The tree reads a family back along
  one proper successor; here no one arrow does — the own arrow turns the cut `box` into a `here`,
  a network arrow encodes the projections before it — but the two together do
  (`eq_of_here_enc`).
-/

namespace V12M

variable [ModalSys]

/-! ## Levels of addresses -/

omit [ModalSys] in
theorem VarSymb.lv_ext (v : VarSymb) (p : List Step) : (v.ext p).lv = v.lv + Step.levels p := by
  simp only [VarSymb.lv, VarSymb.ext_path, Step.levels_append]

omit [ModalSys] in
theorem levels_eq_zero_iff : ∀ {p : List Step}, Step.levels p = 0 ↔ PPath p
  | [] => by simp [Step.levels, PPath]
  | s :: p => by
      rw [Step.levels_cons]
      constructor
      · intro h t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · by_contra hs
          rw [if_neg hs] at h
          omega
        · exact levels_eq_zero_iff.mp (by split_ifs at h <;> omega) t ht
      · intro h
        rw [if_pos (h s List.mem_cons_self),
          levels_eq_zero_iff.mpr fun t ht => h t (List.mem_cons_of_mem _ ht)]

/-! ## Exact levels -/

/-- Every reachable address has exactly `j` levels: `j` views entered, from a context declaring only
    level-free addresses (the network's languages declare only roots). -/
def Ctx.Exact (Δ : Ctx) (j : ℕ) : Prop := ∀ y T, Δ.ref y = some T → y.lv = j

theorem Ctx.Exact.of_decl {Δ : Ctx} {j : ℕ} (h : ∀ y T, Δ y = some T → y.lv = j) :
    Δ.Exact j := by
  intro y
  induction y with
  | root r => intro T hy; exact h _ T hy
  | step v s ih =>
      intro T hy
      by_cases hs : s.isProj = true
      · change (if s.isProj then (Δ.ref v).bind (·.step s) else Δ (.step v s)) = some T at hy
        rw [if_pos hs] at hy
        cases hU : Δ.ref v with
        | none => rw [hU] at hy; cases hy
        | some U =>
            rw [Canon.lv_step, if_pos hs]
            exact ih U hU
      · change (if s.isProj then (Δ.ref v).bind (·.step s) else Δ (.step v s)) = some T at hy
        rw [if_neg hs] at hy
        exact h _ T hy

theorem Ctx.Exact.boxIn {Δ : Ctx} {j : ℕ} (h : Δ.Exact j) : Δ.boxIn.Exact (j + 1) := by
  refine Ctx.Exact.of_decl fun v T hv => ?_
  match v, hv with
  | .step u .box, hv =>
      rw [Canon.lv_step, if_neg (by decide), h u _ (Ctx.boxIn_box hv).2]
  | .step u .keep, hv =>
      rw [Canon.lv_step, if_neg (by decide), h u _ (Ctx.boxIn_keep hv).2.1]
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .dia, hv => cases hv
  | .step _ .here, hv => cases hv

theorem Ctx.Exact.diaIn {Δ : Ctx} {j : ℕ} (h : Δ.Exact j) (x : VarSymb) :
    (Δ.diaIn x).Exact (j + 1) := by
  refine Ctx.Exact.of_decl fun v T hv => ?_
  match v, hv with
  | .step u .dia, hv =>
      change (if u = x then (match Δ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with hux
      subst hux
      cases hx : Δ.ref u with
      | none => rw [hx] at hv; cases hv
      | some X =>
          rw [Canon.lv_step, if_neg (by decide), h u _ hx]
  | .step u .box, hv => exact h.boxIn _ _ ((Ctx.ref_nonproj _ rfl).trans hv)
  | .step u .keep, hv => exact h.boxIn _ _ ((Ctx.ref_nonproj _ rfl).trans hv)
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .here, hv => cases hv

/-- Every label of an annotation at depth `j` is allowed and has exactly `j` levels. -/
def Ann.Exact : ℕ → {A : VarType} → Ann A → Prop
  | _, _, .var => True
  | _, _, .one => True
  | j, _, .prod a b => Ann.Exact j a ∧ Ann.Exact j b
  | j, _, .box a => Ann.Exact (j + 1) a
  | j, _, .dia x a => x.OK ∧ x.lv = j ∧ Ann.Exact (j + 1) a

/-- A term's labels are its context's addresses, so they have its exact levels. -/
theorem Term.ann_exact (hT : ModalSys.T = true) {σ : Signature} :
    ∀ {Δ : Ctx}, Δ.DeclOK → ∀ {j : ℕ}, Δ.Exact j → ∀ {A : VarType} {a : Ann A},
      Term σ Δ A a → a.Exact j
  | _, _, _, _, _, _, .var _ _ => trivial
  | _, _, _, _, _, _, .func _ => trivial
  | _, _, _, _, _, _, .unit => trivial
  | _, hok, _, hex, _, _, .pair s t => ⟨Term.ann_exact hT hok hex s, Term.ann_exact hT hok hex t⟩
  | _, hok, _, hex, _, _, .boxtm t => Term.ann_exact hT (hok.boxIn hT) hex.boxIn t
  | _, hok, _, hex, _, _, .diatm x hx t => by
      obtain ⟨X, h⟩ := hx
      exact ⟨hok.ref x h, hex x _ h, Term.ann_exact hT (hok.diaIn hT x) (hex.diaIn x) t⟩

namespace BArrow

/-- The network's languages declare only roots. -/
theorem exact_ctxOf (l : List VarType) : (ctxOf l).Exact 0 :=
  Ctx.Exact.of_decl fun _ _ hy => by
    obtain ⟨r, rfl⟩ := ctxOf_decl hy
    rfl

/-! ## Addresses past their first `□` -/

omit [ModalSys] in
/-- Collapsing inside a path does not look at what comes before it. -/
theorem collapse_ext_indep : ∀ (q : List Step) (l : ℕ), l < Step.levels q →
    ∃ q', ∀ a : VarSymb, (a.ext q).collapse l = a.ext q' := by
  intro q
  induction q using List.reverseRecOn with
  | nil => intro l h; simp [Step.levels] at h
  | append_singleton r s ih =>
      intro l h
      rw [Step.levels_append, Step.levels_single] at h
      by_cases hs : s.isProj = true
      · rw [if_pos hs, Nat.add_zero] at h
        obtain ⟨q', e⟩ := ih l h
        refine ⟨q' ++ [s], fun a => ?_⟩
        rw [VarSymb.ext_append_ext, VarSymb.ext_append_ext]
        change (VarSymb.step (a.ext r) s).collapse l = VarSymb.step (a.ext q') s
        rw [VarSymb.collapse_proj hs, e]
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        rw [if_neg hs] at h
        cases l with
        | zero =>
            by_cases hk : s = .keep
            · subst hk
              exact ⟨r, fun a => by rw [VarSymb.ext_append_ext]; exact VarSymb.collapse_keep_zero⟩
            · refine ⟨r ++ [.here], fun a => ?_⟩
              rw [VarSymb.ext_append_ext, VarSymb.ext_append_ext]
              exact VarSymb.collapse_level_zero hs' hk
        | succ l =>
            obtain ⟨q', e⟩ := ih l (by omega)
            refine ⟨q' ++ [s], fun a => ?_⟩
            rw [VarSymb.ext_append_ext, VarSymb.ext_append_ext]
            change (VarSymb.step (a.ext r) s).collapse (l + 1) = VarSymb.step (a.ext q') s
            rw [VarSymb.collapse_level_succ hs', e]

omit [ModalSys] in
/-- Cutting inside a path does not look at what comes before it. -/
theorem splitAt_ext_indep : ∀ (q : List Step) (k : ℕ), k < Step.levels q →
    ∃ q₁ t q₂, ∀ a : VarSymb, VarSymb.splitAt (a.ext q) k = some (a.ext q₁, t, q₂) := by
  intro q
  induction q using List.reverseRecOn with
  | nil => intro k h; simp [Step.levels] at h
  | append_singleton r s ih =>
      intro k h
      rw [Step.levels_append, Step.levels_single] at h
      by_cases hs : s.isProj = true
      · rw [if_pos hs, Nat.add_zero] at h
        obtain ⟨q₁, t, q₂, h'⟩ := ih k h
        refine ⟨q₁, t, q₂ ++ [s], fun a => ?_⟩
        rw [VarSymb.ext_append_ext]
        change VarSymb.splitAt (.step (a.ext r) s) k = _
        simp only [VarSymb.splitAt, if_pos hs, h' a, Option.map_some]
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        rw [if_neg hs] at h
        cases k with
        | zero =>
            refine ⟨r, s, [], fun a => ?_⟩
            rw [VarSymb.ext_append_ext]
            change VarSymb.splitAt (.step (a.ext r) s) 0 = _
            simp [VarSymb.splitAt, hs']
        | succ k =>
            obtain ⟨q₁, t, q₂, h'⟩ := ih k (by omega)
            refine ⟨q₁, t, q₂ ++ [s], fun a => ?_⟩
            rw [VarSymb.ext_append_ext]
            change VarSymb.splitAt (.step (a.ext r) s) (k + 1) = _
            simp only [VarSymb.splitAt, hs', Bool.false_eq_true, if_false, h' a, Option.map_some]

/-- ⭐Past an item's `□` step an arrow's index map keeps the path: `u.box` followed by `p` lands at
    the item's image followed by `p`. -/
theorem arrowIdx_boxExt (img : ℕ → ℕ) {u : VarSymb} (hu : PPath u.path) (p : List Step) :
    arrowIdx img ((VarSymb.step u .box).ext p) = (itemImg img u).ext p := by
  rw [arrowIdx, itemPath_item hu, VarSymb.ext_append, VarSymb.ext_rt]
  rfl

theorem lv_itemAt {u : VarSymb} (hu : PPath u.path) (z : Root) : (itemAt z u).lv = 0 :=
  levels_eq_zero_iff.mpr (itemAt_ppath hu z)

theorem ok_itemAt {u : VarSymb} (hu : PPath u.path) (z : Root) : (itemAt z u).OK :=
  fun _ hs => Step.ok_of_proj (itemAt_ppath hu z _ hs)

/-- Under T, the own arrow turns the cut `box` into a `here` and a network arrow encodes the
    projections before it: together they determine both. -/
theorem eq_of_here_enc (hT : ModalSys.T = true) : ∀ {p p' r r' : List Step},
    p ++ .here :: r = p' ++ .here :: r' → encPath p ++ .fst :: r = encPath p' ++ .fst :: r' →
    p = p' ∧ r = r'
  | [], [], _, _, h, _ => ⟨rfl, by simpa using h⟩
  | [], _ :: _, _, _, h, h' => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp [encPath, encStep_here hT] at h'
  | _ :: _, [], _, _, h, h' => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp [encPath, encStep_here hT] at h'
  | _ :: _, _ :: _, _, _, h, h' => by
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have h'' := (List.cons.inj (show encStep _ :: (encPath _ ++ _) = encStep _ :: (encPath _ ++ _)
        from h')).2
      obtain ⟨rfl, rfl⟩ := eq_of_here_enc hT h h''
      exact ⟨rfl, rfl⟩

omit [ModalSys] in
/-- A label past a `box` cut, under its first level step. -/
abbrev BoxCut (y : VarSymb) (k : ℕ) : Prop :=
  ∃ u b, VarSymb.splitAt y k = some (u, .box, b) ∧ PPath u.path

theorem arrowIdx_step_of_cut {img : ℕ → ℕ} {y : VarSymb} {k : ℕ} (h : BoxCut y k) (st : Step) :
    arrowIdx img (.step y st) = .step (arrowIdx img y) st := by
  obtain ⟨u, b, h, hu⟩ := h
  obtain ⟨rfl, -, -⟩ := VarSymb.splitAt_spec h
  change arrowIdx img (((VarSymb.step u .box).ext b).ext [st]) =
    (arrowIdx img ((VarSymb.step u .box).ext b)).ext [st]
  rw [← VarSymb.ext_append, arrowIdx_boxExt img hu, arrowIdx_boxExt img hu, VarSymb.ext_append]

omit [ModalSys] in
theorem BoxCut.extend {y : VarSymb} {k : ℕ} (h : BoxCut y k) (p : List Step) :
    BoxCut (y.ext p) (k + Step.levels p) := by
  obtain ⟨u, b, h, hu⟩ := h
  exact ⟨u, b ++ p, VarSymb.splitAt_extend h p, hu⟩

variable {σ : Signature}

namespace BData

variable [ModalSys.NoFourNoTS] (B : BData σ)

/-! ## Reading a label along an arrow, at any level -/

open Classical in
/-- ⭐Where a label is read along an arrow, the level crossed having `k` level steps after it:
    through the arrow's index map along a network arrow (which cuts at the first `box`), collapsed
    at that level along the world's own.  `succAddr` is the case `k = 0`. -/
noncomputable def succAddrK (s : B.W) (a : B.Acc s) (k : ℕ) (v : VarSymb) : VarSymb :=
  if B.R s a.1 then arrowIdx (B.img s a.1) v else v.collapse k

variable {B}

theorem succAddrK_net {s : B.W} {a : B.Acc s} (h : B.R s a.1) (k : ℕ) (v : VarSymb) :
    B.succAddrK s a k v = arrowIdx (B.img s a.1) v := if_pos h

theorem succAddrK_self {s : B.W} {a : B.Acc s} (h : ¬ B.R s a.1) (k : ℕ) (v : VarSymb) :
    B.succAddrK s a k v = v.collapse k := if_neg h

theorem succAddrK_zero_eq (s : B.W) (a : B.Acc s) : B.succAddrK s a 0 = B.succAddr s a := by
  funext v
  by_cases h : B.R s a.1
  · rw [succAddrK_net h, succAddr_net h]
  · rw [succAddrK_self h, succAddr_self h]

theorem succAddrK_proj {s : B.W} (a : B.Acc s) {k : ℕ} {y : VarSymb} (h : BoxCut y k) {st : Step}
    (hs : st.isProj = true) : B.succAddrK s a k (.step y st) = .step (B.succAddrK s a k y) st := by
  by_cases hR : B.R s a.1
  · rw [succAddrK_net hR, succAddrK_net hR, arrowIdx_step_of_cut h]
  · rw [succAddrK_self hR, succAddrK_self hR, VarSymb.collapse_proj hs]

theorem succAddrK_level {s : B.W} (a : B.Acc s) {k : ℕ} {y : VarSymb} (h : BoxCut y k) {st : Step}
    (hs : st.isProj = false) :
    B.succAddrK s a (k + 1) (.step y st) = .step (B.succAddrK s a k y) st := by
  by_cases hR : B.R s a.1
  · rw [succAddrK_net hR, succAddrK_net hR, arrowIdx_step_of_cut h]
  · rw [succAddrK_self hR, succAddrK_self hR, VarSymb.collapse_level_succ hs]

theorem inner_eq (v : VarSymb) : v.inner = .step v .box :=
  VarSymb.inner_box ModalSys.NoFour.keepOnly

theorem succAddrK_inner {s : B.W} (a : B.Acc s) {k : ℕ} {y : VarSymb} (h : BoxCut y k) :
    B.succAddrK s a (k + 1) y.inner = (B.succAddrK s a k y).inner := by
  rw [inner_eq, inner_eq, succAddrK_level a h rfl]

/-! ## The canonical leaf of a label -/

variable (B)

/-- Canonical leaves on the network. -/
abbrev CLeaf (s : B.W) : Type := Arrows.Leaf B.arrows (fun _ => VarSymb) s

/-- ⭐**The canonical leaf of a label**, as in the tree (`Canon.leafOf`): cut where it leaves the
    anchor's level, a `dia` there keeps the rest as a path, a `□` step is a family over the arrows,
    each entry the leaf of the label read there. -/
noncomputable def leafOf : (s : B.W) → ℕ → VarSymb → B.CLeaf s
  | _, 0, y => .root y []
  | s, m + 1, y =>
      match VarSymb.splitAt y m with
      | some (pre, .dia, rest) => .root pre (.dia :: rest)
      | _ => .fam fun a => leafOf a.1 m (B.succAddrK s a m y)

variable {B}

theorem leafOf_zero (s : B.W) (y : VarSymb) : B.leafOf s 0 y = .root y [] := by
  simp only [leafOf]

theorem leafOf_dia (s : B.W) {m : ℕ} {y pre : VarSymb} {rest : List Step}
    (h : VarSymb.splitAt y m = some (pre, .dia, rest)) :
    B.leafOf s (m + 1) y = .root pre (.dia :: rest) := by
  simp only [leafOf, h]

theorem leafOf_lvl (s : B.W) {m : ℕ} {y pre : VarSymb} {t : Step} {rest : List Step}
    (h : VarSymb.splitAt y m = some (pre, t, rest)) (ht : t ≠ .dia) :
    B.leafOf s (m + 1) y = .fam fun a => B.leafOf a.1 m (B.succAddrK s a m y) := by
  cases t <;> first | exact absurd rfl ht | simp only [leafOf, h]

variable (B)

/-- ⭐An annotation with its labels read canonically: a label at depth `j` is `leafOf s j`. -/
noncomputable def annShp (s : B.W) : ℕ → {A : VarType} → Ann A → B.CShape s A
  | _, _, .var => .var
  | _, _, .one => .one
  | j, _, .prod a b => .prod (annShp s j a) (annShp s j b)
  | j, _, .box a => .box (annShp s (j + 1) a)
  | j, _, .dia x a => .dia (B.leafOf s j x) (annShp s (j + 1) a)

variable {B}

/-- ⭐**Transposition**: an η-annotation whose outermost view is a `□` step at its first level reads,
    canonically, as the family of its readings along the arrows. -/
theorem annShp_eta_transpose : ∀ (A : VarType) (s : B.W) (k : ℕ) (y : VarSymb), BoxCut y k →
    B.annShp s (k + 1) (Ann.eta y A) =
      Arrows.transposeShp (F := B.arrows) (Root := fun _ => VarSymb)
        fun a => B.annShp a.1 k (Ann.eta (B.succAddrK s a k y) A)
  | .Var, _, _, _, _ => rfl
  | .VTypeOne, _, _, _, _ => rfl
  | .VTypeProd A C, s, k, y, h => by
      have hf := h.extend [.fst]
      have hs := h.extend [.snd]
      simp only [Step.levels, Step.isProj, if_true, Nat.add_zero] at hf hs
      change Shp.prod (B.annShp s (k + 1) (Ann.eta (.step y .fst) A))
          (B.annShp s (k + 1) (Ann.eta (.step y .snd) C)) = _
      rw [annShp_eta_transpose A s k (.step y .fst) hf,
        annShp_eta_transpose C s k (.step y .snd) hs]
      simp only [succAddrK_proj _ h (rfl : Step.isProj .fst = true),
        succAddrK_proj _ h (rfl : Step.isProj .snd = true)]
      rfl
  | .VTypeBox A, s, k, y, h => by
      have hi := h.extend [.box]
      simp only [Step.levels, Step.isProj, Bool.false_eq_true, if_false, Nat.add_zero] at hi
      rw [show y.ext [.box] = y.inner from (inner_eq y).symm] at hi
      change Shp.box (B.annShp s (k + 1 + 1) (Ann.eta y.inner A)) = _
      rw [annShp_eta_transpose A s (k + 1) y.inner hi]
      simp only [succAddrK_inner _ h]
      rfl
  | .VTypeDia A, s, k, y, h => by
      have hd := h.extend [.dia]
      simp only [Step.levels, Step.isProj, Bool.false_eq_true, if_false, Nat.add_zero] at hd
      obtain ⟨u, b, hc, hu⟩ := h
      change Shp.dia (B.leafOf s (k + 1) y) (B.annShp s (k + 1 + 1) (Ann.eta (.step y .dia) A)) = _
      rw [leafOf_lvl s hc nofun, annShp_eta_transpose A s (k + 1) (.step y .dia) hd]
      simp only [succAddrK_level _ ⟨u, b, hc, hu⟩ (rfl : Step.isProj .dia = false)]
      rfl

/-- A content's canonical shape is its η-annotation read canonically, from the root and path. -/
theorem rootSh_eq : ∀ (A : VarType) (s : B.W) (v : VarSymb) (π : List Step),
    B.rootSh s v (.dia :: π) A = B.annShp s (Step.levels π + 1) (Ann.eta (v.ext (.dia :: π)) A)
  | .Var, _, _, _ => rfl
  | .VTypeOne, _, _, _ => rfl
  | .VTypeProd A C, s, v, π => by
      change Shp.prod (B.rootSh s v (.dia :: (π ++ [.fst])) A)
          (B.rootSh s v (.dia :: (π ++ [.snd])) C) = _
      rw [rootSh_eq A s v (π ++ [Step.fst]), rootSh_eq C s v (π ++ [Step.snd])]
      simp only [Step.levels_append, Step.levels, Step.isProj, if_true, Nat.add_zero]
      rw [← List.cons_append, VarSymb.ext_append_ext, ← List.cons_append,
        VarSymb.ext_append_ext]
      rfl
  | .VTypeBox A, s, v, π => by
      change Shp.box (B.rootSh s v (.dia :: (π ++ Step.innerPath)) A) = _
      rw [rootSh_eq A s v (π ++ Step.innerPath), Step.levels_append, Canon.levels_innerPath,
        ← List.cons_append, ← VarSymb.inner_ext]
      rfl
  | .VTypeDia A, s, v, π => by
      have hs := VarSymb.splitAt_ext v (rfl : Step.isProj .dia = false) π
      change Shp.dia (.root v (.dia :: π)) (B.rootSh s v (.dia :: (π ++ [.dia])) A) = _
      rw [rootSh_eq A s v (π ++ [Step.dia])]
      change _ = Shp.dia (B.leafOf s (Step.levels π + 1) (v.ext (.dia :: π))) _
      rw [leafOf_dia s hs, Step.levels_append]
      simp only [Step.levels, Step.isProj, Bool.false_eq_true, if_false, Nat.add_zero]
      rw [← List.cons_append, VarSymb.ext_append_ext]
      rfl

/-- Reading a level-free address along an arrow keeps it level-free. -/
theorem ppath_succAddr {s : B.W} (a : B.Acc s) {v : VarSymb} (hv : PPath v.path) :
    PPath (B.succAddr s a v.inner).path := by
  rw [inner_eq]
  by_cases hR : B.R s a.1
  · rw [succAddr_net hR, arrowIdx_item hv]
    exact itemAt_ppath hv _
  · rw [succAddr_self hR, VarSymb.collapse_level_zero (s := .box) rfl (by decide)]
    exact hv.append fun t ht => by rw [List.mem_singleton.mp ht]; rfl

/-- ⭐**The canonical shape of a level-free address is its η-annotation read canonically.** -/
theorem canonSh_eq : ∀ (A : VarType) (s : B.W) (v : VarSymb), PPath v.path →
    B.canonSh s v A = B.annShp s 0 (Ann.eta v A)
  | .Var, _, _, _ => rfl
  | .VTypeOne, _, _, _ => rfl
  | .VTypeProd A C, s, v, hv => by
      change Shp.prod (B.canonSh s (.step v .fst) A) (B.canonSh s (.step v .snd) C) = _
      rw [canonSh_eq A s _ (hv.append fun t ht => by rw [List.mem_singleton.mp ht]; rfl),
        canonSh_eq C s _ (hv.append fun t ht => by rw [List.mem_singleton.mp ht]; rfl)]
      rfl
  | .VTypeBox A, s, v, hv => by
      have hi : BoxCut v.inner 0 := ⟨v, [], by rw [inner_eq]; rfl, hv⟩
      change Shp.box (Arrows.transposeShp (F := B.arrows) (Root := fun _ => VarSymb)
          fun a => B.canonSh a.1 (B.succAddr s a v.inner) A) = Shp.box (B.annShp s (0 + 1) _)
      rw [annShp_eta_transpose A s 0 v.inner hi]
      simp only [succAddrK_zero_eq, fun a => canonSh_eq A a.1 _ (ppath_succAddr a hv)]
  | .VTypeDia A, s, v, _ => by
      change Shp.dia (.root v []) (B.rootSh s v [.dia] A) = _
      rw [rootSh_eq A s v []]
      rfl


/-! ## Cuts at the first level step -/

/-- A label with exactly `m + 1` levels, cut at its first level step that is not a `dia`: a `box`
    (4 is off) after projections. -/
theorem cut_first {x pre : VarSymb} {m : ℕ} {t : Step} {rest : List Step} (hok : x.OK)
    (hlv : x.lv = m + 1) (h : VarSymb.splitAt x m = some (pre, t, rest)) (ht : t ≠ .dia) :
    t = .box ∧ PPath pre.path ∧ x = (VarSymb.step pre .box).ext rest ∧ Step.levels rest = m := by
  obtain ⟨rfl, htp, hl⟩ := VarSymb.splitAt_spec h
  have htok : t.OK := (VarSymb.ok_ext.mp hok).2 t List.mem_cons_self
  have htb : t = .box := by
    cases t
    all_goals first
      | rfl
      | exact absurd htp (by decide)
      | exact absurd rfl ht
      | exact (noFour (htok.2 rfl)).elim
  subst htb
  rw [VarSymb.lv_ext, Step.levels_cons, if_neg (by decide), hl] at hlv
  exact ⟨rfl, levels_eq_zero_iff.mp (show Step.levels pre.path = 0 by
    unfold VarSymb.lv at hlv; omega), rfl, hl⟩

omit [ModalSys] [ModalSys.NoFourNoTS] in
/-- Collapsing the cut `box` makes it a `here`. -/
theorem collapse_cut (pre : VarSymb) (rest : List Step) :
    ((VarSymb.step pre .box).ext rest).collapse (Step.levels rest) =
      (VarSymb.step pre .here).ext rest := by
  have e := VarSymb.collapse_ext (VarSymb.step pre .box) rest 0
  rw [Nat.zero_add] at e
  rw [e, VarSymb.collapse_level_zero (s := .box) rfl (by decide)]

/-- Read along any arrow, a label cut at its first level step stays allowed, loses that level,
    and keeps its cuts further in. -/
theorem succAddrK_cut {s : B.W} (a : B.Acc s) {x pre : VarSymb} {m : ℕ} {rest : List Step}
    (hok : x.OK) (hpre : PPath pre.path) (hx : x = (VarSymb.step pre .box).ext rest)
    (hl : Step.levels rest = m) :
    (B.succAddrK s a m x).OK ∧ (B.succAddrK s a m x).lv = m ∧
      ∀ {l : ℕ} {c : VarSymb} {t : Step} {d : List Step}, l < m →
        VarSymb.splitAt x l = some (c, t, d) →
          ∃ c', VarSymb.splitAt (B.succAddrK s a m x) l = some (c', t, d) := by
  subst hx hl
  have hrest : ∀ st ∈ rest, st.OK := (VarSymb.ok_ext.mp hok).2
  by_cases hR : B.R s a.1
  · rw [succAddrK_net hR, arrowIdx_boxExt _ hpre]
    refine ⟨VarSymb.ok_ext.mpr ⟨ok_itemAt hpre _, hrest⟩,
      by rw [VarSymb.lv_ext, lv_itemAt hpre, Nat.zero_add], ?_⟩
    intro l c t d hlm h
    obtain ⟨q₁, t', q₂, hq⟩ := splitAt_ext_indep rest l hlm
    rw [hq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    exact ⟨_, hq _⟩
  · rw [succAddrK_self hR]
    refine ⟨Canon.VarSymb.ok_collapse _ _ hok, ?_,
      fun hlm h => ⟨_, Canon.splitAt_collapse_above h hlm⟩⟩
    rw [collapse_cut, VarSymb.lv_ext, Canon.lv_step]
    simp [Step.isProj, VarSymb.lv, levels_eq_zero_iff.mpr hpre]

/-- Reading along an arrow commutes with collapsing further in. -/
theorem succAddrK_collapse {s : B.W} (a : B.Acc s) {x pre : VarSymb} {rest : List Step}
    (l j : ℕ) (hpre : PPath pre.path) (hx : x = (VarSymb.step pre .box).ext rest)
    (hl : Step.levels rest = l + j + 1) :
    (B.succAddrK s a (l + j + 1) x).collapse l = B.succAddrK s a (l + j) (x.collapse l) := by
  by_cases hR : B.R s a.1
  · rw [succAddrK_net hR, succAddrK_net hR]
    obtain ⟨q', hq⟩ := collapse_ext_indep rest l (by omega)
    subst hx
    rw [arrowIdx_boxExt _ hpre, hq, hq, arrowIdx_boxExt _ hpre]
  · rw [succAddrK_self hR, succAddrK_self hR, show l + j + 1 = j + 1 + l by omega,
      VarSymb.collapse_collapse x j l, show j + l = l + j by omega]

/-! ## The leaf calculus: canonical leaves commute with collapse -/

/-- ⭐**Collapsing a canonical leaf collapses its label**: at the level `l` steps inside the label
    (counted from its end), which is `j` levels from the anchor. -/
theorem leafOf_collapse (hT : ModalSys.T = true) : ∀ (j : ℕ) (s : B.W) (l : ℕ)
    (x : VarSymb) {a : VarSymb} {t₀ : Step} {b : List Step}, x.OK →
    VarSymb.splitAt x l = some (a, t₀, b) → t₀ ≠ .dia → x.lv = l + j + 1 →
    Arrows.Leaf.collapse hT j (B.leafOf s (l + j + 1) x) = B.leafOf s (l + j) (x.collapse l)
  | 0, s, l, x, a, t₀, b, _, hx, ht₀, _ => by
      change Arrows.Leaf.collapse hT 0 (B.leafOf s (l + 1) x) = B.leafOf s l (x.collapse l)
      rw [leafOf_lvl s hx ht₀]
      change B.leafOf s l (B.succAddrK s (B.arrows.reflAcc hT s) l x) = _
      rw [succAddrK_self (a := B.arrows.reflAcc hT s) (B.irrefl s)]
  | j + 1, s, l, x, a, t₀, b, hok, hx, ht₀, hlv => by
      obtain ⟨pre, t, rest, h⟩ := Canon.splitAt_of_lv (show l + (j + 1) < x.lv by omega)
      obtain ⟨hxe, htp, hlvr⟩ := VarSymb.splitAt_spec h
      by_cases htd : t = .dia
      · subst htd
        change Arrows.Leaf.collapse hT (j + 1) (B.leafOf s (l + (j + 1) + 1) x) =
          B.leafOf s (l + j + 1) (x.collapse l)
        rw [leafOf_dia s h, Arrows.Leaf.collapse_root,
          Step.collapseAt_succ (rfl : Step.isProj .dia = false), if_neg (by simp)]
        have hagree := VarSymb.collapse_agree pre (.dia :: rest) l
          (by rw [Step.levels_cons, if_neg (by decide)]; omega)
          (VarSymb.ok_ext.mp (hxe ▸ hok)).2
          (fun a' t' b' h' => by
            rw [← hxe, hx] at h'
            simp only [Option.some.injEq, Prod.mk.injEq] at h'
            rw [← h'.2.1]
            exact ht₀)
        rw [Step.levels_cons, if_neg (by decide),
          show 1 + Step.levels rest - 1 - l = j + 1 by omega,
          Step.collapseAt_succ (rfl : Step.isProj .dia = false), if_neg (by simp)] at hagree
        rw [hxe, hagree]
        have hl := Canon.levels_collapseAt j rest (by omega)
        have hs := VarSymb.splitAt_ext pre (rfl : Step.isProj .dia = false)
          (Step.collapseAt j rest)
        rw [show Step.levels (Step.collapseAt j rest) = l + j by omega] at hs
        rw [leafOf_dia s hs]
      · obtain ⟨-, hpre, hxb, hrl⟩ := cut_first hok (show x.lv = l + (j + 1) + 1 by omega) h htd
        change Arrows.Leaf.collapse hT (j + 1) (B.leafOf s (l + (j + 1) + 1) x) =
          B.leafOf s (l + j + 1) (x.collapse l)
        rw [leafOf_lvl s h htd]
        obtain ⟨rest', h'⟩ := Canon.splitAt_collapse_below (k := l + j) h (show l ≤ l + j by omega)
        rw [leafOf_lvl s h' htd]
        change Arrows.Leaf.fam (fun (a' : B.Acc s) => Arrows.Leaf.collapse hT j
            (B.leafOf a'.1 (l + j + 1) (B.succAddrK s a' (l + j + 1) x))) = _
        congr 1
        funext a'
        obtain ⟨hok', hlv', hsp⟩ :=
          B.succAddrK_cut a' hok hpre hxb (show Step.levels rest = l + j + 1 by omega)
        obtain ⟨c', hc'⟩ := hsp (by omega) hx
        rw [leafOf_collapse hT j a'.1 l _ hok' hc' ht₀ hlv',
          succAddrK_collapse a' l j hpre hxb (by omega)]

/-- ⭐**Collapsing a canonical annotation** at a level inside its labels collapses its addresses. -/
theorem annShp_eta_collapse (hT : ModalSys.T = true) : ∀ (X : VarType) (s : B.W)
    (j l : ℕ) (z : VarSymb) {a : VarSymb} {t₀ : Step} {b : List Step}, z.OK →
    VarSymb.splitAt z l = some (a, t₀, b) → t₀ ≠ .dia → z.lv = l + j + 1 →
    (B.annShp s (l + j + 1) (Ann.eta z X)).map (Arrows.Leaf.collapse hT j) =
      B.annShp s (l + j) (Ann.eta (z.collapse l) X)
  | .Var, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .VTypeOne, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .VTypeProd A C, s, j, l, z, a, t₀, b, hok, hz, ht₀, hlv => by
      have hf := VarSymb.splitAt_extend hz [.fst]
      have hs := VarSymb.splitAt_extend hz [.snd]
      simp only [Step.levels, Step.isProj, if_true, Nat.add_zero] at hf hs
      change Shp.prod ((B.annShp s (l + j + 1) (Ann.eta (.step z .fst) A)).map _)
          ((B.annShp s (l + j + 1) (Ann.eta (.step z .snd) C)).map _) =
        Shp.prod (B.annShp s (l + j) (Ann.eta (.step (z.collapse l) .fst) A))
          (B.annShp s (l + j) (Ann.eta (.step (z.collapse l) .snd) C))
      rw [annShp_eta_collapse hT A s j l (.step z .fst)
          (VarSymb.ok_step.mpr ⟨hok, Step.ok_of_proj rfl⟩) hf ht₀
          (by rw [Canon.lv_step]; simpa [Step.isProj] using hlv),
        annShp_eta_collapse hT C s j l (.step z .snd)
          (VarSymb.ok_step.mpr ⟨hok, Step.ok_of_proj rfl⟩) hs ht₀
          (by rw [Canon.lv_step]; simpa [Step.isProj] using hlv),
        VarSymb.collapse_proj (rfl : Step.isProj .fst = true),
        VarSymb.collapse_proj (rfl : Step.isProj .snd = true)]
  | .VTypeBox A, s, j, l, z, a, t₀, b, hok, hz, ht₀, hlv => by
      have hi := VarSymb.splitAt_extend hz Step.innerPath
      rw [← List.nil_append Step.innerPath, ← VarSymb.inner_ext z [], List.nil_append,
        Canon.levels_innerPath] at hi
      change Shp.box ((B.annShp s (l + j + 1 + 1) (Ann.eta z.inner A)).map _) =
        Shp.box (B.annShp s (l + j + 1) (Ann.eta (z.collapse l).inner A))
      have ih := annShp_eta_collapse hT A s j (l + 1) z.inner (Canon.ok_inner hT hok) hi ht₀
        (by rw [Canon.lv_inner]; omega)
      rw [show l + 1 + j + 1 = l + j + 1 + 1 by omega, show l + 1 + j = l + j + 1 by omega,
        VarSymb.inner_collapse_succ] at ih
      rw [ih]
  | .VTypeDia A, s, j, l, z, a, t₀, b, hok, hz, ht₀, hlv => by
      have hd := VarSymb.splitAt_extend hz [.dia]
      simp only [Step.levels, Step.isProj, Bool.false_eq_true, if_false, Nat.add_zero] at hd
      change Shp.dia (Arrows.Leaf.collapse hT j (B.leafOf s (l + j + 1) z))
          ((B.annShp s (l + j + 1 + 1) (Ann.eta (.step z .dia) A)).map _) =
        Shp.dia (B.leafOf s (l + j) (z.collapse l))
          (B.annShp s (l + j + 1) (Ann.eta (.step (z.collapse l) .dia) A))
      have ih := annShp_eta_collapse hT A s j (l + 1) (.step z .dia)
        (VarSymb.ok_step.mpr ⟨hok, Step.ok_dia⟩) hd ht₀
        (by rw [Canon.lv_step]; simp [Step.isProj]; omega)
      rw [show l + 1 + j + 1 = l + j + 1 + 1 by omega, show l + 1 + j = l + j + 1 by omega,
        VarSymb.collapse_level_succ (rfl : Step.isProj .dia = false)] at ih
      rw [leafOf_collapse hT j s l z hok hz ht₀ hlv, ih]

/-! ## Shape environments that read every address canonically -/

variable (B) in
/-- ⭐A shape environment at depth `j` **reads every address canonically** when each reachable
    address's shape is its η-annotation read canonically. -/
def Canonical {Δ : Ctx} {s : B.W} (ρ : B.CShEnv Δ s) (j : ℕ) : Prop :=
  ∀ y T (h : Δ.ref y = some T), ρ.ref j y h = B.annShp s j (Ann.eta y T)

/-- A projection moves a canonical η-annotation to the projected address's. -/
theorem shp_proj_annShp {Δ : Ctx} (hok : Δ.DeclOK) {j : ℕ} (hex : Δ.Exact j) (s : B.W)
    {v : VarSymb} {U T : VarType} {st : Step} (hs : st.isProj = true) (hU : Δ.ref v = some U)
    (h : U.step st = some T) :
    GFunc.shp (GFunc.proj (σ := σ) hs h) j (B.annShp s j (Ann.eta v U)) =
      B.annShp s j (Ann.eta (.step v st) T) := by
  cases U <;> cases st <;> (try cases hs) <;> (try cases h)
  · rfl
  · rfl
  · rename_i X
    obtain ⟨hT', rfl⟩ := VarType.step_here h
    change (B.annShp s (j + 1) (Ann.eta v.inner X)).map (Arrows.Leaf.collapse hT' j) = _
    have hi : VarSymb.splitAt v.inner 0 = some (v, .box, []) := by rw [inner_eq]; rfl
    have := annShp_eta_collapse hT' X s j 0 v.inner (Canon.ok_inner hT' (hok.ref v hU)) hi
      nofun (by rw [Canon.lv_inner, hex v _ hU]; omega)
    rw [Nat.zero_add] at this
    rw [this, VarSymb.inner_collapse_zero]

/-- It suffices that the declared addresses read canonically. -/
theorem Canonical.of_decl {Δ : Ctx} (hok : Δ.DeclOK) {j : ℕ} (hex : Δ.Exact j) {s : B.W}
    {ρ : B.CShEnv Δ s} (h : ∀ y T (hy : Δ y = some T), ρ y T hy = B.annShp s j (Ann.eta y T)) :
    B.Canonical ρ j := by
  intro y
  induction y with
  | root r => intro T hy; exact h _ T hy
  | step v st ih =>
      intro T hy
      by_cases hs : st.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Δ.ref v = some U := by
          rw [Ctx.ref_step_proj Δ v hs] at hy
          cases hU : Δ.ref v with
          | none => rw [hU] at hy; cases hy
          | some U => exact ⟨U, rfl⟩
        rw [Model.ShEnv.ref_proj ρ j hs hU hy, ih U hU]
        exact shp_proj_annShp hok hex s hs hU _
      · rw [Model.ShEnv.ref_nonproj ρ j hs hy]
        exact h _ T _

/-- ⭐Pushing a canonical environment into `□` gives a canonical one, one level deeper. -/
theorem Canonical.boxPush (hT : ModalSys.T = true) {Δ : Ctx} (hok : Δ.DeclOK) {j : ℕ}
    (hex : Δ.Exact j) {s : B.W} {ρ : B.CShEnv Δ s} (hρ : B.Canonical ρ j) :
    B.Canonical (ρ.boxPush j) (j + 1) := by
  refine Canonical.of_decl (hok.boxIn hT) hex.boxIn fun v T hv => ?_
  match v, hv with
  | .step u .box, hv =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hv
      change (ρ.ref j u (Ctx.boxIn_step_box hv)).inner = _
      rw [hρ u _ (Ctx.boxIn_step_box hv)]
      change B.annShp s (j + 1) (Ann.eta u.inner T) = _
      rw [VarSymb.inner_box hk]
  | .step u .keep, hv => exact (noFour (Ctx.boxIn_keep hv).1).elim
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .dia, hv => cases hv
  | .step _ .here, hv => cases hv

/-- ⭐Pushing a canonical environment into `◇_x` gives a canonical one, one level deeper. -/
theorem Canonical.diaPush (hT : ModalSys.T = true) {Δ : Ctx} (hok : Δ.DeclOK) {j : ℕ}
    (hex : Δ.Exact j) {s : B.W} {ρ : B.CShEnv Δ s} (hρ : B.Canonical ρ j) {x : VarSymb}
    {X : VarType} (hx : Δ.ref x = some (.VTypeDia X)) :
    B.Canonical (ρ.diaPush j x hx) (j + 1) := by
  refine Canonical.of_decl (hok.diaIn hT x) (hex.diaIn x) fun v T hv => ?_
  match v, hv with
  | .step u .dia, hv =>
      have hux : u = x := by
        change (if u = x then _ else none) = some T at hv
        split_ifs at hv with h'
        exact h'
      subst hux
      have hXT := Ctx.diaIn_step_dia hx hv
      subst hXT
      simp only [Model.ShEnv.diaPush]
      rw [hρ u _ hx]
      rfl
  | .step u .box, hv =>
      have hb : Δ.boxIn.ref (.step u .box) = some T :=
        (Ctx.ref_nonproj _ (show (VarSymb.step u .box).lastProj = false from rfl)).trans hv
      have hc := (hρ.boxPush hT hok hex) _ _ hb
      rw [Model.ShEnv.ref_nonproj _ _ (by decide) hb] at hc
      exact hc
  | .step u .keep, hv =>
      have hb : Δ.boxIn.ref (.step u .keep) = some T :=
        (Ctx.ref_nonproj _ (show (VarSymb.step u .keep).lastProj = false from rfl)).trans hv
      have hc := (hρ.boxPush hT hok hex) _ _ hb
      rw [Model.ShEnv.ref_nonproj _ _ (by decide) hb] at hc
      exact hc
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .here, hv => cases hv

/-- ⭐⭐**The relabelling theorem**: in a canonical environment, a term's shape is its annotation
    read canonically. -/
theorem termShp_canonical (hT : ModalSys.T = true) {s : B.W} :
    ∀ {Δ : Ctx}, Δ.DeclOK → ∀ {j : ℕ}, Δ.Exact j → ∀ {ρ : B.CShEnv Δ s},
      B.Canonical ρ j → ∀ {A : VarType} {a : Ann A} (t : Term σ Δ A a),
        Model.termShp ρ j t = B.annShp s j a
  | _, _, _, _, _, _, _, _, .var _ _ => rfl
  | _, _, _, _, _, _, _, _, .func _ => rfl
  | _, _, _, _, _, _, _, _, .unit => rfl
  | _, hok, _, hex, _, hρ, _, _, .pair u t => by
      change Shp.prod (Model.termShp _ _ u) (Model.termShp _ _ t) = _
      rw [termShp_canonical hT hok hex hρ u, termShp_canonical hT hok hex hρ t]
      rfl
  | _, hok, j, hex, ρ, hρ, _, _, .boxtm t => by
      change Shp.box (Model.termShp (ρ.boxPush j) (j + 1) t) = _
      rw [termShp_canonical hT (hok.boxIn hT) hex.boxIn (hρ.boxPush hT hok hex) t]
      rfl
  | _, hok, j, hex, ρ, hρ, _, _, .diatm x hx t => by
      obtain ⟨X, hr⟩ := id hx
      rw [Model.termShp_diatm ρ j hr hx,
        termShp_canonical hT (hok.diaIn hT x) (hex.diaIn x) (hρ.diaPush hT hok hex hr) t,
        hρ x _ hr]
      rfl

/-- The canonical shape environment of a level-free context reads every address canonically. -/
theorem cEnv_canonical {Γ : Ctx} (hex : Γ.Exact 0) (s : B.W) : B.Canonical (B.cEnv Γ s) 0 := by
  intro y T h
  rw [B.cEnv_ref, canonSh_eq T s y (levels_eq_zero_iff.mp (hex y T h))]

/-! ## Tags determine annotations -/

/-- Under T every world has a network arrow out: `T_box` refutes `□⊥`, so a `□` fails. -/
theorem exists_net (hT : ModalSys.T = true) (s : B.W) : ∃ t, B.R s t := by
  have hnot : WFF.box (.bot : WFF σ ((B.w s).ctx 0).boxIn 0) ∉ (B.w s).M 0 := fun h =>
    ((B.w s).mcs 0).bot_not_mem (BWorld.mem_of_provable (Δ := [.box .bot])
      (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact h)
      ⟨Proof.T_box hT (Proof.lookup List.mem_cons_self)⟩)
  obtain ⟨t, h, _⟩ := B.ex s 0 .bot hnot
  exact ⟨t, h⟩

omit [ModalSys.NoFourNoTS] in
theorem itemTail_T (hT : ModalSys.T = true) : itemTail = [.fst] := by
  simp [itemTail, hT]

/-- ⭐**Canonical leaves determine labels** with exactly as many levels as their depth.  No one
    arrow reads a family back: the own arrow turns the cut `box` into a `here`, a network arrow
    encodes the projections before it — but the two together do (`eq_of_here_enc`). -/
theorem leafOf_inj (hT : ModalSys.T = true) : ∀ (m : ℕ) (s : B.W) {y y' : VarSymb},
    y.OK → y'.OK → y.lv = m → y'.lv = m → B.leafOf s m y = B.leafOf s m y' → y = y'
  | 0, s, y, y', _, _, _, _, h => by
      rw [leafOf_zero, leafOf_zero] at h
      injection h
  | m + 1, s, y, y', hok, hok', hlv, hlv', h => by
      obtain ⟨pre, t, rest, hc⟩ := Canon.splitAt_of_lv (show m < y.lv by omega)
      obtain ⟨pre', t', rest', hc'⟩ := Canon.splitAt_of_lv (show m < y'.lv by omega)
      by_cases ht : t = .dia <;> by_cases ht' : t' = .dia
      · subst ht ht'
        rw [leafOf_dia s hc, leafOf_dia s hc'] at h
        injection h with _ h₁ h₂
        rw [(VarSymb.splitAt_spec hc).1, (VarSymb.splitAt_spec hc').1, h₁, h₂]
      · subst ht
        rw [leafOf_dia s hc, leafOf_lvl s hc' ht'] at h
        cases h
      · subst ht'
        rw [leafOf_lvl s hc ht, leafOf_dia s hc'] at h
        cases h
      · obtain ⟨-, hpre, hy, hl⟩ := cut_first hok hlv hc ht
        obtain ⟨-, hpre', hy', hl'⟩ := cut_first hok' hlv' hc' ht'
        rw [leafOf_lvl s hc ht, leafOf_lvl s hc' ht'] at h
        have hf := Arrows.Leaf.fam.inj h
        -- along the own arrow: the cut `box` becomes a `here`
        have h₀ := congrFun hf ⟨s, ⟨Or.inr ⟨hT, rfl⟩⟩⟩
        obtain ⟨hok₀, hlv₀, -⟩ := B.succAddrK_cut ⟨s, ⟨Or.inr ⟨hT, rfl⟩⟩⟩ hok hpre hy hl
        obtain ⟨hok₀', hlv₀', -⟩ := B.succAddrK_cut ⟨s, ⟨Or.inr ⟨hT, rfl⟩⟩⟩ hok' hpre' hy' hl'
        have e₀ := leafOf_inj hT m s hok₀ hok₀' hlv₀ hlv₀' h₀
        rw [succAddrK_self (a := ⟨s, ⟨Or.inr ⟨hT, rfl⟩⟩⟩) (B.irrefl s),
          succAddrK_self (a := ⟨s, ⟨Or.inr ⟨hT, rfl⟩⟩⟩) (B.irrefl s), hy, hy'] at e₀
        have c := collapse_cut pre rest
        have c' := collapse_cut pre' rest'
        rw [hl] at c
        rw [hl'] at c'
        rw [c, c'] at e₀
        -- along a network arrow: the projections before it are encoded
        obtain ⟨t₁, hR⟩ := B.exists_net hT s
        have h₁ := congrFun hf ⟨t₁, ⟨Or.inl hR⟩⟩
        obtain ⟨hok₁, hlv₁, -⟩ := B.succAddrK_cut ⟨t₁, ⟨Or.inl hR⟩⟩ hok hpre hy hl
        obtain ⟨hok₁', hlv₁', -⟩ := B.succAddrK_cut ⟨t₁, ⟨Or.inl hR⟩⟩ hok' hpre' hy' hl'
        have e₁ := leafOf_inj hT m t₁ hok₁ hok₁' hlv₁ hlv₁' h₁
        rw [succAddrK_net (a := ⟨t₁, ⟨Or.inl hR⟩⟩) hR,
          succAddrK_net (a := ⟨t₁, ⟨Or.inl hR⟩⟩) hR, hy, hy',
          arrowIdx_boxExt _ hpre, arrowIdx_boxExt _ hpre'] at e₁
        -- together
        have p₀ := congrArg VarSymb.path e₀
        have p₁ := congrArg VarSymb.path e₁
        simp only [VarSymb.ext_path, VarSymb.path, List.append_assoc, List.singleton_append,
          itemAt_path, itemTail_T hT] at p₀ p₁
        obtain ⟨hp, hr⟩ := eq_of_here_enc hT p₀ p₁
        have hrt : pre.rt = pre'.rt := by
          simpa [VarSymb.ext_rt, VarSymb.rt] using congrArg VarSymb.rt e₀
        have hpe : pre = pre' := by
          rw [VarSymb.eq_root_ext_path pre, VarSymb.eq_root_ext_path pre', hrt, hp]
        rw [hy, hy', hpe, hr]

/-- Reading annotations canonically is injective, on annotations with exact levels. -/
theorem annShp_injective (hT : ModalSys.T = true) (s : B.W) :
    ∀ {A : VarType} (j : ℕ) (a a' : Ann A), a.Exact j → a'.Exact j →
      B.annShp s j a = B.annShp s j a' → a = a'
  | _, _, .var, .var, _, _, _ => rfl
  | _, _, .one, .one, _, _, _ => rfl
  | _, j, .prod a b, .prod a' b', hab, hab', h => by
      obtain ⟨ha, hb⟩ := hab
      obtain ⟨ha', hb'⟩ := hab'
      injection h with _ _ h₁ h₂
      rw [annShp_injective hT s j a a' ha ha' h₁, annShp_injective hT s j b b' hb hb' h₂]
  | _, j, .box a, .box a', ha, ha', h => by
      injection h with _ h₁
      rw [annShp_injective hT s (j + 1) a a' ha ha' h₁]
  | _, j, .dia x a, .dia x' a', hxa, hxa', h => by
      obtain ⟨hx, hlx, ha⟩ := hxa
      obtain ⟨hx', hlx', ha'⟩ := hxa'
      injection h with _ h₁ h₂
      rw [leafOf_inj hT j s hx hx' hlx hlx' h₁, annShp_injective hT s (j + 1) a a' ha ha' h₂]

/-- ⭐⭐**Canonical shapes determine annotations**: two terms of one type, in a context whose
    addresses are allowed and level-free, with the same canonical shape have the same
    annotation. -/
theorem ann_eq_of_termShp (hT : ModalSys.T = true) {Γ : Ctx} (hok : Γ.DeclOK) (hex : Γ.Exact 0)
    (s : B.W) {A : VarType} {a a' : Ann A} (t : Term σ Γ A a) (t' : Term σ Γ A a')
    (h : Model.termShp (B.cEnv Γ s) 0 t = Model.termShp (B.cEnv Γ s) 0 t') : a = a' := by
  refine annShp_injective hT s 0 a a' (Term.ann_exact hT hok hex t)
    (Term.ann_exact hT hok hex t') ?_
  rw [← termShp_canonical hT hok hex (cEnv_canonical hex s) t,
    ← termShp_canonical hT hok hex (cEnv_canonical hex s) t', h]

/-- ⭐⭐**Tags determine annotations**: two terms with one denotation have one annotation. -/
theorem ann_eq_of_rden (hT : ModalSys.T = true) {Γ : Ctx} (hok : Γ.DeclOK) (hex : Γ.Exact 0)
    {s : B.W} {i : ℕ} (e : Γ.Le ((B.w s).ctx i)) {A : VarType} {a a' : Ann A}
    (t : Term σ Γ A a) (t' : Term σ Γ A a') (h : B.rden s i e t = B.rden s i e t') : a = a' :=
  ann_eq_of_termShp hT hok hex s t t'
    (by rw [← B.rawShape_rden hT s i e t, ← B.rawShape_rden hT s i e t', h])

/-- Tags determine annotations, for terms of a world's language. -/
theorem ann_eq_of_rden_ctx (hT : ModalSys.T = true) {s : B.W} {i : ℕ} {A : VarType}
    {a a' : Ann A} (t : Term σ ((B.w s).ctx i) A a) (t' : Term σ ((B.w s).ctx i) A a')
    (h : B.rden s i (Ctx.Le.refl _) t = B.rden s i (Ctx.Le.refl _) t') : a = a' :=
  ann_eq_of_rden hT (Ctx.Presented.declOK hT _) (exact_ctxOf _) _ t t' h

end BData

end BArrow

end V12M
