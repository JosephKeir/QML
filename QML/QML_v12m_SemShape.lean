import QML.QML_v12m_InterpLemmas

/-!
# QML v12m — semantics: the shapes of values

Under T or strong B (`ModalSys.shaped`) a possible object carries a **shape**, its semantic
annotation (docs §10.27–10.28), and possible objects are identified only by section *and* shape
(`Model.pos_inj`).  So every lemma that identifies two values of possible terms needs the two
shapes to agree.  This file computes them.

The shape of a term's value is computed **symbolically**, by the same recursion as the value but
with shapes in place of objects:

* a **shape environment** (`ShEnv`) gives a shape, anchored at the current world, for each visible
  address, and is pushed into `□` and `◇_x` views (`ShEnv.boxPush`, `ShEnv.diaPush`) without ever
  choosing an arrow — which is what lets it see inside a possible object whose extent is empty;
* `termShp ρ j t` is the shape of `t`, `j` being the number of levels above the current position;
* ⭐`termShp_compile` (S1): compiling a term and moving the shape of its bundle along the compiled
  map (`GFunc.shp`) gives `termShp` — the counterpart of `Term.compile_eval`.
-/

namespace V12M

variable [ModalSys]

universe y

/-! ## Commuting collapses and shifts

The simplicial identities between collapsing and shifting levels, first on paths, then on leaves.
They let a collapse or shift applied to a whole shape environment be moved through `termShp`. -/

namespace Step

omit [ModalSys] in
theorem collapseAt_proj {s : Step} (hs : s.isProj = true) (i : Nat) (p : List Step) :
    collapseAt i (s :: p) = s :: collapseAt i p := by
  conv => lhs; rw [collapseAt.eq_def]
  simp only [hs, if_true]

omit [ModalSys] in
theorem collapseAt_zero {s : Step} (hs : s.isProj = false) (p : List Step) :
    collapseAt 0 (s :: p) = if s = .keep then p else .here :: p := by
  conv => lhs; rw [collapseAt.eq_def]
  simp only [hs, Bool.false_eq_true, if_false]

omit [ModalSys] in
theorem collapseAt_succ {s : Step} (hs : s.isProj = false) (i : Nat) (p : List Step) :
    collapseAt (i + 1) (s :: p) =
      if i = 0 ∧ s = .keep ∧ headLvl p = true then p else s :: collapseAt i p := by
  conv => lhs; rw [collapseAt.eq_def]
  simp only [hs, Bool.false_eq_true, if_false]

omit [ModalSys] in
theorem collapseAt_two {s : Step} (hs : s.isProj = false) (i : Nat) (p : List Step) :
    collapseAt (i + 2) (s :: p) = s :: collapseAt (i + 1) p := by
  rw [collapseAt_succ hs, if_neg (by omega)]

omit [ModalSys] in
theorem shiftAt_proj {s : Step} (hs : s.isProj = true) (i : Nat) (p : List Step) :
    shiftAt i (s :: p) = s :: shiftAt i p := by
  conv => lhs; rw [shiftAt.eq_def]
  simp only [hs, if_true]

omit [ModalSys] in
theorem shiftAt_zero {s : Step} (hs : s.isProj = false) (p : List Step) :
    shiftAt 0 (s :: p) = .keep :: s :: p := by
  conv => lhs; rw [shiftAt.eq_def]
  simp only [hs, Bool.false_eq_true, if_false]

omit [ModalSys] in
theorem shiftAt_succ {s : Step} (hs : s.isProj = false) (i : Nat) (p : List Step) :
    shiftAt (i + 1) (s :: p) = s :: shiftAt i p := by
  conv => lhs; rw [shiftAt.eq_def]
  simp only [hs, Bool.false_eq_true, if_false]

omit [ModalSys] in
/-- The counit: keeping, then reading the next level where it was kept. -/
theorem collapseAt_shiftAt_succ :
    ∀ (j : Nat) (p : List Step), collapseAt (j + 1) (shiftAt j p) = p
  | _, [] => by simp [shiftAt, collapseAt]
  | j, s :: p => by
      cases hs : s.isProj
      · cases j with
        | zero =>
            rw [shiftAt_zero hs, collapseAt_succ (by rfl)]
            simp [headLvl, hs]
        | succ j =>
            rw [shiftAt_succ hs, collapseAt_two hs, collapseAt_shiftAt_succ j p]
      · rw [shiftAt_proj hs, collapseAt_proj hs, collapseAt_shiftAt_succ j p]

omit [ModalSys] in
/-- The other counit: keeping, then reading the kept level at once. -/
theorem collapseAt_shiftAt_self : ∀ (j : Nat) (p : List Step), collapseAt j (shiftAt j p) = p
  | _, [] => by simp [shiftAt, collapseAt]
  | j, s :: p => by
      cases hs : s.isProj
      · cases j with
        | zero => rw [shiftAt_zero hs, collapseAt_zero (by rfl), if_pos rfl]
        | succ j =>
            rw [shiftAt_succ hs, collapseAt_succ hs, collapseAt_shiftAt_self j p]
            by_cases h : j = 0 ∧ s = Step.keep ∧ headLvl (shiftAt j p) = true
            · rw [if_pos h]
              obtain ⟨rfl, rfl, hl⟩ := h
              cases p with
              | nil => simp [headLvl, shiftAt] at hl
              | cons t q =>
                  cases ht : t.isProj
                  · rw [shiftAt_zero ht]
                  · rw [shiftAt_proj ht] at hl
                    simp [headLvl, ht] at hl
            · rw [if_neg h]
      · rw [shiftAt_proj hs, collapseAt_proj hs, collapseAt_shiftAt_self j p]

omit [ModalSys] in
theorem headLvl_collapseAt_succ : ∀ (i : Nat) (p : List Step),
    headLvl p = true → headLvl (collapseAt (i + 1) p) = true
  | _, [], h => by simp [headLvl] at h
  | i, t :: q, h => by
      have ht : t.isProj = false := by simpa [headLvl] using h
      rw [collapseAt_succ ht]
      by_cases hc : i = 0 ∧ t = Step.keep ∧ headLvl q = true
      · rw [if_pos hc]; exact hc.2.2
      · rw [if_neg hc]; simp [headLvl, ht]

omit [ModalSys] in
theorem not_headLvl_collapseAt : ∀ (i : Nat) (p : List Step),
    headLvl p = false → headLvl (collapseAt i p) = false
  | _, [], _ => by simp [collapseAt, headLvl]
  | i, t :: q, h => by
      have ht : t.isProj = true := by simpa [headLvl] using h
      rw [collapseAt_proj ht]; simp [headLvl, ht]

omit [ModalSys] in
theorem headLvl_shiftAt : ∀ (i : Nat) (p : List Step), headLvl (shiftAt i p) = headLvl p
  | _, [] => by simp [shiftAt, headLvl]
  | i, t :: q => by
      cases ht : t.isProj
      · cases i with
        | zero => rw [shiftAt_zero ht]; simp [headLvl, ht]; rfl
        | succ i => rw [shiftAt_succ ht]; rfl
      · rw [shiftAt_proj ht]; rfl

omit [ModalSys] in
theorem collapseAt_collapseAt : ∀ (j d : Nat) (p : List Step),
    collapseAt (j + d) (collapseAt j p) = collapseAt j (collapseAt (j + d + 1) p)
  | _, _, [] => by simp [collapseAt]
  | j, d, s :: p => by
      cases hs : s.isProj
      · match j with
        | 0 =>
            rw [Nat.zero_add, collapseAt_zero hs, collapseAt_succ hs]
            by_cases hk : s = Step.keep
            · subst hk
              rw [if_pos rfl]
              by_cases hc : d = 0 ∧ Step.keep = Step.keep ∧ headLvl p = true
              · rw [if_pos hc, hc.1]
              · rw [if_neg hc, collapseAt_zero (by rfl), if_pos rfl]
            · rw [if_neg hk, if_neg (fun h => hk h.2.1), collapseAt_proj (by rfl),
                collapseAt_zero hs, if_neg hk]
        | 1 =>
            rw [show 1 + d = d + 1 by omega, show d + 1 + 1 = d + 2 by omega, collapseAt_two hs,
              collapseAt_succ hs, collapseAt_succ hs]
            by_cases hk : s = Step.keep
            · subst hk
              cases hp : headLvl p
              · rw [if_neg (by simp), if_neg (by simp [not_headLvl_collapseAt _ _ hp]),
                  collapseAt_succ (by rfl), if_neg (by simp [not_headLvl_collapseAt _ _ hp])]
                have := collapseAt_collapseAt 0 d p
                rw [Nat.zero_add] at this
                rw [this]
              · rw [if_pos (by simp), if_pos (by simp [headLvl_collapseAt_succ _ _ hp])]
            · rw [if_neg (fun h => hk h.2.1), if_neg (fun h => hk h.2.1), collapseAt_succ hs,
                if_neg (fun h => hk h.2.1)]
              have := collapseAt_collapseAt 0 d p
              rw [Nat.zero_add] at this
              rw [this]
        | j + 2 =>
            rw [show j + 2 + d = (j + d) + 2 by omega, collapseAt_two hs, collapseAt_two hs,
              show j + d + 2 + 1 = (j + d + 1) + 2 by omega, collapseAt_two hs, collapseAt_two hs]
            have := collapseAt_collapseAt (j + 1) d p
            rw [show j + 1 + d = j + d + 1 by omega] at this
            rw [this]
      · simp only [collapseAt_proj hs]
        rw [collapseAt_collapseAt j d p]

omit [ModalSys] in
theorem shiftAt_collapseAt : ∀ (j d : Nat) (p : List Step),
    shiftAt (j + d) (collapseAt j p) = collapseAt j (shiftAt (j + d + 1) p)
  | _, _, [] => by simp [collapseAt, shiftAt]
  | j, d, s :: p => by
      cases hs : s.isProj
      · match j with
        | 0 =>
            rw [Nat.zero_add, collapseAt_zero hs, shiftAt_succ hs, collapseAt_zero hs]
            by_cases hk : s = Step.keep
            · rw [if_pos hk, if_pos hk]
            · rw [if_neg hk, if_neg hk, shiftAt_proj (by rfl)]
        | 1 =>
            rw [show 1 + d = d + 1 by omega, show d + 1 + 1 = d + 2 by omega, shiftAt_succ hs,
              collapseAt_succ hs, collapseAt_succ hs]
            by_cases hk : s = Step.keep
            · subst hk
              cases hp : headLvl p
              · rw [if_neg (by simp), if_neg (by simp [headLvl_shiftAt, hp]),
                  shiftAt_succ (by rfl)]
                have := shiftAt_collapseAt 0 d p
                rw [Nat.zero_add] at this
                rw [this]
              · rw [if_pos (by simp), if_pos (by simp [headLvl_shiftAt, hp])]
            · rw [if_neg (fun h => hk h.2.1), if_neg (fun h => hk h.2.1), shiftAt_succ hs]
              have := shiftAt_collapseAt 0 d p
              rw [Nat.zero_add] at this
              rw [this]
        | j + 2 =>
            rw [show j + 2 + d = (j + d + 1) + 1 by omega, collapseAt_two hs, shiftAt_succ hs,
              show j + d + 1 + 1 + 1 = (j + d + 2) + 1 by omega, shiftAt_succ hs, collapseAt_two hs]
            have := shiftAt_collapseAt (j + 1) d p
            rw [show j + 1 + d = j + d + 1 by omega, show j + d + 1 + 1 = j + d + 2 by omega]
              at this
            rw [this]
      · simp only [collapseAt_proj hs, shiftAt_proj hs]
        rw [shiftAt_collapseAt j d p]

omit [ModalSys] in
theorem shiftAt_zero_of_headLvl :
    ∀ (X : List Step), headLvl X = true → shiftAt 0 X = Step.keep :: X
  | [], h => by simp [headLvl] at h
  | t :: q, h => shiftAt_zero (by simpa [headLvl] using h) q

omit [ModalSys] in
theorem collapseAt_shiftAt : ∀ (j d : Nat) (p : List Step),
    collapseAt (j + d + 2) (shiftAt j p) = shiftAt j (collapseAt (j + d + 1) p)
  | _, _, [] => by simp [collapseAt, shiftAt]
  | j, d, s :: p => by
      cases hs : s.isProj
      · cases j with
        | zero =>
            rw [shiftAt_zero hs, Nat.zero_add, collapseAt_two (by rfl)]
            exact (shiftAt_zero_of_headLvl _
              (headLvl_collapseAt_succ d (s :: p) (by simp [headLvl, hs]))).symm
        | succ j =>
            rw [shiftAt_succ hs, show j + 1 + d + 2 = (j + d + 2) + 1 by omega,
              collapseAt_succ hs, if_neg (by omega),
              show j + 1 + d + 1 = (j + d + 1) + 1 by omega, collapseAt_succ hs,
              if_neg (by omega), shiftAt_succ hs, collapseAt_shiftAt j d p]
      · simp only [shiftAt_proj hs, collapseAt_proj hs]
        rw [collapseAt_shiftAt j d p]

omit [ModalSys] in
theorem shiftAt_shiftAt : ∀ (j d : Nat) (p : List Step),
    shiftAt (j + d + 2) (shiftAt j p) = shiftAt j (shiftAt (j + d + 1) p)
  | _, _, [] => by simp [shiftAt]
  | j, d, s :: p => by
      cases hs : s.isProj
      · cases j with
        | zero =>
            rw [shiftAt_zero hs, Nat.zero_add, shiftAt_succ (by rfl), shiftAt_succ hs,
              shiftAt_zero hs]
        | succ j =>
            rw [shiftAt_succ hs, show j + 1 + d + 2 = (j + d + 2) + 1 by omega, shiftAt_succ hs,
              show j + 1 + d + 1 = (j + d + 1) + 1 by omega, shiftAt_succ hs, shiftAt_succ hs,
              shiftAt_shiftAt j d p]
      · simp only [shiftAt_proj hs]
        rw [shiftAt_shiftAt j d p]

omit [ModalSys] in
theorem shiftAt_shiftAt_self :
    ∀ (j : Nat) (p : List Step), shiftAt (j + 1) (shiftAt j p) = shiftAt j (shiftAt j p)
  | _, [] => by simp [shiftAt]
  | j, s :: p => by
      cases hs : s.isProj
      · cases j with
        | zero =>
            rw [shiftAt_zero hs, shiftAt_succ (by rfl), shiftAt_zero hs, shiftAt_zero (by rfl)]
        | succ j =>
            simp only [shiftAt_succ hs]
            rw [shiftAt_shiftAt_self j p]
      · simp only [shiftAt_proj hs]
        rw [shiftAt_shiftAt_self j p]

omit [ModalSys] in
theorem keepAt_proj {s : Step} (hs : s.isProj = true) (i : Nat) (p : List Step) :
    keepAt i (s :: p) = s :: keepAt i p := by
  cases i <;> simp [keepAt, hs]

omit [ModalSys] in
theorem keepAt_succ {s : Step} (hs : s.isProj = false) (i : Nat) (p : List Step) :
    keepAt (i + 1) (s :: p) = s :: keepAt i p := by
  simp [keepAt, hs]

omit [ModalSys] in
/-- Keeping below a shifted level: the two insertions commute, the keep moving one level down. -/
theorem keepAt_shiftAt : ∀ (j d : Nat) (p : List Step),
    keepAt (j + d + 2) (shiftAt j p) = shiftAt j (keepAt (j + d + 1) p)
  | _, _, [] => by simp [keepAt, shiftAt]
  | j, d, s :: p => by
      cases hs : s.isProj
      · cases j with
        | zero =>
            rw [shiftAt_zero hs, Nat.zero_add, keepAt_succ (by rfl), keepAt_succ hs]
            exact (shiftAt_zero hs _).symm
        | succ j =>
            rw [shiftAt_succ hs, show j + 1 + d + 2 = (j + d + 2) + 1 by omega, keepAt_succ hs,
              show j + 1 + d + 1 = (j + d + 1) + 1 by omega, keepAt_succ hs, shiftAt_succ hs,
              keepAt_shiftAt j d p]
      · rw [shiftAt_proj hs, keepAt_proj hs, keepAt_proj hs, shiftAt_proj hs,
          keepAt_shiftAt j d p]

omit [ModalSys] in
/-- Keeping twice at one level: the second `keep` lands right after the first, which is where a
    shift at that level inserts it. -/
theorem shiftAt_keepAt : ∀ (i : Nat) (p : List Step),
    shiftAt i (keepAt i p) = keepAt (i + 1) (keepAt i p)
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | i, s :: p => by
      cases hs : s.isProj
      · cases i with
        | zero =>
            change shiftAt 0 (keepAt 0 (s :: p)) = keepAt 1 (keepAt 0 (s :: p))
            have h0 : keepAt 0 (s :: p) = .keep :: s :: p := by simp [keepAt, hs]
            rw [h0, shiftAt_zero (by rfl), keepAt_succ (by rfl), h0]
        | succ i =>
            rw [keepAt_succ hs, shiftAt_succ hs, keepAt_succ hs, shiftAt_keepAt i p]
      · rw [keepAt_proj hs, shiftAt_proj hs, keepAt_proj hs, shiftAt_keepAt i p]

omit [ModalSys] in
/-- A shift at an existing level adds one level step. -/
theorem levels_shiftAt : ∀ (i : Nat) (p : List Step), i < levels p →
    levels (shiftAt i p) = levels p + 1
  | _, [], h => absurd h (Nat.not_lt_zero _)
  | i, s :: p, h => by
      cases hs : s.isProj
      · cases i with
        | zero =>
            rw [shiftAt_zero hs]
            simp only [levels, Step.isProj, Bool.false_eq_true, ↓reduceIte]
            omega
        | succ i =>
            have h' : i < levels p := by
              simp only [levels, hs, Bool.false_eq_true, ↓reduceIte] at h
              omega
            rw [shiftAt_succ hs]
            simp only [levels, hs, Bool.false_eq_true, ↓reduceIte, levels_shiftAt i p h']
            omega
      · have h' : i < levels p := by
          simp only [levels, hs, ↓reduceIte] at h
          omega
        rw [shiftAt_proj hs]
        simp only [levels, hs, ↓reduceIte, levels_shiftAt i p h']
        omega

omit [ModalSys] in
/-- Keeping at a level that exists, or right after the last one, adds one level step. -/
theorem levels_keepAt : ∀ (i : Nat) (p : List Step), i ≤ levels p →
    levels (keepAt i p) = levels p + 1
  | 0, [], _ => rfl
  | _ + 1, [], h => absurd h (by simp [levels])
  | i, s :: p, h => by
      cases hs : s.isProj
      · cases i with
        | zero =>
            have h0 : keepAt 0 (s :: p) = .keep :: s :: p := by simp [keepAt, hs]
            rw [h0]
            simp only [levels, Step.isProj, Bool.false_eq_true, ↓reduceIte]
            omega
        | succ i =>
            have h' : i ≤ levels p := by
              simp only [levels, hs, Bool.false_eq_true, ↓reduceIte] at h
              omega
            rw [keepAt_succ hs]
            simp only [levels, hs, Bool.false_eq_true, ↓reduceIte, levels_keepAt i p h']
            omega
      · have h' : i ≤ levels p := by
          simp only [levels, hs, ↓reduceIte] at h
          omega
        rw [keepAt_proj hs]
        simp only [levels, hs, ↓reduceIte, levels_keepAt i p h']
        omega

omit [ModalSys] in
/-- Collapsing an existing level removes one level step. -/
theorem levels_collapseAt : ∀ (i : Nat) (p : List Step), i < levels p →
    levels (collapseAt i p) + 1 = levels p
  | _, [], h => absurd h (Nat.not_lt_zero _)
  | i, s :: p, h => by
      cases hs : s.isProj
      · cases i with
        | zero =>
            simp only [collapseAt, hs, Bool.false_eq_true, ↓reduceIte]
            split_ifs
            · simp only [levels, hs, Bool.false_eq_true, ↓reduceIte]
              omega
            · rw [Step.levels_cons, Step.levels_cons, hs]
              simp only [Step.isProj, Bool.false_eq_true, ↓reduceIte]
              omega
        | succ i =>
            have h' : i < levels p := by
              simp only [levels, hs, Bool.false_eq_true, ↓reduceIte] at h
              omega
            simp only [collapseAt, hs, Bool.false_eq_true, ↓reduceIte]
            split_ifs
            · simp only [levels, hs, Bool.false_eq_true, ↓reduceIte]
              omega
            · have := levels_collapseAt i p h'
              simp only [levels, hs, Bool.false_eq_true, ↓reduceIte]
              omega
      · have h' : i < levels p := by
          simp only [levels, hs, ↓reduceIte] at h
          omega
        rw [collapseAt_proj hs]
        have := levels_collapseAt i p h'
        simp only [levels, hs, ↓reduceIte]
        omega

omit [ModalSys] in
theorem headLvl_keepAt_succ (i : Nat) : ∀ p : List Step, headLvl (keepAt (i + 1) p) = headLvl p
  | [] => rfl
  | s :: p => by
      cases hs : s.isProj
      · rw [keepAt_succ hs]
        rfl
      · rw [keepAt_proj hs]
        rfl

omit [ModalSys] in
/-- Keeping after collapsing a lower level is collapsing after keeping, on a path with as many
    level steps as its position (`Arrows.Leaf.WF`) — on a shorter one keeping would append. -/
theorem keepAt_collapseAt : ∀ (j d : Nat) (p : List Step), levels p = j + d + 1 →
    keepAt (j + d) (collapseAt j p) = collapseAt j (keepAt (j + d + 1) p)
  | _, _, [], h => by simp [levels] at h
  | j, d, s :: p, h => by
      cases hs : s.isProj
      · have hl : levels p = j + d := by
          simp only [levels, hs, Bool.false_eq_true, ↓reduceIte] at h
          omega
        cases j with
        | zero =>
            rw [Nat.zero_add, keepAt_succ hs, collapseAt_zero hs, collapseAt_zero hs]
            split_ifs
            · rfl
            · exact keepAt_proj rfl d p
        | succ i =>
            rw [show i + 1 + d + 1 = (i + d + 1) + 1 by omega, keepAt_succ hs,
              collapseAt_succ hs, collapseAt_succ hs, headLvl_keepAt_succ (i + d) p]
            split_ifs with hc
            · obtain ⟨rfl, -, -⟩ := hc
              rw [show 0 + 1 + d = 0 + d + 1 by omega]
            · rw [show i + 1 + d = (i + d) + 1 by omega, keepAt_succ hs,
                keepAt_collapseAt i d p (by omega)]
      · have hl : levels p = j + d + 1 := by
          simp only [levels, hs, ↓reduceIte] at h
          omega
        rw [collapseAt_proj hs, keepAt_proj hs, keepAt_proj hs, collapseAt_proj hs,
          keepAt_collapseAt j d p hl]

omit [ModalSys] in
/-- Collapsing a level just kept is the identity. -/
theorem collapseAt_keepAt_self : ∀ (i : Nat) (p : List Step), collapseAt i (keepAt i p) = p
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | i, s :: p => by
      cases hs : s.isProj
      · cases i with
        | zero =>
            have h0 : keepAt 0 (s :: p) = .keep :: s :: p := by simp [keepAt, hs]
            rw [h0, collapseAt_zero (by rfl), if_pos rfl]
        | succ i =>
            rw [keepAt_succ hs, collapseAt_succ hs]
            split_ifs with hc
            · obtain ⟨rfl, rfl, hl⟩ := hc
              cases p with
              | nil => rfl
              | cons t q =>
                  cases ht : t.isProj
                  · have h0 : keepAt 0 (t :: q) = .keep :: t :: q := by simp [keepAt, ht]
                    rw [h0]
                  · have h0 : keepAt 0 (t :: q) = t :: keepAt 0 q := keepAt_proj ht 0 q
                    rw [h0] at hl
                    simp [headLvl, ht] at hl
            · rw [collapseAt_keepAt_self i p]
      · rw [keepAt_proj hs, collapseAt_proj hs, collapseAt_keepAt_self i p]

/-! ### Paths that do not enter a possibility at a `□` level -/

omit [ModalSys] in
theorem BoxOK_nil : ∀ p : List Step, BoxOK [] p
  | [] => trivial
  | s :: p => by
      unfold BoxOK
      split
      · exact BoxOK_nil p
      · exact ⟨(fun h => by cases h), BoxOK_nil p⟩

omit [ModalSys] in
theorem BoxOK_relax : ∀ (lw q : List Bool) (p : List Step),
    BoxOK (lw ++ true :: q) p → BoxOK (lw ++ false :: q) p
  | _, _, [], _ => trivial
  | lw, q, s :: p, h => by
      unfold BoxOK at h ⊢
      split
      · rename_i hs
        rw [if_pos hs] at h
        exact BoxOK_relax lw q p h
      · rename_i hs
        rw [if_neg hs] at h
        cases lw with
        | nil => exact ⟨(fun h' => by cases h'), h.2⟩
        | cons b lw => exact ⟨h.1, BoxOK_relax lw q p h.2⟩

omit [ModalSys] in
theorem BoxOK_append : ∀ (lw q : List Bool) (p r : List Step), levels p = lw.length →
    BoxOK lw p → BoxOK q r → BoxOK (lw ++ q) (p ++ r)
  | lw, q, [], r, hl, _, hr => by
      have : lw = [] := List.eq_nil_of_length_eq_zero hl.symm
      subst this
      exact hr
  | lw, q, s :: p, r, hl, hp, hr => by
      change BoxOK (lw ++ q) (s :: (p ++ r))
      unfold BoxOK at hp ⊢
      rw [levels_cons] at hl
      split
      · rename_i hs
        rw [if_pos hs] at hp hl
        exact BoxOK_append lw q p r (by omega) hp hr
      · rename_i hs
        rw [if_neg hs] at hp hl
        cases lw with
        | nil => simp at hl
        | cons b lw =>
            exact ⟨hp.1, BoxOK_append lw q p r (by simp at hl; omega) hp.2 hr⟩

omit [ModalSys] in
theorem BoxOK_shiftAt : ∀ (j : ℕ) (lw : List Bool) (c : Bool) (q : List Bool) (p : List Step),
    lw.length = j → levels p = j + 1 + q.length → BoxOK (lw ++ c :: q) p →
      BoxOK (lw ++ true :: c :: q) (shiftAt j p)
  | _, _, _, _, [], _, hl, _ => by change 0 = _ at hl; omega
  | j, lw, c, q, s :: p, hj, hl, h => by
      rw [levels_cons] at hl
      by_cases hs : s.isProj = true
      · rw [shiftAt_proj hs]
        unfold BoxOK at h ⊢
        rw [if_pos hs] at h ⊢
        rw [if_pos hs] at hl
        exact BoxOK_shiftAt j lw c q p hj (by omega) h
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        rw [if_neg hs] at hl
        unfold BoxOK at h
        rw [if_neg hs] at h
        cases j with
        | zero =>
            obtain rfl : lw = [] := List.eq_nil_of_length_eq_zero hj
            rw [shiftAt_zero hs']
            unfold BoxOK
            rw [if_neg (by decide)]
            refine ⟨(fun _ => by decide), ?_⟩
            unfold BoxOK
            rw [if_neg hs]
            exact h
        | succ j =>
            cases lw with
            | nil => cases hj
            | cons b lw =>
                rw [shiftAt_succ hs']
                unfold BoxOK
                rw [if_neg hs]
                exact ⟨h.1, BoxOK_shiftAt j lw c q p (by simpa using hj) (by omega) h.2⟩

omit [ModalSys] in
theorem BoxOK_collapseAt : ∀ (j : ℕ) (lw q : List Bool) (p : List Step),
    lw.length = j → levels p = j + 1 + q.length → BoxOK (lw ++ true :: q) p →
      BoxOK (lw ++ q) (collapseAt j p)
  | _, _, _, [], _, hl, _ => by change 0 = _ at hl; omega
  | j, lw, q, s :: p, hj, hl, h => by
      rw [levels_cons] at hl
      by_cases hs : s.isProj = true
      · rw [collapseAt_proj hs]
        unfold BoxOK at h ⊢
        rw [if_pos hs] at h ⊢
        rw [if_pos hs] at hl
        exact BoxOK_collapseAt j lw q p hj (by omega) h
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        rw [if_neg hs] at hl
        unfold BoxOK at h
        rw [if_neg hs] at h
        cases j with
        | zero =>
            obtain rfl : lw = [] := List.eq_nil_of_length_eq_zero hj
            rw [collapseAt_zero hs']
            split
            · exact h.2
            · unfold BoxOK
              rw [if_pos (show Step.here.isProj = true from rfl)]
              exact h.2
        | succ j =>
            cases lw with
            | nil => cases hj
            | cons b lw =>
                rw [collapseAt_succ hs']
                split
                · rename_i hsp
                  obtain ⟨rfl, rfl, hh⟩ := hsp
                  obtain rfl : lw = [] := List.eq_nil_of_length_eq_zero (by simpa using hj)
                  match p, hh, h with
                  | t :: p', hh, h =>
                      have ht : t.isProj = false := by simpa [headLvl] using hh
                      have h2 := h.2
                      unfold BoxOK at h2 ⊢
                      rw [if_neg (by simp [ht])] at h2 ⊢
                      exact ⟨fun _ => h2.1 rfl, h2.2⟩
                · unfold BoxOK
                  rw [if_neg hs]
                  exact ⟨h.1, BoxOK_collapseAt j lw q p (by simpa using hj) (by omega) h.2⟩

omit [ModalSys] in
theorem keepAt_own : ∀ (p : List Step) (m : ℕ), levels p = m → keepAt m p = p ++ [.keep]
  | [], m, h => by
      change 0 = m at h
      subst h
      rfl
  | s :: p, m, h => by
      change (if s.isProj then 0 else 1) + levels p = m at h
      by_cases hs : s.isProj = true
      · rw [if_pos hs, Nat.zero_add] at h
        cases m <;> simp only [keepAt, hs, if_true, List.cons_append] <;>
          rw [keepAt_own p _ h]
      · rw [if_neg hs] at h
        obtain rfl : m = levels p + 1 := by omega
        simp only [keepAt, hs, Bool.false_eq_true, if_false, List.cons_append]
        rw [keepAt_own p _ rfl]

omit [ModalSys] in
theorem BoxOK_keepAt : ∀ (lw : List Bool) (p : List Step), levels p = lw.length →
    BoxOK lw p → BoxOK (lw ++ [true]) (keepAt lw.length p) := fun lw p hl h => by
  rw [keepAt_own p _ hl]
  refine BoxOK_append lw [true] p [.keep] hl h ?_
  unfold BoxOK
  rw [if_neg (by decide)]
  exact ⟨(fun _ => by decide), trivial⟩

omit [ModalSys] in
theorem BoxOK_snoc_proj (lw : List Bool) (p : List Step) (s : Step) (hl : levels p = lw.length)
    (hp : BoxOK lw p) : BoxOK lw (p ++ [s]) := by
  have := BoxOK_append lw [] p [s] hl hp (BoxOK_nil _)
  simpa using this

omit [ModalSys] in
theorem BoxOK_snoc_dia (lw : List Bool) (p : List Step) (hl : levels p = lw.length)
    (hp : BoxOK lw p) : BoxOK (lw ++ [false]) (p ++ [.dia]) :=
  BoxOK_append lw [false] p [.dia] hl hp (by
    unfold BoxOK
    rw [if_neg (by decide)]
    exact ⟨(fun h => by cases h), trivial⟩)

/-- The path spelling a position's kinds: `keep` at a `□` level, `dia` at a `◇` level. -/
def kindPath (lw : List Bool) : List Step := lw.map fun b => if b then Step.keep else Step.dia

omit [ModalSys] in
theorem levels_kindPath : ∀ lw : List Bool, levels (kindPath lw) = lw.length
  | [] => rfl
  | b :: lw => by
      change levels ((if b then Step.keep else Step.dia) :: kindPath lw) = _
      rw [levels_cons, levels_kindPath lw]
      cases b <;> simp [Step.isProj] <;> omega

omit [ModalSys] in
theorem BoxOK_kindPath : ∀ lw : List Bool, BoxOK lw (kindPath lw)
  | [] => trivial
  | b :: lw => by
      change BoxOK (b :: lw) ((if b then Step.keep else Step.dia) :: kindPath lw)
      unfold BoxOK
      cases b
      · rw [if_neg (by decide)]
        exact ⟨(fun h => by cases h), BoxOK_kindPath lw⟩
      · rw [if_neg (by decide)]
        exact ⟨(fun _ => by decide), BoxOK_kindPath lw⟩

end Step

namespace Arrows.Leaf

variable {σ : Signature} {F : Arrows.{u, v} σ} {Root : F.W → Type u}

theorem collapse_root (hT : ModalSys.T = true) (i : ℕ) {w : F.W} (r : Root w) (p : List Step) :
    collapse hT i (Arrows.Leaf.root (F := F) r p) = .root r (Step.collapseAt i p) := by
  cases i <;> rfl

theorem shift_root (hF : ModalSys.Four = true) (i : ℕ) {w : F.W} (r : Root w) (p : List Step) :
    shift hF i (Arrows.Leaf.root (F := F) r p) = .root r (Step.shiftAt i p) := by
  cases i <;> rfl

theorem collapse_collapse (hT : ModalSys.T = true) :
    ∀ (j d : ℕ) {w : F.W} (ℓ : F.Leaf Root w),
      collapse hT (j + d) (collapse hT j ℓ) = collapse hT j (collapse hT (j + d + 1) ℓ)
  | j, d, _, .root r p => by
      simp only [collapse_root]
      exact congrArg (Arrows.Leaf.root r) (Step.collapseAt_collapseAt j d p)
  | 0, d, w, .fam f => by
      rw [Nat.zero_add]
      rfl
  | j + 1, d, _, .fam f => by
      rw [show j + 1 + d = (j + d) + 1 by omega]
      exact congrArg Arrows.Leaf.fam (funext fun s => collapse_collapse hT j d (f s))

theorem shift_collapse (hT : ModalSys.T = true) (hF : ModalSys.Four = true) :
    ∀ (j d : ℕ) {w : F.W} (ℓ : F.Leaf Root w),
      shift hF (j + d) (collapse hT j ℓ) = collapse hT j (shift hF (j + d + 1) ℓ)
  | j, d, _, .root r p => by
      simp only [collapse_root, shift_root]
      exact congrArg (Arrows.Leaf.root r) (Step.shiftAt_collapseAt j d p)
  | 0, d, w, .fam f => by
      rw [Nat.zero_add]
      rfl
  | j + 1, d, _, .fam f => by
      rw [show j + 1 + d = (j + d) + 1 by omega]
      exact congrArg Arrows.Leaf.fam (funext fun s => shift_collapse hT hF j d (f s))

theorem collapse_shift_self (hT : ModalSys.T = true) (hF : ModalSys.Four = true) :
    ∀ (j : ℕ) {w : F.W} (ℓ : F.Leaf Root w), collapse hT j (shift hF j ℓ) = ℓ
  | j, _, .root r p => by
      simp only [collapse_root, shift_root]
      exact congrArg (Arrows.Leaf.root r) (Step.collapseAt_shiftAt_self j p)
  | 0, w, .fam f => by
      refine congrArg Arrows.Leaf.fam (funext fun t => ?_)
      change f ⟨t.1, ⟨F.trans hF (F.refl hT w) t.2.down⟩⟩ = f t
      rw [F.refl_trans hT hF]
  | j + 1, _, .fam f =>
      congrArg Arrows.Leaf.fam (funext fun s => collapse_shift_self hT hF j (f s))

/-- ⭐The second counit: keeping, then reading the next level where it was kept, is the identity
    — on families by `trans_refl`, on root paths by `Step.collapseAt`'s keep-absorbing case. -/
theorem collapse_shift_succ (hT : ModalSys.T = true) (hF : ModalSys.Four = true) :
    ∀ (j : ℕ) {w : F.W} (ℓ : F.Leaf Root w), collapse hT (j + 1) (shift hF j ℓ) = ℓ
  | j, _, .root r p => by
      simp only [collapse_root, shift_root]
      exact congrArg (Arrows.Leaf.root r) (Step.collapseAt_shiftAt_succ j p)
  | 0, w, .fam f => by
      refine congrArg Arrows.Leaf.fam (funext fun s => ?_)
      change f ⟨s.1, ⟨F.trans hF s.2.down (F.refl hT s.1)⟩⟩ = f s
      rw [F.trans_refl hT hF]
  | j + 1, _, .fam f =>
      congrArg Arrows.Leaf.fam (funext fun s => collapse_shift_succ hT hF j (f s))

theorem collapse_shift (hT : ModalSys.T = true) (hF : ModalSys.Four = true) :
    ∀ (j d : ℕ) {w : F.W} (ℓ : F.Leaf Root w),
      collapse hT (j + d + 2) (shift hF j ℓ) = shift hF j (collapse hT (j + d + 1) ℓ)
  | j, d, _, .root r p => by
      simp only [collapse_root, shift_root]
      exact congrArg (Arrows.Leaf.root r) (Step.collapseAt_shiftAt j d p)
  | 0, d, w, .fam f => by
      rw [Nat.zero_add]
      rfl
  | j + 1, d, _, .fam f => by
      rw [show j + 1 + d + 2 = (j + d + 2) + 1 by omega,
        show j + 1 + d + 1 = (j + d + 1) + 1 by omega]
      exact congrArg Arrows.Leaf.fam (funext fun s => collapse_shift hT hF j d (f s))

theorem shift_shift (hF : ModalSys.Four = true) :
    ∀ (j d : ℕ) {w : F.W} (ℓ : F.Leaf Root w),
      shift hF (j + d + 2) (shift hF j ℓ) = shift hF j (shift hF (j + d + 1) ℓ)
  | j, d, _, .root r p => by
      simp only [shift_root]
      exact congrArg (Arrows.Leaf.root r) (Step.shiftAt_shiftAt j d p)
  | 0, d, w, .fam f => by
      rw [Nat.zero_add]
      rfl
  | j + 1, d, _, .fam f => by
      rw [show j + 1 + d + 2 = (j + d + 2) + 1 by omega,
        show j + 1 + d + 1 = (j + d + 1) + 1 by omega]
      exact congrArg Arrows.Leaf.fam (funext fun s => shift_shift hF j d (f s))

theorem shift_shift_self (hF : ModalSys.Four = true) :
    ∀ (j : ℕ) {w : F.W} (ℓ : F.Leaf Root w),
      shift hF (j + 1) (shift hF j ℓ) = shift hF j (shift hF j ℓ)
  | j, _, .root r p => by
      simp only [shift_root]
      exact congrArg (Arrows.Leaf.root r) (Step.shiftAt_shiftAt_self j p)
  | 0, w, .fam f => by
      refine congrArg Arrows.Leaf.fam (funext fun s => congrArg Arrows.Leaf.fam
        (funext fun t => congrArg Arrows.Leaf.fam (funext fun t' => ?_)))
      change f ⟨t'.1, ⟨F.trans hF s.2.down (F.trans hF t.2.down t'.2.down)⟩⟩ =
        f ⟨t'.1, ⟨F.trans hF (F.trans hF s.2.down t.2.down) t'.2.down⟩⟩
      rw [F.trans_assoc hF]
  | j + 1, _, .fam f =>
      congrArg Arrows.Leaf.fam (funext fun s => shift_shift_self hF j (f s))

section Keep

variable [Arrows.RootKeep F Root]

theorem dk_root_succ (hF : ModalSys.Four = true) (i : ℕ) {w : F.W} (r : Root w)
    (p : List Step) :
    dk hF (i + 1) (Arrows.Leaf.root (F := F) r p) = .root r (Step.keepAt (i + 1) p) :=
  rfl

/-- ⭐Keeping a possibility below a shifted level: `dk` and `shift` commute, `dk` moving one level
    down.  It never acts at the anchor's level here, so no law of the root action is needed. -/
theorem dk_shift (hF : ModalSys.Four = true) :
    ∀ (j d : ℕ) {w : F.W} (ℓ : F.Leaf Root w),
      dk hF (j + d + 2) (shift hF j ℓ) = shift hF j (dk hF (j + d + 1) ℓ)
  | j, d, _, .root r p => by
      rw [shift_root, show j + d + 2 = j + d + 1 + 1 by omega, dk_root_succ hF (j + d + 1),
        dk_root_succ hF (j + d), shift_root, show j + d + 1 + 1 = j + d + 2 by omega]
      exact congrArg (Arrows.Leaf.root r) (Step.keepAt_shiftAt j d p)
  | 0, d, w, .fam f => by
      rw [Nat.zero_add]
      rfl
  | j + 1, d, _, .fam f => by
      rw [show j + 1 + d + 2 = (j + d + 2) + 1 by omega,
        show j + 1 + d + 1 = (j + d + 1) + 1 by omega]
      exact congrArg Arrows.Leaf.fam (funext fun s => dk_shift hF j d (f s))

theorem dkB_root_succ (hF : ModalSys.Four = true) (i : ℕ) {w : F.W} (r : Root w)
    (p : List Step) :
    dkB hF (i + 1) (Arrows.Leaf.root (F := F) r p) = .root r (Step.shiftAt (i + 1) p) :=
  rfl

/-- Keeping inside a possibility below a shifted level: `dkB` and `shift` commute, `dkB` moving
    one level down. -/
theorem dkB_shift (hF : ModalSys.Four = true) :
    ∀ (j d : ℕ) {w : F.W} (ℓ : F.Leaf Root w),
      dkB hF (j + d + 2) (shift hF j ℓ) = shift hF j (dkB hF (j + d + 1) ℓ)
  | j, d, _, .root r p => by
      rw [shift_root, show j + d + 2 = j + d + 1 + 1 by omega, dkB_root_succ hF (j + d + 1),
        dkB_root_succ hF (j + d), shift_root, show j + d + 1 + 1 = j + d + 2 by omega]
      exact congrArg (Arrows.Leaf.root r) (Step.shiftAt_shiftAt j d p)
  | 0, d, w, .fam f => by
      rw [Nat.zero_add]
      rfl
  | j + 1, d, _, .fam f => by
      rw [show j + 1 + d + 2 = (j + d + 2) + 1 by omega,
        show j + 1 + d + 1 = (j + d + 1) + 1 by omega]
      exact congrArg Arrows.Leaf.fam (funext fun s => dkB_shift hF j d (f s))


variable [Arrows.RootKeepLaws F Root]

/-- Restricting a leaf along two arrows is restricting it along their composite. -/
theorem keepAlong_comp (hF : ModalSys.Four = true) {w : F.W} (v : F.Acc w) (s : F.Acc v.1)
    (ℓ : F.Leaf Root w) :
    keepAlong hF s (keepAlong hF v ℓ) =
      keepAlong hF ⟨s.1, ⟨F.trans hF v.2.down s.2.down⟩⟩ ℓ := by
  cases ℓ with
  | root r p => exact Arrows.RootKeepLaws.keep_trans hF r v s p
  | fam f =>
      refine congrArg Arrows.Leaf.fam (funext fun t => ?_)
      change f ⟨t.1, ⟨F.trans hF v.2.down (F.trans hF s.2.down t.2.down)⟩⟩ =
        f ⟨t.1, ⟨F.trans hF (F.trans hF v.2.down s.2.down) t.2.down⟩⟩
      rw [F.trans_assoc hF]

/-- Under T, restricting a leaf along the identity is the leaf. -/
theorem keepAlong_refl (hT : ModalSys.T = true) (hF : ModalSys.Four = true) {w : F.W}
    (ℓ : F.Leaf Root w) : keepAlong hF (F.reflAcc hT w) ℓ = ℓ := by
  cases ℓ with
  | root r p => exact Arrows.RootKeepLaws.keep_refl hT hF r p
  | fam f =>
      refine congrArg Arrows.Leaf.fam (funext fun t => ?_)
      change f ⟨t.1, ⟨F.trans hF (F.refl hT w) t.2.down⟩⟩ = f t
      rw [F.refl_trans hT hF]

/-- ⭐**Keeping a kept possibility**: keeping again at the next level is shifting at this one —
    at the anchor's level by the root action's composition law, below it by path arithmetic. -/
theorem shift_dk (hF : ModalSys.Four = true) :
    ∀ (j : ℕ) {w : F.W} (ℓ : F.Leaf Root w),
      shift hF j (dk hF j ℓ) = dk hF (j + 1) (dk hF j ℓ)
  | 0, _, ℓ =>
      congrArg Arrows.Leaf.fam (funext fun s => congrArg Arrows.Leaf.fam (funext fun t =>
        (keepAlong_comp hF s t ℓ).symm))
  | j + 1, _, .root r p => by
      rw [dk_root_succ hF j, shift_root, dk_root_succ hF (j + 1)]
      exact congrArg (Arrows.Leaf.root r) (Step.shiftAt_keepAt (j + 1) p)
  | j + 1, _, .fam f =>
      congrArg Arrows.Leaf.fam (funext fun s => shift_dk hF j (f s))

/-- Keeping the inside of a kept possibility again at the next level is shifting it at this one. -/
theorem shift_dkB (hF : ModalSys.Four = true) :
    ∀ (j : ℕ) {w : F.W} (ℓ : F.Leaf Root w),
      shift hF j (dkB hF j ℓ) = dkB hF (j + 1) (dkB hF j ℓ)
  | 0, _, ℓ =>
      congrArg Arrows.Leaf.fam (funext fun s => congrArg Arrows.Leaf.fam (funext fun t =>
        (keepAlong_comp hF s t ℓ).symm))
  | j + 1, _, .root r p => by
      rw [dkB_root_succ hF j, shift_root, dkB_root_succ hF (j + 1)]
      exact congrArg (Arrows.Leaf.root r) (Step.shiftAt_shiftAt_self (j + 1) p).symm
  | j + 1, _, .fam f =>
      congrArg Arrows.Leaf.fam (funext fun s => shift_dkB hF j (f s))

/-- Under T, reading a kept possibility's label at the current world gives it back. -/
theorem collapse_dk_self (hT : ModalSys.T = true) (hF : ModalSys.Four = true) :
    ∀ (j : ℕ) {w : F.W} (ℓ : F.Leaf Root w), collapse hT j (dk hF j ℓ) = ℓ
  | 0, _, ℓ => keepAlong_refl hT hF ℓ
  | j + 1, _, .root r p => congrArg (Arrows.Leaf.root r) (Step.collapseAt_keepAt_self (j + 1) p)
  | j + 1, _, .fam f => congrArg Arrows.Leaf.fam (funext fun s => collapse_dk_self hT hF j (f s))

/-- Under T, reading the kept inside of a possibility at the current world gives it back. -/
theorem collapse_dkB_self (hT : ModalSys.T = true) (hF : ModalSys.Four = true) :
    ∀ (j : ℕ) {w : F.W} (ℓ : F.Leaf Root w), collapse hT j (dkB hF j ℓ) = ℓ
  | 0, _, ℓ => keepAlong_refl hT hF ℓ
  | j + 1, _, .root r p => congrArg (Arrows.Leaf.root r) (Step.collapseAt_shiftAt_self (j + 1) p)
  | j + 1, _, .fam f =>
      congrArg Arrows.Leaf.fam (funext fun s => collapse_dkB_self hT hF j (f s))

end Keep

/-! ### Well-formed leaves (docs §3 4, "T + 4") -/

theorem wf_root {lw : List Bool} {w : F.W} (r : Root w) (p : List Step) :
    Arrows.Leaf.WF lw (Arrows.Leaf.root (F := F) r p) ↔
      Step.levels p = lw.length ∧ lw.head? ≠ some true ∧ Step.BoxOK lw p := by
  cases lw <;> rfl

/-- Turning a `□` of the position into a `◇` keeps a leaf well-formed: only the head of a
    position asks anything of its kind. -/
theorem wf_relax : ∀ (lw q : List Bool) {w : F.W} (ℓ : F.Leaf Root w),
    Arrows.Leaf.WF (lw ++ true :: q) ℓ → Arrows.Leaf.WF (lw ++ false :: q) ℓ
  | lw, q, _, .root r p, h => by
      rw [wf_root] at h ⊢
      refine ⟨by simpa using h.1, ?_, Step.BoxOK_relax lw q p h.2.2⟩
      cases lw with
      | nil => simp
      | cons c lw => simpa using h.2.1
  | [], _, _, .fam _, h => h
  | _ :: lw, q, _, .fam f, h => fun s => wf_relax lw q (f s) (h s)

/-- Under T, collapsing a level keeps a leaf well-formed, one level shorter. -/
theorem wf_collapse (hT : ModalSys.T = true) : ∀ (lw q : List Bool) {w : F.W}
    (ℓ : F.Leaf Root w), Arrows.Leaf.WF (lw ++ true :: q) ℓ →
      Arrows.Leaf.WF (lw ++ q) (collapse hT lw.length ℓ)
  | lw, q, _, .root r p, h => by
      rw [wf_root] at h
      rw [collapse_root, wf_root]
      have hl := Step.levels_collapseAt lw.length p (by rw [h.1]; simp)
      refine ⟨by rw [h.1] at hl; simp at hl; simp; omega, ?_,
        Step.BoxOK_collapseAt lw.length lw q p rfl (by rw [h.1]; simp; omega) h.2.2⟩
      cases lw with
      | nil => exact absurd rfl h.2.1
      | cons c lw => simpa using h.2.1
  | [], q, w, .fam f, h => h (F.reflAcc hT w)
  | _ :: lw, q, _, .fam f, h => fun s => wf_collapse hT lw q (f s) (h s)

/-- Under 4, shifting a level keeps a leaf well-formed, one level longer. -/
theorem wf_shift (hF : ModalSys.Four = true) : ∀ (lw q : List Bool) {w : F.W}
    (ℓ : F.Leaf Root w), Arrows.Leaf.WF (lw ++ true :: q) ℓ →
      Arrows.Leaf.WF (lw ++ true :: true :: q) (shift hF lw.length ℓ)
  | lw, q, _, .root r p, h => by
      rw [wf_root] at h
      have hb := Step.BoxOK_shiftAt lw.length lw true q p rfl (by rw [h.1]; simp; omega) h.2.2
      rw [shift_root, wf_root, Step.levels_shiftAt lw.length p (by rw [h.1]; simp), h.1]
      refine ⟨by simp; omega, ?_, hb⟩
      cases lw with
      | nil => exact absurd rfl h.2.1
      | cons c lw => simpa using h.2.1
  | [], q, _, .fam f, h => fun s t => h _
  | _ :: lw, q, _, .fam f, h => fun s => wf_shift hF lw q (f s) (h s)

section KeepWF

variable [Arrows.RootKeep F Root] [Arrows.RootKeepLaws F Root]

/-- Restricting a leaf along an arrow keeps it well-formed at the same position. -/
theorem wf_keepAlong (hF : ModalSys.Four = true) : ∀ (lw : List Bool) {w : F.W}
    (s : F.Acc w) (ℓ : F.Leaf Root w), Arrows.Leaf.WF lw ℓ →
      Arrows.Leaf.WF lw (keepAlong hF s ℓ)
  | lw, _, _, .root r p, h => Arrows.RootKeepLaws.keep_wf hF r _ lw p h
  | [], _, _, .fam _, h => fun _ => h _
  | _ :: _, _, _, .fam _, h => fun _ => h _

/-- ⭐Keeping a possibility's label: well-formed one `□` further down. -/
theorem wf_dk (hF : ModalSys.Four = true) : ∀ (lw : List Bool) {w : F.W} (ℓ : F.Leaf Root w),
    Arrows.Leaf.WF lw ℓ → Arrows.Leaf.WF (lw ++ [true]) (dk hF lw.length ℓ)
  | [], _, ℓ, h => fun s => wf_keepAlong hF [] s ℓ h
  | c :: lw, _, .root r p, h => by
      rw [wf_root] at h
      change Arrows.Leaf.WF (c :: lw ++ [true])
        (Arrows.Leaf.root r (Step.keepAt (lw.length + 1) p))
      have hb := Step.BoxOK_keepAt (c :: lw) p h.1 h.2.2
      rw [wf_root, Step.levels_keepAt (lw.length + 1) p (by rw [h.1]; simp), h.1]
      exact ⟨by simp, by simpa using h.2.1, hb⟩
  | _ :: lw, _, .fam f, h => fun s => wf_dk hF lw (f s) (h s)

/-- ⭐Keeping the inside of a possibility: well-formed with a `□` inserted before its `◇`. -/
theorem wf_dkB (hF : ModalSys.Four = true) : ∀ (lw q : List Bool) {w : F.W}
    (ℓ : F.Leaf Root w), Arrows.Leaf.WF (lw ++ false :: q) ℓ →
      Arrows.Leaf.WF (lw ++ true :: false :: q) (dkB hF lw.length ℓ)
  | [], q, _, ℓ, h => fun s => wf_keepAlong hF (false :: q) s ℓ h
  | c :: lw, q, _, .root r p, h => by
      rw [wf_root] at h
      change Arrows.Leaf.WF (c :: lw ++ true :: false :: q)
        (Arrows.Leaf.root r (Step.shiftAt (lw.length + 1) p))
      have hb := Step.BoxOK_shiftAt (lw.length + 1) (c :: lw) false q p rfl
        (by rw [h.1]; simp; omega) h.2.2
      rw [wf_root, Step.levels_shiftAt (lw.length + 1) p (by rw [h.1]; simp), h.1]
      exact ⟨by simp; omega, by simpa using h.2.1, hb⟩
  | _ :: lw, q, _, .fam f, h => fun s => wf_dkB hF lw q (f s) (h s)

omit [Arrows.RootKeepLaws F Root] in
/-- ⭐On a well-formed leaf under a `□` at level `j`, keeping the inside of a possibility is a
    shift: at the anchor's level the leaf is a family, below it both insert before the level
    step. -/
theorem dkB_eq_shift (hF : ModalSys.Four = true) : ∀ (lw q : List Bool) {w : F.W}
    (ℓ : F.Leaf Root w), Arrows.Leaf.WF (lw ++ true :: q) ℓ →
      dkB hF lw.length ℓ = shift hF lw.length ℓ
  | [], q, _, .root r p, h => by
      rw [wf_root] at h
      exact absurd rfl h.2.1
  | [], _, _, .fam _, _ => rfl
  | _ :: _, _, _, .root _ _, _ => rfl
  | _ :: lw, q, _, .fam f, h =>
      congrArg Arrows.Leaf.fam (funext fun s => dkB_eq_shift hF lw q (f s) (h s))

omit [Arrows.RootKeepLaws F Root] in
/-- Under T, keeping a possibility's label after collapsing a lower level is collapsing after
    keeping, on a well-formed leaf whose position crosses a `□` at the collapsed level. -/
theorem dk_collapse (hT : ModalSys.T = true) (hF : ModalSys.Four = true) :
    ∀ (lw q : List Bool) {w : F.W} (ℓ : F.Leaf Root w), Arrows.Leaf.WF (lw ++ true :: q) ℓ →
      dk hF (lw.length + q.length) (collapse hT lw.length ℓ) =
        collapse hT lw.length (dk hF (lw.length + q.length + 1) ℓ)
  | [], _, _, .root r p, h => by
      rw [wf_root] at h
      exact absurd rfl h.2.1
  | [], q, _, .fam f, _ => by
      simp only [List.length_nil, Nat.zero_add]
      rfl
  | c :: lw, q, _, .root r p, h => by
      rw [wf_root] at h
      have e : (c :: lw).length + q.length = (lw.length + q.length) + 1 := by simp; omega
      rw [e, collapse_root, dk_root_succ, dk_root_succ, collapse_root]
      congr 1
      rw [← e]
      exact Step.keepAt_collapseAt _ _ p (by rw [h.1]; simp; omega)
  | c :: lw, q, _, .fam f, h => by
      have e : (c :: lw).length + q.length = (lw.length + q.length) + 1 := by simp; omega
      rw [e]
      exact congrArg Arrows.Leaf.fam (funext fun s => dk_collapse hT hF lw q (f s) (h s))

omit [Arrows.RootKeepLaws F Root] in
/-- Under T, keeping the inside of a possibility after collapsing a lower level is collapsing
    after keeping; at the anchor's level the leaf is a family. -/
theorem dkB_collapse (hT : ModalSys.T = true) (hF : ModalSys.Four = true) :
    ∀ (lw q : List Bool) (d : ℕ) {w : F.W} (ℓ : F.Leaf Root w),
      Arrows.Leaf.WF (lw ++ true :: q) ℓ →
      dkB hF (lw.length + d) (collapse hT lw.length ℓ) =
        collapse hT lw.length (dkB hF (lw.length + d + 1) ℓ)
  | [], _, _, _, .root r p, h => by
      rw [wf_root] at h
      exact absurd rfl h.2.1
  | [], q, d, _, .fam f, _ => by
      simp only [List.length_nil, Nat.zero_add]
      rfl
  | c :: lw, q, d, _, .root r p, _ => by
      have e : (c :: lw).length + d = (lw.length + d) + 1 := by simp; omega
      rw [e, collapse_root, dkB_root_succ, dkB_root_succ, collapse_root]
      congr 1
      rw [← e]
      exact Step.shiftAt_collapseAt _ _ p
  | c :: lw, q, d, _, .fam f, h => by
      have e : (c :: lw).length + d = (lw.length + d) + 1 := by simp; omega
      rw [e]
      exact congrArg Arrows.Leaf.fam (funext fun s => dkB_collapse hT hF lw q d (f s) (h s))

/-! Keeping the inside of a possibility at level `j` inserts a level there: on a well-formed leaf
it commutes with every operation acting below it, as a shift does — at the anchor's level by the
root action's naturality (`Arrows.RootKeepLaws`), below it by path arithmetic. -/

theorem collapse_dkB (hT : ModalSys.T = true) (hF : ModalSys.Four = true) :
    ∀ (j d : ℕ) (lw q r : List Bool) {w : F.W} (ℓ : F.Leaf Root w), lw.length = j →
      q.length = d → Arrows.Leaf.WF (lw ++ false :: q ++ true :: r) ℓ →
      collapse hT (j + d + 2) (dkB hF j ℓ) = dkB hF j (collapse hT (j + d + 1) ℓ)
  | 0, _, lw, q, r, _, .root r' p, hl, hq, h => by
      obtain rfl : lw = [] := List.eq_nil_of_length_eq_zero hl
      subst hq
      rw [Nat.zero_add]
      exact congrArg Arrows.Leaf.fam (funext fun s =>
        (Arrows.RootKeepLaws.keep_collapseAt hT hF r' s false q r p h).symm)
  | 0, d, _, _, _, _, .fam f, _, _, _ => by
      rw [Nat.zero_add]
      rfl
  | j + 1, d, _, _, _, _, .root r p, _, _, _ => by
      simp only [dkB_root_succ, collapse_root]
      exact congrArg (Arrows.Leaf.root r) (Step.collapseAt_shiftAt (j + 1) d p)
  | j + 1, d, [], _, _, _, .fam _, hl, _, _ => by cases hl
  | j + 1, d, _ :: lw, q, r, _, .fam f, hl, hq, h => by
      rw [show j + 1 + d + 2 = (j + d + 2) + 1 by omega,
        show j + 1 + d + 1 = (j + d + 1) + 1 by omega]
      exact congrArg Arrows.Leaf.fam (funext fun s =>
        collapse_dkB hT hF j d lw q r (f s) (by simpa using hl) hq (h s))

theorem shift_dkB_far (hF : ModalSys.Four = true) :
    ∀ (j d : ℕ) (lw q r : List Bool) {w : F.W} (ℓ : F.Leaf Root w), lw.length = j →
      q.length = d → Arrows.Leaf.WF (lw ++ false :: q ++ true :: r) ℓ →
      shift hF (j + d + 2) (dkB hF j ℓ) = dkB hF j (shift hF (j + d + 1) ℓ)
  | 0, _, lw, q, r, _, .root r' p, hl, hq, h => by
      obtain rfl : lw = [] := List.eq_nil_of_length_eq_zero hl
      subst hq
      rw [Nat.zero_add]
      refine congrArg Arrows.Leaf.fam (funext fun s => ?_)
      have hr : Arrows.Leaf.WF (false :: q ++ false :: r) (Arrows.Leaf.root (F := F) r' p) :=
        wf_relax (false :: q) r _ h
      change shift hF (q.length + 1) (Arrows.RootKeep.keep hF r' s p) =
        Arrows.RootKeep.keep hF r' s (Step.shiftAt (q.length + 1) p)
      rw [Arrows.RootKeepLaws.keep_shiftAt hF r' s false q r p hr]
      exact (dkB_eq_shift hF (false :: q) r _ (wf_keepAlong hF _ s _ h)).symm
  | 0, d, _, _, _, _, .fam f, _, _, _ => by
      rw [Nat.zero_add]
      rfl
  | j + 1, d, _, _, _, _, .root r p, _, _, _ => by
      simp only [dkB_root_succ, shift_root]
      exact congrArg (Arrows.Leaf.root r) (Step.shiftAt_shiftAt (j + 1) d p)
  | j + 1, d, [], _, _, _, .fam _, hl, _, _ => by cases hl
  | j + 1, d, _ :: lw, q, r, _, .fam f, hl, hq, h => by
      rw [show j + 1 + d + 2 = (j + d + 2) + 1 by omega,
        show j + 1 + d + 1 = (j + d + 1) + 1 by omega]
      exact congrArg Arrows.Leaf.fam (funext fun s =>
        shift_dkB_far hF j d lw q r (f s) (by simpa using hl) hq (h s))

theorem dk_dkB (hF : ModalSys.Four = true) :
    ∀ (j d : ℕ) (lw q : List Bool) {w : F.W} (ℓ : F.Leaf Root w), lw.length = j →
      q.length = d → Arrows.Leaf.WF (lw ++ false :: q) ℓ →
      dk hF (j + d + 2) (dkB hF j ℓ) = dkB hF j (dk hF (j + d + 1) ℓ)
  | 0, _, lw, q, _, .root r' p, hl, hq, h => by
      obtain rfl : lw = [] := List.eq_nil_of_length_eq_zero hl
      subst hq
      rw [Nat.zero_add]
      exact congrArg Arrows.Leaf.fam (funext fun s =>
        (Arrows.RootKeepLaws.keep_keepAt hF r' s false q p h).symm)
  | 0, d, _, _, _, .fam f, _, _, _ => by
      rw [Nat.zero_add]
      rfl
  | j + 1, d, _, _, _, .root r p, _, _, _ => by
      rw [dkB_root_succ hF j, show j + 1 + d + 2 = (j + 1 + d + 1) + 1 by omega,
        dk_root_succ hF (j + 1 + d + 1), dk_root_succ hF (j + 1 + d), dkB_root_succ hF j,
        show j + 1 + d + 1 + 1 = (j + 1) + d + 2 by omega]
      exact congrArg (Arrows.Leaf.root r) (Step.keepAt_shiftAt (j + 1) d p)
  | j + 1, d, [], _, _, .fam _, hl, _, _ => by cases hl
  | j + 1, d, _ :: lw, q, _, .fam f, hl, hq, h => by
      rw [show j + 1 + d + 2 = (j + d + 2) + 1 by omega,
        show j + 1 + d + 1 = (j + d + 1) + 1 by omega]
      exact congrArg Arrows.Leaf.fam (funext fun s =>
        dk_dkB hF j d lw q (f s) (by simpa using hl) hq (h s))

theorem dkB_dkB (hF : ModalSys.Four = true) :
    ∀ (j d : ℕ) (lw q r : List Bool) {w : F.W} (ℓ : F.Leaf Root w), lw.length = j →
      q.length = d → Arrows.Leaf.WF (lw ++ false :: q ++ false :: r) ℓ →
      dkB hF (j + d + 2) (dkB hF j ℓ) = dkB hF j (dkB hF (j + d + 1) ℓ)
  | 0, _, lw, q, r, _, .root r' p, hl, hq, h => by
      obtain rfl : lw = [] := List.eq_nil_of_length_eq_zero hl
      subst hq
      rw [Nat.zero_add]
      exact congrArg Arrows.Leaf.fam (funext fun s =>
        (Arrows.RootKeepLaws.keep_shiftAt hF r' s false q r p h).symm)
  | 0, d, _, _, _, _, .fam f, _, _, _ => by
      rw [Nat.zero_add]
      rfl
  | j + 1, d, _, _, _, _, .root r p, _, _, _ => by
      rw [dkB_root_succ hF j, show j + 1 + d + 2 = (j + 1 + d + 1) + 1 by omega,
        dkB_root_succ hF (j + 1 + d + 1), dkB_root_succ hF (j + 1 + d), dkB_root_succ hF j,
        show j + 1 + d + 1 + 1 = (j + 1) + d + 2 by omega]
      exact congrArg (Arrows.Leaf.root r) (Step.shiftAt_shiftAt (j + 1) d p)
  | j + 1, d, [], _, _, _, .fam _, hl, _, _ => by cases hl
  | j + 1, d, _ :: lw, q, r, _, .fam f, hl, hq, h => by
      rw [show j + 1 + d + 2 = (j + d + 2) + 1 by omega,
        show j + 1 + d + 1 = (j + d + 1) + 1 by omega]
      exact congrArg Arrows.Leaf.fam (funext fun s =>
        dkB_dkB hF j d lw q r (f s) (by simpa using hl) hq (h s))

end KeepWF

end Arrows.Leaf

namespace Model

variable {σ : Signature} {F : Arrows.{u, v} σ} {Root : F.W → Type u}
  [Arrows.RootKeep F Root] [Arrows.RootKeepLaws F Root]

variable (F Root) in
/-- Shapes anchored at a world. -/
abbrev Shape (w : F.W) (T : VarType) : Type (max u v) :=
  Shp (F.Leaf Root w) T

variable (F Root) in
/-- A shape environment: a shape, anchored at `w`, for every visible address. -/
abbrev ShEnv (Γ : Ctx) (w : F.W) : Type (max u v) :=
  ∀ v T, Γ v = some T → Shape F Root w T

/-- The shape at a reachable address: projection components from the parent, moved as the
    projection moves them (`GFunc.proj`, so a `here` step collapses the level `j`). -/
def ShEnv.ref {Γ : Ctx} {w : F.W} (ρ : ShEnv F Root Γ w) (j : ℕ) :
    (v : VarSymb) → {T : VarType} → Γ.ref v = some T → Shape F Root w T
  | .root r, _, h => ρ (.root r) _ h
  | .step v s, T, h =>
      if hs : s.isProj = true then
        match hU : Γ.ref v with
        | some _ =>
            GFunc.shp (GFunc.proj (σ := σ) hs (by rw [Ctx.ref_step_proj Γ v hs, hU] at h; exact h))
              j (ShEnv.ref ρ j v hU)
        | none => False.elim (by rw [Ctx.ref_step_proj Γ v hs, hU] at h; cases h)
      else ρ (.step v s) T (by rw [Ctx.ref_step_nonproj Γ v hs] at h; exact h)

/-- Into a `□`: the shapes of the contents, one level further in. -/
def ShEnv.boxPush {Γ : Ctx} {w : F.W} (ρ : ShEnv F Root Γ w) (j : ℕ) : ShEnv F Root Γ.boxIn w
  | .step u .box, _, h => (ρ.ref j u (Ctx.boxIn_step_box h)).inner
  | .step u .keep, _, h =>
      (GFunc.shp (GFunc.keep (σ := σ) (Ctx.boxIn_keep h).1 (Ctx.boxIn_keep h).2.2) j
        (ρ.ref j u (Ctx.boxIn_keep h).2.1)).inner
  | .root _, _, h => False.elim (by cases h)
  | .step _ .fst, _, h => False.elim (by cases h)
  | .step _ .snd, _, h => False.elim (by cases h)
  | .step _ .dia, _, h => False.elim (by cases h)
  | .step _ .here, _, h => False.elim (by cases h)

/-- Into a `◇_x`: the shape of `x`'s content, and the `□` view as for `boxPush`. -/
def ShEnv.diaPush {Γ : Ctx} {w : F.W} (ρ : ShEnv F Root Γ w) (j : ℕ) (x : VarSymb)
    {X : VarType} (hx : Γ.ref x = some (.VTypeDia X)) : ShEnv F Root (Γ.diaIn x) w
  | .step _ .dia, _, h => Ctx.diaIn_step_dia hx h ▸ (ρ.ref j x hx).body
  | .step u .box, T, h => ρ.boxPush j (.step u .box) T h
  | .step u .keep, T, h => ρ.boxPush j (.step u .keep) T h
  | .root _, _, h => False.elim (by cases h)
  | .step _ .fst, _, h => False.elim (by cases h)
  | .step _ .snd, _, h => False.elim (by cases h)
  | .step _ .here, _, h => False.elim (by cases h)

/-- The shape of the tuple of a support. -/
def ShEnv.bundle {Δ : Ctx} {w : F.W} (ρ : ShEnv F Root Δ w) :
    (L : Supp Δ) → Shape F Root w (Supp.ty L)
  | [] => .one
  | e :: L => .prod (ρ e.1 e.2.1 e.2.2) (ShEnv.bundle ρ L)

mutual
  /-- Function terms carry no shape. -/
  def funcShp {Δ : Ctx} {w : F.W} (_ρ : ShEnv F Root Δ w) (_j : ℕ) :
      {n : ℕ} → Func σ Δ n → PUnit.{1}
    | _, .F _ => PUnit.unit
    | _, .eval _ _ => PUnit.unit

  /-- ⭐The shape of a term's value, computed symbolically. -/
  def termShp {Δ : Ctx} {w : F.W} (ρ : ShEnv F Root Δ w) (j : ℕ) :
      {T : VarType} → {a : Ann T} → Term σ Δ T a → Shape F Root w T
    | _, _, .var _ _ => .var
    | _, _, .func _ => .var
    | _, _, .unit => .one
    | _, _, .pair s t => .prod (termShp ρ j s) (termShp ρ j t)
    | _, _, .boxtm t => .box (termShp (ρ.boxPush j) (j + 1) t)
    | _, _, .diatm x hx t =>
        match hr : Δ.ref x with
        | some (.VTypeDia _) =>
            .dia (ρ.ref j x hr).label (termShp (ρ.diaPush j x hr) (j + 1) t)
        | some .Var => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
        | some .VTypeOne => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
        | some (.VTypeProd _ _) => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
        | some (.VTypeBox _) => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
        | none => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
end

/-! ## S1: compilation moves shapes as `termShp` computes them -/

omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.label_dia {L : Type*} {A : VarType} (ℓ : L) (a : Shp L A) :
    (Shp.dia ℓ a).label = ℓ := rfl

omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.body_dia {L : Type*} {A : VarType} (ℓ : L) (a : Shp L A) :
    (Shp.dia ℓ a).body = a := rfl

omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.fst_prod {L : Type*} {A B : VarType} (a : Shp L A)
    (b : Shp L B) : (Shp.prod a b).fst = a := rfl

omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.snd_prod {L : Type*} {A B : VarType} (a : Shp L A)
    (b : Shp L B) : (Shp.prod a b).snd = b := rfl

omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.inner_box {L : Type*} {A : VarType} (a : Shp L A) :
    (Shp.box a).inner = a := rfl

omit [Arrows.RootKeep F Root] [Arrows.RootKeepLaws F Root] in
theorem shp_var_eq {w : F.W} : ∀ a b : Shape F Root w .Var, a = b
  | .var, .var => rfl

omit [Arrows.RootKeepLaws F Root] in
theorem shp_ofEq {w : F.W} {A B : VarType} (h : A = B) (j : ℕ) (a : Shape F Root w A) :
    GFunc.shp (GFunc.ofEq (σ := σ) h) j a = cast (congrArg (Shape F Root w) h) a := by
  subst h
  rfl

omit [Arrows.RootKeepLaws F Root] in
theorem lookup_shp {Δ : Ctx} {w : F.W} (ρ : ShEnv F Root Δ w) (j : ℕ) :
    ∀ (L : Supp Δ) (v : VarSymb) {T : VarType} (h : Δ v = some T)
      (hm : v ∈ List.map PSigma.fst L),
      GFunc.shp (Supp.lookup (σ := σ) L v h hm) j (ρ.bundle L) = ρ v T h
  | [], _, _, _, hm => absurd hm List.not_mem_nil
  | ⟨v', T', h'⟩ :: L, v, T, h, hm => by
      by_cases hvv : v' = v
      · subst hvv
        have hT : T' = T := Option.some.inj (h'.symm.trans h)
        subst hT
        rw [Supp.lookup, dif_pos rfl]
        simp only [GFunc.shp, shp_ofEq, cast_eq, ShEnv.bundle, Shp.fst]
      · rw [Supp.lookup, dif_neg hvv]
        simp only [GFunc.shp, ShEnv.bundle, Shp.snd]
        exact lookup_shp ρ j L v h _

omit [Arrows.RootKeepLaws F Root] in
theorem refGF_shp {Δ : Ctx} {w : F.W} (ρ : ShEnv F Root Δ w) (j : ℕ) (L : Supp Δ) :
    ∀ (v : VarSymb) {T : VarType} (h : Δ.ref v = some T)
      (hm : v.base ∈ List.map PSigma.fst L),
      GFunc.shp (Supp.refGF (σ := σ) L v h hm) j (ρ.bundle L) = ρ.ref j v h
  | .root r, _, h, hm => lookup_shp ρ j L (.root r) h hm
  | .step v s, T, h, hm => by
      by_cases hs : s.isProj = true
      · rw [Supp.refGF, ShEnv.ref, dif_pos hs, dif_pos hs]
        split
        · rename_i U hU
          simp only [GFunc.shp]
          rw [refGF_shp ρ j L v hU]
          split
          · rename_i U' hU'
            have hUU : U = U' := Option.some.inj (hU.symm.trans hU')
            subst hUU
            rfl
          · rename_i hU'
            exfalso
            rw [hU] at hU'
            cases hU'
        · rename_i hU
          exfalso
          rw [Ctx.ref_step_proj Δ v hs, hU] at h
          cases h
      · rw [Supp.refGF, ShEnv.ref, dif_neg hs, dif_neg hs]
        exact lookup_shp ρ j L _ _ _

omit [Arrows.RootKeepLaws F Root] in
theorem gatherBox_shp {Δ : Ctx} {w : F.W} (ρ : ShEnv F Root Δ w) (j : ℕ) (L : Supp Δ) :
    ∀ (L' : Supp Δ.boxIn) (hL : ∀ e ∈ Supp.outerBox L', e.1 ∈ List.map PSigma.fst L),
      GFunc.shp (Supp.gatherBox (σ := σ) L L' hL) j (ρ.bundle L) =
        .box ((ρ.boxPush j).bundle L')
  | [], _ => rfl
  | ⟨.step u .box, T, h⟩ :: L', hL => by
      simp only [Supp.gatherBox, GFunc.shp, Shp.fst, Shp.snd, Shp.inner]
      rw [refGF_shp, gatherBox_shp ρ j L L']
      rfl
  | ⟨.step u .keep, T, h⟩ :: L', hL => by
      simp only [Supp.gatherBox, GFunc.shp, Shp.fst, Shp.snd, Shp.inner]
      rw [refGF_shp, gatherBox_shp ρ j L L']
      rfl
  | ⟨.root _, _, h⟩ :: _, _ => by cases h
  | ⟨.step _ .fst, _, h⟩ :: _, _ => by cases h
  | ⟨.step _ .snd, _, h⟩ :: _, _ => by cases h
  | ⟨.step _ .dia, _, h⟩ :: _, _ => by cases h

omit [Arrows.RootKeepLaws F Root] in
theorem assemble_shp {Δ : Ctx} {w : F.W} (ρ : ShEnv F Root Δ w) (j : ℕ) {x : VarSymb}
    {X : VarType} (hr : Δ.ref x = some (.VTypeDia X)) :
    ∀ (L : Supp (Δ.diaIn x)),
      GFunc.shp (Supp.assemble (σ := σ) hr L) (j + 1)
          (.prod ((ρ.boxPush j).bundle (Supp.boxPart L)) (ρ.ref j x hr).body) =
        (ρ.diaPush j x hr).bundle L
  | [] => rfl
  | ⟨.step u .box, T, h⟩ :: L => by
      simp only [Supp.assemble, Supp.boxPart, GFunc.shp, ShEnv.bundle, Shp.fst, Shp.snd]
      rw [assemble_shp ρ j hr L]
      rfl
  | ⟨.step u .keep, T, h⟩ :: L => by
      simp only [Supp.assemble, Supp.boxPart, GFunc.shp, ShEnv.bundle, Shp.fst, Shp.snd]
      rw [assemble_shp ρ j hr L]
      rfl
  | ⟨.step u .dia, T, h⟩ :: L => by
      have hXT := Ctx.diaIn_step_dia hr h
      subst hXT
      simp only [Supp.assemble, Supp.boxPart, GFunc.shp, ShEnv.bundle, Shp.snd]
      rw [assemble_shp ρ j hr L, shp_ofEq, cast_eq]
      rfl
  | ⟨.root _, _, h⟩ :: _ => by cases h
  | ⟨.step _ .fst, _, h⟩ :: _ => by cases h
  | ⟨.step _ .snd, _, h⟩ :: _ => by cases h

omit [Arrows.RootKeepLaws F Root] in
/-- ⭐**S1**: compilation is faithful to shapes — the counterpart of `Term.compile_eval`. -/
theorem termShp_compile {Δ : Ctx} {w : F.W} (ρ : ShEnv F Root Δ w) (j : ℕ) (L : Supp Δ) :
    ∀ {T : VarType} {a : Ann T} (t : Term σ Δ T a)
      (hL : ∀ e ∈ Term.bases t, e.1 ∈ List.map PSigma.fst L),
      GFunc.shp (Term.compile L t hL) j (ρ.bundle L) = termShp ρ j t
  | _, _, .var _ _, _ => shp_var_eq _ _
  | _, _, .func _, _ => shp_var_eq _ _
  | _, _, .unit, _ => rfl
  | _, _, .pair s t, hL => by
      simp only [Term.compile, GFunc.shp, termShp]
      rw [termShp_compile ρ j L s, termShp_compile ρ j L t]
  | _, _, .boxtm t, hL => by
      simp only [Term.compile, GFunc.shp, termShp]
      rw [gatherBox_shp]
      simp only [Shp.inner]
      rw [termShp_compile (ρ.boxPush j) (j + 1) (Term.bases t) t]
  | _, _, .diatm x hx t, hL => by
      simp only [Term.compile, termShp]
      split
      · rename_i X hr
        split
        · rename_i X' hr'
          obtain rfl : X = X' := by
            rw [hr] at hr'
            cases hr'
            rfl
          simp only [GFunc.shp]
          rw [gatherBox_shp, refGF_shp]
          simp only [Shp.fst_prod, Shp.snd_prod, Shp.inner_box, Shp.label_dia, Shp.body_dia]
          rw [assemble_shp ρ j hr, termShp_compile (ρ.diaPush j x hr) (j + 1) (Term.bases t) t]
        all_goals
          rename_i heq
          exfalso
          rw [hr] at heq
          cases heq
      all_goals
        rename_i heq
        exfalso
        obtain ⟨_, h⟩ := hx
        rw [heq] at h
        cases h

/-! ## Transposition: shapes along every arrow at once -/

omit [ModalSys] in
theorem _root_.V12M.Shp.one_eq {L : Type*} : ∀ a b : Shp L .VTypeOne, a = b
  | .one, .one => rfl

omit [ModalSys] in
theorem _root_.V12M.Shp.prod_eta {L : Type*} {A B : VarType} :
    ∀ a : Shp L (.VTypeProd A B), a = .prod a.fst a.snd
  | .prod _ _ => rfl

omit [ModalSys] in
theorem _root_.V12M.Shp.box_eta {L : Type*} {A : VarType} :
    ∀ a : Shp L (.VTypeBox A), a = .box a.inner
  | .box _ => rfl

omit [ModalSys] in
theorem _root_.V12M.Shp.dia_eta {L : Type*} {A : VarType} :
    ∀ a : Shp L (.VTypeDia A), a = .dia a.label a.body
  | .dia _ _ => rfl


omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.map_fst {L L' : Type y} (g : L → L') {A B : VarType} :
    ∀ a : Shp L (.VTypeProd A B), (a.map g).fst = a.fst.map g
  | .prod _ _ => rfl

omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.map_snd {L L' : Type y} (g : L → L') {A B : VarType} :
    ∀ a : Shp L (.VTypeProd A B), (a.map g).snd = a.snd.map g
  | .prod _ _ => rfl

omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.map_inner {L L' : Type y} (g : L → L') {A : VarType} :
    ∀ a : Shp L (.VTypeBox A), (a.map g).inner = a.inner.map g
  | .box _ => rfl

omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.map_label {L L' : Type y} (g : L → L') {A : VarType} :
    ∀ a : Shp L (.VTypeDia A), (a.map g).label = g a.label
  | .dia _ _ => rfl

omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.map_body {L L' : Type y} (g : L → L') {A : VarType} :
    ∀ a : Shp L (.VTypeDia A), (a.map g).body = a.body.map g
  | .dia _ _ => rfl

omit [Arrows.RootKeep F Root] in
/-- A leaf map that acts on a family member by member passes through transposition. -/
theorem transpose_map {w : F.W} (Φ : F.Leaf Root w → F.Leaf Root w)
    (G : ∀ s : F.Acc w, F.Leaf Root s.1 → F.Leaf Root s.1)
    (hΦ : ∀ f, Φ (.fam f) = .fam fun s => G s (f s)) :
    ∀ {A : VarType} (g : (s : F.Acc w) → Shape F Root s.1 A),
      (Arrows.transposeShp g).map Φ = Arrows.transposeShp fun s => (g s).map (G s)
  | .Var, _ => rfl
  | .VTypeOne, _ => rfl
  | .VTypeProd _ _, g => by
      simp only [Arrows.transposeShp, Shp.map]
      rw [transpose_map Φ G hΦ, transpose_map Φ G hΦ]
      simp only [Shp.map_fst, Shp.map_snd]
  | .VTypeBox _, g => by
      simp only [Arrows.transposeShp, Shp.map]
      rw [transpose_map Φ G hΦ]
      simp only [Shp.map_inner]
  | .VTypeDia _, g => by
      simp only [Arrows.transposeShp, Shp.map]
      rw [transpose_map Φ G hΦ, hΦ]
      simp only [Shp.map_label, Shp.map_body]

omit [Arrows.RootKeep F Root] in
/-- Reading a transposed shape at the identity arrow gives the member there. -/
theorem transpose_collapse_zero (hT : ModalSys.T = true) {w : F.W} :
    ∀ {A : VarType} (g : (s : F.Acc w) → Shape F Root s.1 A),
      (Arrows.transposeShp g).map (Arrows.Leaf.collapse hT 0) = g (F.reflAcc hT w)
  | .Var, g => shp_var_eq _ _
  | .VTypeOne, g => Shp.one_eq _ _
  | .VTypeProd _ _, g => by
      simp only [Arrows.transposeShp, Shp.map]
      rw [transpose_collapse_zero hT, transpose_collapse_zero hT]
      exact (Shp.prod_eta _).symm
  | .VTypeBox _, g => by
      simp only [Arrows.transposeShp, Shp.map]
      rw [transpose_collapse_zero hT]
      exact (Shp.box_eta _).symm
  | .VTypeDia _, g => by
      simp only [Arrows.transposeShp, Shp.map]
      rw [transpose_collapse_zero hT]
      exact (Shp.dia_eta _).symm

omit [Arrows.RootKeep F Root] in
/-- Keeping a transposed shape: one family per arrow, of the members at the composite arrows. -/
theorem transpose_shift_zero (hF : ModalSys.Four = true) {w : F.W} :
    ∀ {A : VarType} (g : (s : F.Acc w) → Shape F Root s.1 A),
      (Arrows.transposeShp g).map (Arrows.Leaf.shift hF 0) =
        Arrows.transposeShp fun s => Arrows.transposeShp fun t =>
          g ⟨t.1, ⟨F.trans hF s.2.down t.2.down⟩⟩
  | .Var, _ => rfl
  | .VTypeOne, _ => rfl
  | .VTypeProd _ _, g => by
      simp only [Arrows.transposeShp, Shp.map, Shp.fst_prod, Shp.snd_prod]
      rw [transpose_shift_zero hF, transpose_shift_zero hF]
  | .VTypeBox _, g => by
      simp only [Arrows.transposeShp, Shp.map, Shp.inner_box]
      rw [transpose_shift_zero hF]
  | .VTypeDia _, g => by
      simp only [Arrows.transposeShp, Shp.map, Shp.label_dia, Shp.body_dia]
      rw [transpose_shift_zero hF]
      rfl

omit [Arrows.RootKeep F Root] in
/-- One shape read through a leaf map per arrow, transposed: each leaf becomes the family of its
    images.  This is how a possible object kept along every arrow gets its shape (`dk 0`). -/
theorem transpose_map_const {w : F.W} (G : ∀ s : F.Acc w, F.Leaf Root w → F.Leaf Root s.1) :
    ∀ {A : VarType} (a : Shape F Root w A),
      (Arrows.transposeShp fun s => a.map (G s)) = a.map fun ℓ => .fam fun s => G s ℓ
  | .Var, .var => rfl
  | .VTypeOne, .one => rfl
  | .VTypeProd _ _, .prod a b => by
      simp only [Arrows.transposeShp, Shp.map, Shp.fst_prod, Shp.snd_prod]
      rw [transpose_map_const G a, transpose_map_const G b]
  | .VTypeBox _, .box a => by
      simp only [Arrows.transposeShp, Shp.map, Shp.inner_box]
      rw [transpose_map_const G a]
  | .VTypeDia _, .dia ℓ a => by
      simp only [Arrows.transposeShp, Shp.map, Shp.label_dia, Shp.body_dia]
      rw [transpose_map_const G a]

omit [F.RootKeep Root] in
/-- **Transposition is injective**: each arrow's shape is read back from the families. -/
theorem transposeShp_inj {w : F.W} :
    ∀ {A : VarType} {g g' : (s : F.Acc w) → Shape F Root s.1 A},
      Arrows.transposeShp g = Arrows.transposeShp g' → g = g'
  | .Var, g, g', _ => funext fun s => by
      generalize g s = a
      generalize g' s = b
      cases a; cases b; rfl
  | .VTypeOne, g, g', _ => funext fun s => by
      generalize g s = a
      generalize g' s = b
      cases a; cases b; rfl
  | .VTypeProd _ _, g, g', h => by
      simp only [Arrows.transposeShp, Shp.prod.injEq] at h
      have e₁ := transposeShp_inj h.1
      have e₂ := transposeShp_inj h.2
      funext s
      rw [Shp.prod_eta (g s), Shp.prod_eta (g' s), congrFun e₁ s, congrFun e₂ s]
  | .VTypeBox _, g, g', h => by
      simp only [Arrows.transposeShp, Shp.box.injEq] at h
      have e := transposeShp_inj h
      funext s
      rw [Shp.box_eta (g s), Shp.box_eta (g' s), congrFun e s]
  | .VTypeDia _, g, g', h => by
      simp only [Arrows.transposeShp, Shp.dia.injEq, Arrows.Leaf.fam.injEq] at h
      have e := transposeShp_inj h.2
      funext s
      rw [Shp.dia_eta (g s), Shp.dia_eta (g' s), congrFun h.1 s, congrFun e s]

omit [Arrows.RootKeepLaws F Root] in
/-- ⭐**Every map's shape transport commutes with transposition**, one level further out. -/
theorem shp_transpose {w : F.W} :
    ∀ {A B : VarType} (f : GFunc σ A B) (j : ℕ) (g : (s : F.Acc w) → Shape F Root s.1 A),
      GFunc.shp f (j + 1) (Arrows.transposeShp g) =
        Arrows.transposeShp fun s => GFunc.shp f j (g s)
  | _, _, .id _, _, _ => rfl
  | _, _, .comp g f, j, h => by
      simp only [GFunc.shp]
      rw [shp_transpose f, shp_transpose g]
  | _, _, .fst, _, _ => rfl
  | _, _, .snd, _, _ => rfl
  | _, _, .pair f g, j, h => by
      simp only [GFunc.shp]
      rw [shp_transpose f, shp_transpose g]
      rfl
  | _, _, .unit _, _, _ => rfl
  | _, _, .func _ _, _, _ => rfl
  | _, _, .boxMap f, j, h => by
      simp only [GFunc.shp]
      rw [show (Arrows.transposeShp h).inner = Arrows.transposeShp fun s => (h s).inner from rfl,
        shp_transpose f]
      rfl
  | _, _, .boxPair _ _, _, _ => rfl
  | _, _, .boxUnit, _, _ => rfl
  | _, _, .diaMap f, j, h => by
      simp only [GFunc.shp]
      rw [show (Arrows.transposeShp h).body = Arrows.transposeShp fun s => (h s).body from rfl,
        shp_transpose f]
      rfl
  | _, _, .strength _ _, _, _ => rfl
  | _, _, .extract hT, j, h => by
      simp only [GFunc.shp]
      exact transpose_map _ _ (fun _ => rfl) _
  | _, _, .dup hF, j, h => by
      simp only [GFunc.shp]
      rw [show (Arrows.transposeShp h).inner = Arrows.transposeShp fun s => (h s).inner from rfl,
        transpose_map _ _ (fun _ => rfl)]
      rfl
  | _, _, .dkeep hF, j, h => by
      simp only [GFunc.shp]
      change Shp.box (Shp.dia (Arrows.Leaf.dk hF (j + 1) (.fam fun s => (h s).label))
          ((Arrows.transposeShp fun s => (h s).body).map (Arrows.Leaf.dkB hF (j + 1)))) = _
      rw [transpose_map _ _ (fun _ => rfl)]
      rfl

/-! ### Unfolding lemmas -/

omit [Arrows.RootKeepLaws F Root] in
theorem ShEnv.ref_proj {Γ : Ctx} {w : F.W} (ρ : ShEnv F Root Γ w) (j : ℕ) {v : VarSymb}
    {s : Step} (hs : s.isProj = true) {U T : VarType} (hU : Γ.ref v = some U)
    (h : Γ.ref (.step v s) = some T) :
    ρ.ref j (.step v s) h =
      GFunc.shp (GFunc.proj (σ := σ) hs (by rw [Ctx.ref_step_proj Γ v hs, hU] at h; exact h)) j
        (ρ.ref j v hU) := by
  rw [ShEnv.ref, dif_pos hs]
  split
  · rename_i U' hU'
    obtain rfl : U = U' := Option.some.inj (hU.symm.trans hU')
    rfl
  · rename_i hU'
    exfalso
    rw [hU] at hU'
    cases hU'

omit [Arrows.RootKeepLaws F Root] in
theorem ShEnv.ref_nonproj {Γ : Ctx} {w : F.W} (ρ : ShEnv F Root Γ w) (j : ℕ) {v : VarSymb}
    {s : Step} (hs : ¬ s.isProj = true) {T : VarType} (h : Γ.ref (.step v s) = some T) :
    ρ.ref j (.step v s) h = ρ (.step v s) T (by rw [Ctx.ref_step_nonproj Γ v hs] at h; exact h) :=
  by rw [ShEnv.ref, dif_neg hs]

omit [Arrows.RootKeepLaws F Root] in
theorem termShp_diatm {Δ : Ctx} {w : F.W} (ρ : ShEnv F Root Δ w) (j : ℕ) {x : VarSymb}
    {X : VarType} (hr : Δ.ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (hx : ∃ X, Δ.ref x = some (.VTypeDia X)) (t : Term σ (Δ.diaIn x) A a) :
    termShp ρ j (Term.diatm x hx t) =
      .dia (ρ.ref j x hr).label (termShp (ρ.diaPush j x hr) (j + 1) t) := by
  simp only [termShp]
  split
  · rename_i X' hr'
    obtain rfl : X = X' := by
      rw [hr] at hr'
      cases hr'
      rfl
    rfl
  all_goals
    rename_i heq
    exfalso
    rw [hr] at heq
    cases heq

/-! ### Transposing shape environments -/

omit [Arrows.RootKeepLaws F Root] in
theorem ShEnv.ref_transpose {Γ : Ctx} {w : F.W} (τ : ShEnv F Root Γ w)
    (ρ : (s : F.Acc w) → ShEnv F Root Γ s.1) (j : ℕ)
    (hτ : ∀ v T h, τ v T h = Arrows.transposeShp fun s => ρ s v T h) :
    ∀ (v : VarSymb) {T : VarType} (h : Γ.ref v = some T),
      τ.ref (j + 1) v h = Arrows.transposeShp fun s => (ρ s).ref j v h
  | .root _, _, h => hτ _ _ h
  | .step v s, T, h => by
      by_cases hs : s.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Γ.ref v = some U := by
          rw [Ctx.ref_step_proj Γ v hs] at h
          cases hU : Γ.ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        rw [ShEnv.ref_proj τ (j + 1) hs hU h, ShEnv.ref_transpose τ ρ j hτ v hU, shp_transpose]
        exact congrArg _ (funext fun s => (ShEnv.ref_proj (ρ s) j hs hU h).symm)
      · rw [ShEnv.ref_nonproj τ (j + 1) hs h, hτ]
        exact congrArg _ (funext fun s => (ShEnv.ref_nonproj (ρ s) j hs h).symm)

omit [Arrows.RootKeepLaws F Root] in
theorem ShEnv.boxPush_transpose {Γ : Ctx} {w : F.W} (τ : ShEnv F Root Γ w)
    (ρ : (s : F.Acc w) → ShEnv F Root Γ s.1) (j : ℕ)
    (hτ : ∀ v T h, τ v T h = Arrows.transposeShp fun s => ρ s v T h) :
    ∀ v T h, τ.boxPush (j + 1) v T h = Arrows.transposeShp fun s => (ρ s).boxPush j v T h
  | .step u .box, _, h => by
      simp only [ShEnv.boxPush]
      rw [ShEnv.ref_transpose τ ρ j hτ]
      rfl
  | .step u .keep, _, h => by
      simp only [ShEnv.boxPush]
      rw [ShEnv.ref_transpose τ ρ j hτ, shp_transpose]
      rfl
  | .root _, _, h => by cases h
  | .step _ .fst, _, h => by cases h
  | .step _ .snd, _, h => by cases h
  | .step _ .dia, _, h => by cases h
  | .step _ .here, _, h => by cases h

omit [Arrows.RootKeepLaws F Root] in
theorem ShEnv.diaPush_transpose {Γ : Ctx} {w : F.W} (τ : ShEnv F Root Γ w)
    (ρ : (s : F.Acc w) → ShEnv F Root Γ s.1) (j : ℕ)
    (hτ : ∀ v T h, τ v T h = Arrows.transposeShp fun s => ρ s v T h) {x : VarSymb} {X : VarType}
    (hx : Γ.ref x = some (.VTypeDia X)) :
    ∀ v T h, τ.diaPush (j + 1) x hx v T h = Arrows.transposeShp fun s => (ρ s).diaPush j x hx v T h
  | .step _ .dia, _, h => by
      have e := Ctx.diaIn_step_dia hx h
      subst e
      simp only [ShEnv.diaPush]
      rw [ShEnv.ref_transpose τ ρ j hτ]
      rfl
  | .step u .box, T, h => ShEnv.boxPush_transpose τ ρ j hτ (.step u .box) T h
  | .step u .keep, T, h => ShEnv.boxPush_transpose τ ρ j hτ (.step u .keep) T h
  | .root _, _, h => by cases h
  | .step _ .fst, _, h => by cases h
  | .step _ .snd, _, h => by cases h
  | .step _ .here, _, h => by cases h

omit [Arrows.RootKeepLaws F Root] in
/-- ⭐**T**: the shape of a term, one level further out, is the transposed family of its shapes —
    when the environment is the transposed family of environments. -/
theorem termShp_transpose {Δ : Ctx} {w : F.W} (τ : ShEnv F Root Δ w)
    (ρ : (s : F.Acc w) → ShEnv F Root Δ s.1) (j : ℕ)
    (hτ : ∀ v T h, τ v T h = Arrows.transposeShp fun s => ρ s v T h) :
    ∀ {T : VarType} {a : Ann T} (t : Term σ Δ T a),
      termShp τ (j + 1) t = Arrows.transposeShp fun s => termShp (ρ s) j t
  | _, _, .var _ _ => rfl
  | _, _, .func _ => rfl
  | _, _, .unit => rfl
  | _, _, .pair s t => by
      simp only [termShp]
      rw [termShp_transpose τ ρ j hτ s, termShp_transpose τ ρ j hτ t]
      rfl
  | _, _, .boxtm t => by
      simp only [termShp]
      rw [termShp_transpose (τ.boxPush (j + 1)) (fun s => (ρ s).boxPush j) (j + 1)
        (ShEnv.boxPush_transpose τ ρ j hτ) t]
      rfl
  | _, _, .diatm x hx t => by
      obtain ⟨X, hr⟩ := id hx
      rw [termShp_diatm τ (j + 1) hr,
        termShp_transpose (τ.diaPush (j + 1) x hr) (fun s => (ρ s).diaPush j x hr) (j + 1)
          (ShEnv.diaPush_transpose τ ρ j hτ hr) t, ShEnv.ref_transpose τ ρ j hτ x hr]
      rw [show (fun s => termShp (ρ s) j (Term.diatm x hx t)) =
          fun s => .dia ((ρ s).ref j x hr).label (termShp ((ρ s).diaPush j x hr) (j + 1) t) from
        funext fun s => termShp_diatm (ρ s) j hr hx t]
      rfl

/-! ## Weakening, and the annotation determines the shape -/

/-- Two shape environments agree along an inclusion of contexts. -/
def ShEnv.Agree {Γ Γ' : Ctx} (h : Γ.Le Γ') {w : F.W} (ρ : ShEnv F Root Γ w)
    (ρ' : ShEnv F Root Γ' w) : Prop :=
  ∀ v T (hv : Γ v = some T), ρ v T hv = ρ' v T (h v T hv)

omit [Arrows.RootKeepLaws F Root] in
theorem ShEnv.ref_agree {Γ Γ' : Ctx} {h : Γ.Le Γ'} {w : F.W} {ρ : ShEnv F Root Γ w}
    {ρ' : ShEnv F Root Γ' w} (hag : ShEnv.Agree h ρ ρ') (j : ℕ) :
    ∀ (v : VarSymb) {T : VarType} (hv : Γ.ref v = some T), ρ.ref j v hv = ρ'.ref j v (h.ref hv)
  | .root r, _, hv => hag (.root r) _ hv
  | .step v s, T, hv => by
      by_cases hs : s.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Γ.ref v = some U := by
          rw [Ctx.ref_step_proj Γ v hs] at hv
          cases hU : Γ.ref v with
          | none => rw [hU] at hv; cases hv
          | some U => exact ⟨U, rfl⟩
        rw [ShEnv.ref_proj ρ j hs hU hv, ShEnv.ref_proj ρ' j hs (h.ref hU) (h.ref hv),
          ShEnv.ref_agree hag j v hU]
      · rw [ShEnv.ref_nonproj ρ j hs hv, ShEnv.ref_nonproj ρ' j hs (h.ref hv)]
        exact hag _ _ _

omit [Arrows.RootKeepLaws F Root] in
theorem ShEnv.boxPush_agree {Γ Γ' : Ctx} {h : Γ.Le Γ'} {w : F.W} {ρ : ShEnv F Root Γ w}
    {ρ' : ShEnv F Root Γ' w} (hag : ShEnv.Agree h ρ ρ') (j : ℕ) :
    ShEnv.Agree h.boxIn (ρ.boxPush j) (ρ'.boxPush j)
  | .step u .box, _, hv => by
      simp only [ShEnv.boxPush]
      rw [ShEnv.ref_agree hag j u]
  | .step u .keep, _, hv => by
      simp only [ShEnv.boxPush]
      rw [ShEnv.ref_agree hag j u]
  | .root _, _, hv => by cases hv
  | .step _ .fst, _, hv => by cases hv
  | .step _ .snd, _, hv => by cases hv
  | .step _ .dia, _, hv => by cases hv
  | .step _ .here, _, hv => by cases hv

omit [Arrows.RootKeepLaws F Root] in
theorem ShEnv.diaPush_agree {Γ Γ' : Ctx} {h : Γ.Le Γ'} {w : F.W} {ρ : ShEnv F Root Γ w}
    {ρ' : ShEnv F Root Γ' w} (hag : ShEnv.Agree h ρ ρ') (j : ℕ) {x : VarSymb} {X : VarType}
    (hx : Γ.ref x = some (.VTypeDia X)) :
    ShEnv.Agree (h.diaIn x) (ρ.diaPush j x hx) (ρ'.diaPush j x (h.ref hx))
  | .step _ .dia, _, hv => by
      have e := Ctx.diaIn_step_dia hx hv
      subst e
      simp only [ShEnv.diaPush]
      rw [ShEnv.ref_agree hag j x hx]
  | .step u .box, T, hv => ShEnv.boxPush_agree hag j (.step u .box) T hv
  | .step u .keep, T, hv => ShEnv.boxPush_agree hag j (.step u .keep) T hv
  | .root _, _, hv => by cases hv
  | .step _ .fst, _, hv => by cases hv
  | .step _ .snd, _, hv => by cases hv
  | .step _ .here, _, hv => by cases hv

omit [Arrows.RootKeepLaws F Root] in
/-- ⭐Shapes are unchanged by weakening. -/
theorem termShp_mono {Γ Γ' : Ctx} {h : Γ.Le Γ'} {w : F.W} {ρ : ShEnv F Root Γ w}
    {ρ' : ShEnv F Root Γ' w} (hag : ShEnv.Agree h ρ ρ') (j : ℕ) :
    ∀ {T : VarType} {a : Ann T} (t : Term σ Γ T a), termShp ρ' j (Term.mono h t) = termShp ρ j t
  | _, _, .var _ _ => rfl
  | _, _, .func _ => rfl
  | _, _, .unit => rfl
  | _, _, .pair s t => by
      change Shp.prod (termShp ρ' j (Term.mono h s)) (termShp ρ' j (Term.mono h t)) = _
      rw [termShp_mono hag j s, termShp_mono hag j t]
      rfl
  | _, _, .boxtm t => by
      change Shp.box (termShp (ρ'.boxPush j) (j + 1) (Term.mono h.boxIn t)) = _
      rw [termShp_mono (ShEnv.boxPush_agree hag j) (j + 1) t]
      rfl
  | _, _, .diatm x hx t => by
      obtain ⟨X, hr⟩ := id hx
      change termShp ρ' j (Term.diatm x _ (Term.mono (h.diaIn x) t)) = _
      rw [termShp_diatm ρ' j (h.ref hr), termShp_diatm ρ j hr,
        termShp_mono (ShEnv.diaPush_agree hag j hr) (j + 1) t, ShEnv.ref_agree hag j x hr]

omit [Arrows.RootKeepLaws F Root] in
/-- ⭐**The annotation determines the shape**: two terms of one annotated type have the same symbolic
    shape.  This is the semantic side of `eqRec` comparing only terms of one annotation. -/
theorem termShp_ann {Δ : Ctx} {w : F.W} (ρ : ShEnv F Root Δ w) (j : ℕ) :
    ∀ {T : VarType} {a : Ann T} (t s : Term σ Δ T a), termShp ρ j t = termShp ρ j s
  | .Var, _, _, _ => shp_var_eq _ _
  | .VTypeOne, _, _, _ => Shp.one_eq _ _
  | _, _, .pair t₁ t₂, .pair s₁ s₂ => by
      simp only [termShp]
      rw [termShp_ann ρ j t₁ s₁, termShp_ann ρ j t₂ s₂]
  | _, _, .boxtm t, .boxtm s => by
      simp only [termShp]
      rw [termShp_ann (ρ.boxPush j) (j + 1) t s]
  | _, _, .diatm x hx t, .diatm _ hx' s => by
      obtain ⟨X, hr⟩ := id hx
      rw [termShp_diatm ρ j hr hx, termShp_diatm ρ j hr hx',
        termShp_ann (ρ.diaPush j x hr) (j + 1) t s]

/-! ## Collapsing or shifting a whole shape environment -/

omit [ModalSys] in
theorem _root_.V12M.Shp.map_map {L L' L'' : Type y} (g : L → L') (g' : L' → L'') :
    ∀ {A : VarType} (a : Shp L A), (a.map g).map g' = a.map (g' ∘ g)
  | _, .var => rfl
  | _, .one => rfl
  | _, .prod a b => by simp only [Shp.map]; rw [Shp.map_map g g' a, Shp.map_map g g' b]
  | _, .box a => by simp only [Shp.map]; rw [Shp.map_map g g' a]
  | _, .dia _ a => by simp only [Shp.map]; rw [Shp.map_map g g' a]; rfl

omit [ModalSys] in
theorem _root_.V12M.Shp.map_congr {L L' : Type y} {g g' : L → L'} (h : ∀ ℓ, g ℓ = g' ℓ) :
    ∀ {A : VarType} (a : Shp L A), a.map g = a.map g'
  | _, .var => rfl
  | _, .one => rfl
  | _, .prod a b => by simp only [Shp.map]; rw [Shp.map_congr h a, Shp.map_congr h b]
  | _, .box a => by simp only [Shp.map]; rw [Shp.map_congr h a]
  | _, .dia ℓ a => by simp only [Shp.map]; rw [Shp.map_congr h a, h]

omit [ModalSys] in
theorem _root_.V12M.Shp.map_id {L : Type y} : ∀ {A : VarType} (a : Shp L A), a.map id = a
  | _, .var => rfl
  | _, .one => rfl
  | _, .prod a b => by simp only [Shp.map]; rw [Shp.map_id a, Shp.map_id b]
  | _, .box a => by simp only [Shp.map]; rw [Shp.map_id a]
  | _, .dia _ a => by simp only [Shp.map]; rw [Shp.map_id a]; rfl

/-! ## Well-formed shapes (docs §3 4, "T + 4") -/

/-- Well-formed shapes, leaves by `Arrows.Leaf.WF`. -/
abbrev ShWF {w : F.W} (lw : List Bool) {A : VarType} (a : Shape F Root w A) : Prop :=
  Shp.WF (fun lw ℓ => Arrows.Leaf.WF lw ℓ) lw a

omit [ModalSys] in
/-- ⭐A leaf map that moves positions by a fixed prefix moves well-formed shapes. -/
theorem _root_.V12M.Shp.wf_map {L : Type y} {P Q : List Bool → L → Prop} (g : L → L)
    (pre pre' : List Bool) (hg : ∀ r ℓ, P (pre ++ r) ℓ → Q (pre' ++ r) (g ℓ)) :
    ∀ {A : VarType} (r : List Bool) (a : Shp L A), Shp.WF P (pre ++ r) a →
      Shp.WF Q (pre' ++ r) (a.map g)
  | _, _, .var, _ => trivial
  | _, _, .one, _ => trivial
  | _, r, .prod a b, h => ⟨Shp.wf_map g pre pre' hg r a h.1, Shp.wf_map g pre pre' hg r b h.2⟩
  | _, r, .box a, h => by
      change Shp.WF Q (pre' ++ r ++ [true]) (a.map g)
      rw [List.append_assoc]
      exact Shp.wf_map g pre pre' hg (r ++ [true]) a (by rw [← List.append_assoc]; exact h)
  | _, r, .dia ℓ a, h => by
      refine ⟨hg r ℓ h.1, ?_⟩
      change Shp.WF Q (pre' ++ r ++ [false]) (a.map g)
      rw [List.append_assoc]
      exact Shp.wf_map g pre pre' hg (r ++ [false]) a (by rw [← List.append_assoc]; exact h.2)

omit [ModalSys] in
/-- Two leaf maps agreeing on the well-formed leaves below a prefix agree on a well-formed
    shape. -/
theorem _root_.V12M.Shp.map_congr_wf {L : Type y} {P : List Bool → L → Prop} {g g' : L → L}
    (pre : List Bool) (hg : ∀ r ℓ, P (pre ++ r) ℓ → g ℓ = g' ℓ) :
    ∀ {A : VarType} (r : List Bool) (a : Shp L A), Shp.WF P (pre ++ r) a → a.map g = a.map g'
  | _, _, .var, _ => rfl
  | _, _, .one, _ => rfl
  | _, r, .prod a b, h => by
      simp only [Shp.map]
      rw [Shp.map_congr_wf pre hg r a h.1, Shp.map_congr_wf pre hg r b h.2]
  | _, r, .box a, h => by
      simp only [Shp.map]
      rw [Shp.map_congr_wf pre hg (r ++ [true]) a (by rw [← List.append_assoc]; exact h)]
  | _, r, .dia ℓ a, h => by
      simp only [Shp.map]
      rw [hg r ℓ h.1,
        Shp.map_congr_wf pre hg (r ++ [false]) a (by rw [← List.append_assoc]; exact h.2)]

omit [Arrows.RootKeep F Root] in
theorem shWF_relax {w : F.W} (lw : List Bool) {A : VarType} (a : Shape F Root w A)
    (h : ShWF (lw ++ [true]) a) : ShWF (lw ++ [false]) a := by
  have := Shp.wf_map (P := fun lw ℓ => Arrows.Leaf.WF lw ℓ)
    (Q := fun lw ℓ => Arrows.Leaf.WF lw ℓ) id (lw ++ [true]) (lw ++ [false])
    (fun r ℓ hℓ => by
      simp only [List.append_assoc, List.singleton_append] at hℓ ⊢
      exact Arrows.Leaf.wf_relax lw r ℓ hℓ) [] a (by simpa using h)
  simpa [Shp.map_id] using this

omit [Arrows.RootKeep F Root] in
/-- ⭐Transposition is well-formed: its leaves are families, of well-formed members. -/
theorem shWF_transpose {w : F.W} (c : Bool) :
    ∀ {A : VarType} (lw : List Bool) (g : (s : F.Acc w) → Shape F Root s.1 A),
      (∀ s, ShWF lw (g s)) → ShWF (c :: lw) (Arrows.transposeShp g)
  | .Var, _, _, _ => trivial
  | .VTypeOne, _, _, _ => trivial
  | .VTypeProd _ _, lw, g, h =>
      ⟨shWF_transpose c lw (fun s => (g s).fst) fun s => by
          have := h s
          rw [Shp.prod_eta (g s)] at this
          exact this.1,
        shWF_transpose c lw (fun s => (g s).snd) fun s => by
          have := h s
          rw [Shp.prod_eta (g s)] at this
          exact this.2⟩
  | .VTypeBox _, lw, g, h =>
      shWF_transpose c (lw ++ [true]) (fun s => (g s).inner) fun s => by
        have := h s
        rw [Shp.box_eta (g s)] at this
        exact this
  | .VTypeDia _, lw, g, h =>
      ⟨fun s => by
          have := h s
          rw [Shp.dia_eta (g s)] at this
          exact this.1,
        shWF_transpose c (lw ++ [false]) (fun s => (g s).body) fun s => by
          have := h s
          rw [Shp.dia_eta (g s)] at this
          exact this.2⟩

/-- ⭐**Every map's shape transport keeps shapes well-formed.** -/
theorem shWF_shp : ∀ {A B : VarType} (f : GFunc σ A B) (lw : List Bool) {w : F.W}
    (a : Shape F Root w A), ShWF lw a → ShWF lw (GFunc.shp f lw.length a)
  | _, _, .id _, _, _, _, h => h
  | _, _, .comp g f, lw, _, a, h => shWF_shp g lw _ (shWF_shp f lw a h)
  | _, _, .fst, _, _, a, h => by
      rw [Shp.prod_eta a] at h
      exact h.1
  | _, _, .snd, _, _, a, h => by
      rw [Shp.prod_eta a] at h
      exact h.2
  | _, _, .pair f g, lw, _, a, h => ⟨shWF_shp f lw a h, shWF_shp g lw a h⟩
  | _, _, .unit _, _, _, _, _ => trivial
  | _, _, .func _ _, _, _, _, _ => trivial
  | _, _, .boxMap f, lw, _, a, h => by
      rw [Shp.box_eta a] at h
      have := shWF_shp f (lw ++ [true]) a.inner (by simpa using h)
      simp only [List.length_append, List.length_singleton] at this
      exact this
  | _, _, .boxPair _ _, lw, _, a, h => by
      rw [Shp.prod_eta a, Shp.box_eta a.fst, Shp.box_eta a.snd] at h
      exact ⟨h.1, h.2⟩
  | _, _, .boxUnit, _, _, _, _ => trivial
  | _, _, .diaMap f, lw, _, a, h => by
      rw [Shp.dia_eta a] at h
      have := shWF_shp f (lw ++ [false]) a.body (by simpa using h.2)
      simp only [List.length_append, List.length_singleton] at this
      exact ⟨h.1, this⟩
  | _, _, .strength _ _, lw, _, a, h => by
      rw [Shp.prod_eta a, Shp.box_eta a.fst, Shp.dia_eta a.snd] at h
      exact ⟨h.2.1, shWF_relax lw _ h.1, h.2.2⟩
  | _, _, .extract hT, lw, _, a, h => by
      rw [Shp.box_eta a] at h
      have := Shp.wf_map (P := fun lw ℓ => Arrows.Leaf.WF lw ℓ)
        (Q := fun lw ℓ => Arrows.Leaf.WF lw ℓ) (Arrows.Leaf.collapse hT lw.length)
        (lw ++ [true]) lw (fun r ℓ hℓ => by
          simp only [List.append_assoc, List.singleton_append] at hℓ
          exact Arrows.Leaf.wf_collapse hT lw r ℓ hℓ) [] a.inner (by simpa using h)
      simpa using this
  | _, _, .dup hF, lw, _, a, h => by
      rw [Shp.box_eta a] at h
      have := Shp.wf_map (P := fun lw ℓ => Arrows.Leaf.WF lw ℓ)
        (Q := fun lw ℓ => Arrows.Leaf.WF lw ℓ) (Arrows.Leaf.shift hF lw.length)
        (lw ++ [true]) (lw ++ [true, true]) (fun r ℓ hℓ => by
          simp only [List.append_assoc, List.cons_append,
            List.nil_append] at hℓ ⊢
          exact Arrows.Leaf.wf_shift hF lw r ℓ hℓ) [] a.inner (by simpa using h)
      change ShWF (lw ++ [true] ++ [true]) _
      simpa using this
  | _, _, .dkeep hF, lw, _, a, h => by
      rw [Shp.dia_eta a] at h
      refine ⟨Arrows.Leaf.wf_dk hF lw a.label h.1, ?_⟩
      have := Shp.wf_map (P := fun lw ℓ => Arrows.Leaf.WF lw ℓ)
        (Q := fun lw ℓ => Arrows.Leaf.WF lw ℓ) (Arrows.Leaf.dkB hF lw.length)
        (lw ++ [false]) (lw ++ [true, false]) (fun r ℓ hℓ => by
          simp only [List.append_assoc, List.cons_append,
            List.nil_append] at hℓ ⊢
          exact Arrows.Leaf.wf_dkB hF lw r ℓ hℓ) [] a.body (by simpa using h.2)
      change ShWF (lw ++ [true] ++ [false]) _
      simpa using this

omit [Arrows.RootKeepLaws F Root] in
/-- ⭐On a well-formed shape under a `□` at level `j`, keeping the inside of a possibility is a
    shift (`Arrows.Leaf.dkB_eq_shift`). -/
theorem shWF_dkB_eq_shift (hF : ModalSys.Four = true) (lw : List Bool) {w : F.W} {A : VarType}
    (a : Shape F Root w A) (h : ShWF (lw ++ [true]) a) :
    a.map (Arrows.Leaf.dkB hF lw.length) = a.map (Arrows.Leaf.shift hF lw.length) :=
  Shp.map_congr_wf (P := fun lw ℓ => Arrows.Leaf.WF lw ℓ) (lw ++ [true])
    (fun r ℓ hℓ => Arrows.Leaf.dkB_eq_shift hF lw r ℓ (by simpa using hℓ)) [] a
    (by simpa using h)

/-- Well-formed shape environments: every entry well-formed at the environment's position. -/
def ShEnv.WF {Γ : Ctx} {w : F.W} (lw : List Bool) (ρ : ShEnv F Root Γ w) : Prop :=
  ∀ v T (h : Γ v = some T), ShWF lw (ρ v T h)

theorem ShEnv.wf_ref {Γ : Ctx} {w : F.W} {lw : List Bool} {ρ : ShEnv F Root Γ w}
    (hρ : ρ.WF lw) : ∀ (v : VarSymb) {T : VarType} (h : Γ.ref v = some T),
      ShWF lw (ρ.ref lw.length v h)
  | .root _, _, h => hρ _ _ h
  | .step v s, T, h => by
      by_cases hs : s.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Γ.ref v = some U := by
          rw [Ctx.ref_step_proj Γ v hs] at h
          cases hU : Γ.ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        rw [ShEnv.ref_proj _ _ hs hU h]
        exact shWF_shp _ lw _ (ShEnv.wf_ref hρ v hU)
      · rw [ShEnv.ref_nonproj _ _ hs h]
        exact hρ _ _ ((Ctx.ref_nonproj _ (by simpa using hs)).symm.trans h)

theorem ShEnv.wf_boxPush {Γ : Ctx} {w : F.W} {lw : List Bool} {ρ : ShEnv F Root Γ w}
    (hρ : ρ.WF lw) : (ρ.boxPush lw.length).WF (lw ++ [true]) := by
  intro v T h
  match v, h with
  | .step u .box, h =>
      have := ShEnv.wf_ref hρ u (Ctx.boxIn_step_box h)
      rw [Shp.box_eta (ρ.ref lw.length u (Ctx.boxIn_step_box h))] at this
      exact this
  | .step u .keep, h =>
      have := shWF_shp (GFunc.keep (σ := σ) (Ctx.boxIn_keep h).1 (Ctx.boxIn_keep h).2.2) lw _
        (ShEnv.wf_ref hρ u (Ctx.boxIn_keep h).2.1)
      rw [Shp.box_eta (GFunc.shp _ _ _)] at this
      exact this
  | .root _, h => cases h
  | .step _ .fst, h => cases h
  | .step _ .snd, h => cases h
  | .step _ .dia, h => cases h
  | .step _ .here, h => cases h

theorem ShEnv.wf_diaPush {Γ : Ctx} {w : F.W} {lw : List Bool} {ρ : ShEnv F Root Γ w}
    (hρ : ρ.WF lw) {x : VarSymb} {X : VarType} (hx : Γ.ref x = some (.VTypeDia X)) :
    (ρ.diaPush lw.length x hx).WF (lw ++ [false]) := by
  intro v T h
  match v, h with
  | .step _ .dia, h =>
      have e := Ctx.diaIn_step_dia hx h
      subst e
      have := ShEnv.wf_ref hρ x hx
      rw [Shp.dia_eta (ρ.ref lw.length x hx)] at this
      exact this.2
  | .step u .box, h => exact shWF_relax lw _ (ShEnv.wf_boxPush hρ (.step u .box) T h)
  | .step u .keep, h => exact shWF_relax lw _ (ShEnv.wf_boxPush hρ (.step u .keep) T h)
  | .root _, h => cases h
  | .step _ .fst, h => cases h
  | .step _ .snd, h => cases h
  | .step _ .here, h => cases h

theorem ShEnv.wf_ref' {Γ : Ctx} {w : F.W} {lw : List Bool} {ρ : ShEnv F Root Γ w} {k : ℕ}
    (hρ : ρ.WF lw) (hk : lw.length = k) (v : VarSymb) {T : VarType} (h : Γ.ref v = some T) :
    ShWF lw (ρ.ref k v h) := by
  subst hk
  exact ShEnv.wf_ref hρ v h

theorem ShEnv.wf_boxPush' {Γ : Ctx} {w : F.W} {lw : List Bool} {ρ : ShEnv F Root Γ w} {k : ℕ}
    (hρ : ρ.WF lw) (hk : lw.length = k) : (ρ.boxPush k).WF (lw ++ [true]) := by
  subst hk
  exact ShEnv.wf_boxPush hρ

theorem ShEnv.wf_diaPush' {Γ : Ctx} {w : F.W} {lw : List Bool} {ρ : ShEnv F Root Γ w} {k : ℕ}
    (hρ : ρ.WF lw) (hk : lw.length = k) {x : VarSymb} {X : VarType}
    (hx : Γ.ref x = some (.VTypeDia X)) : (ρ.diaPush k x hx).WF (lw ++ [false]) := by
  subst hk
  exact ShEnv.wf_diaPush hρ hx

/-- ⭐**A term's symbolic shape is well-formed** in a well-formed environment. -/
theorem shWF_termShp : ∀ {Δ : Ctx} {w : F.W} {lw : List Bool} {ρ : ShEnv F Root Δ w},
    ρ.WF lw → ∀ {T : VarType} {a : Ann T} (t : Term σ Δ T a), ShWF lw (termShp ρ lw.length t)
  | _, _, _, _, _, _, _, .var _ _ => trivial
  | _, _, _, _, _, _, _, .func _ => trivial
  | _, _, _, _, _, _, _, .unit => trivial
  | _, _, _, _, hρ, _, _, .pair s t => ⟨shWF_termShp hρ s, shWF_termShp hρ t⟩
  | _, _, lw, _, hρ, _, _, .boxtm t => by
      have := shWF_termShp (ShEnv.wf_boxPush hρ) t
      simpa using this
  | _, _, lw, ρ, hρ, _, _, .diatm x hx t => by
      obtain ⟨X, hr⟩ := id hx
      rw [termShp_diatm ρ lw.length hr]
      have hl := ShEnv.wf_ref hρ x hr
      rw [Shp.dia_eta (ρ.ref lw.length x hr)] at hl
      exact ⟨hl.1, by simpa using shWF_termShp (ShEnv.wf_diaPush hρ hr) t⟩

/-- A collapse at level `j` passes through any map acting at a level below it, on a shape
    well-formed under 4 at a position crossing a `□` at `j` — keeping a possibility needs it. -/
theorem shp_mapCollapse (hT : ModalSys.T = true) (j : ℕ) {w : F.W} :
    ∀ {A B : VarType} (f : GFunc σ A B) (d : ℕ) (lw q : List Bool) (_hl : lw.length = j)
      (_hq : q.length = d) (a : Shape F Root w A)
      (_ha : ModalSys.Four = true → ShWF (lw ++ true :: q) a),
      GFunc.shp f (j + d) (a.map (Arrows.Leaf.collapse hT j)) =
        (GFunc.shp f (j + d + 1) a).map (Arrows.Leaf.collapse hT j)
  | _, _, .id _, _, _, _, _, _, _, _ => rfl
  | _, _, .comp g f, d, lw, q, hl, hq, a, ha => by
      simp only [GFunc.shp]
      have hlen : (lw ++ true :: q).length = j + d + 1 := by simp [hl, hq]; omega
      rw [shp_mapCollapse hT j f d lw q hl hq a ha,
        shp_mapCollapse hT j g d lw q hl hq _ (fun hF => by
          rw [← hlen]
          exact shWF_shp f _ a (ha hF))]
  | _, _, .fst, _, _, _, _, _, a, _ => Shp.map_fst _ a
  | _, _, .snd, _, _, _, _, _, a, _ => Shp.map_snd _ a
  | _, _, .pair f g, d, lw, q, hl, hq, a, ha => by
      simp only [GFunc.shp, Shp.map]
      rw [shp_mapCollapse hT j f d lw q hl hq a ha, shp_mapCollapse hT j g d lw q hl hq a ha]
  | _, _, .unit _, _, _, _, _, _, _, _ => rfl
  | _, _, .func _ _, _, _, _, _, _, _, _ => rfl
  | _, _, .boxMap f, d, lw, q, hl, hq, a, ha => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner]
      rw [show j + d + 1 = j + (d + 1) from rfl,
        shp_mapCollapse hT j f (d + 1) lw (q ++ [true]) hl (by simp [hq]) a.inner (fun hF => by
          have := ha hF
          rw [Shp.box_eta a] at this
          simpa [Shp.WF] using this)]
  | _, _, .boxPair _ _, _, _, _, _, _, a, _ => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner, Shp.map_fst, Shp.map_snd]
  | _, _, .boxUnit, _, _, _, _, _, _, _ => rfl
  | _, _, .diaMap f, d, lw, q, hl, hq, a, ha => by
      simp only [GFunc.shp, Shp.map, Shp.map_label, Shp.map_body]
      rw [show j + d + 1 = j + (d + 1) from rfl,
        shp_mapCollapse hT j f (d + 1) lw (q ++ [false]) hl (by simp [hq]) a.body (fun hF => by
          have := ha hF
          rw [Shp.dia_eta a] at this
          simpa [Shp.WF] using this.2)]
  | _, _, .strength _ _, _, _, _, _, _, a, _ => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner, Shp.map_fst, Shp.map_snd, Shp.map_label,
        Shp.map_body]
  | _, _, .extract hT', d, _, _, _, _, a, _ => by
      simp only [GFunc.shp, Shp.map_inner, Shp.map_map]
      exact Shp.map_congr (fun ℓ => Arrows.Leaf.collapse_collapse hT j d ℓ) _
  | _, _, .dup hF, d, _, _, _, _, a, _ => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner, Shp.map_map]
      congr 2
      exact Shp.map_congr (fun ℓ => Arrows.Leaf.shift_collapse hT hF j d ℓ) _
  | _, _, .dkeep hF, d, lw, q, hl, hq, a, ha => by
      -- ⭐The kept label by `dk_collapse` (the invariant), the inside by `dkB_collapse`.
      have hW := ha hF
      rw [Shp.dia_eta a] at hW
      subst hl
      subst hq
      simp only [GFunc.shp, Shp.map, Shp.map_map, Shp.map_label, Shp.map_body]
      rw [Arrows.Leaf.dk_collapse hT hF lw q a.label hW.1]
      congr 2
      exact Shp.map_congr_wf (P := fun lw ℓ => Arrows.Leaf.WF lw ℓ) (lw ++ true :: (q ++ [false]))
        (fun r ℓ hℓ => Arrows.Leaf.dkB_collapse hT hF lw (q ++ false :: r) q.length ℓ
          (by simpa using hℓ)) [] a.body (by simpa using hW.2)

omit [Arrows.RootKeepLaws F Root] in
/-- ⭐A leaf map **inserting a level** at `j`: it commutes with every operation acting below that
    level, moving it one level down — a shift (`shift_levelIns`).  Keeping the inside of a
    possibility does so on well-formed shapes (`shp_mapDkB`). -/
structure LevelIns {w : F.W} (j : ℕ) (g : F.Leaf Root w → F.Leaf Root w) : Prop where
  collapse : ∀ (hT : ModalSys.T = true) (d : ℕ) (ℓ : F.Leaf Root w),
    Arrows.Leaf.collapse hT (j + d + 2) (g ℓ) = g (Arrows.Leaf.collapse hT (j + d + 1) ℓ)
  shift : ∀ (hF : ModalSys.Four = true) (d : ℕ) (ℓ : F.Leaf Root w),
    Arrows.Leaf.shift hF (j + d + 2) (g ℓ) = g (Arrows.Leaf.shift hF (j + d + 1) ℓ)
  dk : ∀ (hF : ModalSys.Four = true) (d : ℕ) (ℓ : F.Leaf Root w),
    Arrows.Leaf.dk hF (j + d + 2) (g ℓ) = g (Arrows.Leaf.dk hF (j + d + 1) ℓ)
  dkB : ∀ (hF : ModalSys.Four = true) (d : ℕ) (ℓ : F.Leaf Root w),
    Arrows.Leaf.dkB hF (j + d + 2) (g ℓ) = g (Arrows.Leaf.dkB hF (j + d + 1) ℓ)

omit [Arrows.RootKeepLaws F Root] in
theorem shift_levelIns (hF : ModalSys.Four = true) (j : ℕ) {w : F.W} :
    LevelIns (w := w) j (Arrows.Leaf.shift (F := F) (Root := Root) hF j) :=
  ⟨fun hT d ℓ => Arrows.Leaf.collapse_shift hT hF j d ℓ,
    fun _ d ℓ => Arrows.Leaf.shift_shift hF j d ℓ,
    fun _ d ℓ => Arrows.Leaf.dk_shift hF j d ℓ,
    fun _ d ℓ => Arrows.Leaf.dkB_shift hF j d ℓ⟩

omit [Arrows.RootKeepLaws F Root] in
/-- ⭐**A level-inserting leaf map passes through any map acting below it.** -/
theorem shp_mapIns {w : F.W} {j : ℕ} {g : F.Leaf Root w → F.Leaf Root w}
    (hg : LevelIns j g) :
    ∀ {A B : VarType} (f : GFunc σ A B) (d : ℕ) (a : Shape F Root w A),
      GFunc.shp f (j + d + 2) (a.map g) =
        (GFunc.shp f (j + d + 1) a).map g
  | _, _, .id _, _, _ => rfl
  | _, _, .comp g₁ f, d, a => by
      simp only [GFunc.shp]
      rw [shp_mapIns hg f, shp_mapIns hg g₁]
  | _, _, .fst, _, a => Shp.map_fst _ a
  | _, _, .snd, _, a => Shp.map_snd _ a
  | _, _, .pair f g₁, d, a => by
      simp only [GFunc.shp, Shp.map]
      rw [shp_mapIns hg f, shp_mapIns hg g₁]
  | _, _, .unit _, _, _ => rfl
  | _, _, .func _ _, _, _ => rfl
  | _, _, .boxMap f, d, a => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner]
      rw [show j + d + 2 + 1 = j + (d + 1) + 2 by omega,
        show j + d + 1 + 1 = j + (d + 1) + 1 by omega, shp_mapIns hg f (d + 1)]
  | _, _, .boxPair _ _, _, a => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner, Shp.map_fst, Shp.map_snd]
  | _, _, .boxUnit, _, _ => rfl
  | _, _, .diaMap f, d, a => by
      simp only [GFunc.shp, Shp.map, Shp.map_label, Shp.map_body]
      rw [show j + d + 2 + 1 = j + (d + 1) + 2 by omega,
        show j + d + 1 + 1 = j + (d + 1) + 1 by omega, shp_mapIns hg f (d + 1)]
  | _, _, .strength _ _, _, a => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner, Shp.map_fst, Shp.map_snd, Shp.map_label,
        Shp.map_body]
  | _, _, .extract hT, d, a => by
      simp only [GFunc.shp, Shp.map_inner, Shp.map_map]
      exact Shp.map_congr (fun ℓ => hg.collapse hT d ℓ) _
  | _, _, .dup hF', d, a => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner, Shp.map_map]
      congr 2
      exact Shp.map_congr (fun ℓ => hg.shift hF' d ℓ) _
  | _, _, .dkeep hF', d, a => by
      simp only [GFunc.shp, Shp.map, Shp.map_map, Shp.map_label, Shp.map_body]
      rw [hg.dk hF' d]
      congr 2
      refine Shp.map_congr (fun ℓ => ?_) _
      exact hg.dkB hF' d ℓ

omit [Arrows.RootKeepLaws F Root] in
/-- A shift at level `j` passes through any map acting at a level below it. -/
theorem shp_mapShift (hF : ModalSys.Four = true) (j : ℕ) {w : F.W} :
    ∀ {A B : VarType} (f : GFunc σ A B) (d : ℕ) (a : Shape F Root w A),
      GFunc.shp f (j + d + 2) (a.map (Arrows.Leaf.shift hF j)) =
        (GFunc.shp f (j + d + 1) a).map (Arrows.Leaf.shift hF j) :=
  shp_mapIns (shift_levelIns hF j)

/-- Apply a leaf map to every shape of an environment. -/
def ShEnv.mapLeaves {Γ : Ctx} {w : F.W} (ρ : ShEnv F Root Γ w)
    (g : F.Leaf Root w → F.Leaf Root w) : ShEnv F Root Γ w :=
  fun v T h => (ρ v T h).map g

section MapLeaves

variable {Γ : Ctx} {w : F.W}

theorem ShEnv.ref_mapCollapse (hT : ModalSys.T = true) (j : ℕ) (ρ : ShEnv F Root Γ w) (d : ℕ)
    {lw q : List Bool} (hl : lw.length = j) (hq : q.length = d)
    (hρ : ModalSys.Four = true → ρ.WF (lw ++ true :: q)) :
    ∀ (v : VarSymb) {T : VarType} (h : Γ.ref v = some T),
      (ρ.mapLeaves (Arrows.Leaf.collapse hT j)).ref (j + d) v h =
        (ρ.ref (j + d + 1) v h).map (Arrows.Leaf.collapse hT j)
  | .root _, _, _ => rfl
  | .step v s, T, h => by
      by_cases hs : s.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Γ.ref v = some U := by
          rw [Ctx.ref_step_proj Γ v hs] at h
          cases hU : Γ.ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        rw [ShEnv.ref_proj _ _ hs hU h, ShEnv.ref_proj _ _ hs hU h,
          ShEnv.ref_mapCollapse hT j ρ d hl hq hρ v hU,
          shp_mapCollapse hT j _ d lw q hl hq _ (fun hF =>
            ShEnv.wf_ref' (hρ hF) (by simp [hl, hq]; omega) v hU)]
      · rw [ShEnv.ref_nonproj _ _ hs h, ShEnv.ref_nonproj _ _ hs h]
        rfl

omit [Arrows.RootKeepLaws F Root] in
theorem ShEnv.ref_mapIns {j : ℕ} {g : F.Leaf Root w → F.Leaf Root w} (hg : LevelIns j g)
    (ρ : ShEnv F Root Γ w) (d : ℕ) :
    ∀ (v : VarSymb) {T : VarType} (h : Γ.ref v = some T),
      (ρ.mapLeaves g).ref (j + d + 2) v h =
        (ρ.ref (j + d + 1) v h).map g
  | .root _, _, _ => rfl
  | .step v s, T, h => by
      by_cases hs : s.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Γ.ref v = some U := by
          rw [Ctx.ref_step_proj Γ v hs] at h
          cases hU : Γ.ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        rw [ShEnv.ref_proj _ _ hs hU h, ShEnv.ref_proj _ _ hs hU h,
          ShEnv.ref_mapIns hg ρ d v hU, shp_mapIns hg]
      · rw [ShEnv.ref_nonproj _ _ hs h, ShEnv.ref_nonproj _ _ hs h]
        rfl

omit [Arrows.RootKeepLaws F Root] in
theorem ShEnv.ref_mapShift (hF : ModalSys.Four = true) (j : ℕ) (ρ : ShEnv F Root Γ w) (d : ℕ) :
    ∀ (v : VarSymb) {T : VarType} (h : Γ.ref v = some T),
      (ρ.mapLeaves (Arrows.Leaf.shift hF j)).ref (j + d + 2) v h =
        (ρ.ref (j + d + 1) v h).map (Arrows.Leaf.shift hF j) :=
  ShEnv.ref_mapIns (shift_levelIns hF j) ρ d

theorem ShEnv.boxPush_mapCollapse (hT : ModalSys.T = true) (j : ℕ) (ρ : ShEnv F Root Γ w) (d : ℕ)
    {lw q : List Bool} (hl : lw.length = j) (hq : q.length = d)
    (hρ : ModalSys.Four = true → ρ.WF (lw ++ true :: q)) :
    (ρ.mapLeaves (Arrows.Leaf.collapse hT j)).boxPush (j + d) =
      (ρ.boxPush (j + d + 1)).mapLeaves (Arrows.Leaf.collapse hT j) := by
  funext v T h
  match v with
  | .step u .box =>
      simp only [ShEnv.boxPush, ShEnv.mapLeaves]
      rw [ShEnv.ref_mapCollapse hT j ρ d hl hq hρ, Shp.map_inner]
  | .step u .keep =>
      simp only [ShEnv.boxPush, ShEnv.mapLeaves]
      rw [ShEnv.ref_mapCollapse hT j ρ d hl hq hρ,
        shp_mapCollapse hT j _ d lw q hl hq _ (fun hF =>
          ShEnv.wf_ref' (hρ hF) (by simp [hl, hq]; omega) u (Ctx.boxIn_keep h).2.1),
        Shp.map_inner]
  | .root _ => cases h
  | .step _ .fst => cases h
  | .step _ .snd => cases h
  | .step _ .dia => cases h
  | .step _ .here => cases h

omit [Arrows.RootKeepLaws F Root] in
theorem ShEnv.boxPush_mapIns {j : ℕ} {g : F.Leaf Root w → F.Leaf Root w} (hg : LevelIns j g)
    (ρ : ShEnv F Root Γ w) (d : ℕ) :
    (ρ.mapLeaves g).boxPush (j + d + 2) =
      (ρ.boxPush (j + d + 1)).mapLeaves g := by
  funext v T h
  match v with
  | .step u .box =>
      simp only [ShEnv.boxPush, ShEnv.mapLeaves]
      rw [ShEnv.ref_mapIns hg ρ d, Shp.map_inner]
  | .step u .keep =>
      simp only [ShEnv.boxPush, ShEnv.mapLeaves]
      rw [ShEnv.ref_mapIns hg ρ d, shp_mapIns hg, Shp.map_inner]
  | .root _ => cases h
  | .step _ .fst => cases h
  | .step _ .snd => cases h
  | .step _ .dia => cases h
  | .step _ .here => cases h

omit [Arrows.RootKeepLaws F Root] in
theorem ShEnv.boxPush_mapShift (hF : ModalSys.Four = true) (j : ℕ) (ρ : ShEnv F Root Γ w) (d : ℕ) :
    (ρ.mapLeaves (Arrows.Leaf.shift hF j)).boxPush (j + d + 2) =
      (ρ.boxPush (j + d + 1)).mapLeaves (Arrows.Leaf.shift hF j) :=
  ShEnv.boxPush_mapIns (shift_levelIns hF j) ρ d

theorem ShEnv.diaPush_mapCollapse (hT : ModalSys.T = true) (j : ℕ) (ρ : ShEnv F Root Γ w) (d : ℕ)
    {lw q : List Bool} (hl : lw.length = j) (hq : q.length = d)
    (hρ : ModalSys.Four = true → ρ.WF (lw ++ true :: q))
    {x : VarSymb} {X : VarType} (hx : Γ.ref x = some (.VTypeDia X)) :
    (ρ.mapLeaves (Arrows.Leaf.collapse hT j)).diaPush (j + d) x hx =
      (ρ.diaPush (j + d + 1) x hx).mapLeaves (Arrows.Leaf.collapse hT j) := by
  funext v T h
  match v with
  | .step _ .dia =>
      have e := Ctx.diaIn_step_dia hx h
      subst e
      simp only [ShEnv.diaPush, ShEnv.mapLeaves]
      rw [ShEnv.ref_mapCollapse hT j ρ d hl hq hρ, Shp.map_body]
  | .step u .box =>
      exact congrFun (congrFun (congrFun (ShEnv.boxPush_mapCollapse hT j ρ d hl hq hρ)
        (.step u .box)) T) h
  | .step u .keep =>
      exact congrFun (congrFun (congrFun (ShEnv.boxPush_mapCollapse hT j ρ d hl hq hρ)
        (.step u .keep)) T) h
  | .root _ => cases h
  | .step _ .fst => cases h
  | .step _ .snd => cases h
  | .step _ .here => cases h

omit [Arrows.RootKeepLaws F Root] in
theorem ShEnv.diaPush_mapIns {j : ℕ} {g : F.Leaf Root w → F.Leaf Root w} (hg : LevelIns j g)
    (ρ : ShEnv F Root Γ w) (d : ℕ)
    {x : VarSymb} {X : VarType} (hx : Γ.ref x = some (.VTypeDia X)) :
    (ρ.mapLeaves g).diaPush (j + d + 2) x hx =
      (ρ.diaPush (j + d + 1) x hx).mapLeaves g := by
  funext v T h
  match v with
  | .step _ .dia =>
      have e := Ctx.diaIn_step_dia hx h
      subst e
      simp only [ShEnv.diaPush, ShEnv.mapLeaves]
      rw [ShEnv.ref_mapIns hg ρ d, Shp.map_body]
  | .step u .box =>
      exact congrFun (congrFun (congrFun (ShEnv.boxPush_mapIns hg ρ d) (.step u .box)) T) h
  | .step u .keep =>
      exact congrFun (congrFun (congrFun (ShEnv.boxPush_mapIns hg ρ d) (.step u .keep)) T) h
  | .root _ => cases h
  | .step _ .fst => cases h
  | .step _ .snd => cases h
  | .step _ .here => cases h

omit [Arrows.RootKeepLaws F Root] in
theorem ShEnv.diaPush_mapShift (hF : ModalSys.Four = true) (j : ℕ) (ρ : ShEnv F Root Γ w) (d : ℕ)
    {x : VarSymb} {X : VarType} (hx : Γ.ref x = some (.VTypeDia X)) :
    (ρ.mapLeaves (Arrows.Leaf.shift hF j)).diaPush (j + d + 2) x hx =
      (ρ.diaPush (j + d + 1) x hx).mapLeaves (Arrows.Leaf.shift hF j) :=
  ShEnv.diaPush_mapIns (shift_levelIns hF j) ρ d hx

end MapLeaves

/-- ⭐Collapsing a whole environment at level `j` passes through `termShp`, in an environment
    well-formed under 4 at a position crossing a `□` at `j`. -/
theorem termShp_mapCollapse (hT : ModalSys.T = true) (j : ℕ) :
    ∀ {Γ : Ctx} {w : F.W} (ρ : ShEnv F Root Γ w) (d : ℕ) {lw q : List Bool}
      (_hl : lw.length = j) (_hq : q.length = d)
      (_hρ : ModalSys.Four = true → ρ.WF (lw ++ true :: q)) {T : VarType} {a : Ann T}
      (t : Term σ Γ T a),
      termShp (ρ.mapLeaves (Arrows.Leaf.collapse hT j)) (j + d) t =
        (termShp ρ (j + d + 1) t).map (Arrows.Leaf.collapse hT j)
  | _, _, _, _, _, _, _, _, _, _, _, .var _ _ => rfl
  | _, _, _, _, _, _, _, _, _, _, _, .func _ => rfl
  | _, _, _, _, _, _, _, _, _, _, _, .unit => rfl
  | _, _, ρ, d, _, _, hl, hq, hρ, _, _, .pair s t => by
      simp only [termShp, Shp.map]
      rw [termShp_mapCollapse hT j ρ d hl hq hρ s, termShp_mapCollapse hT j ρ d hl hq hρ t]
  | _, _, ρ, d, lw, q, hl, hq, hρ, _, _, .boxtm t => by
      simp only [termShp, Shp.map]
      rw [ShEnv.boxPush_mapCollapse hT j ρ d hl hq hρ, show j + d + 1 = j + (d + 1) from rfl,
        termShp_mapCollapse hT j _ (d + 1) (q := q ++ [true]) hl (by simp [hq])
          (fun hF => by
            have := ShEnv.wf_boxPush' (hρ hF) (k := j + d + 1) (by simp [hl, hq]; omega)
            simpa using this) t]
  | _, _, ρ, d, lw, q, hl, hq, hρ, _, _, .diatm x hx t => by
      obtain ⟨X, hr⟩ := id hx
      rw [termShp_diatm _ _ hr, termShp_diatm _ _ hr, ShEnv.ref_mapCollapse hT j ρ d hl hq hρ,
        ShEnv.diaPush_mapCollapse hT j ρ d hl hq hρ hr, show j + d + 1 = j + (d + 1) from rfl,
        termShp_mapCollapse hT j _ (d + 1) (q := q ++ [false]) hl (by simp [hq])
          (fun hF => by
            have := ShEnv.wf_diaPush' (hρ hF) (k := j + d + 1) (by simp [hl, hq]; omega) hr
            simpa using this) t]
      simp only [Shp.map, Shp.map_label]

omit [Arrows.RootKeepLaws F Root] in
/-- ⭐**A level-inserting leaf map passes through `termShp`**, one level further in. -/
theorem termShp_mapIns {w : F.W} {j : ℕ} {g : F.Leaf Root w → F.Leaf Root w}
    (hg : LevelIns j g) :
    ∀ {Γ : Ctx} (ρ : ShEnv F Root Γ w) (d : ℕ) {T : VarType} {a : Ann T}
      (t : Term σ Γ T a),
      termShp (ρ.mapLeaves g) (j + d + 2) t =
        (termShp ρ (j + d + 1) t).map g
  | _, _, _, _, _, .var _ _ => rfl
  | _, _, _, _, _, .func _ => rfl
  | _, _, _, _, _, .unit => rfl
  | _, ρ, d, _, _, .pair s t => by
      simp only [termShp, Shp.map]
      rw [termShp_mapIns hg ρ d s, termShp_mapIns hg ρ d t]
  | _, ρ, d, _, _, .boxtm t => by
      simp only [termShp, Shp.map]
      rw [ShEnv.boxPush_mapIns hg ρ d, show j + d + 2 + 1 = j + (d + 1) + 2 by omega,
        show j + d + 1 + 1 = j + (d + 1) + 1 by omega, termShp_mapIns hg _ (d + 1) t]
  | _, ρ, d, _, _, .diatm x hx t => by
      obtain ⟨X, hr⟩ := id hx
      rw [termShp_diatm _ _ hr, termShp_diatm _ _ hr, ShEnv.ref_mapIns hg ρ d,
        ShEnv.diaPush_mapIns hg ρ d hr, show j + d + 2 + 1 = j + (d + 1) + 2 by omega,
        show j + d + 1 + 1 = j + (d + 1) + 1 by omega, termShp_mapIns hg _ (d + 1) t]
      simp only [Shp.map, Shp.map_label]


omit [Arrows.RootKeepLaws F Root] in
/-- ⭐Shifting a whole environment at level `j` passes through `termShp`, one level further in. -/
theorem termShp_mapShift (hF : ModalSys.Four = true) (j : ℕ) {Γ : Ctx} {w : F.W}
    (ρ : ShEnv F Root Γ w) (d : ℕ) {T : VarType} {a : Ann T} (t : Term σ Γ T a) :
    termShp (ρ.mapLeaves (Arrows.Leaf.shift hF j)) (j + d + 2) t =
      (termShp ρ (j + d + 1) t).map (Arrows.Leaf.shift hF j) :=
  termShp_mapIns (shift_levelIns hF j) ρ d t

/-! ### Keeping the inside of a possibility at a level, on well-formed shapes -/

/-- ⭐**Keeping the inside of a possibility at `j` passes through any map acting below it**, on a
    shape well-formed at a position with a `◇` at `j`: as a level insertion (`shp_mapIns`), but
    at the anchor's level by the root action's naturality, which asks for well-formedness. -/
theorem shp_mapDkB (hF : ModalSys.Four = true) (j : ℕ) {w : F.W} :
    ∀ {A B : VarType} (f : GFunc σ A B) (d : ℕ) (lw q : List Bool) (_hl : lw.length = j)
      (_hq : q.length = d) (a : Shape F Root w A) (_ha : ShWF (lw ++ false :: q) a),
      GFunc.shp f (j + d + 2) (a.map (Arrows.Leaf.dkB hF j)) =
        (GFunc.shp f (j + d + 1) a).map (Arrows.Leaf.dkB hF j)
  | _, _, .id _, _, _, _, _, _, _, _ => rfl
  | _, _, .comp g f, d, lw, q, hl, hq, a, ha => by
      simp only [GFunc.shp]
      have hlen : (lw ++ false :: q).length = j + d + 1 := by simp [hl, hq]; omega
      rw [shp_mapDkB hF j f d lw q hl hq a ha,
        shp_mapDkB hF j g d lw q hl hq _ (by rw [← hlen]; exact shWF_shp f _ a ha)]
  | _, _, .fst, _, _, _, _, _, a, _ => Shp.map_fst _ a
  | _, _, .snd, _, _, _, _, _, a, _ => Shp.map_snd _ a
  | _, _, .pair f g, d, lw, q, hl, hq, a, ha => by
      simp only [GFunc.shp, Shp.map]
      rw [shp_mapDkB hF j f d lw q hl hq a ha, shp_mapDkB hF j g d lw q hl hq a ha]
  | _, _, .unit _, _, _, _, _, _, _, _ => rfl
  | _, _, .func _ _, _, _, _, _, _, _, _ => rfl
  | _, _, .boxMap f, d, lw, q, hl, hq, a, ha => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner]
      rw [show j + d + 2 + 1 = j + (d + 1) + 2 by omega,
        show j + d + 1 + 1 = j + (d + 1) + 1 by omega,
        shp_mapDkB hF j f (d + 1) lw (q ++ [true]) hl (by simp [hq]) a.inner (by
          rw [Shp.box_eta a] at ha
          simpa [Shp.WF] using ha)]
  | _, _, .boxPair _ _, _, _, _, _, _, a, _ => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner, Shp.map_fst, Shp.map_snd]
  | _, _, .boxUnit, _, _, _, _, _, _, _ => rfl
  | _, _, .diaMap f, d, lw, q, hl, hq, a, ha => by
      simp only [GFunc.shp, Shp.map, Shp.map_label, Shp.map_body]
      rw [show j + d + 2 + 1 = j + (d + 1) + 2 by omega,
        show j + d + 1 + 1 = j + (d + 1) + 1 by omega,
        shp_mapDkB hF j f (d + 1) lw (q ++ [false]) hl (by simp [hq]) a.body (by
          rw [Shp.dia_eta a] at ha
          simpa [Shp.WF] using ha.2)]
  | _, _, .strength _ _, _, _, _, _, _, a, _ => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner, Shp.map_fst, Shp.map_snd, Shp.map_label,
        Shp.map_body]
  | _, _, .extract hT, d, lw, q, hl, hq, a, ha => by
      simp only [GFunc.shp, Shp.map_inner, Shp.map_map]
      rw [Shp.box_eta a] at ha
      exact Shp.map_congr_wf (P := fun lw ℓ => Arrows.Leaf.WF lw ℓ) (lw ++ false :: q ++ [true])
        (fun r ℓ hℓ => Arrows.Leaf.collapse_dkB hT hF j d lw q r ℓ hl hq (by simpa using hℓ))
        [] a.inner (by simpa [Shp.WF] using ha)
  | _, _, .dup hF', d, lw, q, hl, hq, a, ha => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner, Shp.map_map]
      rw [Shp.box_eta a] at ha
      congr 2
      exact Shp.map_congr_wf (P := fun lw ℓ => Arrows.Leaf.WF lw ℓ) (lw ++ false :: q ++ [true])
        (fun r ℓ hℓ => Arrows.Leaf.shift_dkB_far hF j d lw q r ℓ hl hq (by simpa using hℓ))
        [] a.inner (by simpa [Shp.WF] using ha)
  | _, _, .dkeep hF', d, lw, q, hl, hq, a, ha => by
      rw [Shp.dia_eta a] at ha
      simp only [GFunc.shp, Shp.map, Shp.map_map, Shp.map_label, Shp.map_body]
      rw [Arrows.Leaf.dk_dkB hF j d lw q a.label hl hq ha.1]
      congr 2
      exact Shp.map_congr_wf (P := fun lw ℓ => Arrows.Leaf.WF lw ℓ) (lw ++ false :: q ++ [false])
        (fun r ℓ hℓ => Arrows.Leaf.dkB_dkB hF j d lw q r ℓ hl hq (by simpa using hℓ))
        [] a.body (by simpa using ha.2)

section MapDkB

variable {Γ : Ctx} {w : F.W}

theorem ShEnv.ref_mapDkB (hF : ModalSys.Four = true) (j : ℕ) (ρ : ShEnv F Root Γ w) (d : ℕ)
    {lw q : List Bool} (hl : lw.length = j) (hq : q.length = d)
    (hρ : ρ.WF (lw ++ false :: q)) :
    ∀ (v : VarSymb) {T : VarType} (h : Γ.ref v = some T),
      (ρ.mapLeaves (Arrows.Leaf.dkB hF j)).ref (j + d + 2) v h =
        (ρ.ref (j + d + 1) v h).map (Arrows.Leaf.dkB hF j)
  | .root _, _, _ => rfl
  | .step v s, T, h => by
      by_cases hs : s.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Γ.ref v = some U := by
          rw [Ctx.ref_step_proj Γ v hs] at h
          cases hU : Γ.ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        rw [ShEnv.ref_proj _ _ hs hU h, ShEnv.ref_proj _ _ hs hU h,
          ShEnv.ref_mapDkB hF j ρ d hl hq hρ v hU,
          shp_mapDkB hF j _ d lw q hl hq _
            (ShEnv.wf_ref' hρ (by simp [hl, hq]; omega) v hU)]
      · rw [ShEnv.ref_nonproj _ _ hs h, ShEnv.ref_nonproj _ _ hs h]
        rfl

theorem ShEnv.boxPush_mapDkB (hF : ModalSys.Four = true) (j : ℕ) (ρ : ShEnv F Root Γ w) (d : ℕ)
    {lw q : List Bool} (hl : lw.length = j) (hq : q.length = d)
    (hρ : ρ.WF (lw ++ false :: q)) :
    (ρ.mapLeaves (Arrows.Leaf.dkB hF j)).boxPush (j + d + 2) =
      (ρ.boxPush (j + d + 1)).mapLeaves (Arrows.Leaf.dkB hF j) := by
  funext v T h
  match v with
  | .step u .box =>
      simp only [ShEnv.boxPush, ShEnv.mapLeaves]
      rw [ShEnv.ref_mapDkB hF j ρ d hl hq hρ, Shp.map_inner]
  | .step u .keep =>
      simp only [ShEnv.boxPush, ShEnv.mapLeaves]
      rw [ShEnv.ref_mapDkB hF j ρ d hl hq hρ,
        shp_mapDkB hF j _ d lw q hl hq _
          (ShEnv.wf_ref' hρ (by simp [hl, hq]; omega) u (Ctx.boxIn_keep h).2.1),
        Shp.map_inner]
  | .root _ => cases h
  | .step _ .fst => cases h
  | .step _ .snd => cases h
  | .step _ .dia => cases h
  | .step _ .here => cases h

theorem ShEnv.diaPush_mapDkB (hF : ModalSys.Four = true) (j : ℕ) (ρ : ShEnv F Root Γ w) (d : ℕ)
    {lw q : List Bool} (hl : lw.length = j) (hq : q.length = d)
    (hρ : ρ.WF (lw ++ false :: q))
    {x : VarSymb} {X : VarType} (hx : Γ.ref x = some (.VTypeDia X)) :
    (ρ.mapLeaves (Arrows.Leaf.dkB hF j)).diaPush (j + d + 2) x hx =
      (ρ.diaPush (j + d + 1) x hx).mapLeaves (Arrows.Leaf.dkB hF j) := by
  funext v T h
  match v with
  | .step _ .dia =>
      have e := Ctx.diaIn_step_dia hx h
      subst e
      simp only [ShEnv.diaPush, ShEnv.mapLeaves]
      rw [ShEnv.ref_mapDkB hF j ρ d hl hq hρ, Shp.map_body]
  | .step u .box =>
      exact congrFun (congrFun (congrFun (ShEnv.boxPush_mapDkB hF j ρ d hl hq hρ)
        (.step u .box)) T) h
  | .step u .keep =>
      exact congrFun (congrFun (congrFun (ShEnv.boxPush_mapDkB hF j ρ d hl hq hρ)
        (.step u .keep)) T) h
  | .root _ => cases h
  | .step _ .fst => cases h
  | .step _ .snd => cases h
  | .step _ .here => cases h

end MapDkB

/-- ⭐**Keeping the inside of a possibility at `j`, over a whole environment, passes through
    `termShp`**, one level further in, in an environment well-formed at a position with a `◇` at
    `j`. -/
theorem termShp_mapDkB (hF : ModalSys.Four = true) (j : ℕ) :
    ∀ {Γ : Ctx} {w : F.W} (ρ : ShEnv F Root Γ w) (d : ℕ) {lw q : List Bool}
      (_hl : lw.length = j) (_hq : q.length = d) (_hρ : ρ.WF (lw ++ false :: q))
      {T : VarType} {a : Ann T} (t : Term σ Γ T a),
      termShp (ρ.mapLeaves (Arrows.Leaf.dkB hF j)) (j + d + 2) t =
        (termShp ρ (j + d + 1) t).map (Arrows.Leaf.dkB hF j)
  | _, _, _, _, _, _, _, _, _, _, _, .var _ _ => rfl
  | _, _, _, _, _, _, _, _, _, _, _, .func _ => rfl
  | _, _, _, _, _, _, _, _, _, _, _, .unit => rfl
  | _, _, ρ, d, _, _, hl, hq, hρ, _, _, .pair s t => by
      simp only [termShp, Shp.map]
      rw [termShp_mapDkB hF j ρ d hl hq hρ s, termShp_mapDkB hF j ρ d hl hq hρ t]
  | _, _, ρ, d, lw, q, hl, hq, hρ, _, _, .boxtm t => by
      simp only [termShp, Shp.map]
      rw [ShEnv.boxPush_mapDkB hF j ρ d hl hq hρ, show j + d + 2 + 1 = j + (d + 1) + 2 by omega,
        show j + d + 1 + 1 = j + (d + 1) + 1 by omega,
        termShp_mapDkB hF j _ (d + 1) (q := q ++ [true]) hl (by simp [hq])
          (by
            have := ShEnv.wf_boxPush' hρ (k := j + d + 1) (by simp [hl, hq]; omega)
            simpa using this) t]
  | _, _, ρ, d, lw, q, hl, hq, hρ, _, _, .diatm x hx t => by
      obtain ⟨X, hr⟩ := id hx
      rw [termShp_diatm _ _ hr, termShp_diatm _ _ hr, ShEnv.ref_mapDkB hF j ρ d hl hq hρ,
        ShEnv.diaPush_mapDkB hF j ρ d hl hq hρ hr, show j + d + 2 + 1 = j + (d + 1) + 2 by omega,
        show j + d + 1 + 1 = j + (d + 1) + 1 by omega,
        termShp_mapDkB hF j _ (d + 1) (q := q ++ [false]) hl (by simp [hq])
          (by
            have := ShEnv.wf_diaPush' hρ (k := j + d + 1) (by simp [hl, hq]; omega) hr
            simpa using this) t]
      simp only [Shp.map, Shp.map_label]

section ModelShapes

variable {M : Model.{u, v} σ}

/-! ## S2: the shape of a value is its symbolic shape -/

/-- ⭐**Every object's shape is well-formed**: a necessary one's is a transposition, a possible
    one's is well-formed by the model's law (`Model.posShape_wf`). -/
theorem shWF_domSh (hSh : ModalSys.shaped = true) :
    ∀ {A : VarType} {w : M.frame.W} (o : M.frame.Dom A w),
      ShWF (F := M.arrows) (Root := M.RootPoss) []
        (Frame.domShape M.necEval (fun q => (M.posFull q).2 hSh) o)
  | .Var, _, _ => trivial
  | .VTypeOne, _, _ => trivial
  | .VTypeProd _ _, _, o => ⟨shWF_domSh hSh o.1, shWF_domSh hSh o.2⟩
  | .VTypeBox _, _, n =>
      shWF_transpose true [] _ fun s => shWF_domSh hSh (M.necEval n s)
  | .VTypeDia _, _, p => M.posShape_wf hSh p

/-- The shape of an object, when shaped. -/
abbrev domSh (hSh : ModalSys.shaped = true) {A : VarType} {w : M.frame.W} (o : M.frame.Dom A w) :
    Shape M.arrows M.RootPoss w A :=
  Frame.domShape M.necEval (M.shape hSh) o

/-- The shapes of an environment's objects. -/
def envShape (hSh : ModalSys.shaped = true) {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) :
    ShEnv M.arrows M.RootPoss Γ w :=
  fun v T h => domSh hSh (env v T h)

/-- ⭐A model's environment has well-formed shapes. -/
theorem envShape_wf (hSh : ModalSys.shaped = true) {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) :
    (envShape hSh env).WF [] :=
  fun v T h => shWF_domSh hSh (env v T h)

theorem Env.ref_proj' {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {v : VarSymb} {s : Step}
    (hs : s.isProj = true) {U T : VarType} (hU : Γ.ref v = some U)
    (h : Γ.ref (.step v s) = some T) :
    env.ref (.step v s) h =
      M.stepObj hs (by rw [Ctx.ref_step_proj Γ v hs, hU] at h; exact h) (env.ref v hU) := by
  rw [Env.ref, dif_pos hs]
  split
  · rename_i U' hU'
    obtain rfl : U = U' := Option.some.inj (hU.symm.trans hU')
    rfl
  · rename_i hU'
    exfalso
    rw [hU] at hU'
    cases hU'

theorem Env.ref_nonproj' {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {v : VarSymb} {s : Step}
    (hs : ¬ s.isProj = true) {T : VarType} (h : Γ.ref (.step v s) = some T) :
    env.ref (.step v s) h = env (.step v s) T (by rw [Ctx.ref_step_nonproj Γ v hs] at h; exact h) :=
  by rw [Env.ref, dif_neg hs]

theorem domSh_stepObj (hSh : ModalSys.shaped = true) {w : M.frame.W} {U T : VarType} {s : Step}
    (hs : s.isProj = true) (h : U.step s = some T) (a : M.frame.Dom U w) :
    domSh hSh (M.stepObj hs h a) = GFunc.shp (GFunc.proj (σ := σ) hs h) 0 (domSh hSh a) := by
  cases U <;> cases s <;> (try cases hs) <;> (try cases h)
  · rfl
  · rfl
  · obtain ⟨hT, rfl⟩ := VarType.step_here h
    change domSh hSh (M.necEval a (M.frame.reflAcc hT w)) =
      (Arrows.transposeShp fun s => domSh hSh (M.necEval a s)).map (Arrows.Leaf.collapse hT 0)
    exact (transpose_collapse_zero hT fun s => domSh hSh (M.necEval a s)).symm

/-- The symbolic shape at an address is the shape of the object there. -/
theorem ref_envShape (hSh : ModalSys.shaped = true) {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) :
    ∀ (v : VarSymb) {T : VarType} (h : Γ.ref v = some T),
      (envShape hSh env).ref 0 v h = domSh hSh (env.ref v h)
  | .root _, _, _ => rfl
  | .step v s, T, h => by
      by_cases hs : s.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Γ.ref v = some U := by
          rw [Ctx.ref_step_proj Γ v hs] at h
          cases hU : Γ.ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        rw [ShEnv.ref_proj _ 0 hs hU h, ref_envShape hSh env v hU, Env.ref_proj' env hs hU h,
          domSh_stepObj]
      · rw [ShEnv.ref_nonproj _ 0 hs h, Env.ref_nonproj' env hs h]
        rfl

/-- Pushing the shapes of an environment into a `□` is transposing the shapes of the pushed
    environments. -/
theorem boxPush_envShape (hSh : ModalSys.shaped = true) {Γ : Ctx} {w : M.frame.W}
    (env : M.Env Γ w) :
    ∀ v T h, (envShape hSh env).boxPush 0 v T h =
      Arrows.transposeShp fun s => envShape hSh (env.boxPush s) v T h
  | .step u .box, _, h => by
      simp only [ShEnv.boxPush]
      rw [ref_envShape]
      rfl
  | .step u .keep, T, h => by
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep h
      cases T with
      | VTypeBox A =>
          simp only [ShEnv.boxPush]
          rw [ref_envShape]
          change Shp.box ((Arrows.transposeShp fun s =>
              domSh hSh (M.necEval (env.ref u hu) s)).map (Arrows.Leaf.shift hF 0)) = _
          rw [transpose_shift_zero]
          change _ = Arrows.transposeShp fun s => Shp.box (Arrows.transposeShp fun t =>
              domSh hSh (M.necEval (M.necEval (M.ops.necDup hF (env.ref u hu)) s) t))
          simp only [M.necDup_eval]
          rfl
      | VTypeDia A =>
          simp only [ShEnv.boxPush]
          rw [ref_envShape]
          change Shp.dia (Arrows.Leaf.dk hF 0 ((M.posFull (env.ref u hu)).2 hSh).label)
            (((M.posFull (env.ref u hu)).2 hSh).body.map (Arrows.Leaf.dkB hF 0)) = _
          change _ = Arrows.transposeShp fun s =>
            (M.posFull (M.necEval (M.ops.posKeep hF (env.ref u hu)) s)).2 hSh
          simp only [M.posKeep_full]
          rw [transpose_map_const]
          conv_rhs => rw [Shp.dia_eta ((M.posFull (env.ref u hu)).2 hSh)]
          rfl
      | _ => cases hk
  | .root _, _, h => by cases h
  | .step _ .fst, _, h => by cases h
  | .step _ .snd, _, h => by cases h
  | .step _ .dia, _, h => by cases h
  | .step _ .here, _, h => by cases h

theorem domSh_bundle (hSh : ModalSys.shaped = true) {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) :
    ∀ L : Supp Δ, domSh hSh (env.bundle L) = (envShape hSh env).bundle L
  | [] => rfl
  | _ :: L => by
      change Shp.prod _ (domSh hSh (env.bundle L)) = _
      rw [domSh_bundle hSh env L]
      rfl

theorem ShEnv.bundle_transpose {Γ : Ctx} {w : M.frame.W} (τ : ShEnv M.arrows M.RootPoss Γ w)
    (ρ : (s : M.frame.Acc w) → ShEnv M.arrows M.RootPoss Γ s.1)
    (hτ : ∀ v T h, τ v T h = Arrows.transposeShp fun s => ρ s v T h) :
    ∀ L : Supp Γ, τ.bundle L = Arrows.transposeShp fun s => (ρ s).bundle L
  | [] => rfl
  | e :: L => by
      simp only [ShEnv.bundle]
      rw [hτ, ShEnv.bundle_transpose τ ρ hτ L]
      rfl

theorem interp_diatm {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) {x : VarSymb} {X : VarType}
    (hr : Δ.ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (hx : ∃ X, Δ.ref x = some (.VTypeDia X)) (t : Term σ (Δ.diaIn x) A a) :
    interp env (Term.diatm x hx t) =
      M.ops.posMap (Term.compile (Term.bases t) t (Supp.mem_self _))
        (M.ops.posMap (Supp.assemble hr (Term.bases t))
          (M.ops.posStrength (env.necBundle (Supp.boxPart (Term.bases t))) (env.ref x hr))) := by
  simp only [interp]
  split
  · rename_i X' hr'
    obtain rfl : X = X' := by
      rw [hr] at hr'
      cases hr'
      rfl
    rfl
  all_goals
    rename_i heq
    exfalso
    rw [hr] at heq
    cases heq

/-- ⭐**S2**: the shape of a term's value is its symbolic shape. -/
theorem domSh_interp (hSh : ModalSys.shaped = true) {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) :
    ∀ {T : VarType} {a : Ann T} (t : Term σ Δ T a),
      domSh hSh (interp env t) = termShp (envShape hSh env) 0 t
  | _, _, .var _ _ => shp_var_eq _ _
  | _, _, .func _ => shp_var_eq _ _
  | _, _, .unit => rfl
  | _, _, .pair s t => by
      change Shp.prod (domSh hSh (interp env s)) (domSh hSh (interp env t)) = _
      rw [domSh_interp hSh env s, domSh_interp hSh env t]
      rfl
  | _, _, .boxtm t => by
      change Shp.box (Arrows.transposeShp fun s =>
          domSh hSh (M.necEval (interp env (Term.boxtm t)) s)) =
        Shp.box (termShp ((envShape hSh env).boxPush 0) (0 + 1) t)
      rw [termShp_transpose ((envShape hSh env).boxPush 0) (fun s => envShape hSh (env.boxPush s)) 0
        (boxPush_envShape hSh env)]
      simp only [box_beta, domSh_interp hSh _ t]
  | _, _, .diatm x hx t => by
      obtain ⟨X, hr⟩ := id hx
      rw [termShp_diatm _ 0 hr, interp_diatm env hr hx t]
      change M.shape hSh _ = _
      simp only [M.shape_posMap, M.shape_posStrength, Shp.label_dia, Shp.body_dia]
      rw [ref_envShape,
        ← termShp_compile ((envShape hSh env).diaPush 0 x hr) (0 + 1) (Term.bases t) t
          (Supp.mem_self _),
        ← assemble_shp (envShape hSh env) 0 hr,
        ShEnv.bundle_transpose ((envShape hSh env).boxPush 0)
          (fun s => envShape hSh (env.boxPush s))
          (boxPush_envShape hSh env)]
      simp only [necBundle_eval, domSh_bundle]
      rw [ref_envShape]
      rfl

end ModelShapes

end Model

end V12M
