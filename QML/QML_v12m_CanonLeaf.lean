import QML.QML_v12m_CanonExist

/-!
# QML v12m — the canonical leaf of a label

The labelling convention of docs §10.39, as a function, and what it buys: **canonical shapes
determine annotations**.

*A leaf records a label address by cutting it where it leaves the anchor's level.*  `leafOf w m y`
is the leaf, anchored at `w`, of an address `y` whose last `m` level steps are views entered from
`w`.  If the outermost of them is `dia`, the rest is kept as a path from the root possibility; if it
is a `□` step, it is a family over `w`'s successors, each entry the leaf of the address as seen from
there (`succAddrK`).

This file has the address-level layer first: which steps the flags allow (`Step.OK`), cutting an
address (`VarSymb.splitAt`), the agreement of the leaf operations on paths with collapse and shift
on addresses, and `succAddrK`.
-/

namespace V12M

/-! ## Cutting an address -/

theorem Step.levels_single (s : Step) : Step.levels [s] = if s.isProj then 0 else 1 := by
  simp [Step.levels]

/-- Split an address before the level step with exactly `k` level steps after it: the part before,
    the step, and the steps after it. -/
def VarSymb.splitAt : VarSymb → ℕ → Option (VarSymb × Step × List Step)
  | .root _, _ => none
  | .step v s, k =>
      if s.isProj then (VarSymb.splitAt v k).map fun q => (q.1, q.2.1, q.2.2 ++ [s])
      else match k with
        | 0 => some (v, s, [])
        | k + 1 => (VarSymb.splitAt v k).map fun q => (q.1, q.2.1, q.2.2 ++ [s])

theorem VarSymb.splitAt_spec : ∀ {y : VarSymb} {k : ℕ} {pre : VarSymb} {s : Step}
    {rest : List Step}, VarSymb.splitAt y k = some (pre, s, rest) →
    y = pre.ext (s :: rest) ∧ s.isProj = false ∧ Step.levels rest = k
  | .root _, _, _, _, _, h => by cases h
  | .step v t, k, pre, s, rest, h => by
      by_cases ht : t.isProj = true
      · simp only [VarSymb.splitAt, if_pos ht] at h
        obtain ⟨⟨pre', s', rest'⟩, hq, he⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hy, hs, hl⟩ := VarSymb.splitAt_spec hq
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        refine ⟨?_, hs, ?_⟩
        · rw [hy, VarSymb.step_ext]
          rfl
        · rw [Step.levels_append, Step.levels_single, if_pos ht, hl, Nat.add_zero]
      · have ht' : t.isProj = false := Bool.eq_false_iff.mpr ht
        cases k with
        | zero =>
            simp only [VarSymb.splitAt, ht', Bool.false_eq_true, if_false,
              Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨rfl, ht', rfl⟩
        | succ k =>
            simp only [VarSymb.splitAt, ht', Bool.false_eq_true, if_false] at h
            obtain ⟨⟨pre', s', rest'⟩, hq, he⟩ := Option.map_eq_some_iff.mp h
            obtain ⟨hy, hs, hl⟩ := VarSymb.splitAt_spec hq
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl, rfl⟩ := he
            refine ⟨?_, hs, ?_⟩
            · rw [hy, VarSymb.step_ext]
              rfl
            · rw [Step.levels_append, Step.levels_single, if_neg ht, hl]

/-- Cutting an address that is a prefix, a level step and a path, before that step. -/
theorem VarSymb.splitAt_ext (pre : VarSymb) {s : Step} (hs : s.isProj = false) :
    ∀ rest : List Step, VarSymb.splitAt (pre.ext (s :: rest)) (Step.levels rest) =
      some (pre, s, rest) := by
  intro rest
  induction rest using List.reverseRecOn with
  | nil =>
      change VarSymb.splitAt (.step pre s) 0 = _
      simp [VarSymb.splitAt, hs]
  | append_singleton r t ih =>
      rw [← List.cons_append, ← VarSymb.step_ext, Step.levels_append, Step.levels_single]
      by_cases ht : t.isProj = true
      · rw [if_pos ht, Nat.add_zero]
        simp only [VarSymb.splitAt, if_pos ht, ih, Option.map_some]
      · have ht' : t.isProj = false := Bool.eq_false_iff.mpr ht
        rw [if_neg ht]
        simp only [VarSymb.splitAt, ht', Bool.false_eq_true, if_false, ih, Option.map_some]

/-! ## Steps the flags allow -/

variable [ModalSys]

/-- A step a view can produce under the current flags: `box` only without 4, `keep` only with it.
    Under T, `keepOnly` is 4, so `box` and `keep` never meet. -/
abbrev Step.OK (s : Step) : Prop :=
  (s = .box → ModalSys.Four = false) ∧ (s = .keep → ModalSys.Four = true)

theorem Step.ok_of_proj {s : Step} (hs : s.isProj = true) : s.OK := by
  constructor <;> intro h <;> subst h <;> cases hs

theorem Step.ok_dia : Step.OK .dia := ⟨nofun, nofun⟩

/-- Every step of an address is allowed. -/
def VarSymb.OK (y : VarSymb) : Prop := ∀ s ∈ y.path, s.OK

theorem VarSymb.ok_step {v : VarSymb} {s : Step} : (VarSymb.step v s).OK ↔ v.OK ∧ s.OK := by
  simp only [VarSymb.OK, VarSymb.path, List.mem_append, List.mem_singleton]
  constructor
  · intro h
    exact ⟨fun t ht => h t (Or.inl ht), h s (Or.inr rfl)⟩
  · rintro ⟨h₁, h₂⟩ t (ht | rfl)
    · exact h₁ t ht
    · exact h₂

theorem VarSymb.ok_ext {v : VarSymb} {p : List Step} : (v.ext p).OK ↔ v.OK ∧ ∀ s ∈ p, s.OK := by
  simp only [VarSymb.OK, VarSymb.ext_path, List.mem_append]
  constructor
  · intro h
    exact ⟨fun t ht => h t (Or.inl ht), fun t ht => h t (Or.inr ht)⟩
  · rintro ⟨h₁, h₂⟩ t (ht | ht)
    · exact h₁ t ht
    · exact h₂ t ht

/-- Every declared address is allowed. -/
def Ctx.DeclOK (Γ : Ctx) : Prop := ∀ v T, Γ v = some T → v.OK

theorem Ctx.DeclOK.ref {Γ : Ctx} (h : Γ.DeclOK) : ∀ (v : VarSymb) {T : VarType},
    Γ.ref v = some T → v.OK
  | .root r, T, hv => h _ T hv
  | .step v s, T, hv => by
      by_cases hs : s.isProj = true
      · change (if s.isProj then (Γ.ref v).bind (·.step s) else Γ (.step v s)) = some T at hv
        rw [if_pos hs] at hv
        cases hU : Γ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U => exact VarSymb.ok_step.mpr ⟨Ctx.DeclOK.ref h v hU, Step.ok_of_proj hs⟩
      · change (if s.isProj then (Γ.ref v).bind (·.step s) else Γ (.step v s)) = some T at hv
        rw [if_neg hs] at hv
        exact h _ T hv

theorem Ctx.DeclOK.insert {Γ : Ctx} (h : Γ.DeclOK) (r : Root) (T : VarType) :
    (Γ.insert r T).DeclOK := by
  intro v U hv
  change (if v = .root r then some T else Γ v) = some U at hv
  split_ifs at hv with hvr
  · subst hvr
    intro s hs
    cases hs
  · exact h v U hv

/-- The `□` view reaches only allowed addresses, under T or without 4: either way a `box` step is
    produced only without 4. -/
theorem Ctx.DeclOK.boxIn_of (hTF : ModalSys.T = true ∨ ModalSys.Four = false) {Γ : Ctx}
    (h : Γ.DeclOK) : Γ.boxIn.DeclOK := by
  intro v U hv
  match v, hv with
  | .step u .box, hv =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hv
      refine VarSymb.ok_step.mpr ⟨h.ref u hu, fun _ => ?_, nofun⟩
      rcases hTF with hT | hF
      · simpa [ModalSys.keepOnly, hT] using hk
      · exact hF
  | .step u .keep, hv =>
      obtain ⟨hF, hu, -⟩ := Ctx.boxIn_keep hv
      exact VarSymb.ok_step.mpr ⟨h.ref u hu, nofun, fun _ => hF⟩
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .dia, hv => cases hv
  | .step _ .here, hv => cases hv

theorem Ctx.DeclOK.boxIn (hT : ModalSys.T = true) {Γ : Ctx} (h : Γ.DeclOK) : Γ.boxIn.DeclOK :=
  h.boxIn_of (.inl hT)

theorem Ctx.DeclOK.diaIn_of (hTF : ModalSys.T = true ∨ ModalSys.Four = false) {Γ : Ctx}
    (h : Γ.DeclOK) (x : VarSymb) : (Γ.diaIn x).DeclOK := by
  intro v U hv
  match v, hv with
  | .step u .dia, hv =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some U at hv
      split_ifs at hv with hux
      subst hux
      cases hx : Γ.ref u with
      | none => rw [hx] at hv; cases hv
      | some X => exact VarSymb.ok_step.mpr ⟨h.ref u hx, Step.ok_dia⟩
  | .step u .box, hv => exact (h.boxIn_of hTF) _ U hv
  | .step u .keep, hv => exact (h.boxIn_of hTF) _ U hv
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .here, hv => cases hv

theorem Ctx.DeclOK.diaIn (hT : ModalSys.T = true) {Γ : Ctx} (h : Γ.DeclOK) (x : VarSymb) :
    (Γ.diaIn x).DeclOK :=
  h.diaIn_of (.inl hT) x

theorem CtxExpr.declOK_of (hTF : ModalSys.T = true ∨ ModalSys.Four = false) :
    ∀ e : CtxExpr, e.denote.DeclOK
  | .empty => fun _ _ h => by cases h
  | .insertFree e u T => (CtxExpr.declOK_of hTF e).insert (.free u) T
  | .boxIn e => (CtxExpr.declOK_of hTF e).boxIn_of hTF
  | .diaIn e x => (CtxExpr.declOK_of hTF e).diaIn_of hTF x

/-- ⭐Under T or without 4, a presented context reaches only allowed addresses. -/
theorem Ctx.Presented.declOK_of (hTF : ModalSys.T = true ∨ ModalSys.Four = false) (Γ : Ctx)
    [h : Γ.Presented] : Γ.DeclOK :=
  h.denote_eq ▸ CtxExpr.declOK_of hTF h.expr

/-- ⭐Under T, a presented context reaches only allowed addresses. -/
theorem Ctx.Presented.declOK (hT : ModalSys.T = true) (Γ : Ctx) [Γ.Presented] : Γ.DeclOK :=
  Ctx.Presented.declOK_of (.inl hT) Γ

/-! ## Collapse and shift on paths agree with collapse and shift on addresses -/

omit [ModalSys] in
/-- ⭐Inserting a `keep` into a path, counted from its front, is shifting the address, counted from
    its end. -/
theorem VarSymb.shift_agree : ∀ (pre : VarSymb) (q : List Step) (l : ℕ), l < Step.levels q →
    (pre.ext q).shift l = pre.ext (Step.shiftAt (Step.levels q - 1 - l) q)
  | _, [], _, h => by simp [Step.levels] at h
  | pre, s :: q, l, h => by
      by_cases hs : s.isProj = true
      · rw [Step.levels_cons, if_pos hs, Nat.zero_add] at h ⊢
        rw [Step.shiftAt_proj hs]
        exact VarSymb.shift_agree (.step pre s) q l h
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        rw [Step.levels_cons, if_neg hs] at h ⊢
        by_cases hl : l = Step.levels q
        · subst hl
          rw [show 1 + Step.levels q - 1 - Step.levels q = 0 by omega, Step.shiftAt_zero hs']
          have e := VarSymb.shift_ext (VarSymb.step pre s) q 0
          rw [Nat.zero_add] at e
          change ((VarSymb.step pre s).ext q).shift (Step.levels q) = _
          rw [e, VarSymb.shift_level_zero hs']
          rfl
        · rw [show 1 + Step.levels q - 1 - l = (Step.levels q - 1 - l) + 1 by omega,
            Step.shiftAt_succ hs']
          exact VarSymb.shift_agree (.step pre s) q l (by omega)

/-- ⭐Collapsing a path, counted from its front, is collapsing the address, counted from its end —
    when the steps are allowed and the collapsed step is a `□` step.  The one place the two could
    differ is the keep-absorbing case, a `box` right after a `keep`, which allowed steps exclude. -/
theorem VarSymb.collapse_agree :
    ∀ (pre : VarSymb) (q : List Step) (l : ℕ), l < Step.levels q → (∀ s ∈ q, s.OK) →
      (∀ a t b, VarSymb.splitAt (pre.ext q) l = some (a, t, b) → t ≠ .dia) →
      (pre.ext q).collapse l = pre.ext (Step.collapseAt (Step.levels q - 1 - l) q)
  | _, [], _, h, _, _ => by simp [Step.levels] at h
  | pre, s :: q, l, h, hok, hnd => by
      by_cases hs : s.isProj = true
      · rw [Step.levels_cons, if_pos hs, Nat.zero_add] at h ⊢
        rw [Step.collapseAt_proj hs]
        exact VarSymb.collapse_agree (.step pre s) q l h
          (fun t ht => hok t (List.mem_cons_of_mem _ ht)) hnd
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        rw [Step.levels_cons, if_neg hs] at h ⊢
        by_cases hl : l = Step.levels q
        · subst hl
          rw [show 1 + Step.levels q - 1 - Step.levels q = 0 by omega, Step.collapseAt_zero hs']
          have e := VarSymb.collapse_ext (VarSymb.step pre s) q 0
          rw [Nat.zero_add] at e
          change ((VarSymb.step pre s).ext q).collapse (Step.levels q) = _
          rw [e]
          by_cases hk : s = .keep
          · subst hk
            rw [if_pos rfl]
            rfl
          · rw [if_neg hk, VarSymb.collapse_level_zero hs' hk]
            rfl
        · rw [show 1 + Step.levels q - 1 - l = (Step.levels q - 1 - l) + 1 by omega,
            Step.collapseAt_succ hs']
          by_cases habs : Step.levels q - 1 - l = 0 ∧ s = .keep ∧ Step.headLvl q = true
          · -- the keep-absorbing case: the collapsed step comes right after a `keep`
            rw [if_pos habs]
            obtain ⟨hz, hsk, hh⟩ := habs
            subst hsk
            match q, hh with
            | t :: q', hh =>
                have ht : t.isProj = false := by simpa [Step.headLvl] using hh
                rw [Step.levels_cons, if_neg (by simp [ht])] at hz h hl
                have hlq : l = Step.levels q' := by omega
                subst hlq
                have htd : t ≠ .dia :=
                  hnd _ _ _ (VarSymb.splitAt_ext (VarSymb.step pre .keep) ht q')
                have hokk : Step.OK .keep := hok _ List.mem_cons_self
                have hokt : t.OK := hok t (List.mem_cons_of_mem _ List.mem_cons_self)
                have htk : t = .keep := by
                  cases t
                  · cases ht
                  · cases ht
                  · exact absurd (hokk.2 rfl) (by rw [hokt.1 rfl]; decide)
                  · exact absurd rfl htd
                  · cases ht
                  · rfl
                subst htk
                have e := VarSymb.collapse_ext
                  (VarSymb.step (VarSymb.step pre .keep) .keep) q' 0
                rw [Nat.zero_add] at e
                change ((VarSymb.step (VarSymb.step pre .keep) .keep).ext q').collapse
                  (Step.levels q') = (VarSymb.step pre .keep).ext q'
                rw [e]
                rfl
          · rw [if_neg habs]
            exact VarSymb.collapse_agree (.step pre s) q l (by omega)
              (fun t ht => hok t (List.mem_cons_of_mem _ ht)) hnd

/-! ## Reading an address at a successor, at any level -/

namespace Canon

variable {σ : Signature} {N₀ : ℕ}

/-- An address shifted `n` times at the level with `k` level steps after it. -/
def shiftIterK (k : ℕ) : ℕ → VarSymb → VarSymb
  | 0, v => v
  | n + 1, v => shiftIterK k n (v.shift k)

/-- Where an address is read at a successor `w'` of `w`, the level crossed being the one with `k`
    level steps after it: collapsed at the world itself, shifted `d` times `d + 1` levels deeper.
    `succAddr` is the case `k = 0`. -/
def succAddrK (w w' : World σ N₀) (k : ℕ) (v : VarSymb) : VarSymb :=
  match w'.depth - w.depth with
  | 0 => v.collapse k
  | d + 1 => shiftIterK k d v

theorem succAddrK_zero {w w' : World σ N₀} (h : w'.depth - w.depth = 0) (k : ℕ) (v : VarSymb) :
    succAddrK w w' k v = v.collapse k := by
  simp only [succAddrK, h]

theorem succAddrK_succ {w w' : World σ N₀} {d : ℕ} (h : w'.depth - w.depth = d + 1) (k : ℕ)
    (v : VarSymb) : succAddrK w w' k v = shiftIterK k d v := by
  simp only [succAddrK, h]

omit [ModalSys] in
theorem shiftIterK_proj (k : ℕ) : ∀ (n : ℕ) (v : VarSymb) {s : Step}, s.isProj = true →
    shiftIterK k n (.step v s) = .step (shiftIterK k n v) s
  | 0, _, _, _ => rfl
  | n + 1, v, s, hs => by
      change shiftIterK k n ((VarSymb.step v s).shift k) = .step (shiftIterK k n (v.shift k)) s
      rw [VarSymb.shift_proj hs]
      exact shiftIterK_proj k n _ hs

omit [ModalSys] in
theorem shiftIterK_level (k : ℕ) : ∀ (n : ℕ) (v : VarSymb) {s : Step}, s.isProj = false →
    shiftIterK (k + 1) n (.step v s) = .step (shiftIterK k n v) s
  | 0, _, _, _ => rfl
  | n + 1, v, s, hs => by
      change shiftIterK (k + 1) n ((VarSymb.step v s).shift (k + 1)) =
        .step (shiftIterK k n (v.shift k)) s
      rw [VarSymb.shift_level_succ hs]
      exact shiftIterK_level k n _ hs

theorem shiftIterK_inner (k : ℕ) : ∀ (n : ℕ) (v : VarSymb),
    shiftIterK (k + 1) n v.inner = (shiftIterK k n v).inner
  | 0, _ => rfl
  | n + 1, v => by
      change shiftIterK (k + 1) n (v.inner.shift (k + 1)) = (shiftIterK k n (v.shift k)).inner
      rw [VarSymb.inner_shift_succ]
      exact shiftIterK_inner k n _

omit [ModalSys] in
theorem shiftIterK_zero : ∀ (n : ℕ) (v : VarSymb), shiftIterK 0 n v = VarSymb.shiftIter n v
  | 0, _ => rfl
  | n + 1, v => shiftIterK_zero n (v.shift 0)

theorem succAddrK_proj (w w' : World σ N₀) (k : ℕ) (v : VarSymb) {s : Step}
    (hs : s.isProj = true) : succAddrK w w' k (.step v s) = .step (succAddrK w w' k v) s := by
  rcases h : w'.depth - w.depth with _ | d
  · rw [succAddrK_zero h, succAddrK_zero h, VarSymb.collapse_proj hs]
  · rw [succAddrK_succ h, succAddrK_succ h, shiftIterK_proj k d v hs]

theorem succAddrK_level (w w' : World σ N₀) (k : ℕ) (v : VarSymb) {s : Step}
    (hs : s.isProj = false) :
    succAddrK w w' (k + 1) (.step v s) = .step (succAddrK w w' k v) s := by
  rcases h : w'.depth - w.depth with _ | d
  · rw [succAddrK_zero h, succAddrK_zero h, VarSymb.collapse_level_succ hs]
  · rw [succAddrK_succ h, succAddrK_succ h, shiftIterK_level k d v hs]

theorem succAddrK_inner (w w' : World σ N₀) (k : ℕ) (v : VarSymb) :
    succAddrK w w' (k + 1) v.inner = (succAddrK w w' k v).inner := by
  rcases h : w'.depth - w.depth with _ | d
  · rw [succAddrK_zero h, succAddrK_zero h, VarSymb.inner_collapse_succ]
  · rw [succAddrK_succ h, succAddrK_succ h, shiftIterK_inner k d v]

/-- `succAddr` is `succAddrK` at the innermost level. -/
theorem succAddrK_zero_eq (w w' : World σ N₀) : succAddrK w w' 0 = succAddr w w' := by
  funext v
  rcases h : w'.depth - w.depth with _ | d
  · rw [succAddrK_zero h, succAddr_zero h]
  · rw [succAddrK_succ h, succAddr_succ h, shiftIterK_zero]

/-! ## The canonical leaf of an address -/

omit [ModalSys] in
theorem _root_.V12M.VarSymb.ext_append_ext :
    ∀ (v : VarSymb) (p q : List Step), v.ext (p ++ q) = (v.ext p).ext q
  | _, [], _ => rfl
  | v, s :: p, q => VarSymb.ext_append_ext (.step v s) p q

omit [ModalSys] in
/-- Extending an address by a path moves its cuts out by the path's levels. -/
theorem _root_.V12M.VarSymb.splitAt_extend {y : VarSymb} {k : ℕ} {a : VarSymb} {t : Step}
    {b : List Step} (h : VarSymb.splitAt y k = some (a, t, b)) (p : List Step) :
    VarSymb.splitAt (y.ext p) (k + Step.levels p) = some (a, t, b ++ p) := by
  obtain ⟨rfl, ht, hl⟩ := VarSymb.splitAt_spec h
  rw [← VarSymb.ext_append_ext, List.cons_append, ← hl, ← Step.levels_append]
  exact VarSymb.splitAt_ext a ht (b ++ p)

/-- Canonical leaves. -/
abbrev CLeaf (w : World σ N₀) : Type := Arrows.Leaf (arrows σ N₀) (fun _ => VarSymb) w

/-- ⭐**The canonical leaf of a label** (docs §10.39): the address cut where it leaves the anchor's
    level, its last `m` level steps being views entered from `w`.  A `dia` there keeps the rest as a
    path; a `□` step is a family over the successors, each entry the leaf of the address seen from
    there. -/
def leafOf : (w : World σ N₀) → ℕ → VarSymb → CLeaf w
  | _, 0, y => .root y []
  | w, m + 1, y =>
      match VarSymb.splitAt y m with
      | some (pre, .dia, rest) => .root pre (.dia :: rest)
      | _ => .fam fun s => leafOf s.1 m (succAddrK w s.1 m y)

theorem leafOf_zero (w : World σ N₀) (y : VarSymb) : leafOf w 0 y = .root y [] := by
  simp only [leafOf]

theorem leafOf_dia (w : World σ N₀) {m : ℕ} {y pre : VarSymb} {rest : List Step}
    (h : VarSymb.splitAt y m = some (pre, .dia, rest)) :
    leafOf w (m + 1) y = .root pre (.dia :: rest) := by
  simp only [leafOf, h]

theorem leafOf_lvl (w : World σ N₀) {m : ℕ} {y pre : VarSymb} {t : Step} {rest : List Step}
    (h : VarSymb.splitAt y m = some (pre, t, rest)) (ht : t ≠ .dia) :
    leafOf w (m + 1) y = .fam fun s => leafOf s.1 m (succAddrK w s.1 m y) := by
  cases t <;> first | exact absurd rfl ht | simp only [leafOf, h]

/-- ⭐An annotation with its labels read canonically: a label at depth `j` (views entered from the
    anchor) is `leafOf w j`. -/
def annShp (w : World σ N₀) : ℕ → {A : VarType} → Ann A → CShape w A
  | _, _, .var => .var
  | _, _, .one => .one
  | j, _, .prod a b => .prod (annShp w j a) (annShp w j b)
  | j, _, .box a => .box (annShp w (j + 1) a)
  | j, _, .dia x a => .dia (leafOf w j x) (annShp w (j + 1) a)

theorem levels_innerPath : Step.levels Step.innerPath = 1 := by
  unfold Step.innerPath
  split_ifs <;> rfl

/-- ⭐**Transposition**: an η-annotation whose outermost view is a `□` step reads, canonically, as
    the family of its readings at the successors. -/
theorem annShp_eta_transpose : ∀ (A : VarType) (w : World σ N₀) (k : ℕ) (y : VarSymb)
    {a : VarSymb} {t : Step} {b : List Step}, VarSymb.splitAt y k = some (a, t, b) → t ≠ .dia →
    annShp w (k + 1) (Ann.eta y A) =
      Arrows.transposeShp (F := arrows σ N₀) (Root := fun _ => VarSymb)
        fun s => annShp s.1 k (Ann.eta (succAddrK w s.1 k y) A)
  | .Var, _, _, _, _, _, _, _, _ => rfl
  | .VTypeOne, _, _, _, _, _, _, _, _ => rfl
  | .VTypeProd A B, w, k, y, a, t, b, h, ht => by
      have hf := VarSymb.splitAt_extend h [.fst]
      have hs := VarSymb.splitAt_extend h [.snd]
      simp only [Step.levels, Step.isProj, if_true, Nat.add_zero] at hf hs
      change Shp.prod (annShp w (k + 1) (Ann.eta (.step y .fst) A))
          (annShp w (k + 1) (Ann.eta (.step y .snd) B)) = _
      rw [annShp_eta_transpose A w k (.step y .fst) hf ht,
        annShp_eta_transpose B w k (.step y .snd) hs ht]
      simp only [succAddrK_proj w _ k y (rfl : Step.isProj .fst = true),
        succAddrK_proj w _ k y (rfl : Step.isProj .snd = true)]
      rfl
  | .VTypeBox A, w, k, y, a, t, b, h, ht => by
      have hi := VarSymb.splitAt_extend h Step.innerPath
      rw [← List.nil_append Step.innerPath, ← VarSymb.inner_ext y [], List.nil_append,
        levels_innerPath] at hi
      change Shp.box (annShp w (k + 1 + 1) (Ann.eta y.inner A)) = _
      rw [annShp_eta_transpose A w (k + 1) y.inner hi ht]
      simp only [succAddrK_inner]
      rfl
  | .VTypeDia A, w, k, y, a, t, b, h, ht => by
      have hd := VarSymb.splitAt_extend h [.dia]
      simp only [Step.levels, Step.isProj, Bool.false_eq_true, if_false, Nat.add_zero] at hd
      change Shp.dia (leafOf w (k + 1) y) (annShp w (k + 1 + 1) (Ann.eta (.step y .dia) A)) = _
      rw [leafOf_lvl w h ht, annShp_eta_transpose A w (k + 1) (.step y .dia) hd ht]
      simp only [succAddrK_level w _ k y (rfl : Step.isProj .dia = false)]
      rfl

/-- A content's canonical shape is its η-annotation read canonically, from the root and path. -/
theorem rootSh_eq : ∀ (A : VarType) (w : World σ N₀) (v : VarSymb) (π : List Step),
    rootSh w v (.dia :: π) A = annShp w (Step.levels π + 1) (Ann.eta (v.ext (.dia :: π)) A)
  | .Var, _, _, _ => rfl
  | .VTypeOne, _, _, _ => rfl
  | .VTypeProd A B, w, v, π => by
      change Shp.prod (rootSh w v (.dia :: (π ++ [.fst])) A)
          (rootSh w v (.dia :: (π ++ [.snd])) B) = _
      rw [rootSh_eq A w v (π ++ [Step.fst]), rootSh_eq B w v (π ++ [Step.snd])]
      simp only [Step.levels_append, Step.levels, Step.isProj, if_true, Nat.add_zero]
      rw [← List.cons_append, VarSymb.ext_append_ext, ← List.cons_append,
        VarSymb.ext_append_ext]
      rfl
  | .VTypeBox A, w, v, π => by
      change Shp.box (rootSh w v (.dia :: (π ++ Step.innerPath)) A) = _
      rw [rootSh_eq A w v (π ++ Step.innerPath), Step.levels_append, levels_innerPath,
        ← List.cons_append, ← VarSymb.inner_ext]
      rfl
  | .VTypeDia A, w, v, π => by
      have hs := VarSymb.splitAt_ext v (rfl : Step.isProj .dia = false) π
      change Shp.dia (.root v (.dia :: π)) (rootSh w v (.dia :: (π ++ [.dia])) A) = _
      rw [rootSh_eq A w v (π ++ [Step.dia])]
      change _ = Shp.dia (leafOf w (Step.levels π + 1) (v.ext (.dia :: π))) _
      rw [leafOf_dia w hs, Step.levels_append]
      simp only [Step.levels, Step.isProj, Bool.false_eq_true, if_false, Nat.add_zero]
      rw [← List.cons_append, VarSymb.ext_append_ext]
      rfl

/-- ⭐**The canonical shape of an address is its η-annotation read canonically.** -/
theorem canonSh_eq : ∀ (A : VarType) (w : World σ N₀) (v : VarSymb),
    canonSh w v A = annShp w 0 (Ann.eta v A)
  | .Var, _, _ => rfl
  | .VTypeOne, _, _ => rfl
  | .VTypeProd A B, w, v => by
      change Shp.prod (canonSh w (.step v .fst) A) (canonSh w (.step v .snd) B) = _
      rw [canonSh_eq A w, canonSh_eq B w]
      rfl
  | .VTypeBox A, w, v => by
      have hi : ∃ t b, VarSymb.splitAt v.inner 0 = some (v, t, b) ∧ t ≠ .dia := by
        unfold VarSymb.inner
        split_ifs
        · exact ⟨.keep, [.here], rfl, nofun⟩
        · exact ⟨.box, [], rfl, nofun⟩
      obtain ⟨t, b, hi, ht⟩ := hi
      change Shp.box (Arrows.transposeShp (F := arrows σ N₀) (Root := fun _ => VarSymb)
          fun s => canonSh s.1 (succAddr w s.1 v.inner) A) = Shp.box (annShp w (0 + 1) _)
      rw [annShp_eta_transpose A w 0 v.inner hi ht]
      simp only [succAddrK_zero_eq, canonSh_eq A]
  | .VTypeDia A, w, v => by
      change Shp.dia (.root v []) (rootSh w v [.dia] A) = _
      rw [rootSh_eq A w v []]
      rfl

/-! ## Cuts, levels and allowed steps under collapse and shift -/

omit [ModalSys] in
/-- An address ending in a path with more than `k` levels can be cut at `k`. -/
theorem splitAt_exists (a : VarSymb) : ∀ (q : List Step) (k : ℕ), k < Step.levels q →
    ∃ pre t rest, VarSymb.splitAt (a.ext q) k = some (pre, t, rest) := by
  intro q
  induction q using List.reverseRecOn with
  | nil => intro k h; simp [Step.levels] at h
  | append_singleton r s ih =>
      intro k h
      rw [Step.levels_append, Step.levels_single] at h
      rw [VarSymb.ext_append_ext]
      change ∃ pre t rest, VarSymb.splitAt (.step (a.ext r) s) k = some (pre, t, rest)
      by_cases hs : s.isProj = true
      · rw [if_pos hs, Nat.add_zero] at h
        obtain ⟨pre, t, rest, h'⟩ := ih k h
        exact ⟨pre, t, rest ++ [s], by simp only [VarSymb.splitAt, if_pos hs, h', Option.map_some]⟩
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        rw [if_neg hs] at h
        cases k with
        | zero => exact ⟨a.ext r, s, [], by simp [VarSymb.splitAt, hs']⟩
        | succ k =>
            obtain ⟨pre, t, rest, h'⟩ := ih k (by omega)
            exact ⟨pre, t, rest ++ [s], by
              simp only [VarSymb.splitAt, hs', Bool.false_eq_true, if_false, h', Option.map_some]⟩

omit [ModalSys] in
/-- Collapsing below the end of a path keeps the address a prefix followed by a path with one
    level fewer. -/
theorem collapse_ext_lt (a : VarSymb) : ∀ (q : List Step) (l : ℕ), l < Step.levels q →
    ∃ q', (a.ext q).collapse l = a.ext q' ∧ Step.levels q' + 1 = Step.levels q := by
  intro q
  induction q using List.reverseRecOn with
  | nil => intro l h; simp [Step.levels] at h
  | append_singleton r s ih =>
      intro l h
      rw [Step.levels_append, Step.levels_single] at h ⊢
      rw [VarSymb.ext_append_ext]
      change ∃ q', (VarSymb.step (a.ext r) s).collapse l = a.ext q' ∧ _
      by_cases hs : s.isProj = true
      · rw [if_pos hs, Nat.add_zero] at h ⊢
        obtain ⟨q', e, hl⟩ := ih l h
        refine ⟨q' ++ [s], ?_, ?_⟩
        · rw [VarSymb.collapse_proj hs, e, VarSymb.ext_append_ext]; rfl
        · rw [Step.levels_append, Step.levels_single, if_pos hs]; omega
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        rw [if_neg hs] at h ⊢
        cases l with
        | zero =>
            by_cases hk : s = .keep
            · subst hk
              exact ⟨r, by rw [VarSymb.collapse_keep_zero], by omega⟩
            · refine ⟨r ++ [.here], ?_, ?_⟩
              · rw [VarSymb.collapse_level_zero hs' hk, VarSymb.ext_append_ext]; rfl
              · rw [Step.levels_append]; simp [Step.levels, Step.isProj]
        | succ l =>
            obtain ⟨q', e, hl⟩ := ih l (by omega)
            refine ⟨q' ++ [s], ?_, ?_⟩
            · rw [VarSymb.collapse_level_succ hs', e, VarSymb.ext_append_ext]; rfl
            · rw [Step.levels_append, Step.levels_single, if_neg hs]; omega

omit [ModalSys] in
/-- Shifting below the end of a path keeps the address a prefix followed by a path with one level
    more. -/
theorem shift_ext_lt (a : VarSymb) : ∀ (q : List Step) (l : ℕ), l < Step.levels q →
    ∃ q', (a.ext q).shift l = a.ext q' ∧ Step.levels q' = Step.levels q + 1 := by
  intro q
  induction q using List.reverseRecOn with
  | nil => intro l h; simp [Step.levels] at h
  | append_singleton r s ih =>
      intro l h
      rw [Step.levels_append, Step.levels_single] at h ⊢
      rw [VarSymb.ext_append_ext]
      change ∃ q', (VarSymb.step (a.ext r) s).shift l = a.ext q' ∧ _
      by_cases hs : s.isProj = true
      · rw [if_pos hs, Nat.add_zero] at h ⊢
        obtain ⟨q', e, hl⟩ := ih l h
        refine ⟨q' ++ [s], ?_, ?_⟩
        · rw [VarSymb.shift_proj hs, e, VarSymb.ext_append_ext]; rfl
        · rw [Step.levels_append, Step.levels_single, if_pos hs]; omega
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        rw [if_neg hs] at h ⊢
        cases l with
        | zero =>
            refine ⟨r ++ [.keep, s], ?_, ?_⟩
            · rw [VarSymb.shift_level_zero hs', VarSymb.ext_append_ext]; rfl
            · rw [Step.levels_append]
              simp [Step.levels, hs', show Step.isProj .keep = false from rfl]
        | succ l =>
            obtain ⟨q', e, hl⟩ := ih l (by omega)
            refine ⟨q' ++ [s], ?_, ?_⟩
            · rw [VarSymb.shift_level_succ hs', e, VarSymb.ext_append_ext]; rfl
            · rw [Step.levels_append, Step.levels_single, if_neg hs]; omega

omit [ModalSys] in
/-- Collapsing below a cut keeps the cut. -/
theorem splitAt_collapse_below {x pre : VarSymb} {k l : ℕ} {t : Step} {rest : List Step}
    (h : VarSymb.splitAt x (k + 1) = some (pre, t, rest)) (hl : l ≤ k) :
    ∃ rest', VarSymb.splitAt (x.collapse l) k = some (pre, t, rest') := by
  obtain ⟨rfl, ht, hlv⟩ := VarSymb.splitAt_spec h
  obtain ⟨q', e, hq'⟩ := collapse_ext_lt (VarSymb.step pre t) rest l (by omega)
  refine ⟨q', ?_⟩
  change VarSymb.splitAt (((VarSymb.step pre t).ext rest).collapse l) k = _
  rw [e, show k = Step.levels q' by omega]
  exact VarSymb.splitAt_ext pre ht q'

omit [ModalSys] in
/-- Shifting below a cut keeps the cut, one level further out. -/
theorem splitAt_shift_below {x pre : VarSymb} {k l : ℕ} {t : Step} {rest : List Step}
    (h : VarSymb.splitAt x k = some (pre, t, rest)) (hl : l < k) :
    ∃ rest', VarSymb.splitAt (x.shift l) (k + 1) = some (pre, t, rest') := by
  obtain ⟨rfl, ht, hlv⟩ := VarSymb.splitAt_spec h
  obtain ⟨q', e, hq'⟩ := shift_ext_lt (VarSymb.step pre t) rest l (by omega)
  refine ⟨q', ?_⟩
  change VarSymb.splitAt (((VarSymb.step pre t).ext rest).shift l) (k + 1) = _
  rw [e, show k + 1 = Step.levels q' by omega]
  exact VarSymb.splitAt_ext pre ht q'

omit [ModalSys] in
/-- Shifting at a cut inserts a `keep` before the cut step. -/
theorem splitAt_shift_at {x pre : VarSymb} {l : ℕ} {t : Step} {rest : List Step}
    (h : VarSymb.splitAt x l = some (pre, t, rest)) :
    x.shift l = pre.ext (.keep :: t :: rest) ∧
      VarSymb.splitAt (x.shift l) (l + 1) = some (pre, .keep, t :: rest) ∧
      VarSymb.splitAt (x.shift l) l = some (.step pre .keep, t, rest) := by
  obtain ⟨rfl, ht, hlv⟩ := VarSymb.splitAt_spec h
  have e : (pre.ext (t :: rest)).shift l = pre.ext (.keep :: t :: rest) := by
    have := VarSymb.shift_ext (VarSymb.step pre t) rest 0
    rw [Nat.zero_add, hlv] at this
    change ((VarSymb.step pre t).ext rest).shift l = _
    rw [this, VarSymb.shift_level_zero ht]
    rfl
  refine ⟨e, ?_, ?_⟩
  · rw [e]
    have := VarSymb.splitAt_ext pre (rfl : Step.isProj .keep = false) (t :: rest)
    rwa [Step.levels_cons, if_neg (by simp [ht]), hlv, Nat.add_comm] at this
  · rw [e, ← hlv]
    exact VarSymb.splitAt_ext (VarSymb.step pre .keep) ht rest

omit [ModalSys] in
/-- Collapsing or shifting above a cut keeps the cut step and what follows it. -/
theorem splitAt_collapse_above {x a : VarSymb} {l m : ℕ} {t : Step} {b : List Step}
    (h : VarSymb.splitAt x l = some (a, t, b)) (hm : l < m) :
    VarSymb.splitAt (x.collapse m) l = some (a.collapse (m - (l + 1)), t, b) := by
  obtain ⟨rfl, ht, hlv⟩ := VarSymb.splitAt_spec h
  have := VarSymb.collapse_ext a (t :: b) (m - (l + 1))
  rw [Step.levels_cons, if_neg (by simp [ht]), hlv,
    show m - (l + 1) + (1 + l) = m by omega] at this
  rw [this, ← hlv]
  exact VarSymb.splitAt_ext _ ht b

omit [ModalSys] in
theorem splitAt_shift_above {x a : VarSymb} {l m : ℕ} {t : Step} {b : List Step}
    (h : VarSymb.splitAt x l = some (a, t, b)) (hm : l < m) :
    VarSymb.splitAt (x.shift m) l = some (a.shift (m - (l + 1)), t, b) := by
  obtain ⟨rfl, ht, hlv⟩ := VarSymb.splitAt_spec h
  have := VarSymb.shift_ext a (t :: b) (m - (l + 1))
  rw [Step.levels_cons, if_neg (by simp [ht]), hlv,
    show m - (l + 1) + (1 + l) = m by omega] at this
  rw [this, ← hlv]
  exact VarSymb.splitAt_ext _ ht b

omit [ModalSys] in
theorem splitAt_shiftIterK_above {l m : ℕ} (hm : l < m) :
    ∀ (n : ℕ) {x a : VarSymb} {t : Step} {b : List Step},
      VarSymb.splitAt x l = some (a, t, b) →
      ∃ a', VarSymb.splitAt (shiftIterK m n x) l = some (a', t, b)
  | 0, _, a, _, _, h => ⟨a, h⟩
  | n + 1, _, _, _, _, h => splitAt_shiftIterK_above hm n (splitAt_shift_above h hm)

theorem splitAt_succAddrK_above (w w' : World σ N₀) {x a : VarSymb} {l m : ℕ} {t : Step}
    {b : List Step} (h : VarSymb.splitAt x l = some (a, t, b)) (hm : l < m) :
    ∃ a', VarSymb.splitAt (succAddrK w w' m x) l = some (a', t, b) := by
  rcases hd : w'.depth - w.depth with _ | d
  · rw [succAddrK_zero hd]
    exact ⟨_, splitAt_collapse_above h hm⟩
  · rw [succAddrK_succ hd]
    exact splitAt_shiftIterK_above hm d h

omit [ModalSys] in
theorem shiftIterK_cut (k : ℕ) : ∀ (n : ℕ) (pre : VarSymb) {t : Step} (rest : List Step),
    t.isProj = false → Step.levels rest = k →
    ∃ pre' : VarSymb, shiftIterK k n (pre.ext (t :: rest)) = pre'.ext rest
  | 0, pre, t, _, _, _ => ⟨.step pre t, rfl⟩
  | n + 1, pre, t, rest, ht, hlv => by
      have e := VarSymb.shift_ext (VarSymb.step pre t) rest 0
      rw [Nat.zero_add, hlv] at e
      change ∃ pre', shiftIterK k n (((VarSymb.step pre t).ext rest).shift k) = _
      rw [e, VarSymb.shift_level_zero ht]
      exact shiftIterK_cut k n (.step pre .keep) rest ht hlv

/-- Reading at a successor across the level of a cut keeps everything after it. -/
theorem succAddrK_at_cut (w w' : World σ N₀) {x pre : VarSymb} {k : ℕ} {t : Step}
    {rest : List Step} (h : VarSymb.splitAt x k = some (pre, t, rest)) :
    ∃ pre' : VarSymb, succAddrK w w' k x = pre'.ext rest := by
  obtain ⟨rfl, ht, hlv⟩ := VarSymb.splitAt_spec h
  rcases hd : w'.depth - w.depth with _ | d
  · rw [succAddrK_zero hd]
    have := VarSymb.collapse_ext (VarSymb.step pre t) rest 0
    rw [Nat.zero_add, hlv] at this
    exact ⟨_, this⟩
  · rw [succAddrK_succ hd]
    exact shiftIterK_cut k d pre rest ht hlv


/-- After reading at a successor, an address with a cut at `k + 1` still has one at `k`. -/
theorem splitAt_succAddrK_exists (w w' : World σ N₀) {x pre : VarSymb} {k : ℕ} {t : Step}
    {rest : List Step} (h : VarSymb.splitAt x (k + 1) = some (pre, t, rest)) :
    ∃ a t' b, VarSymb.splitAt (succAddrK w w' (k + 1) x) k = some (a, t', b) := by
  obtain ⟨pre', e⟩ := succAddrK_at_cut w w' h
  obtain ⟨-, -, hlv⟩ := VarSymb.splitAt_spec h
  rw [e]
  exact splitAt_exists pre' rest k (by omega)

/-! ### Allowed steps survive collapse and shift -/

theorem VarSymb.ok_collapse : ∀ (x : VarSymb) (k : ℕ), x.OK → (x.collapse k).OK
  | .root _, _, h => h
  | .step v s, k, h => by
      obtain ⟨hv, hs⟩ := VarSymb.ok_step.mp h
      by_cases hp : s.isProj = true
      · rw [VarSymb.collapse_proj hp]
        exact VarSymb.ok_step.mpr ⟨VarSymb.ok_collapse v k hv, hs⟩
      · have hp' : s.isProj = false := Bool.eq_false_iff.mpr hp
        cases k with
        | zero =>
            by_cases hk : s = .keep
            · subst hk
              rw [VarSymb.collapse_keep_zero]
              exact hv
            · rw [VarSymb.collapse_level_zero hp' hk]
              exact VarSymb.ok_step.mpr ⟨hv, Step.ok_of_proj rfl⟩
        | succ k =>
            rw [VarSymb.collapse_level_succ hp']
            exact VarSymb.ok_step.mpr ⟨VarSymb.ok_collapse v k hv, hs⟩

theorem VarSymb.ok_shift (hF : ModalSys.Four = true) : ∀ (x : VarSymb) (k : ℕ), x.OK →
    (x.shift k).OK
  | .root _, _, h => h
  | .step v s, k, h => by
      obtain ⟨hv, hs⟩ := VarSymb.ok_step.mp h
      by_cases hp : s.isProj = true
      · rw [VarSymb.shift_proj hp]
        exact VarSymb.ok_step.mpr ⟨VarSymb.ok_shift hF v k hv, hs⟩
      · have hp' : s.isProj = false := Bool.eq_false_iff.mpr hp
        cases k with
        | zero =>
            rw [VarSymb.shift_level_zero hp']
            exact VarSymb.ok_step.mpr
              ⟨VarSymb.ok_step.mpr ⟨hv, nofun, fun _ => hF⟩, hs⟩
        | succ k =>
            rw [VarSymb.shift_level_succ hp']
            exact VarSymb.ok_step.mpr ⟨VarSymb.ok_shift hF v k hv, hs⟩

theorem ok_shiftIterK (k : ℕ) : ∀ (n : ℕ), (n ≠ 0 → ModalSys.Four = true) → ∀ x : VarSymb,
    x.OK → (shiftIterK k n x).OK
  | 0, _, _, h => h
  | n + 1, hF, x, h =>
      ok_shiftIterK k n (fun _ => hF (Nat.succ_ne_zero n)) _
        (VarSymb.ok_shift (hF (Nat.succ_ne_zero n)) x k h)

/-- Reading at a successor keeps an address allowed: far successors exist only under 4. -/
theorem ok_succAddrK {w : World σ N₀} (s : Succ w) (k : ℕ) {x : VarSymb} (h : x.OK) :
    (succAddrK w s.1 k x).OK := by
  rcases hd : s.1.depth - w.depth with _ | d
  · rw [succAddrK_zero hd]
    exact VarSymb.ok_collapse x k h
  · rw [succAddrK_succ hd]
    exact ok_shiftIterK k d (s.four hd) x h

/-! ### Levels of a collapsed or shifted path -/

omit [ModalSys] in
theorem levels_collapseAt : ∀ (i : ℕ) (q : List Step), i < Step.levels q →
    Step.levels (Step.collapseAt i q) + 1 = Step.levels q
  | _, [], h => by simp [Step.levels] at h
  | i, s :: q, h => by
      by_cases hs : s.isProj = true
      · rw [Step.collapseAt_proj hs]
        rw [Step.levels_cons, if_pos hs, Nat.zero_add] at h ⊢
        rw [Step.levels_cons, if_pos hs, Nat.zero_add]
        exact levels_collapseAt i q h
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        rw [Step.levels_cons, if_neg hs] at h ⊢
        cases i with
        | zero =>
            rw [Step.collapseAt_zero hs']
            split_ifs
            · omega
            · simp [Step.levels, Step.isProj]; omega
        | succ i =>
            rw [Step.collapseAt_succ hs']
            split_ifs with habs
            · omega
            · rw [Step.levels_cons, if_neg hs]
              have := levels_collapseAt i q (by omega)
              omega

omit [ModalSys] in
theorem levels_shiftAt : ∀ (i : ℕ) (q : List Step), i < Step.levels q →
    Step.levels (Step.shiftAt i q) = Step.levels q + 1
  | _, [], h => by simp [Step.levels] at h
  | i, s :: q, h => by
      by_cases hs : s.isProj = true
      · rw [Step.shiftAt_proj hs]
        rw [Step.levels_cons, if_pos hs, Nat.zero_add] at h ⊢
        rw [Step.levels_cons, if_pos hs, Nat.zero_add]
        exact levels_shiftAt i q h
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        rw [Step.levels_cons, if_neg hs] at h ⊢
        cases i with
        | zero =>
            rw [Step.shiftAt_zero hs']
            simp [Step.levels, hs', show Step.isProj .keep = false from rfl]
            omega
        | succ i =>
            rw [Step.shiftAt_succ hs', Step.levels_cons, if_neg hs]
            have := levels_shiftAt i q (by omega)
            omega

/-! ### Reading at a successor commutes with collapsing and shifting further in -/

omit [ModalSys] in
theorem shiftIterK_collapse (l j : ℕ) : ∀ (n : ℕ) (x : VarSymb),
    (shiftIterK (l + j + 1) n x).collapse l = shiftIterK (l + j) n (x.collapse l)
  | 0, _ => rfl
  | n + 1, x => by
      change (shiftIterK (l + j + 1) n (x.shift (l + j + 1))).collapse l =
        shiftIterK (l + j) n ((x.collapse l).shift (l + j))
      rw [shiftIterK_collapse l j n, show l + j + 1 = j + 1 + l by omega,
        VarSymb.shift_collapse x j l, show j + l = l + j by omega]

omit [ModalSys] in
theorem shiftIterK_shift (l j : ℕ) : ∀ (n : ℕ) (x : VarSymb),
    (shiftIterK (l + j + 1) n x).shift l = shiftIterK (l + j + 2) n (x.shift l)
  | 0, _ => rfl
  | n + 1, x => by
      change (shiftIterK (l + j + 1) n (x.shift (l + j + 1))).shift l =
        shiftIterK (l + j + 2) n ((x.shift l).shift (l + j + 2))
      rw [shiftIterK_shift l j n, show l + j + 1 = j + 1 + l by omega,
        VarSymb.shift_shift x j l, show j + 2 + l = l + j + 2 by omega]

theorem succAddrK_collapse (w w' : World σ N₀) (l j : ℕ) (x : VarSymb) :
    (succAddrK w w' (l + j + 1) x).collapse l = succAddrK w w' (l + j) (x.collapse l) := by
  rcases hd : w'.depth - w.depth with _ | d
  · rw [succAddrK_zero hd, succAddrK_zero hd, show l + j + 1 = j + 1 + l by omega,
      VarSymb.collapse_collapse x j l, show j + l = l + j by omega]
  · rw [succAddrK_succ hd, succAddrK_succ hd, shiftIterK_collapse]

theorem succAddrK_shift (w w' : World σ N₀) (l j : ℕ) (x : VarSymb) :
    (succAddrK w w' (l + j + 1) x).shift l = succAddrK w w' (l + j + 2) (x.shift l) := by
  rcases hd : w'.depth - w.depth with _ | d
  · rw [succAddrK_zero hd, succAddrK_zero hd, show l + j + 1 = j + 1 + l by omega,
      VarSymb.collapse_shift x j l, show j + 2 + l = l + j + 2 by omega]
  · rw [succAddrK_succ hd, succAddrK_succ hd, shiftIterK_shift]

/-! ### Keeping, then reading two steps on -/

omit [ModalSys] in
theorem shiftIterK_succ' (k : ℕ) : ∀ (n : ℕ) (x : VarSymb),
    shiftIterK k (n + 1) x = (shiftIterK k n x).shift k
  | 0, _ => rfl
  | n + 1, x => shiftIterK_succ' k n (x.shift k)

omit [ModalSys] in
theorem shiftIterK_add (k : ℕ) : ∀ (n m : ℕ) (x : VarSymb),
    shiftIterK k m (shiftIterK k n x) = shiftIterK k (n + m) x
  | 0, m, x => by rw [Nat.zero_add]; rfl
  | n + 1, m, x => by
      rw [show n + 1 + m = (n + m) + 1 by omega]
      exact shiftIterK_add k n m (x.shift k)

omit [ModalSys] in
/-- Keeping just inside a keep is keeping again at the same level. -/
theorem shiftIterK_shift_same (l : ℕ) : ∀ (d : ℕ) (x : VarSymb),
    shiftIterK (l + 1) d (x.shift l) = shiftIterK l (d + 1) x
  | 0, _ => rfl
  | d + 1, x => by
      change shiftIterK (l + 1) d ((x.shift l).shift (l + 1)) = shiftIterK l (d + 1) (x.shift l)
      rw [← VarSymb.shift_shift_same]
      exact shiftIterK_shift_same l d (x.shift l)

omit [ModalSys] in
theorem splitAt_shiftIterK_at (l : ℕ) : ∀ (n : ℕ) {x a : VarSymb} {t : Step} {b : List Step},
    VarSymb.splitAt x l = some (a, t, b) →
      ∃ a', VarSymb.splitAt (shiftIterK l n x) l = some (a', t, b)
  | 0, _, a, _, _, h => ⟨a, h⟩
  | n + 1, _, _, _, _, h => splitAt_shiftIterK_at l n (splitAt_shift_at h).2.2

omit [ModalSys] in
/-- Collapsing a kept `keep` gives it back. -/
theorem shift_collapse_keep {y a : VarSymb} {l : ℕ} {b : List Step}
    (h : VarSymb.splitAt y l = some (a, .keep, b)) : (y.shift l).collapse l = y := by
  obtain ⟨e, -, -⟩ := splitAt_shift_at h
  obtain ⟨rfl, -, hlv⟩ := VarSymb.splitAt_spec h
  rw [e]
  have := VarSymb.collapse_ext (VarSymb.step (VarSymb.step a .keep) .keep) b 0
  rw [Nat.zero_add, hlv] at this
  change ((VarSymb.step (VarSymb.step a .keep) .keep).ext b).collapse l = _
  rw [this]
  rfl

/-- ⭐**Keeping, then reading two steps on, is reading at the composite successor** — at any
    level: the level-`l` form of `succAddr_keep`, which the leaf calculus's shift case needs. -/
theorem succAddrK_keep (hF : ModalSys.Four = true) {w s t : World σ N₀} (hs : R w s)
    (ht : R s t) {x a : VarSymb} {l : ℕ} {t₀ : Step} {b : List Step}
    (hx : VarSymb.splitAt x l = some (a, t₀, b)) (ht₀ : t₀ ≠ .dia) (hok : x.OK) :
    succAddrK s t l (succAddrK w s (l + 1) (x.shift l)) = succAddrK w t l x := by
  have hcs : Chain (s.depth - w.depth) w s := (Succ.chain (⟨s, ⟨hs⟩⟩ : Succ w)).1
  have hct : Chain (t.depth - s.depth) s t := (Succ.chain (⟨t, ⟨ht⟩⟩ : Succ s)).1
  have ht₀' : t.depth - s.depth = 0 → ModalSys.T = true := (Succ.chain (⟨t, ⟨ht⟩⟩ : Succ s)).2.1
  rcases e₁ : s.depth - w.depth with _ | d
  · have hsw : s = w := by
      rw [e₁] at hcs
      exact hcs
    subst hsw
    rw [succAddrK_zero e₁, VarSymb.collapse_shift_self]
  · rw [succAddrK_succ e₁ (l + 1), shiftIterK_shift_same]
    rcases e₂ : t.depth - s.depth with _ | d'
    · have hT := ht₀' e₂
      have hts : t = s := by
        rw [e₂] at hct
        exact hct
      subst hts
      rw [succAddrK_zero e₂, succAddrK_succ e₁, shiftIterK_succ']
      -- the cut step is a `keep`: under T and 4, `box` is not an allowed step
      obtain ⟨a', ha'⟩ := splitAt_shiftIterK_at l d hx
      have htk : t₀ = .keep := by
        obtain ⟨rfl, hp, -⟩ := VarSymb.splitAt_spec hx
        have hok₀ : t₀.OK := (VarSymb.ok_ext.mp hok).2 t₀ List.mem_cons_self
        cases t₀
        · cases hp
        · cases hp
        · exact absurd (hok₀.1 rfl) (by rw [hF]; decide)
        · exact absurd rfl ht₀
        · cases hp
        · rfl
      subst htk
      exact shift_collapse_keep ha'
    · have e₃ : t.depth - w.depth = (d + 1 + d') + 1 := by omega
      rw [succAddrK_succ e₂, succAddrK_succ e₃, shiftIterK_add]

/-! ## The leaf calculus: canonical leaves commute with collapse and shift -/

/-- ⭐**Collapsing a canonical leaf collapses its label**: at the level `l` steps inside the label
    (counted from its end), which is `j` levels from the anchor. -/
theorem leafOf_collapse (hT : ModalSys.T = true) : ∀ (j : ℕ) (w : World σ N₀) (l : ℕ)
    (x : VarSymb) {a : VarSymb} {t₀ : Step} {b : List Step}, x.OK →
    VarSymb.splitAt x l = some (a, t₀, b) → t₀ ≠ .dia →
    (∃ p q r, VarSymb.splitAt x (l + j) = some (p, q, r)) →
    Arrows.Leaf.collapse hT j (leafOf w (l + j + 1) x) = leafOf w (l + j) (x.collapse l)
  | 0, w, l, x, a, t₀, b, _, hx, ht₀, _ => by
      change Arrows.Leaf.collapse hT 0 (leafOf w (l + 1) x) = leafOf w l (x.collapse l)
      rw [leafOf_lvl w hx ht₀]
      change leafOf w l (succAddrK w w l x) = _
      rw [succAddrK_zero (Nat.sub_self _)]
  | j + 1, w, l, x, a, t₀, b, hok, hx, ht₀, ⟨pre, t, rest, h⟩ => by
      obtain ⟨hxe, htp, hlv⟩ := VarSymb.splitAt_spec h
      by_cases htd : t = .dia
      · subst htd
        change Arrows.Leaf.collapse hT (j + 1) (leafOf w (l + (j + 1) + 1) x) =
          leafOf w (l + j + 1) (x.collapse l)
        rw [leafOf_dia w h, Arrows.Leaf.collapse_root,
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
        have hl := levels_collapseAt j rest (by omega)
        have hs := VarSymb.splitAt_ext pre (rfl : Step.isProj .dia = false)
          (Step.collapseAt j rest)
        rw [show Step.levels (Step.collapseAt j rest) = l + j by omega] at hs
        rw [leafOf_dia w hs]
      · change Arrows.Leaf.collapse hT (j + 1) (leafOf w (l + (j + 1) + 1) x) =
          leafOf w (l + j + 1) (x.collapse l)
        rw [leafOf_lvl w h htd]
        obtain ⟨rest', h'⟩ := splitAt_collapse_below (k := l + j) h (show l ≤ l + j by omega)
        rw [leafOf_lvl w h' htd]
        change Arrows.Leaf.fam (fun (s : (arrows σ N₀).Acc w) => Arrows.Leaf.collapse hT j
            (leafOf s.1 (l + j + 1) (succAddrK w s.1 (l + j + 1) x))) = _
        congr 1
        funext s
        obtain ⟨a', ha'⟩ := splitAt_succAddrK_above w s.1 hx (show l < l + j + 1 by omega)
        rw [leafOf_collapse hT j s.1 l _ (ok_succAddrK s _ hok) ha' ht₀
          (splitAt_succAddrK_exists w s.1 h), succAddrK_collapse]

/-- ⭐**Shifting a canonical leaf shifts its label.** -/
theorem leafOf_shift (hF : ModalSys.Four = true) : ∀ (j : ℕ) (w : World σ N₀) (l : ℕ)
    (x : VarSymb) {a : VarSymb} {t₀ : Step} {b : List Step}, x.OK →
    VarSymb.splitAt x l = some (a, t₀, b) → t₀ ≠ .dia →
    (∃ p q r, VarSymb.splitAt x (l + j) = some (p, q, r)) →
    Arrows.Leaf.shift hF j (leafOf w (l + j + 1) x) = leafOf w (l + j + 2) (x.shift l)
  | 0, w, l, x, a, t₀, b, hok, hx, ht₀, _ => by
      change Arrows.Leaf.shift hF 0 (leafOf w (l + 1) x) = leafOf w (l + 1 + 1) (x.shift l)
      obtain ⟨-, hk, hl⟩ := splitAt_shift_at hx
      rw [leafOf_lvl w hx ht₀, leafOf_lvl w hk (by decide)]
      change Arrows.Leaf.fam (fun (s : (arrows σ N₀).Acc w) =>
          Arrows.Leaf.fam fun (t : (arrows σ N₀).Acc s.1) =>
            leafOf t.1 l (succAddrK w t.1 l x)) = _
      congr 1
      funext s
      obtain ⟨a', ha'⟩ := splitAt_succAddrK_above w s.1 hl (show l < l + 1 by omega)
      rw [leafOf_lvl s.1 ha' ht₀]
      congr 1
      funext t
      rw [succAddrK_keep hF s.2.down t.2.down hx ht₀ hok]
  | j + 1, w, l, x, a, t₀, b, hok, hx, ht₀, ⟨pre, t, rest, h⟩ => by
      obtain ⟨hxe, htp, hlv⟩ := VarSymb.splitAt_spec h
      by_cases htd : t = .dia
      · subst htd
        change Arrows.Leaf.shift hF (j + 1) (leafOf w (l + (j + 1) + 1) x) =
          leafOf w (l + j + 2 + 1) (x.shift l)
        rw [leafOf_dia w h, Arrows.Leaf.shift_root,
          Step.shiftAt_succ (rfl : Step.isProj .dia = false)]
        have hagree := VarSymb.shift_agree pre (.dia :: rest) l
          (by rw [Step.levels_cons, if_neg (by decide)]; omega)
        rw [Step.levels_cons, if_neg (by decide),
          show 1 + Step.levels rest - 1 - l = j + 1 by omega,
          Step.shiftAt_succ (rfl : Step.isProj .dia = false)] at hagree
        rw [hxe, hagree]
        have hl := levels_shiftAt j rest (by omega)
        have hs := VarSymb.splitAt_ext pre (rfl : Step.isProj .dia = false)
          (Step.shiftAt j rest)
        rw [show Step.levels (Step.shiftAt j rest) = l + j + 2 by omega] at hs
        rw [leafOf_dia w hs]
      · change Arrows.Leaf.shift hF (j + 1) (leafOf w (l + (j + 1) + 1) x) =
          leafOf w (l + j + 1 + 1 + 1) (x.shift l)
        rw [leafOf_lvl w h htd]
        obtain ⟨rest', h'⟩ := splitAt_shift_below (k := l + j + 1) h (show l < l + j + 1 by omega)
        rw [leafOf_lvl w h' htd]
        change Arrows.Leaf.fam (fun (s : (arrows σ N₀).Acc w) => Arrows.Leaf.shift hF j
            (leafOf s.1 (l + j + 1) (succAddrK w s.1 (l + j + 1) x))) = _
        congr 1
        funext s
        obtain ⟨a', ha'⟩ := splitAt_succAddrK_above w s.1 hx (show l < l + j + 1 by omega)
        rw [leafOf_shift hF j s.1 l _ (ok_succAddrK s _ hok) ha' ht₀
          (splitAt_succAddrK_exists w s.1 h), succAddrK_shift]

/-! ## Whole annotations: collapse and shift -/

/-- The number of level steps of an address. -/
def _root_.V12M.VarSymb.lv (y : VarSymb) : ℕ := Step.levels y.path

omit [ModalSys] in
theorem _root_.V12M.VarSymb.eq_root_ext_path :
    ∀ y : VarSymb, y = (VarSymb.root y.rt).ext y.path
  | .root _ => rfl
  | .step v s => by
      change VarSymb.step v s = (VarSymb.root v.rt).ext (v.path ++ [s])
      rw [← VarSymb.step_ext, ← VarSymb.eq_root_ext_path v]

omit [ModalSys] in
/-- An address can be cut at any level below its number of levels. -/
theorem splitAt_of_lv {y : VarSymb} {i : ℕ} (h : i < y.lv) :
    ∃ a t b, VarSymb.splitAt y i = some (a, t, b) := by
  rw [VarSymb.eq_root_ext_path y]
  exact splitAt_exists _ y.path i h

omit [ModalSys] in
theorem lv_step (v : VarSymb) (s : Step) :
    (VarSymb.step v s).lv = v.lv + if s.isProj then 0 else 1 := by
  simp only [VarSymb.lv, VarSymb.path, Step.levels_append, Step.levels_single]

theorem ok_inner {v : VarSymb} (hT : ModalSys.T = true) (h : v.OK) : v.inner.OK := by
  unfold VarSymb.inner
  split_ifs with hk
  · have hF : ModalSys.Four = true := by
      simpa [ModalSys.keepOnly, hT] using hk
    exact VarSymb.ok_step.mpr ⟨VarSymb.ok_step.mpr ⟨h, nofun, fun _ => hF⟩,
      Step.ok_of_proj rfl⟩
  · have hF : ModalSys.Four = false := by
      simpa [ModalSys.keepOnly, hT] using hk
    exact VarSymb.ok_step.mpr ⟨h, fun _ => hF, nofun⟩

theorem lv_inner (v : VarSymb) : v.inner.lv = v.lv + 1 := by
  unfold VarSymb.inner
  split_ifs <;> simp [lv_step, Step.isProj]

/-- The cut of a contents address at its own level is a `□` step. -/
theorem splitAt_inner (v : VarSymb) :
    ∃ t b, VarSymb.splitAt v.inner 0 = some (v, t, b) ∧ t ≠ .dia := by
  unfold VarSymb.inner
  split_ifs
  · exact ⟨.keep, [.here], rfl, nofun⟩
  · exact ⟨.box, [], rfl, nofun⟩

/-- ⭐**Collapsing a canonical annotation** at a level inside its labels collapses its addresses. -/
theorem annShp_eta_collapse (hT : ModalSys.T = true) : ∀ (X : VarType) (w : World σ N₀)
    (j l : ℕ) (z : VarSymb) {a : VarSymb} {t₀ : Step} {b : List Step}, z.OK →
    VarSymb.splitAt z l = some (a, t₀, b) → t₀ ≠ .dia → l + j < z.lv →
    (annShp w (l + j + 1) (Ann.eta z X)).map (Arrows.Leaf.collapse hT j) =
      annShp w (l + j) (Ann.eta (z.collapse l) X)
  | .Var, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .VTypeOne, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .VTypeProd A B, w, j, l, z, a, t₀, b, hok, hz, ht₀, hlv => by
      have hf := VarSymb.splitAt_extend hz [.fst]
      have hs := VarSymb.splitAt_extend hz [.snd]
      simp only [Step.levels, Step.isProj, if_true, Nat.add_zero] at hf hs
      change Shp.prod ((annShp w (l + j + 1) (Ann.eta (.step z .fst) A)).map _)
          ((annShp w (l + j + 1) (Ann.eta (.step z .snd) B)).map _) =
        Shp.prod (annShp w (l + j) (Ann.eta (.step (z.collapse l) .fst) A))
          (annShp w (l + j) (Ann.eta (.step (z.collapse l) .snd) B))
      rw [annShp_eta_collapse hT A w j l (.step z .fst)
          (VarSymb.ok_step.mpr ⟨hok, Step.ok_of_proj rfl⟩) hf ht₀
          (by rw [lv_step]; simpa [Step.isProj] using hlv),
        annShp_eta_collapse hT B w j l (.step z .snd)
          (VarSymb.ok_step.mpr ⟨hok, Step.ok_of_proj rfl⟩) hs ht₀
          (by rw [lv_step]; simpa [Step.isProj] using hlv),
        VarSymb.collapse_proj (rfl : Step.isProj .fst = true),
        VarSymb.collapse_proj (rfl : Step.isProj .snd = true)]
  | .VTypeBox A, w, j, l, z, a, t₀, b, hok, hz, ht₀, hlv => by
      have hi := VarSymb.splitAt_extend hz Step.innerPath
      rw [← List.nil_append Step.innerPath, ← VarSymb.inner_ext z [], List.nil_append,
        levels_innerPath] at hi
      change Shp.box ((annShp w (l + j + 1 + 1) (Ann.eta z.inner A)).map _) =
        Shp.box (annShp w (l + j + 1) (Ann.eta (z.collapse l).inner A))
      have ih := annShp_eta_collapse hT A w j (l + 1) z.inner (ok_inner hT hok) hi ht₀
        (by rw [lv_inner]; omega)
      rw [show l + 1 + j + 1 = l + j + 1 + 1 by omega, show l + 1 + j = l + j + 1 by omega,
        VarSymb.inner_collapse_succ] at ih
      rw [ih]
  | .VTypeDia A, w, j, l, z, a, t₀, b, hok, hz, ht₀, hlv => by
      have hd := VarSymb.splitAt_extend hz [.dia]
      simp only [Step.levels, Step.isProj, Bool.false_eq_true, if_false, Nat.add_zero] at hd
      change Shp.dia (Arrows.Leaf.collapse hT j (leafOf w (l + j + 1) z))
          ((annShp w (l + j + 1 + 1) (Ann.eta (.step z .dia) A)).map _) =
        Shp.dia (leafOf w (l + j) (z.collapse l))
          (annShp w (l + j + 1) (Ann.eta (.step (z.collapse l) .dia) A))
      have ih := annShp_eta_collapse hT A w j (l + 1) (.step z .dia)
        (VarSymb.ok_step.mpr ⟨hok, Step.ok_dia⟩) hd ht₀
        (by rw [lv_step]; simp [Step.isProj]; omega)
      rw [show l + 1 + j + 1 = l + j + 1 + 1 by omega, show l + 1 + j = l + j + 1 by omega,
        VarSymb.collapse_level_succ (rfl : Step.isProj .dia = false)] at ih
      rw [leafOf_collapse hT j w l z hok hz ht₀ (splitAt_of_lv hlv), ih]

/-- ⭐**Shifting a canonical annotation** at a level inside its labels shifts its addresses. -/
theorem annShp_eta_shift (hT : ModalSys.T = true) (hF : ModalSys.Four = true) :
    ∀ (X : VarType) (w : World σ N₀) (j l : ℕ) (z : VarSymb) {a : VarSymb} {t₀ : Step}
      {b : List Step}, z.OK → VarSymb.splitAt z l = some (a, t₀, b) → t₀ ≠ .dia →
      l + j < z.lv →
      (annShp w (l + j + 1) (Ann.eta z X)).map (Arrows.Leaf.shift hF j) =
        annShp w (l + j + 2) (Ann.eta (z.shift l) X)
  | .Var, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .VTypeOne, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .VTypeProd A B, w, j, l, z, a, t₀, b, hok, hz, ht₀, hlv => by
      have hf := VarSymb.splitAt_extend hz [.fst]
      have hs := VarSymb.splitAt_extend hz [.snd]
      simp only [Step.levels, Step.isProj, if_true, Nat.add_zero] at hf hs
      change Shp.prod ((annShp w (l + j + 1) (Ann.eta (.step z .fst) A)).map _)
          ((annShp w (l + j + 1) (Ann.eta (.step z .snd) B)).map _) =
        Shp.prod (annShp w (l + j + 2) (Ann.eta (.step (z.shift l) .fst) A))
          (annShp w (l + j + 2) (Ann.eta (.step (z.shift l) .snd) B))
      rw [annShp_eta_shift hT hF A w j l (.step z .fst)
          (VarSymb.ok_step.mpr ⟨hok, Step.ok_of_proj rfl⟩) hf ht₀
          (by rw [lv_step]; simpa [Step.isProj] using hlv),
        annShp_eta_shift hT hF B w j l (.step z .snd)
          (VarSymb.ok_step.mpr ⟨hok, Step.ok_of_proj rfl⟩) hs ht₀
          (by rw [lv_step]; simpa [Step.isProj] using hlv),
        VarSymb.shift_proj (rfl : Step.isProj .fst = true),
        VarSymb.shift_proj (rfl : Step.isProj .snd = true)]
  | .VTypeBox A, w, j, l, z, a, t₀, b, hok, hz, ht₀, hlv => by
      have hi := VarSymb.splitAt_extend hz Step.innerPath
      rw [← List.nil_append Step.innerPath, ← VarSymb.inner_ext z [], List.nil_append,
        levels_innerPath] at hi
      change Shp.box ((annShp w (l + j + 1 + 1) (Ann.eta z.inner A)).map _) =
        Shp.box (annShp w (l + j + 2 + 1) (Ann.eta (z.shift l).inner A))
      have ih := annShp_eta_shift hT hF A w j (l + 1) z.inner (ok_inner hT hok) hi ht₀
        (by rw [lv_inner]; omega)
      rw [show l + 1 + j + 1 = l + j + 1 + 1 by omega, show l + 1 + j + 2 = l + j + 2 + 1 by omega,
        VarSymb.inner_shift_succ] at ih
      rw [ih]
  | .VTypeDia A, w, j, l, z, a, t₀, b, hok, hz, ht₀, hlv => by
      have hd := VarSymb.splitAt_extend hz [.dia]
      simp only [Step.levels, Step.isProj, Bool.false_eq_true, if_false, Nat.add_zero] at hd
      change Shp.dia (Arrows.Leaf.shift hF j (leafOf w (l + j + 1) z))
          ((annShp w (l + j + 1 + 1) (Ann.eta (.step z .dia) A)).map _) =
        Shp.dia (leafOf w (l + j + 2) (z.shift l))
          (annShp w (l + j + 2 + 1) (Ann.eta (.step (z.shift l) .dia) A))
      have ih := annShp_eta_shift hT hF A w j (l + 1) (.step z .dia)
        (VarSymb.ok_step.mpr ⟨hok, Step.ok_dia⟩) hd ht₀
        (by rw [lv_step]; simp [Step.isProj]; omega)
      rw [show l + 1 + j + 1 = l + j + 1 + 1 by omega, show l + 1 + j + 2 = l + j + 2 + 1 by omega,
        VarSymb.shift_level_succ (rfl : Step.isProj .dia = false)] at ih
      rw [leafOf_shift hF j w l z hok hz ht₀ (splitAt_of_lv hlv), ih]

/-! ## Shape environments that read every address canonically -/

/-- Every reachable address has at least `j` levels: `j` views have been entered. -/
def _root_.V12M.Ctx.Deep (Δ : Ctx) (j : ℕ) : Prop := ∀ y T, Δ.ref y = some T → j ≤ y.lv

theorem _root_.V12M.Ctx.deep_zero (Δ : Ctx) : Δ.Deep 0 := fun _ _ _ => Nat.zero_le _

theorem _root_.V12M.Ctx.Deep.of_decl {Δ : Ctx} {j : ℕ}
    (h : ∀ y T, Δ y = some T → j ≤ y.lv) : Δ.Deep j := by
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
            rw [lv_step, if_pos hs]
            exact ih U hU
      · change (if s.isProj then (Δ.ref v).bind (·.step s) else Δ (.step v s)) = some T at hy
        rw [if_neg hs] at hy
        exact h _ T hy

theorem _root_.V12M.Ctx.Deep.boxIn {Δ : Ctx} {j : ℕ} (h : Δ.Deep j) : Δ.boxIn.Deep (j + 1) := by
  refine Ctx.Deep.of_decl fun v T hv => ?_
  match v, hv with
  | .step u .box, hv =>
      rw [lv_step, if_neg (by decide)]
      exact Nat.add_le_add_right (h u _ (Ctx.boxIn_box hv).2) 1
  | .step u .keep, hv =>
      rw [lv_step, if_neg (by decide)]
      exact Nat.add_le_add_right (h u _ (Ctx.boxIn_keep hv).2.1) 1
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .dia, hv => cases hv
  | .step _ .here, hv => cases hv

theorem _root_.V12M.Ctx.Deep.diaIn {Δ : Ctx} {j : ℕ} (h : Δ.Deep j) (x : VarSymb) :
    (Δ.diaIn x).Deep (j + 1) := by
  refine Ctx.Deep.of_decl fun v T hv => ?_
  match v, hv with
  | .step u .dia, hv =>
      change (if u = x then (match Δ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with hux
      subst hux
      cases hx : Δ.ref u with
      | none => rw [hx] at hv; cases hv
      | some X =>
          rw [lv_step, if_neg (by decide)]
          exact Nat.add_le_add_right (h u _ hx) 1
  | .step u .box, hv => exact h.boxIn _ _ ((Ctx.ref_nonproj _ rfl).trans hv)
  | .step u .keep, hv => exact h.boxIn _ _ ((Ctx.ref_nonproj _ rfl).trans hv)
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .here, hv => cases hv

/-- ⭐A shape environment at depth `j` **reads every address canonically** when each reachable
    address's shape is its η-annotation read canonically. -/
def Canonical {Δ : Ctx} {w : World σ N₀} (ρ : CShEnv Δ w) (j : ℕ) : Prop :=
  ∀ y T (h : Δ.ref y = some T), ρ.ref j y h = annShp w j (Ann.eta y T)

/-- A projection moves a canonical η-annotation to the projected address's. -/
theorem shp_proj_annShp {Δ : Ctx} (hok : Δ.DeclOK) {j : ℕ}
    (hdeep : Δ.Deep j) (w : World σ N₀) {v : VarSymb} {U T : VarType} {s : Step}
    (hs : s.isProj = true) (hU : Δ.ref v = some U) (h : U.step s = some T) :
    GFunc.shp (GFunc.proj (σ := σ) hs h) j (annShp w j (Ann.eta v U)) =
      annShp w j (Ann.eta (.step v s) T) := by
  cases U <;> cases s <;> (try cases hs) <;> (try cases h)
  · rfl
  · rfl
  · rename_i X
    obtain ⟨hT', rfl⟩ := VarType.step_here h
    change (annShp w (j + 1) (Ann.eta v.inner X)).map (Arrows.Leaf.collapse hT' j) = _
    obtain ⟨t, b, hi, ht⟩ := splitAt_inner v
    have := annShp_eta_collapse hT' X w j 0 v.inner (ok_inner hT' (hok.ref v hU)) hi ht
      (by rw [lv_inner]; have := hdeep v _ hU; omega)
    rw [Nat.zero_add] at this
    rw [this, VarSymb.inner_collapse_zero]

/-- It suffices that the declared addresses read canonically. -/
theorem Canonical.of_decl {Δ : Ctx} (hok : Δ.DeclOK) {j : ℕ}
    (hdeep : Δ.Deep j) {w : World σ N₀} {ρ : CShEnv Δ w}
    (h : ∀ y T (hy : Δ y = some T), ρ y T hy = annShp w j (Ann.eta y T)) :
    Canonical ρ j := by
  intro y
  induction y with
  | root r => intro T hy; exact h _ T hy
  | step v s ih =>
      intro T hy
      by_cases hs : s.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Δ.ref v = some U := by
          rw [Ctx.ref_step_proj Δ v hs] at hy
          cases hU : Δ.ref v with
          | none => rw [hU] at hy; cases hy
          | some U => exact ⟨U, rfl⟩
        rw [Model.ShEnv.ref_proj ρ j hs hU hy, ih U hU]
        exact shp_proj_annShp hok hdeep w hs hU _
      · rw [Model.ShEnv.ref_nonproj ρ j hs hy]
        exact h _ T _

/-- ⭐Pushing a canonical environment into `□` gives a canonical one, one level deeper. -/
theorem Canonical.boxPush (hT : ModalSys.T = true) {Δ : Ctx} (hok : Δ.DeclOK) {j : ℕ}
    (hdeep : Δ.Deep j) {w : World σ N₀} {ρ : CShEnv Δ w} (hρ : Canonical ρ j) :
    Canonical (ρ.boxPush j) (j + 1) := by
  refine Canonical.of_decl (hok.boxIn hT) hdeep.boxIn fun v T hv => ?_
  match v, hv with
  | .step u .box, hv =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hv
      change (ρ.ref j u (Ctx.boxIn_step_box hv)).inner = _
      rw [hρ u _ (Ctx.boxIn_step_box hv)]
      change annShp w (j + 1) (Ann.eta u.inner T) = _
      rw [VarSymb.inner_box hk]
  | .step u .keep, hv =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep hv
      change (GFunc.shp (GFunc.dup (σ := σ) hF) j (ρ.ref j u hu)).inner = _
      rw [hρ u _ hu]
      change Shp.box ((annShp w (j + 1) (Ann.eta u.inner A)).map (Arrows.Leaf.shift hF j)) =
        Shp.box (annShp w (j + 1 + 1) (Ann.eta (VarSymb.step u .keep).inner A))
      obtain ⟨t, b, hi, ht⟩ := splitAt_inner u
      have := annShp_eta_shift hT hF A w j 0 u.inner (ok_inner hT (hok.ref u hu)) hi ht
        (by rw [lv_inner]; have := hdeep u _ hu; omega)
      rw [Nat.zero_add] at this
      rw [this, VarSymb.inner_shift_zero]
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .dia, hv => cases hv
  | .step _ .here, hv => cases hv

/-- ⭐Pushing a canonical environment into `◇_x` gives a canonical one, one level deeper. -/
theorem Canonical.diaPush (hT : ModalSys.T = true) {Δ : Ctx} (hok : Δ.DeclOK) {j : ℕ}
    (hdeep : Δ.Deep j) {w : World σ N₀} {ρ : CShEnv Δ w} (hρ : Canonical ρ j) {x : VarSymb}
    {X : VarType} (hx : Δ.ref x = some (.VTypeDia X)) :
    Canonical (ρ.diaPush j x hx) (j + 1) := by
  refine Canonical.of_decl (hok.diaIn hT x) (hdeep.diaIn x) fun v T hv => ?_
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
      have hc := (hρ.boxPush hT hok hdeep) _ _ hb
      rw [Model.ShEnv.ref_nonproj _ _ (by decide) hb] at hc
      exact hc
  | .step u .keep, hv =>
      have hb : Δ.boxIn.ref (.step u .keep) = some T :=
        (Ctx.ref_nonproj _ (show (VarSymb.step u .keep).lastProj = false from rfl)).trans hv
      have hc := (hρ.boxPush hT hok hdeep) _ _ hb
      rw [Model.ShEnv.ref_nonproj _ _ (by decide) hb] at hc
      exact hc
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .here, hv => cases hv

/-- ⭐⭐**The relabelling theorem**: in a canonical environment, a term's shape is its annotation
    read canonically. -/
theorem termShp_canonical (hT : ModalSys.T = true) {w : World σ N₀} :
    ∀ {Δ : Ctx}, Δ.DeclOK → ∀ {j : ℕ}, Δ.Deep j → ∀ {ρ : CShEnv Δ w},
      Canonical ρ j → ∀ {A : VarType} {a : Ann A} (t : Term σ Δ A a),
        Model.termShp ρ j t = annShp w j a
  | _, _, _, _, _, _, _, _, .var _ _ => rfl
  | _, _, _, _, _, _, _, _, .func _ => rfl
  | _, _, _, _, _, _, _, _, .unit => rfl
  | _, hok, _, hdeep, _, hρ, _, _, .pair s t => by
      change Shp.prod (Model.termShp _ _ s) (Model.termShp _ _ t) = _
      rw [termShp_canonical hT hok hdeep hρ s, termShp_canonical hT hok hdeep hρ t]
      rfl
  | _, hok, j, hdeep, ρ, hρ, _, _, .boxtm t => by
      change Shp.box (Model.termShp (ρ.boxPush j) (j + 1) t) = _
      rw [termShp_canonical hT (hok.boxIn hT) hdeep.boxIn (hρ.boxPush hT hok hdeep) t]
      rfl
  | _, hok, j, hdeep, ρ, hρ, _, _, .diatm x hx t => by
      obtain ⟨X, hr⟩ := id hx
      rw [Model.termShp_diatm ρ j hr hx,
        termShp_canonical hT (hok.diaIn hT x) (hdeep.diaIn x) (hρ.diaPush hT hok hdeep hr) t,
        hρ x _ hr]
      rfl

/-- The canonical shape environment reads every address canonically. -/
theorem cEnv_canonical (Γ : Ctx) (w : World σ N₀) : Canonical (cEnv Γ w) 0 := by
  intro y T h
  rw [cEnv_ref, canonSh_eq]

/-! ## Tags determine annotations -/

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- Under T every canonical world has a proper successor: `T_box` refutes `□⊥`, so a `□` fails and
    `exists_box_fail` builds a child.  (A general T model need not have one; the canonical one
    does.) -/
theorem exists_acc (hT : ModalSys.T = true) (w : World σ N₀) : ∃ w', Acc' w w' := by
  have hnot : (⟨(0, 0), .box .bot⟩ : w.L.sys.Sentence σ) ∉ w.T := fun h =>
    w.mcs.bot_not_mem (World.mem_of_provable (Δ := [.box .bot])
      (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact h)
      ⟨Proof.T_box hT (Proof.lookup List.mem_cons_self)⟩)
  obtain ⟨w', ha, -⟩ := exists_box_fail w (i := (0, 0)) .bot hnot
  exact ⟨w', ha⟩

/-- A chosen proper successor of each world, under T. -/
noncomputable def properSucc (hT : ModalSys.T = true) (w : World σ N₀) : (arrows σ N₀).Acc w :=
  ⟨(exists_acc hT w).choose, ⟨R.of_acc (exists_acc hT w).choose_spec⟩⟩

theorem properSucc_depth (hT : ModalSys.T = true) (w : World σ N₀) :
    (properSucc hT w).1.depth - w.depth = 0 + 1 := by
  have := (exists_acc hT w).choose_spec.1
  change (exists_acc hT w).choose.depth - w.depth = _
  omega

/-- ⭐**The decoder**: follow every family along a proper successor — where `succAddrK` is the
    identity — and put the root and its path back together. -/
noncomputable def dec (hT : ModalSys.T = true) : {w : World σ N₀} → CLeaf w → VarSymb
  | _, .root r p => VarSymb.ext r p
  | w, .fam f => dec hT (f (properSucc hT w))

/-- ⭐**The decoder reads a canonical leaf back to its label.** -/
theorem dec_leafOf (hT : ModalSys.T = true) : ∀ (m : ℕ) (w : World σ N₀) (y : VarSymb),
    dec hT (leafOf w m y) = y
  | 0, w, y => by rw [leafOf_zero]; rfl
  | m + 1, w, y => by
      have hfam : (leafOf w (m + 1) y = .fam fun s => leafOf s.1 m (succAddrK w s.1 m y)) →
          dec hT (leafOf w (m + 1) y) = y := by
        intro e
        rw [e]
        change dec hT (leafOf (properSucc hT w).1 m (succAddrK w (properSucc hT w).1 m y)) = y
        rw [dec_leafOf hT m, succAddrK_succ (properSucc_depth hT w)]
        rfl
      rcases h : VarSymb.splitAt y m with _ | ⟨pre, t, rest⟩
      · exact hfam (by simp only [leafOf, h])
      · by_cases htd : t = .dia
        · subst htd
          rw [leafOf_dia w h]
          exact (VarSymb.splitAt_spec h).1.symm
        · exact hfam (leafOf_lvl w h htd)

/-- Reading annotations canonically is injective. -/
theorem annShp_injective (hT : ModalSys.T = true) (w : World σ N₀) :
    ∀ {A : VarType} (j : ℕ) (a a' : Ann A), annShp w j a = annShp w j a' → a = a'
  | _, _, .var, .var, _ => rfl
  | _, _, .one, .one, _ => rfl
  | _, j, .prod a b, .prod a' b', h => by
      injection h with _ _ h₁ h₂
      rw [annShp_injective hT w j a a' h₁, annShp_injective hT w j b b' h₂]
  | _, j, .box a, .box a', h => by
      injection h with _ h₁
      rw [annShp_injective hT w (j + 1) a a' h₁]
  | _, j, .dia x a, .dia x' a', h => by
      injection h with _ h₁ h₂
      have hx : x = x' := by
        have := congrArg (dec hT) h₁
        rwa [dec_leafOf, dec_leafOf] at this
      rw [hx, annShp_injective hT w (j + 1) a a' h₂]

/-- ⭐⭐**Canonical shapes determine annotations**: two terms of one type, in a context whose
    addresses are allowed (every presented one), with the same canonical shape have the same
    annotation. -/
theorem ann_eq_of_termShp (hT : ModalSys.T = true) {Γ : Ctx} (hok : Γ.DeclOK)
    (w : World σ N₀) {A : VarType} {a a' : Ann A} (t : Term σ Γ A a) (t' : Term σ Γ A a')
    (h : Model.termShp (cEnv Γ w) 0 t = Model.termShp (cEnv Γ w) 0 t') : a = a' := by
  refine annShp_injective hT w 0 a a' ?_
  rw [← termShp_canonical hT hok (Γ.deep_zero) (cEnv_canonical Γ w) t,
    ← termShp_canonical hT hok (Γ.deep_zero) (cEnv_canonical Γ w) t', h]

/-- ⭐⭐**Tags determine annotations**: two terms with one denotation have one annotation. -/
theorem ann_eq_of_rden (hT : ModalSys.T = true) {Γ : Ctx} (hok : Γ.DeclOK) {w : World σ N₀}
    {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) {A : VarType} {a a' : Ann A} (t : Term σ Γ A a)
    (t' : Term σ Γ A a') (h : rden w i e t = rden w i e t') : a = a' :=
  ann_eq_of_termShp hT hok w t t'
    (by rw [← rawShape_rden hT w i e t, ← rawShape_rden hT w i e t', h])

end Canon

end V12M
