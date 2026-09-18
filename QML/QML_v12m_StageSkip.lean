import QML.QML_v12m_Stages

/-!
# QML v12m — a stage with one own variable left out

Strong T's canonical model reads a `T_dia` hypothesis at a later stage, and the lemmas about the
`◇_c` view want the witness to be the *outermost* declaration of the context it works in
(`WFF.subst_diaViewRead`).  The contexts of a world do not have that shape: the witness `ρ n` is
declared in the middle, with the constants of the later stages on top of it.

Since a context is a function, the declarations commute (`Ctx.insert_swap`), so the stage is the
stage-without-`ρ n` with `ρ n` declared last.

* `Ctx.stageSkip`: the stage with the `n`-th own variable left out;
* ⭐`Ctx.stage_eq_skip_insert`: the stage is that, with the `n`-th declared on top;
* `Ctx.stageSkip_cases`: what a raw entry of it can be — a base entry, or one of the own roots.
-/

namespace V12M

variable [ModalSys]

namespace Ctx

omit [ModalSys] in
/-- Declarations at different roots commute. -/
theorem insert_swap {Γ : Ctx} {r r' : Root} (h : r ≠ r') (T T' : VarType) :
    (Γ.insert r T).insert r' T' = (Γ.insert r' T').insert r T := by
  funext v
  change (if v = .root r' then some T' else if v = .root r then some T else Γ v) =
    (if v = .root r then some T else if v = .root r' then some T' else Γ v)
  by_cases h' : v = .root r'
  · subst h'
    rw [if_pos rfl, if_neg (fun he => h (VarSymb.root.inj he).symm), if_pos rfl]
  · rw [if_neg h']
    by_cases h'' : v = .root r
    · rw [if_pos h'', if_pos h'']
    · rw [if_neg h'', if_neg h'', if_neg h']

variable (B : Ctx) (τ : ℕ → VarType) (ρ : ℕ → ℕ) (n : ℕ)

/-- The stage with the `n`-th own variable left out. -/
def stageSkip : ℕ → Ctx
  | 0 => B
  | k + 1 => if k = n then stageSkip k else (stageSkip k).insert (.free (ρ k)) (τ k)

variable {B τ ρ n}

omit [ModalSys] in
/-- Before the skipped variable, nothing is left out. -/
theorem stageSkip_le : ∀ {k : ℕ}, k ≤ n → B.stageSkip τ ρ n k = B.stage τ ρ k
  | 0, _ => rfl
  | k + 1, h => by
      have hk : k ≠ n := by omega
      change (if k = n then _ else (B.stageSkip τ ρ n k).insert (.free (ρ k)) (τ k)) = _
      rw [if_neg hk, stageSkip_le (Nat.le_of_succ_le h)]
      rfl

omit [ModalSys] in
/-- ⭐The stage is the stage without the `n`-th own variable, with that variable declared last. -/
theorem stage_eq_skip_insert (hρ : Function.Injective ρ) :
    ∀ {j : ℕ}, n < j → B.stage τ ρ j = (B.stageSkip τ ρ n j).insert (.free (ρ n)) (τ n)
  | j + 1, h => by
      rcases Nat.lt_or_ge n j with hn | hn
      · have hj : j ≠ n := by omega
        change (B.stage τ ρ j).insert (.free (ρ j)) (τ j) = _
        rw [stage_eq_skip_insert hρ hn,
          Ctx.insert_swap (Γ := B.stageSkip τ ρ n j) (r := .free (ρ n)) (r' := .free (ρ j))
            (fun he => hj (hρ (Root.free.inj he)).symm) (τ n) (τ j)]
        change _ = (if j = n then _ else (B.stageSkip τ ρ n j).insert (.free (ρ j)) (τ j)).insert
          (.free (ρ n)) (τ n)
        rw [if_neg hj]
      · have hn' : n = j := by omega
        subst hn'
        change (B.stage τ ρ n).insert (.free (ρ n)) (τ n) = _
        change _ = (if n = n then B.stageSkip τ ρ n n else _).insert (.free (ρ n)) (τ n)
        rw [if_pos rfl, stageSkip_le (le_refl n)]

omit [ModalSys] in
/-- A raw entry of the skipped stage is a base entry or one of the own roots. -/
theorem stageSkip_cases : ∀ (j : ℕ) {v : VarSymb} {T : VarType},
    B.stageSkip τ ρ n j v = some T →
      B v = some T ∨ ∃ k, k < j ∧ k ≠ n ∧ v = .root (.free (ρ k)) ∧ T = τ k
  | 0, _, _, h => Or.inl h
  | j + 1, v, T, h => by
      by_cases hj : j = n
      · rw [show B.stageSkip τ ρ n (j + 1) = B.stageSkip τ ρ n j from if_pos hj] at h
        rcases stageSkip_cases j h with h' | ⟨k, hk, hkn, hv, hT⟩
        · exact Or.inl h'
        · exact Or.inr ⟨k, Nat.lt_succ_of_lt hk, hkn, hv, hT⟩
      · rw [show B.stageSkip τ ρ n (j + 1) =
          (B.stageSkip τ ρ n j).insert (.free (ρ j)) (τ j) from if_neg hj] at h
        by_cases hv : v = .root (.free (ρ j))
        · subst hv
          change (if (VarSymb.root (.free (ρ j))) = .root (.free (ρ j)) then some (τ j)
            else _) = some T at h
          rw [if_pos rfl] at h
          exact Or.inr ⟨j, Nat.lt_succ_self j, hj, rfl, (Option.some.inj h).symm⟩
        · change (if v = .root (.free (ρ j)) then some (τ j) else _) = some T at h
          rw [if_neg hv] at h
          rcases stageSkip_cases j h with h' | ⟨k, hk, hkn, hv', hT⟩
          · exact Or.inl h'
          · exact Or.inr ⟨k, Nat.lt_succ_of_lt hk, hkn, hv', hT⟩

omit [ModalSys] in
/-- Own names from `j` on are fresh in the skipped stage. -/
theorem stageSkip_fresh (hρ : Function.Injective ρ) (hB : ∀ p, B.RootFresh (.free (ρ p))) :
    ∀ {j k : ℕ}, j ≤ k → (B.stageSkip τ ρ n j).RootFresh (.free (ρ k))
  | 0, _, _ => hB _
  | j + 1, k, h => by
    intro v hv
    by_cases hj : j = n
    · rw [show B.stageSkip τ ρ n (j + 1) = B.stageSkip τ ρ n j from if_pos hj]
      exact stageSkip_fresh hρ hB (by omega) v hv
    · rw [show B.stageSkip τ ρ n (j + 1) =
        (B.stageSkip τ ρ n j).insert (.free (ρ j)) (τ j) from if_neg hj]
      change (if v = .root (.free (ρ j)) then some (τ j) else _) = none
      rw [if_neg (fun he => by
        subst he
        exact absurd (hρ (Root.free.inj hv)) (by omega))]
      exact stageSkip_fresh hρ hB (by omega) v hv

/-- A variable other than the skipped one is reachable in the skipped stage at its own type. -/
theorem stageSkip_ref_root (hρ : Function.Injective ρ) (hB : ∀ p, B.RootFresh (.free (ρ p)))
    {k : ℕ} : ∀ {j : ℕ}, k < j → k ≠ n →
      (B.stageSkip τ ρ n j).ref (.root (.free (ρ k))) = some (τ k)
  | j + 1, h, hkn => by
      by_cases hj : j = n
      · rw [show B.stageSkip τ ρ n (j + 1) = B.stageSkip τ ρ n j from if_pos hj]
        exact stageSkip_ref_root hρ hB (by omega) hkn
      · rw [show B.stageSkip τ ρ n (j + 1) =
          (B.stageSkip τ ρ n j).insert (.free (ρ j)) (τ j) from if_neg hj]
        change (if (VarSymb.root (.free (ρ k))) = .root (.free (ρ j)) then some (τ j)
          else (B.stageSkip τ ρ n j) (.root (.free (ρ k)))) = _
        by_cases hkj : k = j
        · subst hkj
          rw [if_pos rfl]
        · rw [if_neg (fun he => hkj (hρ (Root.free.inj (VarSymb.root.inj he))))]
          exact stageSkip_ref_root hρ hB (by omega) hkn

omit [ModalSys] in
/-- Nothing else is written at an own root of the skipped stage. -/
theorem stageSkip_only_root (hρ : Function.Injective ρ) (hB : ∀ p, B.RootFresh (.free (ρ p)))
    {k : ℕ} : ∀ (j : ℕ) (v : VarSymb), v.rt = .free (ρ k) → v ≠ .root (.free (ρ k)) →
      (B.stageSkip τ ρ n j) v = none
  | 0, v, hv, _ => hB k v hv
  | j + 1, v, hv, hne => by
      by_cases hj : j = n
      · rw [show B.stageSkip τ ρ n (j + 1) = B.stageSkip τ ρ n j from if_pos hj]
        exact stageSkip_only_root hρ hB j v hv hne
      · rw [show B.stageSkip τ ρ n (j + 1) =
          (B.stageSkip τ ρ n j).insert (.free (ρ j)) (τ j) from if_neg hj]
        change (if v = .root (.free (ρ j)) then some (τ j) else _) = none
        rw [if_neg ?_]
        · exact stageSkip_only_root hρ hB j v hv hne
        · intro he
          subst he
          exact hne (congrArg (fun r => VarSymb.root (Root.free r)) (Root.free.inj hv))

omit [ModalSys] in
/-- The skipped variable itself is fresh in the skipped stage. -/
theorem stageSkip_fresh_skipped (hρ : Function.Injective ρ) (hB : ∀ p, B.RootFresh (.free (ρ p))) :
    ∀ (j : ℕ), (B.stageSkip τ ρ n j).RootFresh (.free (ρ n))
  | 0 => hB n
  | j + 1 => by
      by_cases hj : j = n
      · rw [show B.stageSkip τ ρ n (j + 1) = B.stageSkip τ ρ n j from if_pos hj]
        exact stageSkip_fresh_skipped hρ hB j
      · rw [show B.stageSkip τ ρ n (j + 1) =
          (B.stageSkip τ ρ n j).insert (.free (ρ j)) (τ j) from if_neg hj]
        intro v hv
        change (if v = .root (.free (ρ j)) then some (τ j) else _) = none
        rw [if_neg (fun he => by subst he; exact hj (hρ (Root.free.inj hv)))]
        exact stageSkip_fresh_skipped hρ hB j v hv

omit [ModalSys] in
/-- The skipped stage has no slots. -/
theorem stageSkip_slots (hB : B.SlotsFrom 0) : ∀ j, (B.stageSkip τ ρ n j).SlotsFrom 0
  | 0 => hB
  | j + 1 => by
      by_cases hj : j = n
      · rw [show B.stageSkip τ ρ n (j + 1) = B.stageSkip τ ρ n j from if_pos hj]
        exact stageSkip_slots hB j
      · rw [show B.stageSkip τ ρ n (j + 1) =
          (B.stageSkip τ ρ n j).insert (.free (ρ j)) (τ j) from if_neg hj]
        exact (stageSkip_slots hB j).insertFree (ρ j) (τ j)

omit [ModalSys] in
/-- The stage at the witness embeds in every later skipped stage. -/
theorem stage_le_stageSkip (hρ : Function.Injective ρ) (hB : ∀ p, B.RootFresh (.free (ρ p))) :
    ∀ {j : ℕ}, n ≤ j → (B.stage τ ρ n).Le (B.stageSkip τ ρ n j)
  | 0, h => by
      have hn : n = 0 := Nat.le_zero.mp h
      subst hn
      exact Ctx.Le.refl _
  | j + 1, h => by
      rcases Nat.lt_or_ge n (j + 1) with hn | hn
      · have hnj : n ≤ j := by omega
        by_cases hj : j = n
        · rw [show B.stageSkip τ ρ n (j + 1) = B.stageSkip τ ρ n j from if_pos hj]
          exact stage_le_stageSkip hρ hB hnj
        · rw [show B.stageSkip τ ρ n (j + 1) =
            (B.stageSkip τ ρ n j).insert (.free (ρ j)) (τ j) from if_neg hj]
          exact (stage_le_stageSkip hρ hB hnj).trans
            (Ctx.le_insert (stageSkip_fresh hρ hB (le_refl j)).root (τ j))
      · have hn' : n = j + 1 := by omega
        subst hn'
        rw [stageSkip_le (le_refl _)]
        exact Ctx.Le.refl _

end Ctx

end V12M
