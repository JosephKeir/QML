import QML.QML_v12m_CanonExist

/-!
# QML v12m — early check for the arrow-based canonical model: the finite-piece lemma

An early check for `docs/v12-arrow-canonical.md` §6, written against the *current* canonical
worlds, without a B flag: weak B enters only as a hypothesis on the source world's theory
(closure under `◇□ψ ⊢ ψ` for closed `ψ`), and the arrow only as a substitution with necessity
transfer. Nothing imports this file.

⭐`finite_piece_closed` (and `finite_piece`, along an arrow): if `v` is accessible from `w`,
and `v`'s theory says `□χ(s)` for a formula `χ` closed apart from its hole and any term `s` of
`v`'s `□` view, then some term `t` of `w` has `χ(t)` in `w`'s theory. A finite set of `v`'s
`□`-items is covered by taking `s` to be their tuple.

The proof is shorter than the paper sketch in the design note: `∃x` is pushed *inside* the `□` at
`v` (`K_box` on `ex_intro`), which makes `□∃x.χ(x)` a closed formula, so it crosses the arrow
unchanged (`WFF.subst_mono_empty`). No quantifier over `□A` is needed, and the arrow's translation
plays no part: the finite pieces need only accessibility on closed formulas.

1. At `v`: `□χ(s)` gives `□∃x.χ(x)`.
2. At `w`: `◇□∃x.χ(x)` — otherwise `□¬□∃x.χ(x)` would cross the arrow to `¬□∃x.χ(x)` at `v`.
3. Weak B: `∃x.χ(x)` at `w`.
4. The Henkin witness of that `∃` is `t`.
-/

namespace V12M

variable [ModalSys]

namespace Canon

variable {σ : Signature} {N₀ : ℕ}

omit [ModalSys] in
theorem Ctx.empty_le (Γ : Ctx) : Ctx.empty.Le Γ := fun _ _ h => nomatch h

theorem Ctx.ref_empty (v : VarSymb) : Ctx.empty.ref v = none :=
  Ctx.ref_none_of_rootFresh (fun _ _ => rfl) v rfl

/-- ⭐Substitution fixes closed formulas: a formula of the empty context, weakened into the source,
    comes out as the same formula weakened into the target. -/
theorem WFF.subst_mono_empty {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d : ℕ}
    (h : Ctx.empty.Le Γ) (h' : Ctx.empty.Le Δ) (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d)
    (φ : WFF σ Ctx.empty d) :
    WFF.subst ι θ hθ hc hΓ hΔ (WFF.mono h φ) = WFF.mono h' φ := by
  have hE : Ctx.empty.SlotsFrom d := fun _ _ _ _ => rfl
  have e := WFF.subst_mono_eq h h' (Subst.idS σ Ctx.empty) Subst.ok_idS Subst.coh_idS θ hθ hc
    hE hΓ hE hΔ (fun v _ hv => by rw [Ctx.ref_empty] at hv; cases hv) φ
  rw [WFF.subst_id] at e
  exact e

/-- ⭐**The finite-piece lemma, closed form.** If every closed formula necessary at `w` holds at `v`
    — accessibility seen through closed formulas only — then whatever `v` says necessarily of one of
    its `□`-view terms, by a formula closed apart from its hole, is realised at `w` by a term of
    `w`, provided `w`'s theory is closed under weak B for closed formulas.

    No translation appears: the only formula that has to cross from `w` to `v` is `□¬□∃x.χ(x)`,
    which is closed. So the finite pieces of a back-type are *propositional* information; a
    translation is needed only to realise a whole type at once. -/
theorem finite_piece_closed (w v : World σ N₀) {i j : ℕ × ℕ}
    (hB : ∀ ψ : WFF σ Ctx.empty 0,
      (⟨i, (WFF.box (WFF.box (WFF.mono (Ctx.empty_le _) ψ)).neg).neg⟩ :
        w.L.sys.Sentence σ) ∈ w.T →
      (⟨i, WFF.mono (Ctx.empty_le _) ψ⟩ : w.L.sys.Sentence σ) ∈ w.T)
    (htr : ∀ ψ : WFF σ Ctx.empty 0,
      (⟨i, .box (WFF.mono (Ctx.empty_le _) ψ)⟩ : w.L.sys.Sentence σ) ∈ w.T →
      (⟨j, WFF.mono (Ctx.empty_le _) ψ⟩ : v.L.sys.Sentence σ) ∈ v.T)
    {A : VarType} (χ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1)
    {a : Ann A} (s : Term σ (v.L.ctx j).boxIn A a)
    (hs : (⟨j, .box (WFF.instantiate Ctx.NoSlots.slots s
      (WFF.mono ((Ctx.empty_le _).insert (.bnd 0) A) χ))⟩ : v.L.sys.Sentence σ) ∈ v.T) :
    ∃ (i' : ℕ × ℕ) (_ : i ≤ i') (b : Ann A) (t : Term σ (w.L.ctx i') A b),
      (⟨i', WFF.instantiate Ctx.NoSlots.slots t
        (WFF.mono ((Ctx.empty_le _).insert (.bnd 0) A) χ)⟩ : w.L.sys.Sentence σ) ∈ w.T := by
  -- 1. At `v`, `∃x` goes inside the `□`: `□∃x.χ(x)`, a closed formula.
  have h1 : (⟨j, .box (WFF.mono (Ctx.empty_le _) (.ex A χ))⟩ : v.L.sys.Sentence σ) ∈ v.T :=
    World.mem_of_provable (Δ := [.box (WFF.instantiate Ctx.NoSlots.slots s
        (WFF.mono ((Ctx.empty_le _).insert (.bnd 0) A) χ))])
      (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hs)
      ⟨Proof.K_box (Δ := [WFF.instantiate Ctx.NoSlots.slots s
        (WFF.mono ((Ctx.empty_le _).insert (.bnd 0) A) χ)])
        (Proof.ex_intro A s (Proof.lookup List.mem_cons_self))⟩
  -- 2. At `w`, `◇□∃x.χ(x)`: otherwise `□¬□∃x.χ(x)`, and its body, closed, holds at `v`.
  have h2 : (⟨i, (WFF.box (WFF.box (WFF.mono (Ctx.empty_le _) (.ex A χ))).neg).neg⟩ :
      w.L.sys.Sentence σ) ∈ w.T := by
    by_contra hnot
    have hX : (⟨i, WFF.box (WFF.box (WFF.mono (Ctx.empty_le _) (.ex A χ))).neg⟩ :
        w.L.sys.Sentence σ) ∈ w.T := by
      by_contra hX
      exact hnot (w.mcs.neg_mem_iff.mpr hX)
    -- The body `¬□∃x.χ(x)`, as a closed formula.
    have hv := htr (WFF.box (WFF.mono (Ctx.empty_le _) (.ex A χ))).neg (by
      change (⟨i, WFF.box (WFF.box (WFF.mono _ (WFF.mono _ (.ex A χ)))).neg⟩ :
        w.L.sys.Sentence σ) ∈ w.T
      rw [WFF.mono_mono]
      exact hX)
    change (⟨j, (WFF.box (WFF.mono _ (WFF.mono _ (.ex A χ)))).neg⟩ :
      v.L.sys.Sentence σ) ∈ v.T at hv
    rw [WFF.mono_mono] at hv
    exact v.mcs.neg_mem_iff.mp hv h1
  -- 3. Weak B, and 4. the Henkin witness of the `∃`.
  obtain ⟨i', hi, b, t, hmem⟩ := w.exW (hB _ h2)
  rw [WFF.mono_mono] at hmem
  exact ⟨i', hi, b, t, hmem⟩

/-- ⭐**The finite-piece lemma along an arrow** `θ : w → v` — a substitution from `w`'s `□` view
    into `v`'s context with necessity transfer. An arrow gives closed-formula transfer, since
    substitution fixes closed formulas (`WFF.subst_mono_empty`); so this is
    `finite_piece_closed`. -/
theorem finite_piece (w v : World σ N₀) {i j : ℕ × ℕ}
    (hB : ∀ ψ : WFF σ Ctx.empty 0,
      (⟨i, (WFF.box (WFF.box (WFF.mono (Ctx.empty_le _) ψ)).neg).neg⟩ :
        w.L.sys.Sentence σ) ∈ w.T →
      (⟨i, WFF.mono (Ctx.empty_le _) ψ⟩ : w.L.sys.Sentence σ) ∈ w.T)
    {ι : VarSymb → VarSymb} (θ : Subst σ (v.L.ctx j)) (hθ : Subst.Ok (w.L.ctx i).boxIn θ)
    (hc : Subst.Coh ι (w.L.ctx i).boxIn θ)
    (htr : ∀ ψ : WFF σ (w.L.ctx i).boxIn 0, (⟨i, .box ψ⟩ : w.L.sys.Sentence σ) ∈ w.T →
      (⟨j, WFF.subst ι θ hθ hc Ctx.NoSlots.slots Ctx.NoSlots.slots ψ⟩ :
        v.L.sys.Sentence σ) ∈ v.T)
    {A : VarType} (χ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1)
    {a : Ann A} (s : Term σ (v.L.ctx j).boxIn A a)
    (hs : (⟨j, .box (WFF.instantiate Ctx.NoSlots.slots s
      (WFF.mono ((Ctx.empty_le _).insert (.bnd 0) A) χ))⟩ : v.L.sys.Sentence σ) ∈ v.T) :
    ∃ (i' : ℕ × ℕ) (_ : i ≤ i') (b : Ann A) (t : Term σ (w.L.ctx i') A b),
      (⟨i', WFF.instantiate Ctx.NoSlots.slots t
        (WFF.mono ((Ctx.empty_le _).insert (.bnd 0) A) χ)⟩ : w.L.sys.Sentence σ) ∈ w.T :=
  finite_piece_closed w v hB (fun ψ h => by
    have hv := htr _ h
    rw [WFF.subst_mono_empty _ (Ctx.empty_le _)] at hv
    exact hv) χ s hs

/-- `χ(s)` for a formula `χ` closed apart from one hole: `s` plugged into the hole, `χ` weakened
    into the context of `s`. -/
abbrev WFF.fill1 {Γ : Ctx} [Γ.NoSlots] {B : VarType} {b : Ann B} (s : Term σ Γ B b)
    (χ : WFF σ (Ctx.empty.insert (.bnd 0) B) 1) : WFF σ Γ 0 :=
  WFF.instantiate Ctx.NoSlots.slots s (WFF.mono ((Ctx.empty_le _).insert (.bnd 0) B) χ)

/-- `t` **realises the complete back-type** of `v`'s `□`-view term `s`: every formula closed apart
    from its hole that `v` necessitates of `s` holds of `t` at `w`. This is the invariant of the
    back-and-forth construction (`docs/v12-arrow-canonical.md` §6). -/
def RealisesBackType (w v : World σ N₀) (i j : ℕ × ℕ) {B : VarType} {b b' : Ann B}
    (t : Term σ (w.L.ctx i) B b) (s : Term σ (v.L.ctx j).boxIn B b') : Prop :=
  ∀ χ : WFF σ (Ctx.empty.insert (.bnd 0) B) 1,
    (⟨j, .box (WFF.fill1 s χ)⟩ : v.L.sys.Sentence σ) ∈ v.T →
    (⟨i, WFF.fill1 t χ⟩ : w.L.sys.Sentence σ) ∈ w.T

/-- ⭐**Back-types extend over fixed realisers.** Suppose `t` realises the complete back-type of
    `s` (`RealisesBackType`), and `v` necessitates `χ(s, s')` of `s` and a further term `s'`. Then
    `∃y. χ(t, y)` holds at `w`: a realiser for `s'` compatible with the one already fixed for `s`
    exists, and by `World.exW` some term of `w` is one.

    This is the step of the back-and-forth construction that seemed to need a way of referring to
    "back at the origin". It does not: `∃`-introduction inside the `□` at `v` turns `□χ(s, s')` into
    `□∃y. χ(s, y)`, a formula about `s` alone, which the realisation hypothesis already covers.
    Weak B is not used here; it enters only through the base case, `finite_piece_closed`.

    `χ` has two holes, `bnd 0 : B` for the fixed item and `bnd 1 : A` for the new one, so
    `∃y. χ(x, y)` is just `.ex A χ`. The joint formula `χ(s, s')` is given as `Φ` with `s'` in its
    hole, where `Φ` is the body of `(∃y. χ)(s)` (`hΦ`, which holds by `rfl` for the body). -/
theorem backType_extend (w v : World σ N₀) {i j : ℕ × ℕ} {A B : VarType} {b b' : Ann B}
    (t : Term σ (w.L.ctx i) B b) (s : Term σ (v.L.ctx j).boxIn B b')
    (hR : RealisesBackType w v i j t s)
    (χ : WFF σ ((Ctx.empty.insert (.bnd 0) B).insert (.bnd 1) A) 2)
    (Φ : WFF σ ((v.L.ctx j).boxIn.insert (.bnd 0) A) 1)
    (hΦ : WFF.fill1 s (.ex A χ) = .ex A Φ)
    {a : Ann A} (s' : Term σ (v.L.ctx j).boxIn A a)
    (hs : (⟨j, .box (WFF.instantiate Ctx.NoSlots.slots s' Φ)⟩ : v.L.sys.Sentence σ) ∈ v.T) :
    (⟨i, WFF.fill1 t (.ex A χ)⟩ : w.L.sys.Sentence σ) ∈ w.T := by
  refine hR (.ex A χ) ?_
  rw [hΦ]
  exact World.mem_of_provable (Δ := [.box (WFF.instantiate Ctx.NoSlots.slots s' Φ)])
    (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hs)
    ⟨Proof.K_box (Δ := [WFF.instantiate Ctx.NoSlots.slots s' Φ])
      (Proof.ex_intro A s' (Proof.lookup List.mem_cons_self))⟩

/-- `hΦ` is satisfiable: the body of `(∃y. χ)(s)` is what substitution produces. -/
example (v : World σ N₀) {j : ℕ × ℕ} {A B : VarType} {b' : Ann B}
    (s : Term σ (v.L.ctx j).boxIn B b')
    (χ : WFF σ ((Ctx.empty.insert (.bnd 0) B).insert (.bnd 1) A) 2) :
    ∃ Φ, WFF.fill1 s (.ex A χ) = .ex A Φ := ⟨_, rfl⟩

end Canon

end V12M
