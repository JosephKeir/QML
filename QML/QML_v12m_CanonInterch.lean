import QML.QML_v12m_CanonWorld

/-!
# QML v12m — interchangeable `◇`-terms (strong T, `◇`-typed contents)

The canonical model's `◇`-objects have to be indexed by what the theory can *distinguish*, not by
the witness a term happens to be written over.  Two names for one content may stand over different
witnesses, and no formula equates them — `WFF.eqRec` compares terms at one annotation, which at a
`◇` type means one witness (§10.3).  What the theory does give is **indiscernibility**: substituting
one for the other preserves membership, which is exactly `Proof.here_subst`'s conclusion.

* ⭐`Canon.Interch`: two `◇`-terms are interchangeable at a stage when every formula with a slot
  of their type has the same status at both.  An equivalence, trivially.
* ⭐`Canon.interch_of_coname`: **co-naming implies it** — if the theory says both are the content
  of one address here, they are interchangeable.  This is the only way the relation is ever
  established, and it is the pairing principle in force: the two possibilities are linked by the
  address whose content they both are (§10.10).

The canonical `◇`-object of a term is then its interchangeability class: the extent is the union of
the members' own witnesses' children and the content at an arrow is read from the member that
contributed it (§10.10, §10.17).  That construction is `QML_v12m_CanonDom`'s; this file is only the
relation.
-/

namespace V12M

namespace Canon

variable [ModalSys] {σ : Signature} {N₀ : ℕ}

/-- ⭐**Interchangeability**: every formula with a slot of the two terms' type has the same status at
    both.  Stated at one stage and one content type — the type must agree for the slot to exist, and
    the annotations need not, which is the whole point: `s` and `s'` may stand over different
    witnesses.  Contrast `WFF.eqRec`, which compares within one annotation, so within one fibre. -/
def Interch (w : World σ N₀) {A : VarType} {i : ℕ × ℕ} {a a' : Ann (.VTypeDia A)}
    (s : Term σ (w.L.ctx i) (.VTypeDia A) a) (s' : Term σ (w.L.ctx i) (.VTypeDia A) a') : Prop :=
  ∀ φ : WFF σ ((w.L.ctx i).insert (.bnd 0) (.VTypeDia A)) 1,
    (⟨i, WFF.instantiate Ctx.NoSlots.slots s φ⟩ : w.L.sys.Sentence σ) ∈ w.T ↔
      (⟨i, WFF.instantiate Ctx.NoSlots.slots s' φ⟩ : w.L.sys.Sentence σ) ∈ w.T

namespace Interch

variable {w : World σ N₀} {A : VarType} {i : ℕ × ℕ}

theorem refl {a : Ann (.VTypeDia A)} (s : Term σ (w.L.ctx i) (.VTypeDia A) a) :
    Interch w s s := fun _ => Iff.rfl

theorem symm {a a' : Ann (.VTypeDia A)} {s : Term σ (w.L.ctx i) (.VTypeDia A) a}
    {s' : Term σ (w.L.ctx i) (.VTypeDia A) a'} (h : Interch w s s') : Interch w s' s :=
  fun φ => (h φ).symm

theorem trans {a a' a'' : Ann (.VTypeDia A)} {s : Term σ (w.L.ctx i) (.VTypeDia A) a}
    {s' : Term σ (w.L.ctx i) (.VTypeDia A) a'} {s'' : Term σ (w.L.ctx i) (.VTypeDia A) a''}
    (h : Interch w s s') (h' : Interch w s' s'') : Interch w s s'' :=
  fun φ => (h φ).trans (h' φ)

end Interch

/-- ⭐**Co-naming implies interchangeability**: if the theory says the possible objects `s` and `s'`
    are both the content of `p` here, then substituting one for the other preserves membership.
    This is `Proof.here_subst` under the theory's closure, and it is the only source of the
    relation — the two possibilities are joined by `p`, which is what §2d asks for before they may
    be compared. -/
theorem interch_of_coname {w : World σ N₀} (hT : ModalSys.T = true) {A : VarType} {i : ℕ × ℕ}
    {b : Ann (.VTypeDia A)} {s : Term σ (w.L.ctx i) (.VTypeDia A) b}
    {b' : Ann (.VTypeDia A)} {s' : Term σ (w.L.ctx i) (.VTypeDia A) b'}
    {c : Ann (.VTypeDia (.VTypeDia A))} (p : Term σ (w.L.ctx i) (.VTypeDia (.VTypeDia A)) c)
    (h : (⟨i, WFF.here hT p s⟩ : w.L.sys.Sentence σ) ∈ w.T)
    (h' : (⟨i, WFF.here hT p s'⟩ : w.L.sys.Sentence σ) ∈ w.T) :
    Interch w s s' := by
  intro φ
  constructor
  · intro hmem
    exact World.mem_of_provable
      (Δ := [WFF.here hT p s, WFF.here hT p s', WFF.instantiate Ctx.NoSlots.slots s φ])
      (fun ψ hψ => by
        rcases List.mem_cons.mp hψ with rfl | hψ₁
        · exact h
        rcases List.mem_cons.mp hψ₁ with rfl | hψ₂
        · exact h'
        · rw [List.mem_singleton.mp hψ₂]
          exact hmem)
      ⟨Proof.here_subst hT p s s' φ (Proof.lookup List.mem_cons_self)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
        (Proof.lookup (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
  · intro hmem
    exact World.mem_of_provable
      (Δ := [WFF.here hT p s', WFF.here hT p s, WFF.instantiate Ctx.NoSlots.slots s' φ])
      (fun ψ hψ => by
        rcases List.mem_cons.mp hψ with rfl | hψ₁
        · exact h'
        rcases List.mem_cons.mp hψ₁ with rfl | hψ₂
        · exact h
        · rw [List.mem_singleton.mp hψ₂]
          exact hmem)
      ⟨Proof.here_subst hT p s' s φ (Proof.lookup List.mem_cons_self)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
        (Proof.lookup (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩

/-- ⭐**Interchangeable terms have the same `◇`-facts.**  The transfer the truth lemma's `dia` case
    needs when an arrow of a class-keyed extent was contributed by another member: read
    interchangeability at the test formula `WFF.diaSlot ψ`, whose instances are the two `◇`-facts
    (`WFF.instantiate_diaSlot`). -/
theorem Interch.dia_iff {w : World σ N₀} {A : VarType} {i : ℕ × ℕ} {y z : VarSymb}
    (hy : ∃ X, (w.L.ctx i).ref y = some (.VTypeDia X))
    (hz : ∃ X, (w.L.ctx i).ref z = some (.VTypeDia X)) {β β' : Ann A}
    {bd : Term σ ((w.L.ctx i).diaIn y) A β} {b : Term σ ((w.L.ctx i).diaIn z) A β'}
    (h : Interch w (Term.diatm y hy bd) (Term.diatm z hz b))
    (ψ : WFF σ ((w.L.ctx i).boxIn.insert (.bnd 0) A) 1) :
    (⟨i, WFF.dia y hy (WFF.viewReadTm bd ψ)⟩ : w.L.sys.Sentence σ) ∈ w.T ↔
      (⟨i, WFF.dia z hz (WFF.viewReadTm b ψ)⟩ : w.L.sys.Sentence σ) ∈ w.T := by
  have key := h (WFF.diaSlot ψ)
  rwa [WFF.instantiate_diaSlot, WFF.instantiate_diaSlot] at key

/-- **Interchangeability is contravariant in the stage**: a later stage has more test formulas, so
    terms interchangeable when lifted are interchangeable below.  `World.mem_lift` carries
    membership between the stages and `WFF.mono_instantiate` carries the test formula up. -/
theorem Interch.of_lift {w : World σ N₀} {A : VarType} {i j : ℕ × ℕ} (hij : i ≤ j)
    {a a' : Ann (.VTypeDia A)} {s : Term σ (w.L.ctx i) (.VTypeDia A) a}
    {s' : Term σ (w.L.ctx i) (.VTypeDia A) a'}
    (h : Interch w (Term.mono (w.L.ctx_le hij) s) (Term.mono (w.L.ctx_le hij) s')) :
    Interch w s s' := by
  intro φ
  rw [World.mem_lift hij, World.mem_lift hij (φ := WFF.instantiate _ s' φ),
    WFF.mono_instantiate (w.L.ctx_le hij) Ctx.NoSlots.slots Ctx.NoSlots.slots s φ,
    WFF.mono_instantiate (w.L.ctx_le hij) Ctx.NoSlots.slots Ctx.NoSlots.slots s' φ]
  exact h _

/-! ## Stage-free interchangeability

`Interch` compares at one stage, and a later stage has more test formulas, so it is
*contravariant* in the stage (`Interch.of_lift`): a class read at one stage can shrink at a later
one.  `rden` reads a term at any stage and must not depend on which (`rden_mono`), so the class has
to be stage-free.  A `◇`-term is taken together with its stage (`DTerm`), and two are related when
they are interchangeable at **every** stage both reach (`DTerm.Rel`).  By contravariance that is
the same as at every sufficiently large stage, which is what makes it transitive, and it makes a
term and its lift one class (`DTerm.rel_lift`) — §10.20. -/

/-- A `◇`-term of content type `A`, together with the stage of `w`'s language it is written at. -/
structure DTerm (w : World σ N₀) (A : VarType) where
  i : ℕ × ℕ
  a : Ann (.VTypeDia A)
  t : Term σ (w.L.ctx i) (.VTypeDia A) a

namespace DTerm

variable {w : World σ N₀} {A : VarType}

/-- The term at a later stage. -/
abbrev lift (s : DTerm w A) (j : ℕ × ℕ) (h : s.i ≤ j) : Term σ (w.L.ctx j) (.VTypeDia A) s.a :=
  Term.mono (w.L.ctx_le h) s.t

/-- ⭐**Stage-free interchangeability**: interchangeable at every stage both terms reach. -/
def Rel (s s' : DTerm w A) : Prop :=
  ∀ (j : ℕ × ℕ) (h : s.i ≤ j) (h' : s'.i ≤ j), Interch w (s.lift j h) (s'.lift j h')

theorem Rel.refl (s : DTerm w A) : Rel s s := fun _ _ _ => Interch.refl _

theorem Rel.symm {s s' : DTerm w A} (h : Rel s s') : Rel s' s :=
  fun j h₁ h₂ => (h j h₂ h₁).symm

/-- Transitive, by comparing at a stage all three terms reach and descending again
    (`Interch.of_lift`). -/
theorem Rel.trans {s s' s'' : DTerm w A} (h : Rel s s') (h' : Rel s' s'') : Rel s s'' := by
  intro j hj hj''
  have hm : j ≤ j ⊔ s'.i := le_sup_left
  refine Interch.of_lift hm ?_
  rw [Term.mono_mono, Term.mono_mono]
  exact (h _ (hj.trans hm) le_sup_right).trans (h' _ le_sup_right (hj''.trans hm))

/-- ⭐**A term and its lift are one class**, so reading a term at a later stage does not change
    its class: `Term.mono_mono`, then reflexivity. -/
theorem rel_lift (s : DTerm w A) {k : ℕ × ℕ} (hk : s.i ≤ k) : Rel s ⟨k, s.a, s.lift k hk⟩ := by
  intro j h₁ h₂
  change Interch w (Term.mono _ s.t) (Term.mono _ (Term.mono _ s.t))
  rw [Term.mono_mono]
  exact Interch.refl _

/-- ⭐**Co-naming implies stage-free interchangeability**: the two `Here` atoms lift to every later
    stage (`World.mem_lift`), where `interch_of_coname` applies. -/
theorem rel_of_coname (hT : ModalSys.T = true) {i : ℕ × ℕ} {b b' : Ann (.VTypeDia A)}
    {s : Term σ (w.L.ctx i) (.VTypeDia A) b} {s' : Term σ (w.L.ctx i) (.VTypeDia A) b'}
    {c : Ann (.VTypeDia (.VTypeDia A))} (p : Term σ (w.L.ctx i) (.VTypeDia (.VTypeDia A)) c)
    (h : (⟨i, WFF.here hT p s⟩ : w.L.sys.Sentence σ) ∈ w.T)
    (h' : (⟨i, WFF.here hT p s'⟩ : w.L.sys.Sentence σ) ∈ w.T) :
    Rel (⟨i, b, s⟩ : DTerm w A) ⟨i, b', s'⟩ := fun _ hj _ =>
  interch_of_coname hT (Term.mono (w.L.ctx_le hj) p)
    ((World.mem_lift hj).mp h) ((World.mem_lift hj).mp h')

end DTerm

/-! ## The extent of a `◇`-term, read off its class

`Canon.extent` is keyed to an **address**, and that is what fails once the theory can co-name one
content over two witnesses: the two atoms force the two objects to be *equal elements*, so their
extents must be equal *as sets*, which address-keyed extents never are (§10.9).  Keying the extent
to the term's class fixes it, and — the point §10.9 missed — it fixes it without asking anything of
the other objects over those witnesses: a term the theory says nothing about has a singleton class,
hence exactly the arrows it has today, so nothing needs its body read at another witness's child
(§10.10).
-/

/-- ⭐The extent of a `◇`-term, read off its class: the proper arrows are the children built for
    the witness of *any* member of its stage-free class, and the world itself is there when a
    member's witness is realised.  A term the theory says nothing about has a singleton class, so
    this is `Canon.extent` at its witness (`extent_subset_extentTm`); related terms give one and the
    same set (`extentTm_congr`), which is what the `here` atoms demand; and a term and its lift give
    the same set (`extentTm_lift`), which is what `rden_mono` needs. -/
def extentTm (w : World σ N₀) {A : VarType} (s : DTerm w A) : Set (Succ w) :=
  {w' |
    (w'.1.depth = w.depth + 1 ∧ ∃ (j : ℕ × ℕ) (z : VarSymb)
        (hz : ∃ X, (w.L.ctx j).ref z = some (.VTypeDia X)) (β : Ann A)
        (b : Term σ ((w.L.ctx j).diaIn z) A β),
        s.Rel ⟨j, _, Term.diatm z hz b⟩ ∧ DiaView z w w'.1 ∧ BoxxContents z w w'.1) ∨
    (w'.1 = w ∧ ∃ (j : ℕ × ℕ) (z : VarSymb)
        (hz : ∃ X, (w.L.ctx j).ref z = some (.VTypeDia X)) (β : Ann A)
        (b : Term σ ((w.L.ctx j).diaIn z) A β),
        s.Rel ⟨j, _, Term.diatm z hz b⟩ ∧ w.Realised z)}

/-- ⭐**Related terms have the same extent** — by transitivity, since the clauses quantify over the
    class.  This is the property the `here` atoms need: two names of one content denote objects
    whose first components agree *as sets*. -/
theorem extentTm_congr {w : World σ N₀} {A : VarType} {s s' : DTerm w A} (h : s.Rel s') :
    extentTm w s = extentTm w s' := by
  have key : ∀ {u u' : DTerm w A}, u.Rel u' → extentTm w u ⊆ extentTm w u' := by
    intro u u' hu w' hw'
    rcases hw' with ⟨hd, j, z, hz, β, bb, hi, hv, hb⟩ | ⟨he, j, z, hz, β, bb, hi, hr⟩
    · exact Or.inl ⟨hd, j, z, hz, β, bb, hu.symm.trans hi, hv, hb⟩
    · exact Or.inr ⟨he, j, z, hz, β, bb, hu.symm.trans hi, hr⟩
  exact Set.Subset.antisymm (key h) (key h.symm)

/-- ⭐**The extent does not depend on the stage a term is read at** — the property `rden_mono`
    needs, and the reason the class is stage-free. -/
theorem extentTm_lift {w : World σ N₀} {A : VarType} (s : DTerm w A) {k : ℕ × ℕ}
    (hk : s.i ≤ k) : extentTm w ⟨k, s.a, s.lift k hk⟩ = extentTm w s :=
  (extentTm_congr (s.rel_lift hk)).symm

/-- A term's own witness contributes its arrows: `Canon.extent` at the witness is contained in the
    class-keyed extent, by reflexivity. -/
theorem extent_subset_extentTm {w : World σ N₀} {A : VarType} {j : ℕ × ℕ} {z : VarSymb}
    (hz : ∃ X, (w.L.ctx j).ref z = some (.VTypeDia X)) {β : Ann A}
    (b : Term σ ((w.L.ctx j).diaIn z) A β) :
    extent w z ⊆ extentTm w ⟨j, _, Term.diatm z hz b⟩ := by
  intro w' hw'
  rcases hw' with ⟨hd, hv, hb⟩ | ⟨he, hr⟩
  · exact Or.inl ⟨hd, j, z, hz, β, b, DTerm.Rel.refl _, hv, hb⟩
  · exact Or.inr ⟨he, j, z, hz, β, b, DTerm.Rel.refl _, hr⟩

/-- A member of the class-keyed extent is the world itself or one level deeper, as for
    `Canon.extent_cases`. -/
theorem extentTm_cases {w : World σ N₀} {A : VarType} {s : DTerm w A} {w' : Succ w}
    (hw' : w' ∈ extentTm w s) :
    (w'.1.depth - w.depth = 1 ∧ ∃ (j : ℕ × ℕ) (z : VarSymb)
        (hz : ∃ X, (w.L.ctx j).ref z = some (.VTypeDia X)) (β : Ann A)
        (b : Term σ ((w.L.ctx j).diaIn z) A β),
        s.Rel ⟨j, _, Term.diatm z hz b⟩ ∧ DiaView z w w'.1 ∧ BoxxContents z w w'.1) ∨
      (w'.1.depth - w.depth = 0 ∧ w'.1 = w ∧ ∃ (j : ℕ × ℕ) (z : VarSymb)
        (hz : ∃ X, (w.L.ctx j).ref z = some (.VTypeDia X)) (β : Ann A)
        (b : Term σ ((w.L.ctx j).diaIn z) A β),
        s.Rel ⟨j, _, Term.diatm z hz b⟩ ∧ w.Realised z) := by
  rcases hw' with ⟨hd, hrest⟩ | ⟨he, hrest⟩
  · exact Or.inl ⟨by omega, hrest⟩
  · exact Or.inr ⟨by rw [he]; omega, he, hrest⟩

end Canon

end V12M
