import QML.QML_v12m_CanonWorld

/-!
# QML v12m — interchangeable terms

The canonical model's `Ind` (docs §10.33) is read off what the theory can *distinguish*: two
terms are related when no formula tells them apart.  At a `◇`-free type this is provable
equality; at a `◇` type it is strictly weaker, because terms over different witnesses are never
equal yet may be co-named.  Two names for one content may stand over different
witnesses, and no formula equates them — `WFF.eqRec` compares terms at one annotation, which at a
`◇` type means one witness (§10.3).  What the theory does give is **indiscernibility**: substituting
one for the other preserves membership, which is exactly `Proof.here_subst`'s conclusion.

* ⭐`Canon.Interch`: two `◇`-terms are interchangeable at a stage when every formula with a slot
  of their type has the same status at both.  An equivalence, trivially.
* ⭐`Canon.interch_of_coname`: **co-naming implies it** — if the theory says both are the content
  of one address here, they are interchangeable.  This is the only way the relation is ever
  established, and it is the pairing principle in force: the two possibilities are linked by the
  address whose content they both are (§10.10).

The relation is stated at every type, since `Here`'s content may have any type.  It is made
stage-free (`DTerm.Rel`) so that it can be read off denotations computed at any stage.
-/

namespace V12M

namespace Canon

variable [ModalSys] {σ : Signature} {N₀ : ℕ}

/-- ⭐**Interchangeability**: every formula with a slot of the two terms' type has the same status at
    both.  Stated at one stage and one content type — the type must agree for the slot to exist, and
    the annotations need not, which is the whole point: `s` and `s'` may stand over different
    witnesses.  Contrast `WFF.eqRec`, which compares within one annotation, so within one fibre. -/
def Interch (w : World σ N₀) {A : VarType} {i : ℕ × ℕ} {a a' : Ann A}
    (s : Term σ (w.L.ctx i) A a) (s' : Term σ (w.L.ctx i) A a') : Prop :=
  ∀ φ : WFF σ ((w.L.ctx i).insert (.bnd 0) A) 1,
    (⟨i, WFF.instantiate Ctx.NoSlots.slots s φ⟩ : w.L.sys.Sentence σ) ∈ w.T ↔
      (⟨i, WFF.instantiate Ctx.NoSlots.slots s' φ⟩ : w.L.sys.Sentence σ) ∈ w.T

namespace Interch

variable {w : World σ N₀} {A : VarType} {i : ℕ × ℕ}

theorem refl {a : Ann A} (s : Term σ (w.L.ctx i) A a) :
    Interch w s s := fun _ => Iff.rfl

theorem symm {a a' : Ann A} {s : Term σ (w.L.ctx i) A a}
    {s' : Term σ (w.L.ctx i) A a'} (h : Interch w s s') : Interch w s' s :=
  fun φ => (h φ).symm

theorem trans {a a' a'' : Ann A} {s : Term σ (w.L.ctx i) A a}
    {s' : Term σ (w.L.ctx i) A a'} {s'' : Term σ (w.L.ctx i) A a''}
    (h : Interch w s s') (h' : Interch w s' s'') : Interch w s s'' :=
  fun φ => (h φ).trans (h' φ)

end Interch

/-- ⭐**Co-naming implies interchangeability**: if the theory says `s` and `s'` are both the
    content of the possible object `p` here, then substituting one for the other preserves
    membership.  This is `Proof.here_subst` under the theory's closure, and it is how the relation
    is established at a `◇` type — the two possibilities are joined by `p`, which is what §2d asks
    for before they may be compared. -/
theorem interch_of_coname {w : World σ N₀} (hT : ModalSys.T = true) {A : VarType} {i : ℕ × ℕ}
    {b : Ann A} {s : Term σ (w.L.ctx i) A b} {b' : Ann A} {s' : Term σ (w.L.ctx i) A b'}
    {c : Ann (.VTypeDia A)} (p : Term σ (w.L.ctx i) (.VTypeDia A) c)
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
    (h : Interch w (A := .VTypeDia A) (Term.diatm y hy bd) (Term.diatm z hz b))
    (ψ : WFF σ ((w.L.ctx i).boxIn.insert (.bnd 0) A) 1) :
    (⟨i, WFF.dia y hy (WFF.viewReadTm bd ψ)⟩ : w.L.sys.Sentence σ) ∈ w.T ↔
      (⟨i, WFF.dia z hz (WFF.viewReadTm b ψ)⟩ : w.L.sys.Sentence σ) ∈ w.T := by
  have key := h (WFF.diaSlot ψ)
  rwa [WFF.instantiate_diaSlot, WFF.instantiate_diaSlot] at key

/-- **Interchangeability is contravariant in the stage**: a later stage has more test formulas, so
    terms interchangeable when lifted are interchangeable below.  `World.mem_lift` carries
    membership between the stages and `WFF.mono_instantiate` carries the test formula up. -/
theorem Interch.of_lift {w : World σ N₀} {A : VarType} {i j : ℕ × ℕ} (hij : i ≤ j)
    {a a' : Ann A} {s : Term σ (w.L.ctx i) A a} {s' : Term σ (w.L.ctx i) A a'}
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
to be stage-free.  A term is taken together with its stage (`DTerm`), and two are related when
they are interchangeable at **every** stage both reach (`DTerm.Rel`).  By contravariance that is
the same as at every sufficiently large stage, which is what makes it transitive, and it makes a
term and its lift one class (`DTerm.rel_lift`) — §10.20. -/

/-- A term of type `A`, together with the stage of `w`'s language it is written at. -/
structure DTerm (w : World σ N₀) (A : VarType) where
  i : ℕ × ℕ
  a : Ann A
  t : Term σ (w.L.ctx i) A a

namespace DTerm

variable {w : World σ N₀} {A : VarType}

/-- The term at a later stage. -/
abbrev lift (s : DTerm w A) (j : ℕ × ℕ) (h : s.i ≤ j) : Term σ (w.L.ctx j) A s.a :=
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
theorem rel_of_coname (hT : ModalSys.T = true) {i : ℕ × ℕ} {b b' : Ann A}
    {s : Term σ (w.L.ctx i) A b} {s' : Term σ (w.L.ctx i) A b'}
    {c : Ann (.VTypeDia A)} (p : Term σ (w.L.ctx i) (.VTypeDia A) c)
    (h : (⟨i, WFF.here hT p s⟩ : w.L.sys.Sentence σ) ∈ w.T)
    (h' : (⟨i, WFF.here hT p s'⟩ : w.L.sys.Sentence σ) ∈ w.T) :
    Rel (⟨i, b, s⟩ : DTerm w A) ⟨i, b', s'⟩ := fun _ hj _ =>
  interch_of_coname hT (Term.mono (w.L.ctx_le hj) p)
    ((World.mem_lift hj).mp h) ((World.mem_lift hj).mp h')

end DTerm


end Canon

end V12M
