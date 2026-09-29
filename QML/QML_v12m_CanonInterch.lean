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

/-! ## The extent of a `◇`-term, read off its class

`Canon.extent` is keyed to an **address**, and that is what fails once the theory can co-name one
content over two witnesses: the two atoms force the two objects to be *equal elements*, so their
extents must be equal *as sets*, which address-keyed extents never are (§10.9).  Keying the extent
to the term's interchangeability class fixes it, and — the point §10.9 missed — it fixes it without
asking anything of the other objects over those witnesses: a term the theory says nothing about has
a singleton class, hence exactly the arrows it has today, so nothing needs its body read at another
witness's child (§10.10).
-/

/-- ⭐The extent of a `◇`-**term**: the proper arrows are the children built for the witness of *any*
    member of its interchangeability class, and the world itself is there when a member's witness is
    realised.  At a term the theory says nothing about, that is `Canon.extent` at its witness
    (`extent_subset_extentTm`); at co-named terms it is one and the same set (`extentTm_congr`),
    which is what the `here` atoms demand. -/
def extentTm (w : World σ N₀) {A : VarType} {i : ℕ × ℕ} {a : Ann (.VTypeDia A)}
    (s : Term σ (w.L.ctx i) (.VTypeDia A) a) : Set (Succ w) :=
  {w' |
    (w'.1.depth = w.depth + 1 ∧ ∃ (z : VarSymb) (hz : ∃ X, (w.L.ctx i).ref z = some (.VTypeDia X))
        (β : Ann A) (b : Term σ ((w.L.ctx i).diaIn z) A β),
        Interch w s (Term.diatm z hz b) ∧ DiaView z w w'.1 ∧ BoxxContents z w w'.1) ∨
    (w'.1 = w ∧ ∃ (z : VarSymb) (hz : ∃ X, (w.L.ctx i).ref z = some (.VTypeDia X))
        (β : Ann A) (b : Term σ ((w.L.ctx i).diaIn z) A β),
        Interch w s (Term.diatm z hz b) ∧ w.Realised z)}

/-- ⭐**Interchangeable terms have the same extent** — by transitivity of the relation, since the
    clauses quantify over the class.  This is the property the `here` atoms need: two names of one
    content denote objects whose first components agree *as sets*. -/
theorem extentTm_congr {w : World σ N₀} {A : VarType} {i : ℕ × ℕ} {a a' : Ann (.VTypeDia A)}
    {s : Term σ (w.L.ctx i) (.VTypeDia A) a} {s' : Term σ (w.L.ctx i) (.VTypeDia A) a'}
    (h : Interch w s s') : extentTm w s = extentTm w s' := by
  have key : ∀ {b b' : Ann (.VTypeDia A)} {u : Term σ (w.L.ctx i) (.VTypeDia A) b}
      {u' : Term σ (w.L.ctx i) (.VTypeDia A) b'}, Interch w u u' →
      extentTm w u ⊆ extentTm w u' := by
    intro b b' u u' hu w' hw'
    rcases hw' with ⟨hd, z, hz, β, bb, hi, hv, hb⟩ | ⟨he, z, hz, β, bb, hi, hr⟩
    · exact Or.inl ⟨hd, z, hz, β, bb, (hu.symm).trans hi, hv, hb⟩
    · exact Or.inr ⟨he, z, hz, β, bb, (hu.symm).trans hi, hr⟩
  exact Set.Subset.antisymm (key h) (key h.symm)

/-- A term's own witness contributes its arrows: `Canon.extent` at the witness is contained in the
    class-keyed extent, by reflexivity of the relation. -/
theorem extent_subset_extentTm {w : World σ N₀} {A : VarType} {i : ℕ × ℕ} {z : VarSymb}
    (hz : ∃ X, (w.L.ctx i).ref z = some (.VTypeDia X)) {β : Ann A}
    (b : Term σ ((w.L.ctx i).diaIn z) A β) :
    extent w z ⊆ extentTm w (Term.diatm z hz b) := by
  intro w' hw'
  rcases hw' with ⟨hd, hv, hb⟩ | ⟨he, hr⟩
  · exact Or.inl ⟨hd, z, hz, β, b, Interch.refl _, hv, hb⟩
  · exact Or.inr ⟨he, z, hz, β, b, Interch.refl _, hr⟩

/-- A member of the class-keyed extent is the world itself or one level deeper, as for
    `Canon.extent_cases`. -/
theorem extentTm_cases {w : World σ N₀} {A : VarType} {i : ℕ × ℕ} {a : Ann (.VTypeDia A)}
    {s : Term σ (w.L.ctx i) (.VTypeDia A) a} {w' : Succ w} (hw' : w' ∈ extentTm w s) :
    (w'.1.depth - w.depth = 1 ∧ ∃ (z : VarSymb)
        (hz : ∃ X, (w.L.ctx i).ref z = some (.VTypeDia X)) (β : Ann A)
        (b : Term σ ((w.L.ctx i).diaIn z) A β),
        Interch w s (Term.diatm z hz b) ∧ DiaView z w w'.1 ∧ BoxxContents z w w'.1) ∨
      (w'.1.depth - w.depth = 0 ∧ w'.1 = w ∧ ∃ (z : VarSymb)
        (hz : ∃ X, (w.L.ctx i).ref z = some (.VTypeDia X)) (β : Ann A)
        (b : Term σ ((w.L.ctx i).diaIn z) A β),
        Interch w s (Term.diatm z hz b) ∧ w.Realised z) := by
  rcases hw' with ⟨hd, hrest⟩ | ⟨he, hrest⟩
  · exact Or.inl ⟨by omega, hrest⟩
  · exact Or.inr ⟨by rw [he]; omega, he, hrest⟩

end Canon

end V12M
