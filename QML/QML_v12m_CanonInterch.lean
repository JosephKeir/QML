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

Everything here is about a **staged theory** — a stage system `S` and a set `T` of its sentences,
maximal consistent (`Fact (StageSys.IsMCS T)`) — not about the tree's worlds, so the network model
for B uses it too (docs/v12-arrow-canonical.md §9.3).  A tree world is `w.L.sys` with `w.T`.
-/

namespace V12M

namespace Canon

variable [ModalSys] {σ : Signature} {N₀ : ℕ} {I : Type} [Preorder I]

/-- A tree world's theory is maximal consistent, as an instance for the staged-theory lemmas. -/
instance World.mcsFact (w : World σ N₀) : Fact (StageSys.IsMCS w.T) := ⟨w.mcs⟩

/-- ⭐**Interchangeability**: every formula with a slot of the two terms' type has the same status at
    both.  Stated at one stage and one content type — the type must agree for the slot to exist, and
    the annotations need not, which is the whole point: `s` and `s'` may stand over different
    witnesses.  Contrast `WFF.eqRec`, which compares within one annotation, so within one fibre. -/
def Interch {S : StageSys I} (T : Set (S.Sentence σ)) {A : VarType} {i : I} {a a' : Ann A}
    (s : Term σ (S.ctx i) A a) (s' : Term σ (S.ctx i) A a') : Prop :=
  ∀ φ : WFF σ ((S.ctx i).insert (.bnd 0) A) 1,
    (⟨i, WFF.instantiate Ctx.NoSlots.slots s φ⟩ : S.Sentence σ) ∈ T ↔
      (⟨i, WFF.instantiate Ctx.NoSlots.slots s' φ⟩ : S.Sentence σ) ∈ T

namespace Interch

variable {S : StageSys I} {T : Set (S.Sentence σ)} {A : VarType} {i : I}

theorem refl {a : Ann A} (s : Term σ (S.ctx i) A a) :
    Interch T s s := fun _ => Iff.rfl

theorem symm {a a' : Ann A} {s : Term σ (S.ctx i) A a}
    {s' : Term σ (S.ctx i) A a'} (h : Interch T s s') : Interch T s' s :=
  fun φ => (h φ).symm

theorem trans {a a' a'' : Ann A} {s : Term σ (S.ctx i) A a}
    {s' : Term σ (S.ctx i) A a'} {s'' : Term σ (S.ctx i) A a''}
    (h : Interch T s s') (h' : Interch T s' s'') : Interch T s s'' :=
  fun φ => (h φ).trans (h' φ)

end Interch

section MCS

variable {S : StageSys I} {T : Set (S.Sentence σ)} [hmcs : Fact (StageSys.IsMCS T)]

/-- Membership from a proof at one stage. -/
theorem mem_of_provable' {i : I} {Δ : List (WFF σ (S.ctx i) 0)} {φ : WFF σ (S.ctx i) 0}
    (hΔ : ∀ ψ ∈ Δ, (⟨i, ψ⟩ : S.Sentence σ) ∈ T) (p : Provable Δ φ) :
    (⟨i, φ⟩ : S.Sentence σ) ∈ T :=
  hmcs.out.closed (StageSys.derives_of_mems hΔ p)

/-- ⭐**Co-naming implies interchangeability**: if the theory says `s` and `s'` are both the
    content of the possible object `p` here, then substituting one for the other preserves
    membership.  This is `Proof.here_subst` under the theory's closure, and it is how the relation
    is established at a `◇` type — the two possibilities are joined by `p`, which is what §2d asks
    for before they may be compared. -/
theorem interch_of_coname (hT : ModalSys.T = true) {A : VarType} {i : I}
    {b : Ann A} {s : Term σ (S.ctx i) A b} {b' : Ann A} {s' : Term σ (S.ctx i) A b'}
    {c : Ann (.VTypeDia A)} (p : Term σ (S.ctx i) (.VTypeDia A) c)
    (h : (⟨i, WFF.here hT p s⟩ : S.Sentence σ) ∈ T)
    (h' : (⟨i, WFF.here hT p s'⟩ : S.Sentence σ) ∈ T) :
    Interch T s s' := by
  intro φ
  constructor
  · intro hmem
    exact mem_of_provable'
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
    exact mem_of_provable'
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

end MCS

/-- ⭐**Interchangeable terms have the same `◇`-facts.**  The transfer the truth lemma's `dia` case
    needs when an arrow of a class-keyed extent was contributed by another member: read
    interchangeability at the test formula `WFF.diaSlot ψ`, whose instances are the two `◇`-facts
    (`WFF.instantiate_diaSlot`). -/
theorem Interch.dia_iff {S : StageSys I} {T : Set (S.Sentence σ)} {A : VarType} {i : I}
    {y z : VarSymb} (hy : ∃ X, (S.ctx i).ref y = some (.VTypeDia X))
    (hz : ∃ X, (S.ctx i).ref z = some (.VTypeDia X)) {β β' : Ann A}
    {bd : Term σ ((S.ctx i).diaIn y) A β} {b : Term σ ((S.ctx i).diaIn z) A β'}
    (h : Interch T (A := .VTypeDia A) (Term.diatm y hy bd) (Term.diatm z hz b))
    (ψ : WFF σ ((S.ctx i).boxIn.insert (.bnd 0) A) 1) :
    (⟨i, WFF.dia y hy (WFF.viewReadTm bd ψ)⟩ : S.Sentence σ) ∈ T ↔
      (⟨i, WFF.dia z hz (WFF.viewReadTm b ψ)⟩ : S.Sentence σ) ∈ T := by
  have key := h (WFF.diaSlot ψ)
  rwa [WFF.instantiate_diaSlot, WFF.instantiate_diaSlot] at key

/-- **Interchangeability is contravariant in the stage**: a later stage has more test formulas, so
    terms interchangeable when lifted are interchangeable below.  Maximal consistency carries
    membership between the stages and `WFF.mono_instantiate` carries the test formula up. -/
theorem Interch.of_lift [IsDirected I (· ≤ ·)] {S : StageSys I} {T : Set (S.Sentence σ)}
    [hmcs : Fact (StageSys.IsMCS T)] {A : VarType} {i j : I} (hij : i ≤ j)
    {a a' : Ann A} {s : Term σ (S.ctx i) A a} {s' : Term σ (S.ctx i) A a'}
    (h : Interch T (Term.mono (S.le hij) s) (Term.mono (S.le hij) s')) :
    Interch T s s' := by
  intro φ
  rw [← hmcs.out.mem_lift_iff hij, ← hmcs.out.mem_lift_iff hij (φ := WFF.instantiate _ s' φ)]
  change (⟨j, WFF.mono (S.le hij) _⟩ : S.Sentence σ) ∈ T ↔
    (⟨j, WFF.mono (S.le hij) _⟩ : S.Sentence σ) ∈ T
  rw [WFF.mono_instantiate (S.le hij) Ctx.NoSlots.slots Ctx.NoSlots.slots s φ,
    WFF.mono_instantiate (S.le hij) Ctx.NoSlots.slots Ctx.NoSlots.slots s' φ]
  exact h _

/-! ## Stage-free interchangeability

`Interch` compares at one stage, and a later stage has more test formulas, so it is
*contravariant* in the stage (`Interch.of_lift`): a class read at one stage can shrink at a later
one.  `rden` reads a term at any stage and must not depend on which (`rden_mono`), so the class has
to be stage-free.  A term is taken together with its stage (`DTerm`), and two are related when
they are interchangeable at **every** stage both reach (`DTerm.Rel`).  By contravariance that is
the same as at every sufficiently large stage, which is what makes it transitive, and it makes a
term and its lift one class (`DTerm.rel_lift`) — §10.20. -/

/-- A term of type `A`, together with the stage it is written at.  The theory `T` is a parameter
    only, so that `DTerm.Rel` can read it off the terms' type. -/
structure DTerm (S : StageSys I) (_T : Set (S.Sentence σ)) (A : VarType) where
  i : I
  a : Ann A
  t : Term σ (S.ctx i) A a

namespace DTerm

variable {S : StageSys I} {T : Set (S.Sentence σ)} {A : VarType}

/-- The term at a later stage. -/
abbrev lift (s : DTerm S T A) (j : I) (h : s.i ≤ j) : Term σ (S.ctx j) A s.a :=
  Term.mono (S.le h) s.t

/-- ⭐**Stage-free interchangeability**: interchangeable at every stage both terms reach. -/
def Rel (s s' : DTerm S T A) : Prop :=
  ∀ (j : I) (h : s.i ≤ j) (h' : s'.i ≤ j), Interch T (s.lift j h) (s'.lift j h')

theorem Rel.refl (s : DTerm S T A) : Rel s s := fun _ _ _ => Interch.refl _

theorem Rel.symm {s s' : DTerm S T A} (h : Rel s s') : Rel s' s :=
  fun j h₁ h₂ => (h j h₂ h₁).symm

/-- Transitive, by comparing at a stage all three terms reach and descending again
    (`Interch.of_lift`). -/
theorem Rel.trans [IsDirected I (· ≤ ·)] [Fact (StageSys.IsMCS T)] {s s' s'' : DTerm S T A}
    (h : Rel s s') (h' : Rel s' s'') : Rel s s'' := by
  intro j hj hj''
  obtain ⟨k, hm, hs'⟩ := directed_of (· ≤ ·) j s'.i
  refine Interch.of_lift hm ?_
  rw [Term.mono_mono, Term.mono_mono]
  exact (h _ (hj.trans hm) hs').trans (h' _ hs' (hj''.trans hm))

/-- ⭐**A term and its lift are one class**, so reading a term at a later stage does not change
    its class: `Term.mono_mono`, then reflexivity. -/
theorem rel_lift (s : DTerm S T A) {k : I} (hk : s.i ≤ k) : Rel s ⟨k, s.a, s.lift k hk⟩ := by
  intro j h₁ h₂
  change Interch T (Term.mono _ s.t) (Term.mono _ (Term.mono _ s.t))
  rw [Term.mono_mono]
  exact Interch.refl _

/-- ⭐**Co-naming implies stage-free interchangeability**: the two `Here` atoms lift to every later
    stage, where `interch_of_coname` applies. -/
theorem rel_of_coname [IsDirected I (· ≤ ·)] [hmcs : Fact (StageSys.IsMCS T)]
    (hT : ModalSys.T = true) {i : I} {b b' : Ann A}
    {s : Term σ (S.ctx i) A b} {s' : Term σ (S.ctx i) A b'}
    {c : Ann (.VTypeDia A)} (p : Term σ (S.ctx i) (.VTypeDia A) c)
    (h : (⟨i, WFF.here hT p s⟩ : S.Sentence σ) ∈ T)
    (h' : (⟨i, WFF.here hT p s'⟩ : S.Sentence σ) ∈ T) :
    Rel (⟨i, b, s⟩ : DTerm S T A) ⟨i, b', s'⟩ := fun _ hj _ =>
  interch_of_coname hT (Term.mono (S.le hj) p)
    ((hmcs.out.mem_lift_iff hj).mpr h) ((hmcs.out.mem_lift_iff hj).mpr h')

end DTerm

end Canon

variable [ModalSys]


/-- ⭐**The round trip, for terms**: a term of the `◇_x` view is its abstraction read back with the
    content address's η-expansion in the hole. -/
theorem Term.viewReadTm_eta_diaAbsA {σ : Signature} {Γ : Ctx} [hp : Γ.Presented] (x : VarSymb)
    {A : VarType} (hxA : Γ.ref x = some (.VTypeDia A)) {T : VarType} {b : Ann T}
    (t : Term σ (Γ.diaIn x) T b) :
    (⟨_, Term.viewReadTm (Term.eta (.step x .dia) A (Ctx.ref_diaIn_of hxA))
        (Term.diaAbsA x hxA t)⟩ : Σ c, Term σ (Γ.diaIn x) T c) = ⟨b, t⟩ := by
  unfold Term.viewReadTm
  rw [Term.subst_mono]
  unfold Term.diaAbsA
  refine (Term.subst_comp_sig _ _ (Subst.idS σ (Γ.diaIn x)) _ _ _ _ Subst.ok_idS Subst.coh_idS
    ?_ t).trans ?_
  · refine Subst.sim_of ?_
    intro v T' hlp hv
    rcases Subst.diaIn_casesA (σ := σ) hxA (hp.not_below hxA rfl) hv with
      ⟨rfl, rfl⟩ | ⟨_, _, hen, hroot⟩
    · change SubE.Sim _ (.ren (.step x .dia))
        ((if x = x then SubE.ren (.root (.bnd 0)) else .hide).comp _ _ _)
      rw [if_pos rfl]
      change SubE.Sim _ (.ren (.step x .dia))
        (if (VarSymb.root (Root.bnd 0)) = .root (.bnd 0) then
          SubE.tm (Term.eta (.step x .dia) T' (Ctx.ref_diaIn_of hxA))
        else .ren (.root (.bnd 0)))
      rw [if_pos rfl]
      exact .ren_eta _ _
    · change SubE.Sim _ (.ren v) ((Subst.diaAbsA σ _ x v).comp _ _ _)
      rw [hen _]
      change SubE.Sim _ (.ren v)
        ((Subst.single (σ := σ) (Δ := Γ.diaIn x) (.bnd 0)
          (.tm (Term.eta (.step x .dia) A (Ctx.ref_diaIn_of hxA)))).at v)
      rw [Subst.at_nonproj _ hlp]
      change SubE.Sim _ (.ren v) (if v = .root (.bnd 0) then _ else .ren v)
      rw [if_neg (hroot (.bnd 0))]
      exact .refl _
  · exact (Term.subst_idS_mono (Ctx.Le.refl _) _ _ t).trans
      (congrArg (Sigma.mk _) (Term.mono_refl _ t))
namespace Canon

variable {σ : Signature} {I : Type} [Preorder I]

/-! ## Realisation read off a staged theory -/

/-- Henkin witnessing at a **declared root**, for a staged theory: what naming a `Here` atom's
    content needs.  A tree world has it as `World.exW`; the network's worlds witness with a fresh
    variable too. -/
def RootWitnessed (S : StageSys I) (T : Set (S.Sentence σ)) : Prop :=
  ∀ {i : I} {A : VarType} {ψ : WFF σ ((S.ctx i).insert (.bnd 0) A) 1},
    (⟨i, .ex A ψ⟩ : S.Sentence σ) ∈ T →
    ∃ (i' : I) (hi : i ≤ i') (c : ℕ) (hc : (S.ctx i').ref (.root (.free c)) = some A),
      (⟨i', WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free c)) A hc)
        (WFF.mono ((S.le hi).insert (.bnd 0) A) ψ)⟩ : S.Sentence σ) ∈ T

variable {S : StageSys I} {T : Set (S.Sentence σ)}

/-- ⭐**A `Here` atom about a possible object gives its witness a datum.**  `here_beta` at the unit
    reduces the atom to realisedness, `here_name` names the witness's content, and root witnessing
    declares the name. -/
theorem datum_of_here [Fact (StageSys.IsMCS T)] (hex : RootWitnessed S T)
    (hT : ModalSys.T = true) {x : VarSymb} {i : I} {X : VarType}
    (hx : (S.ctx i).ref x = some (.VTypeDia X)) {B : VarType} {β : Ann B}
    (bd : Term σ ((S.ctx i).diaIn x) B β) {a : Ann B} (t : Term σ (S.ctx i) B a)
    (h : (⟨i, WFF.here hT (Term.diatm x ⟨X, hx⟩ bd) t⟩ : S.Sentence σ) ∈ T) :
    Nonempty (RealDatum σ S T x) := by
  have hex' := mem_of_provable' (T := T) (Δ := [_]) (fun ψ hψ => by
      rw [List.mem_singleton.mp hψ]; exact h)
    ⟨Proof.here_name hT x ⟨X, hx⟩ (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx))
      (Proof.here_beta hT x ⟨X, hx⟩ t bd (Term.unit) (Proof.lookup List.mem_cons_self))⟩
  obtain ⟨i', hi, c, hc, hmem⟩ := hex hex'
  have e : WFF.mono ((S.le hi).insert (.bnd 0) X)
      (WFF.here hT (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := S.ctx i)).root X)
          (Term.eta x (.VTypeDia X) hx))
        (Term.eta (.root (.bnd 0)) X (Ctx.ref_insert_root _ (.bnd 0) X)) : WFF σ _ 1) =
      WFF.here hT (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := S.ctx i')).root X)
          (Term.eta x (.VTypeDia X) ((S.le hi).ref hx)))
        (Term.eta (.root (.bnd 0)) X (Ctx.ref_insert_root _ (.bnd 0) X)) := by
    change WFF.here hT (Term.mono _ (Term.mono _ (Term.eta x (.VTypeDia X) hx)))
      (Term.mono _ (Term.eta (.root (.bnd 0)) X _)) = _
    rw [Term.mono_mono, Term.mono_eta, Term.mono_eta, Term.mono_eta]
  change (⟨i', WFF.instantiate _ _ (WFF.mono _ (WFF.here hT (Term.mono _
      (Term.eta x (.VTypeDia X) hx)) (Term.eta (.root (.bnd 0)) X _)))⟩ :
    S.Sentence σ) ∈ T at hmem
  rw [e, WFF.instantiate_here_slot] at hmem
  exact ⟨⟨hT, X, i', .root (.free c), hc, (S.le hi).ref hx, hmem⟩⟩

/-- ⭐**A datum's possible object has its realisation as content here**: from the datum's atom
    `Here (η x) t₀`, `here_beta` with the body abstracted, and the round trip — at any stage `k`
    above both the body's and the datum's. -/
theorem mem_here_datum [IsDirected I (· ≤ ·)] [hmcs : Fact (StageSys.IsMCS T)] {x : VarSymb}
    (d : RealDatum σ S T x) {i k : I} (hik : i ≤ k) (hdk : d.i₀ ≤ k) {X : VarType}
    (hx : (S.ctx i).ref x = some (.VTypeDia X)) {B : VarType} {β : Ann B}
    (bd : Term σ ((S.ctx i).diaIn x) B β) :
    (⟨k, WFF.here d.hT (Term.mono (S.le hik) (Term.diatm x ⟨X, hx⟩ bd))
        (Term.realiseAtA d.hT x (d.hdeclOf k ⟨X, (S.le hik).ref hx⟩)
          (Term.mono (S.le hdk) d.t₀) (Term.mono ((S.le hik).diaIn x) bd))⟩ :
      S.Sentence σ) ∈ T := by
  have hdecl : (S.ctx k).ref x = some (.VTypeDia d.A) := d.hdeclOf k ⟨X, (S.le hik).ref hx⟩
  have hat := d.hhereAt hmcs.out k hdk hdecl
  have hmem := mem_of_provable' (T := T) (Δ := [_]) (fun ψ hψ => by
      rw [List.mem_singleton.mp hψ]; exact hat)
    ⟨Proof.here_beta d.hT x ⟨_, hdecl⟩ (Term.mono (S.le hdk) d.t₀)
      (Term.eta (.step x .dia) d.A (Ctx.ref_diaIn_of hdecl))
      (Term.diaAbsA x hdecl (Term.mono ((S.le hik).diaIn x) bd))
      (Proof.lookup List.mem_cons_self)⟩
  rwa [WFF.here_congr d.hT (sig_diatm (Term.viewReadTm_eta_diaAbsA x hdecl _)) rfl] at hmem

end Canon


/-! ## Interchangeability is a congruence (§11.15)

A model proper needs `Ind` preserved by hole terms and by pairing.  The canonical `Ind` is
interchangeability, and that is a congruence for any term over a slot: the test formula for
`X(s)` is the test formula with its slot replaced by `X` (`WFF.bodyRepl`), instantiated at `s`. -/

/-- ⭐**Filling a replaced slot** is filling the original slot with the replacement, filled. -/
theorem WFF.instantiate_bodyRepl {σ : Signature} {V : Ctx} [V.NoSlots] {A B : VarType}
    {b : Ann B} (X : Term σ (V.insert (.bnd 0) A) B b) (φ : WFF σ (V.insert (.bnd 0) B) 1)
    {a : Ann A} (t : Term σ V A a) :
    WFF.instantiate Ctx.NoSlots.slots t (WFF.bodyRepl X φ) =
      WFF.instantiate Ctx.NoSlots.slots (Term.subst (Subst.singleIdx (.bnd 0) (.tm t))
        (Subst.single (.bnd 0) (.tm t)) (Subst.ok_single (Ctx.Le.refl V) rfl)
        (Subst.coh_single ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) (Ctx.Le.refl V)
          rfl) X) φ := by
  unfold WFF.bodyRepl WFF.instantiate WFF.substRoot
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ (Subst.sim_of fun v U hlp hv => ?_) φ
  rw [Subst.comp_apply]
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    rw [Subst.set_root]
    change SubE.Sim U (if (VarSymb.root (.bnd 0)) = .root (.bnd 0) then _ else _) _
    rw [if_pos rfl]
    exact .refl _
  · rw [Subst.set_ne _ _ hvr, show (Subst.idS σ (V.insert (.bnd 0) A) v) = .ren v from rfl,
      SubE.comp_ren, Subst.at_nonproj _ hlp]
    change SubE.Sim U (if v = .root (.bnd 0) then _ else _) (if v = .root (.bnd 0) then _ else _)
    rw [if_neg hvr, if_neg hvr]
    exact .refl _

namespace Canon

variable {σ : Signature} {I : Type} [Preorder I]

namespace Interch

variable {S : StageSys I} {T : Set (S.Sentence σ)} {A : VarType} {i : I}

/-- ⭐**Interchangeable terms stay interchangeable in any term over a slot.** -/
theorem subst_slot {a a' : Ann A} {s : Term σ (S.ctx i) A a} {s' : Term σ (S.ctx i) A a'}
    (h : Interch T s s') {B : VarType} {b : Ann B}
    (X : Term σ ((S.ctx i).insert (.bnd 0) A) B b) :
    Interch T
      (Term.subst (Subst.singleIdx (.bnd 0) (.tm s)) (Subst.single (.bnd 0) (.tm s))
        (Subst.ok_single (Ctx.Le.refl _) rfl)
        (Subst.coh_single ((Ctx.NoSlots.slots (Γ := S.ctx i)).rootFresh (le_refl 0))
          (Ctx.Le.refl _) rfl) X)
      (Term.subst (Subst.singleIdx (.bnd 0) (.tm s')) (Subst.single (.bnd 0) (.tm s'))
        (Subst.ok_single (Ctx.Le.refl _) rfl)
        (Subst.coh_single ((Ctx.NoSlots.slots (Γ := S.ctx i)).rootFresh (le_refl 0))
          (Ctx.Le.refl _) rfl) X) := fun φ => by
  rw [← WFF.instantiate_bodyRepl, ← WFF.instantiate_bodyRepl]
  exact h _

/-- Interchangeability depends on its terms only as dependent pairs. -/
theorem of_sig {a₁ a₂ a₁' a₂' : Ann A} {s₁ : Term σ (S.ctx i) A a₁} {s₂ : Term σ (S.ctx i) A a₂}
    {u₁ : Term σ (S.ctx i) A a₁'} {u₂ : Term σ (S.ctx i) A a₂'}
    (h₁ : (⟨a₁, s₁⟩ : Σ b, Term σ (S.ctx i) A b) = ⟨a₁', u₁⟩)
    (h₂ : (⟨a₂, s₂⟩ : Σ b, Term σ (S.ctx i) A b) = ⟨a₂', u₂⟩) (h : Interch T s₁ s₂) :
    Interch T u₁ u₂ := by
  cases h₁
  cases h₂
  exact h

/-- Under a hole term. -/
theorem holeAt {a a' : Ann A} {s : Term σ (S.ctx i) A a} {s' : Term σ (S.ctx i) A a'}
    (h : Interch T s s') {B : VarType} {b : Ann B} (hh : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    Interch T (Term.holeAt s hh) (Term.holeAt s' hh) := by
  rw [← Term.holeRead_eq_holeAt, ← Term.holeRead_eq_holeAt]
  exact h.subst_slot _

/-- Under pairing. -/
theorem pair {a₁ a₁' : Ann A} {s₁ : Term σ (S.ctx i) A a₁} {s₁' : Term σ (S.ctx i) A a₁'}
    (h₁ : Interch T s₁ s₁') {B : VarType} {b₂ b₂' : Ann B} {s₂ : Term σ (S.ctx i) B b₂}
    {s₂' : Term σ (S.ctx i) B b₂'} (h₂ : Interch T s₂ s₂') :
    Interch T (Term.pair s₁ s₂) (Term.pair s₁' s₂') := by
  have hr := Ctx.NoSlots.slots (Γ := S.ctx i)
  refine trans (s' := Term.pair s₁' s₂) (of_sig ?_ ?_ (h₁.subst_slot (Term.pair
      (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root _ (.bnd 0) A))
      (Term.mono (Ctx.le_insert hr.root A) s₂))))
    (of_sig ?_ ?_ (h₂.subst_slot (Term.pair (Term.mono (Ctx.le_insert hr.root B) s₁')
      (Term.eta (.root (.bnd 0)) B (Ctx.ref_insert_root _ (.bnd 0) B)))))
  · exact sig_pair (Term.subst_eta_tm _ _ _ A _ _ s₁ (Subst.at_single_root _ _))
      (Term.subst_single_mono_sig s₁ s₂)
  · exact sig_pair (Term.subst_eta_tm _ _ _ A _ _ s₁' (Subst.at_single_root _ _))
      (Term.subst_single_mono_sig s₁' s₂)
  · exact sig_pair (Term.subst_single_mono_sig s₂ s₁')
      (Term.subst_eta_tm _ _ _ B _ _ s₂ (Subst.at_single_root _ _))
  · exact sig_pair (Term.subst_single_mono_sig s₂' s₁')
      (Term.subst_eta_tm _ _ _ B _ _ s₂' (Subst.at_single_root _ _))

end Interch

namespace DTerm

variable {S : StageSys I} {T : Set (S.Sentence σ)} {A : VarType}

/-- ⭐Related terms stay related under a hole term. -/
theorem Rel.holeAt {s s' : DTerm S T A} (h : s.Rel s') {B : VarType} {b : Ann B}
    (hh : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    Rel (⟨s.i, _, Term.holeAt s.t hh⟩ : DTerm S T B) ⟨s'.i, _, Term.holeAt s'.t hh⟩ := by
  intro j hj hj'
  exact Interch.of_sig (Term.mono_holeAt_sig _ s.t hh).symm (Term.mono_holeAt_sig _ s'.t hh).symm
    ((h j hj hj').holeAt hh)

/-- ⭐Related terms stay related under pairing, read at stages above both components. -/
theorem Rel.pair {s₁ s₁' : DTerm S T A} (h₁ : s₁.Rel s₁') {B : VarType} {s₂ s₂' : DTerm S T B}
    (h₂ : s₂.Rel s₂') (k : I) (hk₁ : s₁.i ≤ k) (hk₂ : s₂.i ≤ k) (k' : I) (hk₁' : s₁'.i ≤ k')
    (hk₂' : s₂'.i ≤ k') :
    Rel (⟨k, _, Term.pair (s₁.lift k hk₁) (s₂.lift k hk₂)⟩ : DTerm S T (.VTypeProd A B))
      ⟨k', _, Term.pair (s₁'.lift k' hk₁') (s₂'.lift k' hk₂')⟩ := by
  intro j hj hj'
  change Interch T (Term.pair (Term.mono (S.le hj) (Term.mono (S.le hk₁) s₁.t))
      (Term.mono (S.le hj) (Term.mono (S.le hk₂) s₂.t)))
    (Term.pair (Term.mono (S.le hj') (Term.mono (S.le hk₁') s₁'.t))
      (Term.mono (S.le hj') (Term.mono (S.le hk₂') s₂'.t)))
  rw [Term.mono_mono, Term.mono_mono, Term.mono_mono, Term.mono_mono]
  exact (h₁ j (hk₁.trans hj) (hk₁'.trans hj')).pair (h₂ j (hk₂.trans hj) (hk₂'.trans hj'))

end DTerm

end Canon
end V12M
