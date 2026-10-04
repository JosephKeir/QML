import QML.QML_v12m_SubstEta
import QML.QML_v12m_Presented
import QML.QML_v12m_BackSyntax

/-!
# QML v12m — the proof system

Classical natural deduction.  The hypotheses form a LIST, with explicit weakening, contraction and
exchange; `Proof.lookup` / `Proof.ofSubset` and the tactics `by_hyp` / `hyps_from` handle them in
practice, so the structural rules never need to be applied by hand.

* **Proofs live at binder depth 0**: no rule changes the depth, so it is fixed once and for all.
  The slot side conditions are the type class `Ctx.NoSlots`, found by instance search.
* **Binder-introducing rules take a free variable** `u` (fresh at its root: the `fresh` tactic),
  and the rule binds it to the slot (`WFF.bindFree`).  **Binder-eliminating rules** substitute for
  the slot (`WFF.instantiate`), with a term of ANY annotation: quantifiers range over plain types.
* **Equality** is primitive only at base type; compound equality is `eqRec`.
* **Pair elimination** renames the user's components `u₁ u₂` to `z.fst`, `z.snd`.
* **Modal K** rules state their premises in the `□` / `◇_x` views of the conclusion's context.
-/

namespace V12M

variable [ModalSys]

/-- Strong D's axiom: some possible object has a nonempty extent, `∃x:◇𝟙. ◇_x ⊤`.  It is closed.
    Everything else strong D says follows from it in K: re-using the witness with new content
    (`diatm`, the syntactic side of `strength`) gives `□φ(u.box) ⊢ ∃x:◇A. ◇_x φ(x.dia)` at every
    type (`Proof.D_schema`). -/
def WFF.somePoss {σ : Signature} {Γ : Ctx} : WFF σ Γ 0 :=
  .ex (.VTypeDia .VTypeOne)
    (.dia (.root (.bnd 0)) ⟨.VTypeOne, Ctx.ref_insert_root Γ (.bnd 0) _⟩ .top)

/-- A closed formula, weakened into a context. -/
abbrev WFF.closed {σ : Signature} {d : ℕ} (Γ : Ctx) (ψ : WFF σ Ctx.empty d) : WFF σ Γ d :=
  WFF.mono (Ctx.empty_le Γ) ψ

/-- `◇□φ`, with `◇` the dual `¬□¬`: the premise of weak B's rule. -/
abbrev WFF.diaBox {σ : Signature} {Γ : Ctx} (φ : WFF σ Γ.boxIn.boxIn 0) : WFF σ Γ 0 :=
  (WFF.box (Γ := Γ) (WFF.box (Γ := Γ.boxIn) φ).neg).neg

inductive Proof (σ : Signature) : (Γ : Ctx) → List (WFF σ Γ 0) → WFF σ Γ 0 → Type where
  -- Structural
  | ax {Γ : Ctx} (φ : WFF σ Γ 0) : Proof σ Γ [φ] φ
  | weak {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (ψ : WFF σ Γ 0) :
      Proof σ Γ Δ φ → Proof σ Γ (ψ :: Δ) φ
  | contr {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} :
      Proof σ Γ (ψ :: ψ :: Δ) φ → Proof σ Γ (ψ :: Δ) φ
  | exch {Γ : Ctx} (Δ₁ Δ₂ : List (WFF σ Γ 0)) {φ ψ χ : WFF σ Γ 0} :
      Proof σ Γ (Δ₁ ++ ψ :: χ :: Δ₂) φ → Proof σ Γ (Δ₁ ++ χ :: ψ :: Δ₂) φ
  | weak_ctx {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (u : ℕ) (T : VarType)
      (hu : Γ.RootFresh (.free u)) :
      Proof σ Γ Δ φ →
      Proof σ (Γ.insert (.free u) T) (Δ.map (WFF.weaken hu.root T)) (φ.weaken hu.root T)
  -- Conjunction
  | and_intro {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} :
      Proof σ Γ Δ φ → Proof σ Γ Δ ψ → Proof σ Γ Δ (φ.and ψ)
  | and_elim_l {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} :
      Proof σ Γ Δ (φ.and ψ) → Proof σ Γ Δ φ
  | and_elim_r {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} :
      Proof σ Γ Δ (φ.and ψ) → Proof σ Γ Δ ψ
  -- Disjunction
  | or_intro_l {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (ψ : WFF σ Γ 0) :
      Proof σ Γ Δ φ → Proof σ Γ Δ (φ.or ψ)
  | or_intro_r {Γ : Ctx} {Δ : List (WFF σ Γ 0)} (φ : WFF σ Γ 0) {ψ : WFF σ Γ 0} :
      Proof σ Γ Δ ψ → Proof σ Γ Δ (φ.or ψ)
  | or_elim {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ ψ χ : WFF σ Γ 0} :
      Proof σ Γ Δ (φ.or ψ) → Proof σ Γ (φ :: Δ) χ → Proof σ Γ (ψ :: Δ) χ → Proof σ Γ Δ χ
  -- Implication
  | imp_intro {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} :
      Proof σ Γ (φ :: Δ) ψ → Proof σ Γ Δ (φ.imp ψ)
  | imp_elim {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} :
      Proof σ Γ Δ (φ.imp ψ) → Proof σ Γ Δ φ → Proof σ Γ Δ ψ
  -- Truth and falsity
  | top_intro {Γ : Ctx} {Δ : List (WFF σ Γ 0)} : Proof σ Γ Δ .top
  | bot_elim {Γ : Ctx} {Δ : List (WFF σ Γ 0)} (φ : WFF σ Γ 0) :
      Proof σ Γ Δ .bot → Proof σ Γ Δ φ
  -- Classical logic
  | lem {Γ : Ctx} {Δ : List (WFF σ Γ 0)} (φ : WFF σ Γ 0) : Proof σ Γ Δ (φ.or φ.neg)
  -- ⭐Universal quantifier: the eigenvariable `u` is free in the subproof and bound to the slot.
  | all_intro {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (u : ℕ) (T : VarType)
      (hu : Γ.RootFresh (.free u)) {φ : WFF σ (Γ.insert (.free u) T) 0} :
      Proof σ (Γ.insert (.free u) T) (Δ.map (WFF.weaken hu.root T)) φ →
      Proof σ Γ Δ (.all T (WFF.bindFree u hu Ctx.NoSlots.slots T φ))
  -- Elimination substitutes a term of any annotation for the slot.
  | all_elim {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (T : VarType)
      {φ : WFF σ (Γ.insert (.bnd 0) T) 1} {a : Ann T} (t : Term σ Γ T a) :
      Proof σ Γ Δ (.all T φ) → Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ)
  -- Existential quantifier
  | ex_intro {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (T : VarType)
      {φ : WFF σ (Γ.insert (.bnd 0) T) 1} {a : Ann T} (t : Term σ Γ T a) :
      Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ) → Proof σ Γ Δ (.ex T φ)
  | ex_elim {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (u : ℕ) (T : VarType)
      (hu : Γ.RootFresh (.free u)) {φ : WFF σ (Γ.insert (.free u) T) 0} {ψ : WFF σ Γ 0} :
      Proof σ Γ Δ (.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T φ)) →
      Proof σ (Γ.insert (.free u) T) (φ :: Δ.map (WFF.weaken hu.root T)) (ψ.weaken hu.root T) →
      Proof σ Γ Δ ψ
  -- ⭐Equality, primitive only at base type (compound equality is `eqRec`).
  | eq_intro {Γ : Ctx} {Δ : List (WFF σ Γ 0)} (t : Term σ Γ .Var .var) : Proof σ Γ Δ (.eq t t)
  -- The formula `φ` has its hole at the slot `bnd 0`, as for `all_elim`.
  | eq_elim {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} {φ : WFF σ (Γ.insert (.bnd 0) .Var) 1}
      (t s : Term σ Γ .Var .var) :
      Proof σ Γ Δ (.eq t s) → Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ) →
      Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots s φ)
  -- ⭐Pairing: the user's components `u₁ u₂` become `z.fst`, `z.snd`.
  | pair_elim {Γ : Ctx} [Γ.NoSlots] (A B : VarType) (u₁ u₂ z : ℕ) (hu : u₁ ≠ u₂) (hz₁ : z ≠ u₁)
      (hu₁ : Γ.RootFresh (.free u₁)) (hu₂ : Γ.RootFresh (.free u₂))
      (hzf : Γ.RootFresh (.free z))
      {Δ : List (WFF σ ((Γ.insert (.free u₁) A).insert (.free u₂) B) 0)}
      {φ : WFF σ ((Γ.insert (.free u₁) A).insert (.free u₂) B) 0} :
      Proof σ ((Γ.insert (.free u₁) A).insert (.free u₂) B) Δ φ →
      Proof σ (Γ.insert (.free z) (.VTypeProd A B))
        (Δ.map (WFF.bindPair u₁ u₂ z hu hz₁ hu₁ hu₂ hzf Ctx.NoSlots.slots A B))
        (WFF.bindPair u₁ u₂ z hu hz₁ hu₁ hu₂ hzf Ctx.NoSlots.slots A B φ)
  -- Modal K
  | K_box {Γ : Ctx} {Δ : List (WFF σ Γ.boxIn 0)} {φ : WFF σ Γ.boxIn 0} :
      Proof σ Γ.boxIn Δ φ → Proof σ Γ (Δ.map fun ψ => WFF.box (Γ := Γ) ψ) (.box φ)
  /-- From `ψ, Δ₂, Δ₁ ⊢ φ` inside `◇_x` conclude `◇_x ψ, □_x Δ₂, □ Δ₁ ⊢ ◇_x φ`: `Δ₁` is
      witness-free (plain `□`), `Δ₂` may mention the witness content `x.dia`. -/
  | K_dia {Γ : Ctx} (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
      {Δ₁ : List (WFF σ Γ.boxIn 0)} {Δ₂ : List (WFF σ (Γ.diaIn x) 0)}
      {φ ψ : WFF σ (Γ.diaIn x) 0} :
      Proof σ (Γ.diaIn x) (ψ :: (Δ₂ ++ Δ₁.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))) φ →
      Proof σ Γ (.dia x hx ψ :: (Δ₂.map (WFF.boxx x hx) ++ Δ₁.map fun χ => WFF.box (Γ := Γ) χ))
        (.dia x hx φ)
  | dia_bot {Γ : Ctx} {Δ : List (WFF σ Γ 0)} (x : VarSymb)
      (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) :
      Proof σ Γ Δ (.dia x hx .bot) → Proof σ Γ Δ .bot
  -- Weak D
  /-- Something is accessible, so not everything is impossible: `□⊥ ⊢ ⊥`.  The familiar
      `□φ ⊢ ◇φ` is derived from it (`Proof.D_dia`). -/
  | D_box {Γ : Ctx} {Δ : List (WFF σ Γ 0)} (hD : ModalSys.D = true) :
      Proof σ Γ Δ (.box .bot) → Proof σ Γ Δ .bot
  -- Strong D
  /-- Some possible object has a nonempty extent (`WFF.somePoss`). -/
  | D_ex {Γ : Ctx} {Δ : List (WFF σ Γ 0)} (hDS : ModalSys.DStrong = true) :
      Proof σ Γ Δ WFF.somePoss
  -- Weak T
  /-- What is necessary holds here: the `□` view collapsed onto the current level. -/
  | T_box {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true) {Δ : List (WFF σ Γ 0)}
      {φ : WFF σ Γ.boxIn 0} :
      Proof σ Γ Δ (.box φ) →
      Proof σ Γ Δ (WFF.collapse (Ctx.collapses_boxIn_self hT Γ) Ctx.NoSlots.slots φ)
  -- Weak 4
  /-- What is necessary is necessarily necessary: the `□` view shifted one view further in. -/
  | four_box {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)}
      {φ : WFF σ Γ.boxIn 0} :
      Proof σ Γ Δ (.box φ) →
      Proof σ Γ Δ (.box (.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots φ)))
  -- Strong T
  /-- ⭐**Every object has a possible object realised here**, as an `∃`-elimination: the witness
      `c : ◇A` is fresh, and the subproof gets the single hypothesis `Here (η c) t`.  Its validity
      is `Model.posRet_exists`, read as `Model.sat_here_ex`.

      *This used to hand over the realisation schema `WFF.retHyp` instead* — for finitely many
      `□`-view hole formulas with a parameter, that what holds of `t` here holds of the witness
      content in `◇_c`.  Each such instance is `here_intro`'s conclusion for its hole formula, so
      nothing is lost: the schema follows from the atom, not the other way round.  The atom is
      strictly better: no parameter name, no hole-formula list, `◇_c` usable at either polarity,
      and — the reason it matters — the canonical model can put the *atom* into its theory, which is
      what the truth lemma's `here` case needs and what no schema instance supplies (§2d,
      `Model.sat_here_ex`).  The chain now adds exactly that atom (`WorldLang.retSet`), and
      `Canon.spec_of_here` derives `RealDatum.spec` from it. -/
  | T_dia {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true) (hS : ModalSys.TStrong = true)
      (A : VarType) {a : Ann A} (t : Term σ Γ A a) (c : ℕ)
      (hc : Γ.RootFresh (.free c))
      {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} :
      Proof σ (Γ.insert (.free c) (.VTypeDia A))
        (WFF.hereAt hT (.root (.free c)) (Ctx.ref_insert_root Γ (.free c) (.VTypeDia A))
            (Term.weaken hc.root (.VTypeDia A) t) ::
          Δ.map (WFF.weaken hc.root (.VTypeDia A)))
          (φ.weaken hc.root (.VTypeDia A)) →
      Proof σ Γ Δ φ
  -- Strong T, inwards: the realisation predicate
  /-- ⭐**Elimination**: if the possible object `◇_x`-with-content-`bd` is realised here by `t`, then
      what is necessary over `x`'s extent holds of `t` — weak T relativised to the witness.  The
      premise and the conclusion read one hole formula `ψ` twice: inside the view with `bd` in the
      hole (`WFF.viewReadTm`), and here with `t` in it (`WFF.hereRead`).

      Stating it at a `◇`-**term** rather than at a bare address is what makes it survive
      substitution: an entry for a `◇`-typed address is such a term, and its body takes the
      content's place.  The pinned case `bd = x.dia` is the rule one expects, `Here x t, □_x χ ⊢
      χ(t)` (`Proof.here_elimAt`), since every view formula is its abstraction read back. -/
  | here_elim {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hT : ModalSys.T = true) (x : VarSymb)
      (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType}
      {a : Ann A} (t : Term σ Γ A a)
      {a' : Ann A} (bd : Term σ (Γ.diaIn x) A a')
      (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
      Proof σ Γ Δ (WFF.here hT (Term.diatm x hx bd) t) →
      Proof σ Γ Δ (WFF.boxx x hx (WFF.viewReadTm bd ψ)) →
      Proof σ Γ Δ (WFF.hereRead hT t ψ)
  /-- ⭐**Introduction**: what holds of the realisation here is possible for the witness, this very
      world witnessing it.  The converse of `here_elim` across the same two readings, so the pair is
      one biconditional (`Model.sat_viewReadTm`) split by polarity. -/
  | here_intro {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hT : ModalSys.T = true) (x : VarSymb)
      (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType}
      {a : Ann A} (t : Term σ Γ A a)
      {a' : Ann A} (bd : Term σ (Γ.diaIn x) A a')
      (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
      Proof σ Γ Δ (WFF.here hT (Term.diatm x hx bd) t) →
      Proof σ Γ Δ (WFF.hereRead hT t ψ) →
      Proof σ Γ Δ (WFF.dia x hx (WFF.viewReadTm bd ψ))
  /-- ⭐**β for the realisation predicate**: the realisation of a body read through a hole term is
      the realisation of the body, read here through the same hole.  This is what lets a witness's
      own realisation decide every `Here` formula about it: with `bd` the witness content, `s`
      ranges over the view terms (`Term.diaAbs` abstracts one), and the value on the right is
      `Term.realiseAt`. -/
  | here_beta {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hT : ModalSys.T = true) (x : VarSymb)
      (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType}
      {a : Ann A} (t : Term σ Γ A a)
      {a' : Ann A} (bd : Term σ (Γ.diaIn x) A a')
      {B : VarType} {b : Ann B}
      (s : Term σ (Γ.boxIn.insert (.bnd 0) A) B b) :
      Proof σ Γ Δ (WFF.here hT (Term.diatm x hx bd) t) →
      Proof σ Γ Δ
        (WFF.here hT (Term.diatm x hx (Term.viewReadTm bd s)) (Term.hereRead hT t s))
  /-- ⭐**A realised witness has a content**: if the world itself lies in `x`'s extent, then every
      possible object over `x` has a value here.  The other half of the pair whose first half is
      `T_dia`: that says every value has a realised witness, this says every realised witness has a
      value.  `Model.posRet_exists` is the first; the totality of a `Pos`-object's content function
      on its extent is the second, so the rule is sound with no condition on the type (§10.15).

      *The premise is realisedness in its minimal expressible form.*  `Dom 𝟙 w` is a single
      point, so
      `Here (diatm x hx unit) unit` says exactly that the reflexive arrow lies in `x`'s extent, and
      `here_beta` at `s := Term.unit` derives it from any atom about `x` — which is why no separate
      formula for realisedness is needed (§10.14).

      *Why the body is arbitrary.*  Stated at the pinned subject `η x` alone the rule would not
      survive substitution: an entry sends `x` to a `◇`-term over another witness, and the pinned
      form is not closed under that — the general form is its closure (§10.11).  With the body
      arbitrary the image of the conclusion is the rule's own conclusion at the substituted body,
      and
      the pinned instance, `bd := η x.dia`, is the one the canonical model consumes. -/
  | here_name {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hT : ModalSys.T = true) (x : VarSymb)
      (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {B : VarType} {β : Ann B}
      (bd : Term σ (Γ.diaIn x) B β) :
      Proof σ Γ Δ (WFF.here hT (Term.diatm x hx Term.unit) Term.unit) →
      Proof σ Γ Δ (WFF.hereEx hT (Term.diatm x hx bd))
  /-- ⭐**Functionality, substitutionally**: a possible object has one content here, so its two
      candidates are interchangeable in every formula.  This is the form functionality must take
      a `◇`-typed content, where no equation is available: `WFF.eqRec` compares terms at **one**
      annotation, and two names of one content may stand over different witnesses, which no formula
      can equate (§10.3).  Substitutivity needs no annotation agreement — the two instances are
      simply two formulas — so the rule is stated at any subject, any content type and **any two
      annotations**.

      What it subsumes.  The `◇`-free equation is `Proof.here_fun`, the instance at the hole formula
      `eqRec A (η slot) t` with reflexivity as its minor premise.  The transfer of `◇`-facts between
      two names is the instance at `φ = ◇_{.bnd 0} ψ`: substituting a `◇`-term for a witness address
      is `Subst.dia`/`SubE.diaBody`, i.e. `WFF.viewReadTm`, so that instance reads
      `◇_y (viewReadTm bd ψ) ⊢ ◇_{y'} (viewReadTm bd' ψ)` (§10.11).  A `◇`-typed term occurs in a
      formula only inside a `Here` atom — as its subject or within its content — so substitution for
      the slot covers every occurrence there is. -/
  | here_subst {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hT : ModalSys.T = true)
      {A : VarType} {b : Ann (.VTypeDia A)} (s : Term σ Γ (.VTypeDia A) b)
      {a a' : Ann A} (t : Term σ Γ A a) (t' : Term σ Γ A a')
      (φ : WFF σ (Γ.insert (.bnd 0) A) 1) :
      Proof σ Γ Δ (WFF.here hT s t) → Proof σ Γ Δ (WFF.here hT s t') →
      Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ) →
      Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t' φ)
  /-- ⭐**Leibniz for the content** (docs §10.24–10.25): a realised possible object's content can be
      replaced by an equal one.  `Here` relates a possible object directly to an object one level
      down, a cross-level relation that K's Leibniz cannot see — without `Here`, a possible object
      is only ever used inside a `◇` with its own witness.  `eqRec` compares terms of one
      annotation only, so this never relates contents over different witnesses. -/
  | here_eq {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hT : ModalSys.T = true)
      {A : VarType} {b : Ann (.VTypeDia A)} (s : Term σ Γ (.VTypeDia A) b)
      {a : Ann A} (t t' : Term σ Γ A a) :
      Proof σ Γ Δ (WFF.here hT s t) → Proof σ Γ Δ (eqRec A t t') →
      Proof σ Γ Δ (WFF.here hT s t')
  -- Weak B
  /-- What is possibly necessary is true, `◇□ψ ⊢ ψ`, for a closed `ψ`: some accessible world
      makes `ψ` necessary, and an arrow leads back from it.  `ψ` must be closed because nothing
      of the origin's context can be read two levels in and back.  The familiar `ψ ⊢ □◇ψ` is
      derived from it (`Proof.B_box`). -/
  | B_dia {Γ : Ctx} {Δ : List (WFF σ Γ 0)} (hB : ModalSys.B = true) (ψ : WFF σ Ctx.empty 0) :
      Proof σ Γ Δ (WFF.diaBox (ψ.closed _)) → Proof σ Γ Δ (ψ.closed Γ)
  -- Strong B: `Back` (docs §11.2, §11.5, §11.14).  Stated once over the out leg (`OutLeg`), at the
  -- carrier's body, with hole formulas and terms closed apart from the hole.
  /-- ⭐**`Back`, elimination**: what is necessary at the end of some arrow of the out leg, of the
      carrier's value there, holds of the value it comes back as — along that arrow's way home. -/
  | back_elim {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
      (O : OutLeg Γ) {A : VarType} {a₀ : Ann A}
      (bd : Term σ O.view.boxIn A a₀) {a : Ann A} (t : Term σ Γ A a)
      (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) :
      Proof σ Γ Δ (O.back hS bd t) →
      Proof σ Γ Δ (O.dia (WFF.box (WFF.holeRead bd ψ))) →
      Proof σ Γ Δ (WFF.holeRead t ψ)
  /-- ⭐**`Back`, introduction**: what holds of the value it comes back as is, from every arrow of
      the out leg, possible of the carrier's value — the way home witnessing it. -/
  | back_intro {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
      (O : OutLeg Γ) {A : VarType} {a₀ : Ann A}
      (bd : Term σ O.view.boxIn A a₀) {a : Ann A} (t : Term σ Γ A a)
      (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) :
      Proof σ Γ Δ (O.back hS bd t) →
      Proof σ Γ Δ (WFF.holeRead t ψ) →
      Proof σ Γ Δ (O.box (WFF.box (WFF.holeRead bd ψ).neg).neg)
  /-- `Back` asserts that its round trip exists: the out leg is nonempty (§11.1, decision of
      2026-10-03). -/
  | back_ne {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
      (O : OutLeg Γ) {A : VarType} {a₀ : Ann A}
      (bd : Term σ O.view.boxIn A a₀) {a : Ann A} (t : Term σ Γ A a) :
      Proof σ Γ Δ (O.back hS bd t) → Proof σ Γ Δ (O.dia .top)
  /-- ⭐**β**: a carrier mapped by a hole term comes back as its value mapped by the same term. -/
  | back_beta {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
      (O : OutLeg Γ) {A : VarType} {a₀ : Ann A}
      (bd : Term σ O.view.boxIn A a₀) {a : Ann A} (t : Term σ Γ A a) {B : VarType}
      {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
      Proof σ Γ Δ (O.back hS bd t) →
      Proof σ Γ Δ (O.back hS (Term.holeRead bd s) (Term.holeRead t s))
  /-- ⭐**Pairing** (§11.14 check 3): two carriers over one out leg come back as the pair of their
      values — each arrow has one way home, so both are read along it. -/
  | back_pair {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
      (O : OutLeg Γ) {A : VarType} {a₀ : Ann A}
      (bd : Term σ O.view.boxIn A a₀) {a : Ann A} (t : Term σ Γ A a) {B : VarType}
      {b₀ : Ann B} (bd' : Term σ O.view.boxIn B b₀) {b : Ann B}
      (t' : Term σ Γ B b) :
      Proof σ Γ Δ (O.back hS bd t) → Proof σ Γ Δ (O.back hS bd' t') →
      Proof σ Γ Δ (O.back hS (Term.pair bd bd') (Term.pair t t'))
  /-- **Leibniz for the value.** -/
  | back_eq {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
      (L : BLeg) {A : VarType} {b : Ann (L.carrier A)}
      (s : Term σ Γ (L.carrier A) b) {a : Ann A} (t t' : Term σ Γ A a) :
      Proof σ Γ Δ (WFF.back hS L s t) → Proof σ Γ Δ (eqRec A t t') →
      Proof σ Γ Δ (WFF.back hS L s t')
  /-- ⭐**The own arrow** (§11.5 (4)): under T the identity is an arrow out, and its only way home
      is the identity, so the carrier read here twice is interchangeable with its value. -/
  | back_here {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
      (hT : ModalSys.T = true) {A : VarType} {a₀ : Ann A}
      (bd : Term σ Γ.boxIn.boxIn A a₀) {a : Ann A} (t : Term σ Γ A a)
      (φ : WFF σ (Γ.insert (.bnd 0) A) 1) :
      Proof σ Γ Δ ((OutLeg.nec : OutLeg Γ).back hS bd t) →
      Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ) →
      Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots (Term.collapse
        (Ctx.collapses_boxIn_self hT Γ) (Term.collapse (Ctx.collapses_boxIn_self hT Γ.boxIn) bd)) φ)
  /-- ⭐**Definition** (§11.5 (3)): if a hole formula holds at the end of every way on from every
      arrow of a nonempty out leg, and singles out `t` here, the carrier comes back as `t` — weak B
      gives every arrow a way home, and the return satisfies the formula.  The one rule that makes a
      `Back` atom about a given carrier; the canonical model's negative atoms need it. -/
  | back_def {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
      (hB : ModalSys.B = true) (O : OutLeg Γ) {A : VarType} (hA : A.diaFree = true) {a₀ : Ann A}
      (bd : Term σ O.view.boxIn A a₀) {a : Ann A} (t : Term σ Γ A a)
      (θ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) :
      Proof σ Γ Δ (O.dia .top) →
      Proof σ Γ Δ (O.box (WFF.box (WFF.holeRead bd θ))) →
      Proof σ Γ Δ (WFF.all A (WFF.imp (WFF.mono ((Ctx.empty_le Γ).insert (.bnd 0) A) θ)
        (eqRec A (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root Γ (.bnd 0) A))
          (Term.castAnn hA (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root A) t))))) →
      Proof σ Γ Δ (O.back hS bd t)
  /-- ⭐**Every object comes back** (row 1), as an `∃`-elimination like `T_dia`: wherever there is
      a way out, a fresh carrier `c : □□A` comes back as `t`.  Its validity is
      `Model.backRet_exists`.  Row 2 needs no rule of its own (`Model.backRet_exists`). -/
  | B_strong {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) {A : VarType}
      {a : Ann A} (t : Term σ Γ A a) (c : ℕ)
      (hc : Γ.RootFresh (.free c)) {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} :
      Proof σ Γ Δ ((OutLeg.nec : OutLeg Γ).dia .top) →
      Proof σ (Γ.insert (.free c) (.VTypeBox (.VTypeBox A)))
        (WFF.back hS .nec (Term.eta (.root (.free c)) _
            (Ctx.ref_insert_root Γ (.free c) (.VTypeBox (.VTypeBox A))))
            (Term.weaken hc.root _ t) ::
          Δ.map (WFF.weaken hc.root (.VTypeBox (.VTypeBox A))))
        (φ.weaken hc.root (.VTypeBox (.VTypeBox A))) →
      Proof σ Γ Δ φ
  -- Strong B: the returning possibility `◇[d ↦ t] Φ(d)` (`WFF.ret`, docs §11.14).  Its body binds
  -- one necessary object `d : □A` of the far world; several items are packed into one by pairing.
  /-- ⭐**A new returning possibility** (existence, no items yet), as an `∃`-elimination: if some
      accessible world has a necessary object with `Φ`, then for a fresh `c` it comes back as `c` —
      weak B gives the way home. -/
  | ret_new {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
      {A : VarType} (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
      (c : ℕ) (hc : Γ.RootFresh (.free c)) {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} :
      Proof σ Γ Δ ((OutLeg.nec : OutLeg Γ).dia (WFF.ex (.VTypeBox A) Φ)) →
      Proof σ (Γ.insert (.free c) A)
        (WFF.ret hS (Term.eta (.root (.free c)) A (Ctx.ref_insert_root Γ (.free c) A))
            (WFF.mono ((Ctx.le_insert hc.root A).boxIn.insert (.bnd 0) _) Φ) ::
          Δ.map (WFF.weaken hc.root A))
        (φ.weaken hc.root A) →
      Proof σ Γ Δ φ
  /-- ⭐**One more item of the same child** (existence, extension form): if the returning
      possibility's object has a companion `b` with `Φ(d, b)`, then for a fresh `c` the pair
      `⟨d, b⟩` comes back as `⟨t, c⟩` — the body split into the pair's components. -/
  | ret_ext {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) {A B : VarType}
      {a : Ann A} (t : Term σ Γ A a)
      (Φ : WFF σ ((Γ.boxIn.insert (.bnd 0) (.VTypeBox A)).insert (.bnd 1) (.VTypeBox B)) 2)
      (c : ℕ) (hc : Γ.RootFresh (.free c)) {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} :
      Proof σ Γ Δ (WFF.ret hS t (WFF.ex (.VTypeBox B) Φ)) →
      Proof σ (Γ.insert (.free c) B)
        (WFF.ret hS
            (Term.pair (Term.weaken hc.root B t)
              (Term.eta (.root (.free c)) B (Ctx.ref_insert_root Γ (.free c) B)))
            (WFF.mono ((Ctx.le_insert hc.root B).boxIn.insert (.bnd 0) _) (WFF.bodySplit
              (Term.boxFst (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox (.VTypeProd A B))))
              (Term.boxSnd (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox (.VTypeProd A B))))
              Φ)) ::
          Δ.map (WFF.weaken hc.root B))
        (φ.weaken hc.root B) →
      Proof σ Γ Δ φ
  /-- ⭐**Elimination**: what is necessary of the object out there holds of the value it comes back
      as. -/
  | ret_elim {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
      {A : VarType} {a : Ann A} (t : Term σ Γ A a)
      (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) :
      Proof σ Γ Δ (WFF.ret hS t (WFF.box (WFF.holeAt
        ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert (.VTypeBox A)).boxIn
        (Term.eta (VarSymb.root (.bnd 0)).inner A
          (Ctx.ref_inner (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox A)))) ψ))) →
      Proof σ Γ Δ (WFF.holeRead t ψ)
  /-- ⭐**Elimination with a carrier** (§11.14): from the arrow out that the returning possibility
      found, the carrier's image comes home along the one way back too, so what is necessary of the
      object and the image together holds of the value and the carrier's value.  Several carriers
      are one by pairing (`back_pair`). -/
  | ret_elimC {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
      {A C : VarType} {a : Ann A} (y : Term σ Γ A a) {c₀ : Ann C}
      (bd : Term σ Γ.boxIn.boxIn C c₀) {c : Ann C} (t : Term σ Γ C c)
      (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A C)) 1) :
      Proof σ Γ Δ (WFF.ret hS y (WFF.box (WFF.holeAt
        ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert (.VTypeBox A)).boxIn
        (Term.pair (Term.eta (VarSymb.root (.bnd 0)).inner A
            (Ctx.ref_inner (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox A))))
          (Term.mono ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root (.VTypeBox A)).boxIn)
            bd)) ψ))) →
      Proof σ Γ Δ ((OutLeg.nec : OutLeg Γ).back hS bd t) →
      Proof σ Γ Δ (WFF.holeRead (Term.pair y t) ψ)
  /-- **Monotonicity** in the body. -/
  | ret_mono {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
      {A : VarType} {a : Ann A} (t : Term σ Γ A a)
      (Φ Φ' : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1) :
      Proof σ Γ Δ (WFF.ret hS t Φ) →
      Proof σ Γ Δ (WFF.box (WFF.all (.VTypeBox A) (WFF.imp Φ Φ'))) →
      Proof σ Γ Δ (WFF.ret hS t Φ')
  /-- A returning possibility is a possibility. -/
  | ret_dia {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
      {A : VarType} {a : Ann A} (t : Term σ Γ A a)
      (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1) :
      Proof σ Γ Δ (WFF.ret hS t Φ) →
      Proof σ Γ Δ ((OutLeg.nec : OutLeg Γ).dia (WFF.ex (.VTypeBox A) Φ))
  /-- ⭐**β**: an object built from the item by a hole term comes back as the value built by the same
      term. -/
  | ret_beta {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
      {A B : VarType} {a : Ann A}
      (y : Term σ Γ A a) {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b)
      (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox B)) 1) :
      Proof σ Γ Δ (WFF.ret hS y (WFF.bodyRepl
        (Term.boxtm (Term.holeAt (Term.eta (VarSymb.root (.bnd 0)).inner A
          (Ctx.ref_inner (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox A)))) s)) Φ)) →
      Proof σ Γ Δ (WFF.ret hS (Term.holeRead y s) Φ)
  /-- **Leibniz for the value.** -/
  | ret_eq {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
      {A : VarType} {a : Ann A} (t t' : Term σ Γ A a)
      (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1) :
      Proof σ Γ Δ (WFF.ret hS t Φ) → Proof σ Γ Δ (eqRec A t t') →
      Proof σ Γ Δ (WFF.ret hS t' Φ)
  /-- ⭐**The own arrow** (T): a necessary object here with `Φ` at this very world comes back as its
      value here — the identity is an arrow out and its own way home. -/
  | ret_here {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
      (hT : ModalSys.T = true) {A : VarType} {a₀ : Ann A}
      (sb : Term σ Γ.boxIn A a₀) (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1) :
      Proof σ Γ Δ (WFF.hereRead hT (Term.boxtm sb) Φ) →
      Proof σ Γ Δ (WFF.ret hS (Term.collapse (Ctx.collapses_boxIn_self hT Γ) sb) Φ)
  /-- ⭐**Bridging** (§11.14): a carrier that comes back as `t`, possibly with `Φ` of its image out
      there, is a returning possibility with value `t` — from any arrow of its out leg, plain or
      witnessed. -/
  | ret_bridge {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
      (O : OutLeg Γ) {A : VarType} {a₀ : Ann A}
      (bd : Term σ O.view.boxIn A a₀) {a : Ann A} (t : Term σ Γ A a)
      (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1) :
      Proof σ Γ Δ (O.back hS bd t) →
      Proof σ Γ Δ (O.dia (O.bodyRead (Term.boxtm bd) Φ)) →
      Proof σ Γ Δ (WFF.ret hS t Φ)

/-! ## Handling hypotheses -/

namespace Proof

variable {σ : Signature} {Γ : Ctx}

/-- Weaken by a whole list at the front. -/
def weakenAll : (pre : List (WFF σ Γ 0)) → {Δ : List (WFF σ Γ 0)} → {φ : WFF σ Γ 0} →
    Proof σ Γ Δ φ → Proof σ Γ (pre ++ Δ) φ
  | [], _, _, p => p
  | ψ :: pre, _, _, p => Proof.weak ψ (weakenAll pre p)

/-- Bring the hypothesis after `pre` to the front, by exchanges. -/
def rise {φ : WFF σ Γ 0} : (outer pre : List (WFF σ Γ 0)) → (x : WFF σ Γ 0) →
    (rest : List (WFF σ Γ 0)) →
    Proof σ Γ (outer ++ (pre ++ x :: rest)) φ → Proof σ Γ (outer ++ x :: (pre ++ rest)) φ
  | _, [], _, _, p => p
  | outer, y :: pre, x, rest, p => by
      have p₁ : Proof σ Γ ((outer ++ [y]) ++ (pre ++ x :: rest)) φ := by
        rw [List.append_assoc]
        exact p
      have p₂ := rise (outer ++ [y]) pre x rest p₁
      rw [List.append_assoc] at p₂
      exact Proof.exch outer (pre ++ rest) p₂

/-- ⭐A hypothesis proves itself. -/
def lookup : {Δ : List (WFF σ Γ 0)} → {x : WFF σ Γ 0} → x ∈ Δ → Proof σ Γ Δ x
  | [], _, h => absurd h List.not_mem_nil
  | y :: Δ, x, h =>
      if hxy : x = y then by
        subst hxy
        have p : Proof σ Γ (Δ ++ [x]) x := weakenAll Δ (Proof.ax x)
        have p' := rise [] Δ x [] p
        simpa using p'
      else Proof.weak y (lookup ((List.mem_cons.mp h).resolve_left hxy))

/-- ⭐Move a proof to any hypothesis list containing its hypotheses. -/
def ofSubset : {Δ Δ' : List (WFF σ Γ 0)} → {φ : WFF σ Γ 0} → (∀ ψ ∈ Δ, ψ ∈ Δ') →
    Proof σ Γ Δ φ → Proof σ Γ Δ' φ
  | [], Δ', _, _, p => by
      have p' := weakenAll Δ' p
      rw [List.append_nil] at p'
      exact p'
  | x :: Δ, _, _, h, p =>
      Proof.imp_elim (ofSubset (fun ψ hψ => h ψ (List.mem_cons_of_mem x hψ)) (Proof.imp_intro p))
        (lookup (h x List.mem_cons_self))

/-- ⭐Weak D in its familiar form, `□φ ⊢ ◇φ`, with `◇φ` the dual `¬□¬φ`: from `□¬φ` and `□φ`,
    `K_box` gives `□⊥`, which the rule `D_box` refutes. -/
def D_dia (hD : ModalSys.D = true) (φ : WFF σ Γ.boxIn 0) :
    Proof σ Γ [.box φ] (WFF.box (Γ := Γ) φ.neg).neg :=
  .imp_intro (.D_box hD (Proof.K_box (Δ := [φ.neg, φ])
    (.imp_elim (lookup List.mem_cons_self) (lookup (List.mem_cons_of_mem _ List.mem_cons_self)))))

/-- Conversely `□⊥ ⊢ ⊥` is the instance `φ := ⊥` of `□φ ⊢ ◇φ`, since `□¬⊥` is a theorem: the two
    forms of weak D are interderivable in K. -/
def D_box_of_dia {Δ : List (WFF σ Γ 0)}
    (hdia : Proof σ Γ [.box .bot] (WFF.box (Γ := Γ) (WFF.bot : WFF σ Γ.boxIn 0).neg).neg)
    (p : Proof σ Γ Δ (.box .bot)) : Proof σ Γ Δ .bot :=
  .imp_elim
    (.imp_elim (ofSubset (fun _ h => by simp at h) (.imp_intro hdia)) p)
    (ofSubset (fun _ h => by simp at h)
      (Proof.K_box (Δ := []) (.imp_intro (lookup List.mem_cons_self))))

/-- ⭐Weak B in its familiar form, `ψ ⊢ □◇ψ` for a closed `ψ`, with `◇` the dual `¬□¬`.  Its
    negation `¬□◇ψ` is, as a formula, `◇□¬ψ`, which the rule `B_dia` turns into `¬ψ`. -/
def B_box (hB : ModalSys.B = true) (ψ : WFF σ Ctx.empty 0) :
    Proof σ Γ [ψ.closed Γ] (.box (WFF.box (Γ := Γ.boxIn) (ψ.closed _).neg).neg) :=
  .or_elim (.lem _) (lookup List.mem_cons_self)
    (.bot_elim _ (.imp_elim (.B_dia hB ψ.neg (lookup List.mem_cons_self))
      (lookup (List.mem_cons_of_mem _ List.mem_cons_self))))

/-- Conversely the rule is the familiar form at `¬ψ`, read contrapositively: `¬ψ ⊢ □◇¬ψ`, and
    `□◇¬ψ` gives `□¬□ψ` by K (`□ψ ⊢ □¬¬ψ` inside the `□`), which refutes `◇□ψ` unless `ψ`.  So
    the two forms of weak B are interderivable in K. -/
def B_dia_of_box {Δ : List (WFF σ Γ 0)} (ψ : WFF σ Ctx.empty 0)
    (hbox : Proof σ Γ [ψ.neg.closed Γ]
      (.box (WFF.box (Γ := Γ.boxIn) (ψ.neg.closed _).neg).neg))
    (p : Proof σ Γ Δ (WFF.diaBox (ψ.closed _))) : Proof σ Γ Δ (ψ.closed Γ) :=
  -- Inside the outer `□`: `¬□¬¬ψ ⊢ ¬□ψ`, since `□ψ ⊢ □¬¬ψ`.
  have hdn : Proof σ Γ.boxIn [.box (ψ.closed _)] (.box (ψ.closed _).neg.neg) :=
    Proof.K_box (Δ := [ψ.closed _]) (.imp_intro (.imp_elim (lookup List.mem_cons_self)
      (lookup (List.mem_cons_of_mem _ List.mem_cons_self))))
  have hin : Proof σ Γ.boxIn [(WFF.box (ψ.closed _).neg.neg).neg] (WFF.box (ψ.closed _)).neg :=
    .imp_intro (.imp_elim (lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (weakenAll [] (ofSubset (fun _ h => by
        rw [List.mem_singleton.mp h]
        exact List.mem_cons_self) hdn)))
  have hk := Proof.K_box (Δ := [(WFF.box (ψ.closed _).neg.neg).neg]) hin
  .or_elim (.lem _) (lookup List.mem_cons_self)
    (.bot_elim _ (.imp_elim (weakenAll [_] p)
      (.imp_elim (ofSubset (fun _ h => by simp at h) (.imp_intro hk))
        (.imp_elim (ofSubset (fun _ h => by simp at h) (.imp_intro hbox))
          (lookup List.mem_cons_self)))))

end Proof

/-- Close `Proof σ Γ Δ φ` when `φ` is among the hypotheses. -/
macro "by_hyp" : tactic => `(tactic| exact Proof.lookup (by first | decide | simp))

/-- Close `Proof σ Γ Δ' φ` from `p : Proof σ Γ Δ φ` when every hypothesis of `Δ` is in `Δ'`. -/
macro "hyps_from " p:term : tactic =>
  `(tactic| exact Proof.ofSubset (by first | decide | simp) $p)

/-- Discharge `Γ.RootFresh (.free u)` for presented contexts (`u` beyond the bound), contexts built
    from `Ctx.empty` by adding variables and taking views, or from a freshness hypothesis. -/
macro "fresh" : tactic =>
  `(tactic| repeat (first
    | exact Ctx.RootFresh.empty _
    | assumption
    | exact Ctx.Presented.fresh_bound _ (by decide)
    | refine Ctx.RootFresh.insert_ne ?_ (by decide) _
    | refine Ctx.RootFresh.boxIn ?_
    | refine Ctx.RootFresh.diaIn ?_ _))

/-! ## Examples -/

namespace ProofCheck

variable {σ : Signature} {Γ : Ctx}

example (φ ψ : WFF σ Γ 0) : Proof σ Γ [ψ, φ] φ := by by_hyp

example (φ ψ χ : WFF σ Γ 0) (p : Proof σ Γ [φ, ψ] χ) : Proof σ Γ [ψ, χ, φ, φ] χ := by
  hyps_from p

/-- `φ ∧ ψ ⊢ ψ ∧ φ`. -/
example (φ ψ : WFF σ Γ 0) : Proof σ Γ [φ.and ψ] (ψ.and φ) :=
  .and_intro (.and_elim_r (.ax _)) (.and_elim_l (.ax _))

/-- `⊢ □(φ → φ)`. -/
example (φ : WFF σ Γ.boxIn 0) : Proof σ Γ [] (.box (φ.imp φ)) :=
  .K_box (Δ := []) (.imp_intro (.ax φ))

/-- `□φ, □ψ ⊢ □(φ ∧ ψ)`. -/
example (φ ψ : WFF σ Γ.boxIn 0) : Proof σ Γ [.box φ, .box ψ] (.box (φ.and ψ)) :=
  .K_box (Δ := [φ, ψ]) (.and_intro (by by_hyp) (by by_hyp))

example : (Ctx.empty.insert (.free 3) .Var).boxIn.RootFresh (.free 7) := by fresh

end ProofCheck

end V12M
