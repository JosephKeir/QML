import QML.QML_v12m_Subst
import QML.QML_v12m_Presented

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

/-! ## Strong T: the two readings of a `□`-view formula with a hole

`ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1` is a formula of the `□` view with a hole for an object.
It is read either at the current world (`hereRead`, under weak T: the view collapses and the hole
takes a term) or inside a `◇_c` view (`viewRead`: the hole takes the witness content `c.dia`).
-/

/-- The `□`-view formula `ψ` read at the current world, with `t` in its hole. -/
def WFF.hereRead {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true) {A : VarType}
    {a : Ann A} (t : Term σ Γ A a) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) : WFF σ Γ 0 :=
  WFF.instantiate Ctx.NoSlots.slots t
    (WFF.collapse ((Ctx.collapses_boxIn_self hT Γ).insert
        ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) A)
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A) ψ)

/-- The `□`-view formula `ψ` read inside `◇_c`, with the witness content in its hole. -/
def WFF.viewRead {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (c : ℕ) (hc : Γ.RootFresh (.free c))
    (A : VarType) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    WFF σ ((Γ.insert (.free c) (.VTypeDia A)).diaIn (.root (.free c))) 0 :=
  WFF.renameRoot (.bnd 0) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0))
    ((Ctx.le_insert hc.root (.VTypeDia A)).boxIn.trans
      (Ctx.le_boxIn_diaIn _ (.root (.free c))))
    (.step (.root (.free c)) .dia)
    (Ctx.ref_diaIn_of (Ctx.ref_insert_root Γ (.free c) (.VTypeDia A)))
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A) Ctx.NoSlots.slots ψ

/-- One hypothesis of `T_dia`: for every value of the parameter `y : B`, what holds of `t` here
    holds of the witness content in `◇_c`.  The hole formula `ψ` may mention the parameter's
    box-components.  The parameter is bound *inside* the scope of `c`, which is what makes the
    witness uniform in it (`∃x ∀y`, not `∀y ∃x`); `B` = unit gives the unparameterised form. -/
def WFF.retHyp {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true) {A : VarType}
    {a : Ann A} (t : Term σ Γ A a) (c y : ℕ) (hc : Γ.RootFresh (.free c))
    (hy : Γ.RootFresh (.free y)) (hyc : y ≠ c) (B : VarType)
    (ψ : WFF σ ((Γ.insert (.free y) B).boxIn.insert (.bnd 0) A) 1) :
    WFF σ (Γ.insert (.free c) (.VTypeDia A)) 0 :=
  have hne : Root.free y ≠ Root.free c := fun h => hyc (Root.free.inj h)
  have hcy : (Γ.insert (.free y) B).RootFresh (.free c) := hc.insert_ne hne B
  WFF.all B (WFF.bindFree y (hy.insert_ne hne.symm (.VTypeDia A)) Ctx.NoSlots.slots B
    (WFF.mono (Ctx.insert_swap_le hne B (.VTypeDia A))
      (WFF.imp
        ((WFF.hereRead hT (Term.mono (Ctx.le_insert hy.root B) t) ψ).weaken hcy.root
          (.VTypeDia A))
        (.dia (.root (.free c)) ⟨A, Ctx.ref_insert_root _ (.free c) (.VTypeDia A)⟩
          (WFF.viewRead c hcy A ψ)))))

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
  /-- Every object has a possible object realised here.  The witness `c : ◇A` is fresh, and the
      subproof may use, for finitely many `□`-view formulas with a hole and a parameter, that for
      every value of the parameter what holds of `t` here holds of the witness content in `◇_c`
      (`WFF.retHyp`).  One parameter name `y` serves all the hypotheses; several parameters pack
      into a product type.  As only that direction is available, `◇_c` is only used positively;
      on paper this rule is equivalent to the positive-polarity schema
      `Φ⟨x := t⟩ ⊢ ∃x:◇A. Φ(x)`. -/
  | T_dia {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true) (hS : ModalSys.TStrong = true)
      (A : VarType) {a : Ann A} (t : Term σ Γ A a) (c y : ℕ) (hc : Γ.RootFresh (.free c))
      (hy : Γ.RootFresh (.free y)) (hyc : y ≠ c)
      {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0}
      (Ψ : List (Σ B : VarType, WFF σ ((Γ.insert (.free y) B).boxIn.insert (.bnd 0) A) 1)) :
      Proof σ (Γ.insert (.free c) (.VTypeDia A))
        (Ψ.map (fun ψ => WFF.retHyp hT t c y hc hy hyc ψ.1 ψ.2) ++
          Δ.map (WFF.weaken hc.root (.VTypeDia A)))
          (φ.weaken hc.root (.VTypeDia A)) →
      Proof σ Γ Δ φ
  -- Weak B
  /-- What is possibly necessary is true, `◇□ψ ⊢ ψ`, for a closed `ψ`: some accessible world
      makes `ψ` necessary, and an arrow leads back from it.  `ψ` must be closed because nothing
      of the origin's context can be read two levels in and back.  The familiar `ψ ⊢ □◇ψ` is
      derived from it (`Proof.B_box`). -/
  | B_dia {Γ : Ctx} {Δ : List (WFF σ Γ 0)} (hB : ModalSys.B = true) (ψ : WFF σ Ctx.empty 0) :
      Proof σ Γ Δ (WFF.diaBox (ψ.closed _)) → Proof σ Γ Δ (ψ.closed Γ)

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
    | exact Ctx.Presented.fresh _ (by decide)
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
