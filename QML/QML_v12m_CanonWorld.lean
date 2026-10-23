import QML.QML_v12m_HenkinFinal
import QML.QML_v12m_Soundness
import QML.QML_v12m_DiaAbs
import QML.QML_v12m_ViewFresh
import QML.QML_v12m_AbsRules

/-!
# QML v12m — the canonical model: worlds and accessibility

A **world** is a world language with a maximal consistent theory that has witnesses for its
existentials and counter-instances for its failing universals.  Its own variables are named by
its modal depth (`names N₀ d n = N₀ + ⟪d, n⟫`), so the variables of a world reached through a
modality are fresh for the world it was reached from.

* `BoxView w w'` / `DiaView x w w'`: the base of `w'` is the `□` / `◇_x` view of `w`'s language;
* `Acc' w w'`: `w'` is one level deeper, has one of the views, holds everything necessary at `w`
  and has `w` as its parent — the **proper** successors.  A world records its parent, so the
  worlds form a genuine tree: a chain is determined by its ends (`Chain.unique`), while
  accessibility stays a relation;
* `Chain n w w'`: `n` proper steps; `R w w'`: a chain, of length 0 only under T (the world itself)
  and of length at least 2 only under 4.  So `R` is reflexive under T and transitive under 4.  A
  successor's chain is as long as its depth difference (`Succ.chain`): 0 is the world itself
  (`Succ.self`), 1 a proper successor (`Succ.acc`), and a far successor is a successor of a proper
  successor (`Succ.split`).  The views along a chain embed into its last world (`Chain.le`).
* `extent w x`: the proper successors with the `◇_x` view that hold everything `□_x`-necessary at
  `w`, under strong T the world itself when `x` is realised, and under 4 without shapes the
  **kept** members: the members of `x.keep`'s extent at a proper successor (`KeepExt`).  Pulling
  the extent back along an arrow is then the extent of the kept address (`extent_keep`) — what
  makes `posKeep` definable — because a world's ancestors are unique.
-/

namespace V12M

namespace Canon

/-- The name of the `n`-th own variable of a world at modal depth `d`. -/
def names (N₀ d n : ℕ) : ℕ := N₀ + Nat.pair d n

theorem names_injective (N₀ d : ℕ) : Function.Injective (names N₀ d) :=
  fun _ _ h => (Nat.pair_eq_pair.mp (Nat.add_left_cancel h)).2

theorem names_ne {N₀ d d' n n' : ℕ} (h : d ≠ d') : names N₀ d n ≠ names N₀ d' n' :=
  fun he => h (Nat.pair_eq_pair.mp (Nat.add_left_cancel he)).1

end Canon

variable [ModalSys]

theorem CtxExpr.noProjLast : ∀ e : CtxExpr, e.denote.NoProjLast
  | .empty => fun _ _ h => by simp [CtxExpr.denote, Ctx.empty] at h
  | .insertFree e _ T => (CtxExpr.noProjLast e).insert _ T
  | .boxIn _ => Ctx.noProjLast_boxIn _
  | .diaIn _ x => Ctx.noProjLast_diaIn _ x

/-- ⭐**Every world context names no address at two view depths, with nothing extra to assume.**  A
    `WorldLang`'s bases are presented by construction (`WorldLang.basePres`) and the own-variable
    stages keep that (`Ctx.stagePresented`), so `Ctx.Presented.viewFresh` propagates through the
    whole canonical construction — children included — by instance resolution.  This is what lets a
    `◇` view be abstracted at an arbitrary declared address (§2d, §9): the collision that blocked it
    is ruled out by the naming discipline the presentation already carries. -/
theorem WorldLang.viewFresh (L : WorldLang) (i : ℕ × ℕ) : (L.ctx i).ViewFresh :=
  Ctx.Presented.viewFresh inferInstance

/-- Presented contexts have no visible address ending in a projection. -/
theorem Ctx.Presented.noProjLast (Γ : Ctx) [h : Γ.Presented] : Γ.NoProjLast :=
  h.denote_eq ▸ h.expr.noProjLast

/-- The `□` view taken `n` times, innermost first. -/
def Ctx.boxIter : ℕ → Ctx → Ctx
  | 0, Γ => Γ
  | n + 1, Γ => Ctx.boxIter n Γ.boxIn

theorem Ctx.Le.boxIter : ∀ (n : ℕ) {Γ Γ' : Ctx}, Γ.Le Γ' →
    (Ctx.boxIter n Γ).Le (Ctx.boxIter n Γ')
  | 0, _, _, h => h
  | n + 1, _, _, h => Ctx.Le.boxIter n h.boxIn

namespace Canon

variable (σ : Signature) (N₀ : ℕ)

/-- ⭐Strong T: the data making the **address** `x` a realised witness of the language `L` under the
    theory `T`.  Everything here is one stage's worth: at `i₀` the address is declared at `◇A`, its
    content address `b₀` is declared at `A`, and the theory contains the `Here` atom linking them.
    The readings at other stages (`hdeclOf`, `hhereAt`) and `spec` all follow — so a datum is
    exactly what the *theory* says at one stage, which is what `Proof.T_dia` puts there.

    ⭐It is indexed by an address rather than a root (§2d, §9): `WFF.here`'s subject is any `◇`-typed
    term, so the truth lemma meets `Term.diatm x hx s` at an arbitrary declared `x`, and the
    abstraction now works there (`WFF.diaAbsA`).  No freshness field is needed any more — what the
    root version demanded of its name, `Ctx.ViewFresh` gives for every address of a presented
    context. -/
structure RealDatum {I : Type} [Preorder I] (S : StageSys I) (T : Set (S.Sentence σ)) (x : VarSymb)
    where
  hT : ModalSys.T = true
  /-- The content type: any type, as `WFF.here`'s is (§10.16).  Weak T realises a witness too,
      whenever the theory says so; strong T only guarantees that there are enough of them. -/
  A : VarType
  i₀ : I
  /-- ⭐The content is an **address**, declared at `i₀` — naming (§2d).  Interpreting it is then a
      lookup (`interp_canon_eta`) rather than a recursive call at an unrelated type, which is what
      took the stage out of `interp_canon`'s measure and let the old `hstage` field go.  Any `Here`
      atom yields one: `here_name` and the witnessed theory (`Canon.realised_of_here`). -/
  b₀ : VarSymb
  hb₀ : (S.ctx i₀).ref b₀ = some A
  /-- ⭐The witness is declared at `◇A` **at that one stage** — where its content is declared too.
      Type uniqueness at every stage follows by monotonicity (`RealDatum.hdeclOf`), so the datum
      makes no claim about the stage order at all, which is what lets it be read off the theory
      (§2d, step 4). -/
  hd₀ : (S.ctx i₀).ref x = some (.VTypeDia A)
  /-- ⭐**The theory says the witness is realised by its content**: the single sentence at `i₀`,
      which is what `Proof.T_dia` hands over.  The readings at every later stage follow, because the
      atom is invariant (`RealDatum.hhereAt`), and `RealDatum.spec` — everything the content
      satisfies at a stage, the witness satisfies in its view — follows from those
      (`spec_of_here`). -/
  hhere : (⟨i₀, WFF.hereAt hT x hd₀ (Term.eta b₀ A hb₀)⟩ : S.Sentence σ) ∈ T

/-- The content's annotation, as `Term.eta` builds it. -/
@[reducible] def RealDatum.a₀ {I : Type} [Preorder I] {S : StageSys I} {T : Set (S.Sentence σ)}
    {x : VarSymb} (d : RealDatum σ S T x) : Ann d.A := Ann.eta d.b₀ d.A

/-- ⭐The realising **term**: the content address's η-expansion.  Consumers use this as before; what
    changed is that it is an η-expansion by construction. -/
@[reducible] def RealDatum.t₀ {I : Type} [Preorder I] {S : StageSys I} {T : Set (S.Sentence σ)}
    {x : VarSymb} (d : RealDatum σ S T x) : Term σ (S.ctx d.i₀) d.A d.a₀ := Term.eta d.b₀ d.A d.hb₀
/-- A world of the canonical model. -/
structure World where
  depth : ℕ
  L : WorldLang
  hρ : ∀ n, L.ρ n = names N₀ depth n
  hfresh : ∀ m d n, depth ≤ d → (L.base m).RootFresh (.free (names N₀ d n))
  T : Set (L.sys.Sentence σ)
  mcs : StageSys.IsMCS T
  /-- Henkin witnessing for `∃`, **at a declared root**: the chain witnesses an existential by
      declaring a fresh constant, and naming a term needs that root rather than a term
      (§2d).  The term-valued form is `World.exW_term`. -/
  exW : ∀ {i : ℕ × ℕ} {A : VarType} {ψ : WFF σ ((L.ctx i).insert (.bnd 0) A) 1},
    (⟨i, .ex A ψ⟩ : L.sys.Sentence σ) ∈ T →
    ∃ (i' : ℕ × ℕ) (hi : i ≤ i') (c : ℕ)
      (hc : (L.ctx i').ref (.root (.free c)) = some A),
      (⟨i', WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free c)) A hc)
        (WFF.mono ((L.ctx_le hi).insert (.bnd 0) A) ψ)⟩ : L.sys.Sentence σ) ∈ T
  allW : ∀ {i : ℕ × ℕ} {A : VarType} {ψ : WFF σ ((L.ctx i).insert (.bnd 0) A) 1},
    (⟨i, .all A ψ⟩ : L.sys.Sentence σ) ∉ T →
    ∃ (i' : ℕ × ℕ) (hi : i ≤ i') (a : Ann A) (t : Term σ (L.ctx i') A a),
      (⟨i', (WFF.instantiate Ctx.NoSlots.slots t
        (WFF.mono ((L.ctx_le hi).insert (.bnd 0) A) ψ)).neg⟩ : L.sys.Sentence σ) ∈ T
  /-- ⭐Strong T: every term, of **any** type, is the content of some witness by the theory's own
      word — a `Here` atom about a declared root, at some later stage.  This is what
      `posRet_exists` needs: the atom makes the witness realised (`Canon.realised_of_here`) and
      its content indistinguishable from the term's value (`DTerm.rel_of_coname`), so no naming is
      involved and `◇`-typed contents are covered too (§10.41). -/
  retW : (hT : ModalSys.T = true) → ModalSys.TStrong = true → ∀ (i : ℕ × ℕ) {A : VarType}
      {a : Ann A} (t : Term σ (L.ctx i) A a),
      ∃ (i' : ℕ × ℕ) (hi : i ≤ i') (y : VarSymb) (hy : (L.ctx i').ref y = some (.VTypeDia A)),
        (⟨i', WFF.hereAt hT y hy (Term.mono (L.ctx_le hi) t)⟩ : L.sys.Sentence σ) ∈ T
  /-- ⭐The world this one was built as a successor of, if any.  Recording it makes the worlds a
      genuine tree — a proper successor's parent is the world it succeeds (`Acc'`) — so a world's
      ancestors are unique and an arrow is determined by its ends, with accessibility still a
      relation.  This is what lets a possible object be kept along an arrow (docs §3 4). -/
  parent : Option World

variable {σ N₀}


/-- The term-valued form of `World.exW`: a declared root's η-expansion is a term.  This is what the
    truth lemma's `∃` case uses; the root itself is what naming needs. -/
theorem World.exW_term {w : World σ N₀} {i : ℕ × ℕ} {A : VarType}
    {ψ : WFF σ ((w.L.ctx i).insert (.bnd 0) A) 1}
    (h : (⟨i, .ex A ψ⟩ : w.L.sys.Sentence σ) ∈ w.T) :
    ∃ (i' : ℕ × ℕ) (hi : i ≤ i') (a : Ann A) (t : Term σ (w.L.ctx i') A a),
      (⟨i', WFF.instantiate Ctx.NoSlots.slots t
        (WFF.mono ((w.L.ctx_le hi).insert (.bnd 0) A) ψ)⟩ : w.L.sys.Sentence σ) ∈ w.T := by
  obtain ⟨i', hi, c, hc, hmem⟩ := w.exW h
  exact ⟨i', hi, _, Term.eta (.root (.free c)) A hc, hmem⟩
namespace World

/-- Names of deeper worlds are fresh at every stage. -/
theorem fresh_deeper (w : World σ N₀) {d : ℕ} (hd : w.depth < d) (n : ℕ) (i : ℕ × ℕ) :
    (w.L.ctx i).RootFresh (.free (names N₀ d n)) :=
  w.L.fresh_ctx_of (fun m => w.hfresh m d n hd.le)
    (fun n' => by
      rw [w.hρ]
      exact names_ne (Nat.ne_of_lt hd)) i

/-- An own variable is declared with its own type. -/
theorem ctx_ref_own (w : World σ N₀) {m j k : ℕ} (h : k < j) :
    (w.L.ctx (m, j)).ref (.root (.free (w.L.ρ k))) = some (w.L.τ k) :=
  Ctx.stage_ref_root w.L.ρ w.L.ρ_inj (fun n => w.L.fresh m n) h

/-- Declaring an own variable writes only at its root, so nothing else there is reachable. -/
theorem ctx_only_root (w : World σ N₀) {m j k : ℕ} :
    ∀ v : VarSymb, v.rt = .free (w.L.ρ k) → v ≠ .root (.free (w.L.ρ k)) →
      (w.L.ctx (m, j)) v = none :=
  Ctx.stage_only_root w.L.ρ w.L.ρ_inj (fun n => w.L.fresh m n) j

end World

/-- ⭐**Type uniqueness**: the witness is declared at `◇A` wherever it is declared at a `◇`-type at
    all.  Contexts grow, so a declaration at `◇Y` and the one at `◇A` past `i₀` meet at a common
    stage, where they are the same declaration.  This — not the stage order — is what the `rden`
    layer asks of a datum, so that realisedness read off the theory can supply it (§2d, step 4). -/
theorem RealDatum.hdeclOf {I : Type} [Preorder I] [IsDirected I (· ≤ ·)] {S : StageSys I}
    {T : Set (S.Sentence σ)} {x : VarSymb} (d : RealDatum σ S T x) (i : I)
    (hi : ∃ Y, (S.ctx i).ref x = some (.VTypeDia Y)) :
    (S.ctx i).ref x = some (.VTypeDia d.A) := by
  obtain ⟨Y, hY⟩ := hi
  obtain ⟨k, hik, hdk⟩ := directed_of (· ≤ ·) i d.i₀
  have h₁ := (S.le hik).ref hY
  have h₂ := (S.le hdk).ref d.hd₀
  have hYA : Y = d.A := by
    have := h₁.symm.trans h₂
    simpa using this
  exact hYA ▸ hY

/-- ⭐The realisation reading at **every** later stage, from the single atom: a maximal consistent
    theory lifts a sentence to any later stage (`StageSys.IsMCS.mem_lift_iff`) and the atom is
    invariant under that lifting (`WFF.mono_hereAt_of_le`).  So "the theory says so at every stage"
    is nothing a datum has to carry. -/
theorem RealDatum.hhereAt {I : Type} [Preorder I] [IsDirected I (· ≤ ·)] {S : StageSys I}
    {T : Set (S.Sentence σ)} {x : VarSymb} (d : RealDatum σ S T x) (hmcs : StageSys.IsMCS T)
    (i : I) (hi : d.i₀ ≤ i) (hd : (S.ctx i).ref x = some (.VTypeDia d.A)) :
    (⟨i, WFF.hereAt d.hT x hd
        (Term.mono (S.le hi) d.t₀)⟩ : S.Sentence σ) ∈ T := by
  refine Eq.mp (congrArg (fun φ => (⟨i, φ⟩ : S.Sentence σ) ∈ T) ?_)
    ((hmcs.mem_lift_iff hi).mpr d.hhere)
  exact WFF.mono_hereAt_of_le d.hT _ _ _ hd _

/-- The same, under the name the earlier `hdecl` field went by. -/
theorem RealDatum.declType {I : Type} [Preorder I] [IsDirected I (· ≤ ·)] {S : StageSys I}
    {T : Set (S.Sentence σ)} {x : VarSymb} (d : RealDatum σ S T x) (i : I)
    (h : ∃ Y, (S.ctx i).ref x = some (.VTypeDia Y)) :
    (S.ctx i).ref x = some (.VTypeDia d.A) :=
  d.hdeclOf i h

/-- ⭐**The collapse**: `RealDatum.spec` is a *derivation* as soon as the theory itself says the
    witness is realised by `t₀`.  `Proof.here_introAt` turns the realisation reading of a view
    formula into the `◇` one, and a maximal consistent theory is closed under provability — so the
    field is not data the construction has to arrange, but a consequence of one sentence being in
    the theory.  At every `◇`-free content type, as `WFF.here` is (§2d). -/
theorem spec_of_here {I : Type} [Preorder I] {S : StageSys I} {T : Set (S.Sentence σ)}
    (hmcs : StageSys.IsMCS T) (hT : ModalSys.T = true) {x : VarSymb} {i₀ : I} {A : VarType}
    {a₀ : Ann A} (t₀ : Term σ (S.ctx i₀) A a₀)
    (hhere : ∀ (i : I) (hi : i₀ ≤ i) (hd : (S.ctx i).ref x = some (.VTypeDia A)),
      (⟨i, WFF.hereAt hT x hd (Term.mono (S.le hi) t₀)⟩ : S.Sentence σ) ∈ T) :
    ∀ (i : I) (hi : i₀ ≤ i) (hd : (S.ctx i).ref x = some (.VTypeDia A))
      (χ : WFF σ ((S.ctx i).diaIn x) 0),
      (⟨i, WFF.realiseAtA hT x hd (Term.mono (S.le hi) t₀) χ⟩ : S.Sentence σ) ∈ T →
      (⟨i, .dia x ⟨A, hd⟩ χ⟩ : S.Sentence σ) ∈ T := by
  intro i hi hd χ hr
  refine hmcs.closed (StageSys.derives_of_mems
    (Δ := [WFF.hereAt hT x hd (Term.mono (S.le hi) t₀),
      WFF.realiseAtA hT x hd (Term.mono (S.le hi) t₀) χ]) ?_ ?_)
  · intro ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ'
    · exact hhere i hi hd
    · rw [List.mem_singleton.mp hψ']
      exact hr
  · exact ⟨Proof.here_introAtA hT x hd (Term.mono (S.le hi) t₀) χ
      (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩

/-- ⭐What used to be the `spec` field, now **derived** from the `Here` atom the datum carries: a
    maximal consistent theory closed under provability turns the realisation reading of a view
    formula into the `◇` one. -/
theorem RealDatum.spec {I : Type} [Preorder I] [IsDirected I (· ≤ ·)] {S : StageSys I}
    {T : Set (S.Sentence σ)} {x : VarSymb} (d : RealDatum σ S T x) (hmcs : StageSys.IsMCS T) :
    ∀ (i : I) (hi : d.i₀ ≤ i) (hd : (S.ctx i).ref x = some (.VTypeDia d.A))
      (χ : WFF σ ((S.ctx i).diaIn x) 0),
      (⟨i, WFF.realiseAtA d.hT x hd (Term.mono (S.le hi) d.t₀) χ⟩ :
        S.Sentence σ) ∈ T →
        (⟨i, .dia x ⟨d.A, hd⟩ χ⟩ : S.Sentence σ) ∈ T :=
  spec_of_here hmcs d.hT d.t₀ (d.hhereAt hmcs)

/-! ## Realised witnesses (strong T) -/

namespace World

variable (w : World σ N₀)

open Classical in
/-- ⭐**Realisedness is read off the theory** (§2d, step 4), and at an **address** rather than a root
    (§2d, §9).  Every field of a `RealDatum` is a fact about the language and the theory — one
    stage's declarations and one `Here` atom — so a world realises `x` exactly when its theory says
    so, and nothing has to be *chosen* when the world is built.  A choice is still made here, among
    data the theory allows, and it is immaterial: any two of them give co-named contents, hence
    related ones (`DTerm.rel_of_coname`), and `Ind` is all that `Here` and strong T read. -/
noncomputable def real (x : VarSymb) : Option (RealDatum σ w.L.sys w.T x) :=
  if h : Nonempty (RealDatum σ w.L.sys w.T x) then some h.some else none

/-- ⭐The addresses realised at `w`.  No wrapper is needed any more: a datum is indexed by the
    address itself, so the root and the equation the old `RealData` carried are gone. -/
def Realised (x : VarSymb) : Prop := (w.real x).isSome

variable {w}

/-- The realisation named at a realised address — determined by the theory, not chosen here. -/
noncomputable def Realised.data {x : VarSymb} (h : w.Realised x) : RealDatum σ w.L.sys w.T x :=
  (w.real x).get h

theorem Realised.T {x : VarSymb} (h : w.Realised x) : ModalSys.T = true := h.data.hT

/-- What the world names at an address is what it realises there. -/
theorem realised_of_real {x : VarSymb} {d : RealDatum σ w.L.sys w.T x} (hsome : w.real x = some d) :
    w.Realised x := by
  unfold Realised
  rw [hsome]
  rfl

/-- … by that datum. -/
theorem data_of_real {x : VarSymb} {d : RealDatum σ w.L.sys w.T x} (hsome : w.real x = some d) :
    (realised_of_real hsome).data = d := by
  unfold Realised.data
  simp only [hsome]
  rfl

/-- ⭐**What the theory says, the world realises**: a datum for `x` — declarations and the `Here`
    atom at one stage — makes that address realised, and it is the only way realisedness is ever
    established. -/
theorem realised_of_datum {x : VarSymb} (d : RealDatum σ w.L.sys w.T x) : w.Realised x :=
  realised_of_real (dif_pos (⟨d⟩ : Nonempty (RealDatum σ w.L.sys w.T x)))

/-- Conversely, a realised address carries the datum the world names there. -/
theorem real_of_realised {x : VarSymb} (h : w.Realised x) : w.real x = some h.data :=
  (Option.some_get h).symm

/-! ## Theory membership at a stage -/

section Mem

variable {w : World σ N₀}

theorem mem_lift {i j : ℕ × ℕ} (h : i ≤ j) {φ : WFF σ (w.L.ctx i) 0} :
    (⟨i, φ⟩ : w.L.sys.Sentence σ) ∈ w.T ↔
      (⟨j, WFF.mono (w.L.ctx_le h) φ⟩ : w.L.sys.Sentence σ) ∈ w.T :=
  (w.mcs.mem_lift_iff h).symm

/-- Membership from a proof at one stage. -/
theorem mem_of_provable {i : ℕ × ℕ} {Δ : List (WFF σ (w.L.ctx i) 0)} {φ : WFF σ (w.L.ctx i) 0}
    (hΔ : ∀ ψ ∈ Δ, (⟨i, ψ⟩ : w.L.sys.Sentence σ) ∈ w.T) (p : Provable Δ φ) :
    (⟨i, φ⟩ : w.L.sys.Sentence σ) ∈ w.T :=
  w.mcs.closed (StageSys.derives_of_mems hΔ p)

end Mem
end World

/-! ## Views and accessibility -/

/-- The base of `w'` is the `□` view of `w`'s language. -/
def BoxView (w w' : World σ N₀) : Prop := ∀ m, w'.L.base m = (w.L.ctx (m, m)).boxIn

/-- The base of `w'` is the `◇_x` view of `w`'s language. -/
def DiaView (x : VarSymb) (w w' : World σ N₀) : Prop :=
  ∀ m, w'.L.base m = (w.L.ctx (m, m)).diaIn x

theorem BoxView.le {w w' : World σ N₀} (h : BoxView w w') {i : ℕ × ℕ} {k : ℕ} (h₁ : i.1 ≤ k)
    (h₂ : i.2 ≤ k) (j : ℕ) : (w.L.ctx i).boxIn.Le (w'.L.ctx (k, j)) := by
  have hb : (w.L.ctx i).boxIn.Le (w'.L.base k) := by
    rw [h k]
    exact (w.L.le_diag h₁ h₂).boxIn
  exact hb.trans (w'.L.base_le_ctx k j)

theorem DiaView.le {x : VarSymb} {w w' : World σ N₀} (h : DiaView x w w') {i : ℕ × ℕ} {k : ℕ}
    (h₁ : i.1 ≤ k) (h₂ : i.2 ≤ k) (j : ℕ) : ((w.L.ctx i).diaIn x).Le (w'.L.ctx (k, j)) := by
  have hb : ((w.L.ctx i).diaIn x).Le (w'.L.base k) := by
    rw [h k]
    exact (w.L.le_diag h₁ h₂).diaIn x
  exact hb.trans (w'.L.base_le_ctx k j)

theorem DiaView.le_boxIn {x : VarSymb} {w w' : World σ N₀} (h : DiaView x w w') {i : ℕ × ℕ}
    {k : ℕ} (h₁ : i.1 ≤ k) (h₂ : i.2 ≤ k) (j : ℕ) : (w.L.ctx i).boxIn.Le (w'.L.ctx (k, j)) :=
  (Ctx.le_boxIn_diaIn _ x).trans (h.le h₁ h₂ j)

/-- Everything necessary at `w` holds at `w'`. -/
def BoxContents (w w' : World σ N₀) : Prop :=
  ∀ (i : ℕ × ℕ) (χ : WFF σ (w.L.ctx i).boxIn 0) (j : ℕ × ℕ)
    (h : (w.L.ctx i).boxIn.Le (w'.L.ctx j)),
    (⟨i, .box χ⟩ : w.L.sys.Sentence σ) ∈ w.T → (⟨j, WFF.mono h χ⟩ : w'.L.sys.Sentence σ) ∈ w'.T

/-- Everything `□_x`-necessary at `w` holds at `w'`. -/
def BoxxContents (x : VarSymb) (w w' : World σ N₀) : Prop :=
  ∀ (i : ℕ × ℕ) (hx : ∃ X, (w.L.ctx i).ref x = some (.VTypeDia X))
    (χ : WFF σ ((w.L.ctx i).diaIn x) 0) (j : ℕ × ℕ) (h : ((w.L.ctx i).diaIn x).Le (w'.L.ctx j)),
    (⟨i, WFF.boxx x hx χ⟩ : w.L.sys.Sentence σ) ∈ w.T →
      (⟨j, WFF.mono h χ⟩ : w'.L.sys.Sentence σ) ∈ w'.T

/-- Proper accessibility: one level deeper, with a view, holding everything necessary, and built
    as a successor of `w`. -/
def Acc' (w w' : World σ N₀) : Prop :=
  w'.depth = w.depth + 1 ∧ (BoxView w w' ∨ ∃ x, DiaView x w w') ∧ BoxContents w w' ∧
    w'.parent = some w

/-- A proper successor has one parent. -/
theorem Acc'.unique {w w' v : World σ N₀} (h : Acc' w v) (h' : Acc' w' v) : w = w' :=
  Option.some_injective _ (h.2.2.2.symm.trans h'.2.2.2)

/-- The stage of a successor that contains the modal views of stage `i`. -/
def childStage (i : ℕ × ℕ) : ℕ × ℕ := (max i.1 i.2, 0)

/-- The stage reached after `n` proper steps. -/
def childIter : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, i => i
  | n + 1, i => childIter n (childStage i)

theorem Acc'.boxIn_le {w w' : World σ N₀} (h : Acc' w w') (i : ℕ × ℕ) :
    (w.L.ctx i).boxIn.Le (w'.L.ctx (childStage i)) := by
  rcases h.2.1 with hv | ⟨x, hv⟩
  · exact hv.le (le_max_left _ _) (le_max_right _ _) 0
  · exact hv.le_boxIn (le_max_left _ _) (le_max_right _ _) 0

/-- A chain of `n` proper steps, the first step first. -/
def Chain : ℕ → World σ N₀ → World σ N₀ → Prop
  | 0, w, w' => w' = w
  | n + 1, w, w' => ∃ u, Acc' w u ∧ Chain n u w'

theorem Chain.depth : ∀ {n : ℕ} {w w' : World σ N₀}, Chain n w w' → w'.depth = w.depth + n
  | 0, w, w', h => by
      subst h
      rfl
  | _ + 1, _, _, ⟨_, hu, hc⟩ => by
      rw [Chain.depth hc, hu.1]
      omega

theorem Chain.comp : ∀ {n m : ℕ} {w v s : World σ N₀}, Chain n w v → Chain m v s →
    Chain (m + n) w s
  | 0, _, w, v, s, h, hm => by
      subst h
      exact hm
  | _ + 1, _, _, _, _, ⟨u, hu, hc⟩, hm => ⟨u, hu, Chain.comp hc hm⟩

/-- The views along a chain embed into the stages of its last world. -/
theorem Chain.le : ∀ {n : ℕ} {w w' : World σ N₀}, Chain n w w' → ∀ {Γ : Ctx} {i : ℕ × ℕ},
    Γ.Le (w.L.ctx i) → (Ctx.boxIter n Γ).Le (w'.L.ctx (childIter n i))
  | 0, w, w', h, _, _, e => by
      subst h
      exact e
  | _ + 1, _, _, ⟨_, hu, hc⟩, _, i, e => Chain.le hc (e.boxIn.trans (hu.boxIn_le i))

/-- A chain splits at any point. -/
theorem Chain.split : ∀ {n m : ℕ} {w s : World σ N₀}, Chain (m + n) w s →
    ∃ v, Chain n w v ∧ Chain m v s
  | 0, _, w, _, h => ⟨w, rfl, h⟩
  | _ + 1, _, _, _, ⟨u, hu, hc⟩ => by
      obtain ⟨v, h₁, h₂⟩ := Chain.split hc
      exact ⟨v, ⟨u, hu, h₁⟩, h₂⟩

/-- The last step of a chain. -/
theorem Chain.last {n : ℕ} {w s : World σ N₀} (h : Chain (n + 1) w s) :
    ∃ v, Chain n w v ∧ Acc' v s := by
  obtain ⟨v, h₁, u, hu, rfl⟩ := Chain.split (n := n) (m := 1) (by rwa [Nat.add_comm] at h)
  exact ⟨v, h₁, hu⟩

/-- ⭐**A chain is determined by its end**: worlds record their parents, so a world's ancestor at
    each distance is unique. -/
theorem Chain.unique : ∀ {n : ℕ} {w w' s : World σ N₀}, Chain n w s → Chain n w' s → w = w'
  | 0, _, _, _, h, h' => h.symm.trans h'
  | _ + 1, _, _, _, h, h' => by
      obtain ⟨v, hv, hvs⟩ := h.last
      obtain ⟨v', hv', hvs'⟩ := h'.last
      obtain rfl := hvs.unique hvs'
      exact Chain.unique hv hv'

/-- ⭐Accessibility: a chain of proper steps — the empty chain under T, chains of two or more
    steps under 4. -/
def R (w w' : World σ N₀) : Prop :=
  ∃ n, Chain n w w' ∧ (n = 0 → ModalSys.T = true) ∧ (2 ≤ n → ModalSys.Four = true)

theorem R.refl (hT : ModalSys.T = true) (w : World σ N₀) : R w w :=
  ⟨0, rfl, fun _ => hT, fun h => absurd h (by omega)⟩

theorem R.of_acc {w w' : World σ N₀} (h : Acc' w w') : R w w' :=
  ⟨1, ⟨w', h, rfl⟩, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

theorem R.trans (hF : ModalSys.Four = true) {w v s : World σ N₀} : R w v → R v s → R w s
  | ⟨n, hn, h₀, _⟩, ⟨m, hm, _, _⟩ => ⟨m + n, hn.comp hm, fun h => h₀ (by omega), fun _ => hF⟩

/-- The successors of a world. -/
abbrev Succ (w : World σ N₀) : Type := Σ w' : World σ N₀, PLift (R w w')

/-- A successor is reached by a chain as long as the depth difference. -/
theorem Succ.chain {w : World σ N₀} (w' : Succ w) :
    Chain (w'.1.depth - w.depth) w w'.1 ∧ (w'.1.depth - w.depth = 0 → ModalSys.T = true) ∧
      (2 ≤ w'.1.depth - w.depth → ModalSys.Four = true) := by
  obtain ⟨n, hn, h₀, h₂⟩ := w'.2.down
  have e : w'.1.depth - w.depth = n := by
    rw [hn.depth]
    omega
  rw [e]
  exact ⟨hn, h₀, h₂⟩

/-- A successor at the same depth is the world itself. -/
theorem Succ.self {w : World σ N₀} (w' : Succ w) (h : w'.1.depth - w.depth = 0) :
    ModalSys.T = true ∧ w'.1 = w := by
  obtain ⟨hc, h₀, _⟩ := w'.chain
  rw [h] at hc
  exact ⟨h₀ h, hc⟩

/-- A successor one level deeper is proper. -/
theorem Succ.acc {w : World σ N₀} (w' : Succ w) (h : w'.1.depth - w.depth = 1) : Acc' w w'.1 := by
  have hc := w'.chain.1
  rw [h] at hc
  obtain ⟨u, hu, rfl⟩ := hc
  exact hu

/-- A successor more than one level deeper exists only under 4. -/
theorem Succ.four {w : World σ N₀} (w' : Succ w) {d : ℕ} (h : w'.1.depth - w.depth = d + 1) :
    d ≠ 0 → ModalSys.Four = true :=
  fun hd => w'.chain.2.2 (by omega)

theorem Succ.chainLe {w : World σ N₀} (w' : Succ w) {d : ℕ} (h : w'.1.depth - w.depth = d + 1)
    {Γ : Ctx} {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) :
    (Ctx.boxIter (d + 1) Γ).Le (w'.1.L.ctx (childIter (d + 1) i)) := by
  have hc := w'.chain.1
  rw [h] at hc
  exact hc.le e

/-- A far successor is a successor of a proper successor. -/
theorem Succ.split {w : World σ N₀} (w' : Succ w) {d : ℕ} (h : w'.1.depth - w.depth = d + 2) :
    ∃ (u : World σ N₀) (_ : Acc' w u) (_ : R u w'.1), w'.1.depth - u.depth = d + 1 := by
  obtain ⟨hc, _, h₂⟩ := w'.chain
  rw [h] at hc
  obtain ⟨u, hu, hc'⟩ := hc
  refine ⟨u, hu, ⟨d + 1, hc', fun h => absurd h (by omega), fun _ => h₂ (by omega)⟩, ?_⟩
  rw [hc'.depth, hu.1]
  omega

/-- Under T, any deeper successor is a successor of a proper successor. -/
theorem Succ.split₁ (hT : ModalSys.T = true) {w : World σ N₀} (w' : Succ w) {d : ℕ}
    (h : w'.1.depth - w.depth = d + 1) :
    ∃ (u : World σ N₀) (_ : Acc' w u) (_ : R u w'.1), w'.1.depth - u.depth = d := by
  obtain ⟨hc, _, h₂⟩ := w'.chain
  rw [h] at hc
  obtain ⟨u, hu, hc'⟩ := hc
  refine ⟨u, hu, ⟨d, hc', fun _ => hT, fun _ => h₂ (by omega)⟩, ?_⟩
  rw [hc'.depth, hu.1]
  omega


/-- The view of a stage embeds into the child's stage for it — `extent_le`'s content, from the view
    alone, for the places that have the `DiaView` rather than the membership. -/
theorem DiaView.leChild {x : VarSymb} {w w' : World σ N₀} (h : DiaView x w w') (i : ℕ × ℕ) :
    ((w.L.ctx i).diaIn x).Le (w'.L.ctx (childStage i)) :=
  h.le (le_max_left _ _) (le_max_right _ _) 0

/-- `keep` taken `n` times: where an address of a world is read `n` proper steps on. -/
def _root_.V12M.VarSymb.keepIter : ℕ → VarSymb → VarSymb
  | 0, v => v
  | n + 1, v => VarSymb.keepIter n (.step v .keep)

/-- Possible objects are kept `k` times: none for `k = 0`, under 4 otherwise. -/
abbrev KeepOK (k : ℕ) : Prop := k ≠ 0 → ModalSys.Four = true

/-- A `◇` entry kept `n` times is a `◇` entry `n` views further in. -/
theorem _root_.V12M.Ctx.ref_keepIter : ∀ (n : ℕ), KeepOK n → ∀ {Γ : Ctx} {x : VarSymb}
    {X : VarType}, Γ.ref x = some (.VTypeDia X) →
      (Ctx.boxIter n Γ).ref (VarSymb.keepIter n x) = some (.VTypeDia X)
  | 0, _, _, _, _, h => h
  | n + 1, hK, _, _, _, h =>
      Ctx.ref_keepIter n (fun _ => hK (Nat.succ_ne_zero n))
        (Ctx.ref_keep_of' (hK (Nat.succ_ne_zero n)) h VarType.keepable_dia)

/-- ⭐**T and 4 together.**  Then extents are read off realisation (`extent`, docs §3 4, "T + 4
    on paper" (b)). -/
abbrev TFour : Prop := ModalSys.T = true ∧ ModalSys.Four = true

/-- Under 4 but not T + 4, there is no T. -/
theorem T_false_of_not_tFour (hF : ModalSys.Four = true) (h4 : ¬TFour) : ModalSys.T = false := by
  cases hT : ModalSys.T
  · rfl
  · exact absurd ⟨hT, hF⟩ h4

/-- ⭐The members of `x`'s extent reached by keeping it `k` times: for `k = 0` the proper
    successors with the `◇_x` view that hold everything `□_x`-necessary, for `k + 1` the members
    of `x.keep`'s at a proper successor — `four_dia` puts everything `□_x`-necessary into
    them. -/
def KeepExt : ℕ → VarSymb → World σ N₀ → World σ N₀ → Prop
  | 0, x, w, b => Acc' w b ∧ DiaView x w b ∧ BoxxContents x w b
  | k + 1, x, w, b => ∃ u, Acc' w u ∧ KeepExt k (.step x .keep) u b

theorem KeepExt.chain : ∀ {k : ℕ} {x : VarSymb} {w b : World σ N₀}, KeepExt k x w b →
    Chain (k + 1) w b
  | 0, _, _, b, h => ⟨b, h.1, rfl⟩
  | _ + 1, _, _, _, ⟨u, hu, h⟩ => ⟨u, hu, KeepExt.chain h⟩

theorem KeepExt.depth {k : ℕ} {x : VarSymb} {w b : World σ N₀} (h : KeepExt k x w b) :
    b.depth = w.depth + (k + 1) :=
  h.chain.depth

/-- The view along a kept member: the `◇_{x.keep^k}` view `k` steps on. -/
theorem KeepExt.le : ∀ {k : ℕ} {x : VarSymb} {w b : World σ N₀}, KeepExt k x w b →
    ∀ {Γ : Ctx} {i : ℕ × ℕ}, Γ.Le (w.L.ctx i) →
      ((Ctx.boxIter k Γ).diaIn (VarSymb.keepIter k x)).Le (b.L.ctx (childIter (k + 1) i))
  | 0, x, _, _, h, _, _, e => (e.diaIn x).trans (h.2.1.le (le_max_left _ _) (le_max_right _ _) 0)
  | _ + 1, _, _, _, ⟨_, hu, h⟩, _, i, e => KeepExt.le h (e.boxIn.trans (hu.boxIn_le i))

/-- ⭐The extent of the possible object named by `x`.
    * Under T + 4, **by realisation**: the successors realising `x` kept as many times as they are
      deeper.  At the world itself this is `x` realised; `here_keep` puts every `◇_x`-child in
      (docs §3 4, "T + 4 on paper" (b)).
    * Otherwise: the proper successors with the `◇_x` view that hold everything `□_x`-necessary
      here; under T, the world itself when `x` is realised; and under 4, the kept members
      (`KeepExt`). -/
def extent (w : World σ N₀) (x : VarSymb) : Set (Succ w) :=
  if TFour then {w' | w'.1.Realised (VarSymb.keepIter (w'.1.depth - w.depth) x)}
  else {w' | (∃ k, KeepOK k ∧ KeepExt k x w w'.1) ∨ (w'.1 = w ∧ w.Realised x)}

theorem extent_of_not {w : World σ N₀} {x : VarSymb} (h4 : ¬TFour) :
    extent w x = {w' | (∃ k, KeepOK k ∧ KeepExt k x w w'.1) ∨ (w'.1 = w ∧ w.Realised x)} :=
  if_neg h4

/-- ⭐Under T + 4, membership is realisation of the kept address. -/
theorem mem_extent_tFour (h4 : TFour) {w : World σ N₀} {x : VarSymb} {w' : Succ w} :
    w' ∈ extent w x ↔ w'.1.Realised (VarSymb.keepIter (w'.1.depth - w.depth) x) := by
  rw [extent, if_pos h4]
  rfl

/-- A member of the extent is the world itself or a kept member as many levels deeper. -/
theorem extent_cases (h4 : ¬TFour) {w : World σ N₀} {x : VarSymb} {w' : Succ w}
    (hw' : w' ∈ extent w x) :
    (∃ k, w'.1.depth - w.depth = k + 1 ∧ KeepOK k ∧ KeepExt k x w w'.1) ∨
      (w'.1.depth - w.depth = 0 ∧ w'.1 = w ∧ w.Realised x) := by
  rw [extent_of_not h4] at hw'
  rcases hw' with ⟨k, hk, h⟩ | ⟨he, hr⟩
  · exact Or.inl ⟨k, by rw [h.depth]; omega, hk, h⟩
  · exact Or.inr ⟨by rw [he]; omega, he, hr⟩

/-- A member of the extent `k + 1` levels deeper is kept `k` times. -/
theorem extent_far (h4 : ¬TFour) {w : World σ N₀} {x : VarSymb} {w' : Succ w}
    (hw' : w' ∈ extent w x) {k : ℕ} (hd : w'.1.depth - w.depth = k + 1) :
    KeepOK k ∧ KeepExt k x w w'.1 := by
  rcases extent_cases h4 hw' with ⟨k', hd', hk, h⟩ | ⟨h, _⟩
  · obtain rfl : k' = k := by omega
    exact ⟨hk, h⟩
  · omega

/-- A member of the extent one level deeper is a proper one. -/
theorem extent_proper (h4 : ¬TFour) {w : World σ N₀} {x : VarSymb} {w' : Succ w}
    (hw' : w' ∈ extent w x) (hd : w'.1.depth - w.depth = 1) :
    Acc' w w'.1 ∧ DiaView x w w'.1 ∧ BoxxContents x w w'.1 :=
  (extent_far h4 hw' (k := 0) hd).2

/-- A member of the extent at this depth is the world itself, and then `x` is realised. -/
theorem extent_self {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth = 0) : w'.1 = w ∧ w.Realised x := by
  by_cases h4 : TFour
  · have hr := (mem_extent_tFour h4).mp hw'
    rw [hd] at hr
    obtain ⟨w₁, hw₁⟩ := w'
    obtain ⟨_, he⟩ := Succ.self ⟨w₁, hw₁⟩ hd
    change w₁ = w at he
    subst he
    exact ⟨rfl, hr⟩
  · rcases extent_cases h4 hw' with ⟨_, h, _⟩ | ⟨_, h⟩
    · omega
    · exact h

theorem extent_le (h4 : ¬TFour) {w : World σ N₀} {x : VarSymb} {w' : Succ w}
    (hw' : w' ∈ extent w x) (hd : w'.1.depth - w.depth = 1) (i : ℕ × ℕ) :
    ((w.L.ctx i).diaIn x).Le (w'.1.L.ctx (childStage i)) :=
  (extent_proper h4 hw' hd).2.1.le (le_max_left _ _) (le_max_right _ _) 0

/-- The view along a member `k + 1` levels deeper. -/
theorem extent_leK (h4 : ¬TFour) {w : World σ N₀} {x : VarSymb} {w' : Succ w}
    (hw' : w' ∈ extent w x) {k : ℕ} (hd : w'.1.depth - w.depth = k + 1) {Γ : Ctx} {i : ℕ × ℕ}
    (e : Γ.Le (w.L.ctx i)) :
    ((Ctx.boxIter k Γ).diaIn (VarSymb.keepIter k x)).Le (w'.1.L.ctx (childIter (k + 1) i)) :=
  (extent_far h4 hw' hd).2.le e

/-- A kept member is in the extent. -/
theorem mem_extent_of_keep (h4 : ¬TFour) {w : World σ N₀} {x : VarSymb} {k : ℕ} (hk : KeepOK k)
    {w' : Succ w} (h : KeepExt k x w w'.1) : w' ∈ extent w x := by
  rw [extent_of_not h4]
  exact Or.inl ⟨k, hk, h⟩

/-- ⭐**Keeping an extent along a proper step** (docs §3 4): the members of `x`'s extent past a
    proper successor `u` are the extent there of `x.keep`.  Past `u` every member is kept, and it
    was kept through `u` itself — a world's ancestors are unique (`Chain.unique`).  Neither side
    has the world itself in it, as there is no T. -/
theorem extent_keep (hF : ModalSys.Four = true) (h4 : ¬TFour)
    {w u : World σ N₀} (hu : Acc' w u) {x : VarSymb} (b : Succ u) :
    (⟨b.1, ⟨R.trans hF (R.of_acc hu) b.2.down⟩⟩ : Succ w) ∈ extent w x ↔
      b ∈ extent u (.step x .keep) := by
  have hnT := T_false_of_not_tFour hF h4
  rw [extent_of_not h4, extent_of_not h4]
  obtain ⟨hc, h₀, _⟩ := b.chain
  have hdb : b.1.depth - u.depth ≠ 0 := fun h => by
    rw [h₀ h] at hnT
    cases hnT
  constructor
  · rintro (⟨k, -, h⟩ | ⟨-, hr⟩)
    · cases k with
      | zero =>
          have h₁ : b.1.depth = w.depth + (0 + 1) := h.depth
          have := hu.1
          omega
      | succ k =>
          obtain ⟨u', hu', h'⟩ := h
          have e : b.1.depth - u.depth = k + 1 := by
            have h₁ : b.1.depth = u'.depth + (k + 1) := h'.depth
            have := hu.1
            have := hu'.1
            omega
          rw [e] at hc
          obtain rfl := h'.chain.unique hc
          exact Or.inl ⟨k, fun _ => hF, h'⟩
    · rw [hr.T] at hnT
      cases hnT
  · rintro (⟨k, -, h⟩ | ⟨-, hr⟩)
    · exact Or.inl ⟨k + 1, fun _ => hF, u, hu, h⟩
    · rw [hr.T] at hnT
      cases hnT

/-- ⭐**Under T + 4 the law is definitional**: past a proper successor `u`, both sides read
    realisation of one address, `keepIter (d + 1) x = keepIter d (x.keep)`. -/
theorem extent_keep_tFour (h4 : TFour) {w u : World σ N₀} (hu : Acc' w u) {x : VarSymb}
    (b : Succ u) :
    (⟨b.1, ⟨R.trans h4.2 (R.of_acc hu) b.2.down⟩⟩ : Succ w) ∈ extent w x ↔
      b ∈ extent u (.step x .keep) := by
  rw [mem_extent_tFour h4, mem_extent_tFour h4]
  have e : b.1.depth - w.depth = (b.1.depth - u.depth) + 1 := by
    have h₁ := b.chain.1.depth
    have h₂ := hu.1
    omega
  change b.1.Realised (VarSymb.keepIter (b.1.depth - w.depth) x) ↔ _
  rw [e]
  rfl

/-- Under T + 4, a member as many levels deeper as `d` realises `x` kept `d` times. -/
theorem extent_realised (h4 : TFour) {w : World σ N₀} {x : VarSymb} {w' : Succ w}
    (hm : w' ∈ extent w x) {d : ℕ} (hd : w'.1.depth - w.depth = d) :
    w'.1.Realised (VarSymb.keepIter d x) :=
  hd ▸ (mem_extent_tFour h4).mp hm

/-- The view `d` levels on, at a successor `d` levels deeper. -/
theorem Succ.chainLeAt {w : World σ N₀} (w' : Succ w) {d : ℕ} (hd : w'.1.depth - w.depth = d)
    {Γ : Ctx} {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) :
    (Ctx.boxIter d Γ).Le (w'.1.L.ctx (childIter d i)) :=
  (hd ▸ w'.chain.1).le e

/-- The world itself is in the extent of a realised address. -/
theorem self_mem_extent {w : World σ N₀} {x : VarSymb} (h : w.Realised x) :
    (⟨w, ⟨R.refl h.T w⟩⟩ : Succ w) ∈ extent w x := by
  by_cases h4 : TFour
  · refine (mem_extent_tFour h4).mpr ?_
    change w.Realised (VarSymb.keepIter (w.depth - w.depth) x)
    rw [Nat.sub_self]
    exact h
  · rw [extent_of_not h4]
    exact Or.inr ⟨rfl, h⟩

end Canon

end V12M
