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
* `Acc' w w'`: `w'` is one level deeper, has one of the views, and holds everything necessary at
  `w` — the **proper** successors;
* `Chain n w w'`: `n` proper steps; `R w w'`: a chain, of length 0 only under T (the world itself)
  and of length at least 2 only under 4.  So `R` is reflexive under T and transitive under 4.  A
  successor's chain is as long as its depth difference (`Succ.chain`): 0 is the world itself
  (`Succ.self`), 1 a proper successor (`Succ.acc`), and a far successor is a successor of a proper
  successor (`Succ.split`).  The views along a chain embed into its last world (`Chain.le`).
* `extent w x`: the proper successors with the `◇_x` view that hold everything `□_x`-necessary at
  `w`.
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
structure RealDatum (L : WorldLang) (T : Set (L.sys.Sentence σ)) (x : VarSymb) where
  hT : ModalSys.T = true
  /-- The content type: any type, as `WFF.here`'s is (§10.16).  Weak T realises a witness too,
      whenever the theory says so; strong T only guarantees that there are enough of them. -/
  A : VarType
  i₀ : ℕ × ℕ
  /-- ⭐The content is an **address**, declared at `i₀` — naming (§2d).  Interpreting it is then a
      lookup (`interp_canon_eta`) rather than a recursive call at an unrelated type, which is what
      took the stage out of `interp_canon`'s measure and let the old `hstage` field go.  Every
      object has such a name: `Canon.exists_name`. -/
  b₀ : VarSymb
  hb₀ : (L.ctx i₀).ref b₀ = some A
  /-- ⭐The witness is declared at `◇A` **at that one stage** — where its content is declared too.
      Type uniqueness at every stage follows by monotonicity (`RealDatum.hdeclOf`), so the datum
      makes no claim about the stage order at all, which is what lets it be read off the theory
      (§2d, step 4). -/
  hd₀ : (L.ctx i₀).ref x = some (.VTypeDia A)
  /-- ⭐**The theory says the witness is realised by its content**: the single sentence at `i₀`,
      which is what `Proof.T_dia` hands over.  The readings at every later stage follow, because the
      atom is invariant (`RealDatum.hhereAt`), and `RealDatum.spec` — everything the content
      satisfies at a stage, the witness satisfies in its view — follows from those
      (`spec_of_here`). -/
  hhere : (⟨i₀, WFF.hereAt hT x hd₀ (Term.eta b₀ A hb₀)⟩ : L.sys.Sentence σ) ∈ T

/-- The content's annotation, as `Term.eta` builds it. -/
@[reducible] def RealDatum.a₀ {L : WorldLang} {T : Set (L.sys.Sentence σ)} {x : VarSymb}
    (d : RealDatum σ L T x) : Ann d.A := Ann.eta d.b₀ d.A

/-- ⭐The realising **term**: the content address's η-expansion.  Consumers use this as before; what
    changed is that it is an η-expansion by construction. -/
@[reducible] def RealDatum.t₀ {L : WorldLang} {T : Set (L.sys.Sentence σ)} {x : VarSymb}
    (d : RealDatum σ L T x) : Term σ (L.ctx d.i₀) d.A d.a₀ := Term.eta d.b₀ d.A d.hb₀
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
  /-- ⭐Strong T: every **declared address** is the content of some realised root.  This is what
      `posRet_exists` needs — every object of a domain is the content, at the world itself, of a
      possible object — and naming (`Canon.exists_name`) is what brings an arbitrary term into
      this form.  Mere *existence* of a datum is enough, and all three equations are between
      non-dependent data, because the content is an address (§2d, step 3) and because what the
      content denotes does not depend on which datum the world picks
      (`Canon.rden_datum_wd`, §2d step 4). -/
  realW : ModalSys.T = true → ModalSys.TStrong = true → ∀ (i : ℕ × ℕ) {A : VarType},
      A.diaFree = true → ∀ (v : VarSymb), (L.ctx i).ref v = some A →
      ∃ (y : VarSymb) (d : RealDatum σ L T y), d.A = A ∧ d.b₀ = v ∧ i ≤ d.i₀

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
theorem RealDatum.hdeclOf {L : WorldLang} {T : Set (L.sys.Sentence σ)} {x : VarSymb}
    (d : RealDatum σ L T x) (i : ℕ × ℕ)
    (hi : ∃ Y, (L.ctx i).ref x = some (.VTypeDia Y)) :
    (L.ctx i).ref x = some (.VTypeDia d.A) := by
  obtain ⟨Y, hY⟩ := hi
  have h₁ : (L.ctx (max i.1 d.i₀.1, max i.2 d.i₀.2)).ref x = some (.VTypeDia Y) :=
    (L.ctx_le (Prod.le_def.mpr ⟨le_max_left _ _, le_max_left _ _⟩)).ref hY
  have h₂ : (L.ctx (max i.1 d.i₀.1, max i.2 d.i₀.2)).ref x = some (.VTypeDia d.A) :=
    (L.ctx_le (Prod.le_def.mpr ⟨le_max_right _ _, le_max_right _ _⟩)).ref d.hd₀
  have hYA : Y = d.A := by
    have := h₁.symm.trans h₂
    simpa using this
  exact hYA ▸ hY

/-- ⭐The realisation reading at **every** later stage, from the single atom: a maximal consistent
    theory lifts a sentence to any later stage (`StageSys.IsMCS.mem_lift_iff`) and the atom is
    invariant under that lifting (`WFF.mono_hereAt_of_le`).  So "the theory says so at every stage"
    is nothing a datum has to carry. -/
theorem RealDatum.hhereAt {L : WorldLang} {T : Set (L.sys.Sentence σ)} {x : VarSymb}
    (d : RealDatum σ L T x) (hmcs : StageSys.IsMCS T) (i : ℕ × ℕ) (hi : d.i₀ ≤ i)
    (hd : (L.ctx i).ref x = some (.VTypeDia d.A)) :
    (⟨i, WFF.hereAt d.hT x hd
        (Term.mono (L.ctx_le hi) d.t₀)⟩ : L.sys.Sentence σ) ∈ T := by
  refine Eq.mp (congrArg (fun φ => (⟨i, φ⟩ : L.sys.Sentence σ) ∈ T) ?_)
    ((hmcs.mem_lift_iff hi).mpr d.hhere)
  exact WFF.mono_hereAt_of_le d.hT _ _ _ hd _

/-- The same, under the name the earlier `hdecl` field went by. -/
theorem RealDatum.declType {L : WorldLang} {T : Set (L.sys.Sentence σ)} {x : VarSymb}
    (d : RealDatum σ L T x) (i : ℕ × ℕ)
    (h : ∃ Y, (L.ctx i).ref x = some (.VTypeDia Y)) :
    (L.ctx i).ref x = some (.VTypeDia d.A) :=
  d.hdeclOf i h

/-- ⭐**The collapse**: `RealDatum.spec` is a *derivation* as soon as the theory itself says the
    witness is realised by `t₀`.  `Proof.here_introAt` turns the realisation reading of a view
    formula into the `◇` one, and a maximal consistent theory is closed under provability — so the
    field is not data the construction has to arrange, but a consequence of one sentence being in
    the theory.  At every `◇`-free content type, as `WFF.here` is (§2d). -/
theorem spec_of_here {L : WorldLang} {T : Set (L.sys.Sentence σ)} (hmcs : StageSys.IsMCS T)
    (hT : ModalSys.T = true) {x : VarSymb} {i₀ : ℕ × ℕ} {A : VarType} {a₀ : Ann A}
    (t₀ : Term σ (L.ctx i₀) A a₀)
    (hhere : ∀ (i : ℕ × ℕ) (hi : i₀ ≤ i) (hd : (L.ctx i).ref x = some (.VTypeDia A)),
      (⟨i, WFF.hereAt hT x hd (Term.mono (L.ctx_le hi) t₀)⟩ : L.sys.Sentence σ) ∈ T) :
    ∀ (i : ℕ × ℕ) (hi : i₀ ≤ i) (hd : (L.ctx i).ref x = some (.VTypeDia A))
      (χ : WFF σ ((L.ctx i).diaIn x) 0),
      (⟨i, WFF.realiseAtA hT x hd (Term.mono (L.ctx_le hi) t₀) χ⟩ : L.sys.Sentence σ) ∈ T →
      (⟨i, .dia x ⟨A, hd⟩ χ⟩ : L.sys.Sentence σ) ∈ T := by
  intro i hi hd χ hr
  refine hmcs.closed (StageSys.derives_of_mems
    (Δ := [WFF.hereAt hT x hd (Term.mono (L.ctx_le hi) t₀),
      WFF.realiseAtA hT x hd (Term.mono (L.ctx_le hi) t₀) χ]) ?_ ?_)
  · intro ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ'
    · exact hhere i hi hd
    · rw [List.mem_singleton.mp hψ']
      exact hr
  · exact ⟨Proof.here_introAtA hT x hd (Term.mono (L.ctx_le hi) t₀) χ
      (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩

/-- ⭐What used to be the `spec` field, now **derived** from the `Here` atom the datum carries: a
    maximal consistent theory closed under provability turns the realisation reading of a view
    formula into the `◇` one. -/
theorem RealDatum.spec {L : WorldLang} {T : Set (L.sys.Sentence σ)} {x : VarSymb}
    (d : RealDatum σ L T x) (hmcs : StageSys.IsMCS T) :
    ∀ (i : ℕ × ℕ) (hi : d.i₀ ≤ i) (hd : (L.ctx i).ref x = some (.VTypeDia d.A))
      (χ : WFF σ ((L.ctx i).diaIn x) 0),
      (⟨i, WFF.realiseAtA d.hT x hd (Term.mono (L.ctx_le hi) d.t₀) χ⟩ :
        L.sys.Sentence σ) ∈ T →
        (⟨i, .dia x ⟨d.A, hd⟩ χ⟩ : L.sys.Sentence σ) ∈ T :=
  spec_of_here hmcs d.hT d.t₀ (d.hhereAt hmcs)

/-! ## Realised witnesses (strong T) -/

namespace World

variable (w : World σ N₀)

open Classical in
/-- ⭐**Realisedness is read off the theory** (§2d, step 4), and at an **address** rather than a root
    (§2d, §9).  Every field of a `RealDatum` is a fact about the language and the theory — one
    stage's declarations and one `Here` atom — so a world realises `x` exactly when its theory says
    so, and nothing has to be *chosen* when the world is built.  A choice is still made here, among
    data the theory allows, and it is immaterial: `Canon.rden_datum_wd` says any two of them give
    the content the same denotation. -/
noncomputable def real (x : VarSymb) : Option (RealDatum σ w.L w.T x) :=
  if h : Nonempty (RealDatum σ w.L w.T x) then some h.some else none

/-- ⭐The addresses realised at `w`.  No wrapper is needed any more: a datum is indexed by the
    address itself, so the root and the equation the old `RealData` carried are gone. -/
def Realised (x : VarSymb) : Prop := (w.real x).isSome

variable {w}

/-- The realisation named at a realised address — determined by the theory, not chosen here. -/
noncomputable def Realised.data {x : VarSymb} (h : w.Realised x) : RealDatum σ w.L w.T x :=
  (w.real x).get h

theorem Realised.T {x : VarSymb} (h : w.Realised x) : ModalSys.T = true := h.data.hT

/-- What the world names at an address is what it realises there. -/
theorem realised_of_real {x : VarSymb} {d : RealDatum σ w.L w.T x} (hsome : w.real x = some d) :
    w.Realised x := by
  unfold Realised
  rw [hsome]
  rfl

/-- … by that datum. -/
theorem data_of_real {x : VarSymb} {d : RealDatum σ w.L w.T x} (hsome : w.real x = some d) :
    (realised_of_real hsome).data = d := by
  unfold Realised.data
  simp only [hsome]
  rfl

/-- ⭐**What the theory says, the world realises**: a datum for `x` — declarations and the `Here`
    atom at one stage — makes that address realised, and it is the only way realisedness is ever
    established. -/
theorem realised_of_datum {x : VarSymb} (d : RealDatum σ w.L w.T x) : w.Realised x :=
  realised_of_real (dif_pos (⟨d⟩ : Nonempty (RealDatum σ w.L w.T x)))

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

/-- Proper accessibility: one level deeper, with a view, holding everything necessary. -/
def Acc' (w w' : World σ N₀) : Prop :=
  w'.depth = w.depth + 1 ∧ (BoxView w w' ∨ ∃ x, DiaView x w w') ∧ BoxContents w w'

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


/-- The view of a stage embeds into the child's stage for it — `extent_le`'s content, from the view
    alone, for the places that have the `DiaView` rather than the membership. -/
theorem DiaView.leChild {x : VarSymb} {w w' : World σ N₀} (h : DiaView x w w') (i : ℕ × ℕ) :
    ((w.L.ctx i).diaIn x).Le (w'.L.ctx (childStage i)) :=
  h.le (le_max_left _ _) (le_max_right _ _) 0

/-- ⭐The extent of the possible object named by `x`: the proper successors with the `◇_x` view
    that hold everything `□_x`-necessary here and, under strong T, the world itself when `x` is
    realised. -/
def extent (w : World σ N₀) (x : VarSymb) : Set (Succ w) :=
  {w' | (w'.1.depth = w.depth + 1 ∧ DiaView x w w'.1 ∧ BoxxContents x w w'.1) ∨
    (w'.1 = w ∧ w.Realised x)}

/-- A member of the extent is the world itself or one level deeper. -/
theorem extent_cases {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x) :
    (w'.1.depth - w.depth = 1 ∧ DiaView x w w'.1 ∧ BoxxContents x w w'.1) ∨
      (w'.1.depth - w.depth = 0 ∧ w'.1 = w ∧ w.Realised x) := by
  rcases hw' with ⟨hd, hv, hb⟩ | ⟨he, hr⟩
  · exact Or.inl ⟨by omega, hv, hb⟩
  · exact Or.inr ⟨by rw [he]; omega, he, hr⟩

/-- A member of the extent one level deeper is a proper one. -/
theorem extent_proper {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth ≠ 0) :
    w'.1.depth - w.depth = 1 ∧ DiaView x w w'.1 ∧ BoxxContents x w w'.1 := by
  rcases extent_cases hw' with h | ⟨h, _⟩
  · exact h
  · exact absurd h hd

/-- A member of the extent at this depth is the world itself, and then `x` is realised. -/
theorem extent_self {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth = 0) : w'.1 = w ∧ w.Realised x := by
  rcases extent_cases hw' with ⟨h, _⟩ | ⟨_, h⟩
  · omega
  · exact h

theorem extent_dist {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth ≠ 0) : w'.1.depth - w.depth = 1 :=
  (extent_proper hw' hd).1

theorem extent_acc {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth ≠ 0) : Acc' w w'.1 :=
  w'.acc (extent_dist hw' hd)

theorem extent_le {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth ≠ 0) (i : ℕ × ℕ) :
    ((w.L.ctx i).diaIn x).Le (w'.1.L.ctx (childStage i)) :=
  (extent_proper hw' hd).2.1.le (le_max_left _ _) (le_max_right _ _) 0

/-- The world itself is in the extent of a realised address. -/
theorem self_mem_extent {w : World σ N₀} {x : VarSymb} (h : w.Realised x) :
    (⟨w, ⟨R.refl h.T w⟩⟩ : Succ w) ∈ extent w x :=
  Or.inr ⟨rfl, h⟩

end Canon

end V12M
