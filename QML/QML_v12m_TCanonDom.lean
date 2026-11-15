import QML.QML_v12m_OCanonChild
import QML.QML_v12m_CanonFunc
import QML.QML_v12m_ReadNamesFunc

/-!
# QML v12m — the canonical tree with `Opt` on: domains and denotations

The successors of a world are its proper `Opt` children (`AccO`) and, under T, the world itself
(`RT`, docs §12.36); 4, B and 5 are off with `Opt`.  The self arrow is told apart by depth
(`SuccO.self`, `SuccO.acc`), as in the `Opt`-off tree.

* `Opened w w' x`: the child `w'` of `w` opened the witness `x` — its content `x.dia` is declared in
  `w'`'s base.  ⭐Opened at one stage means opened at every stage where `x` is a witness
  (`AccO.opened_at`): otherwise the child's theory says `¬◇⁰_x ⊤` there, which reopening refutes.
* `SelfIn w x`: under T, `x` is identity-present at `w` (`TCanon.IdPres`) and `w`'s stages declare
  no identity reading, so `x`'s content at the world itself is read at its **identity name**
  (`selfTerm`: the body collapsed onto the identity view and read at the name).
* `extentO w x`: the children that opened `x`, and the world itself when `SelfIn`.  The `◇_x` view
  of a stage sits in a child that opened `x` (`extentO_le`).
* `RDomO`, `rdenO`: raw objects (no shapes) and the denotation of a term at a world, with
  weakening (`rdenO_mono`) and stage independence (`rdenO_congr`).
-/

namespace V12M

set_option linter.unusedSectionVars false

variable [ModalSys]

namespace OCanon

open Canon

variable {σ : Signature} {N₀ : ℕ}

/-- The child `w'` of `w` **opened** the witness `x`: its content is declared in `w'`'s base. -/
def Opened (w w' : World σ N₀) (x : VarSymb) : Prop :=
  ∃ m X, (bview w m).wit x = some X ∧ w'.L.base m (.step x .dia) = some X

variable (hO) in
/-- ⭐A world **decides its witnesses**: at each base stage each witness is opened there (its
    content declared) or absent by the theory (`¬◇⁰_y ⊤`).  Children do (`AccO.decides`), and so
    must the root. -/
def DecidesO (hO : ModalSys.Opt = true) (w : World σ N₀) : Prop :=
  ∀ m y X (hX : (w.L.base m).wit y = some X), w.L.base m (.step y .dia) = some X ∨
    (⟨(m, 0), (WFF.optx hO .arrow y ⟨X, hX⟩ .top).neg⟩ : w.L.sys.Sentence σ) ∈ w.T

variable {hO : ModalSys.Opt = true}

theorem AccO.decides {w w' : World σ N₀} (h : AccO hO w w') : DecidesO hO w' :=
  fun m y X hX => h.decide m y X ((h.wit m y).symm.trans hX)

/-- ⭐**Opened at one stage, opened at all**: where `y` is a witness and not opened, a world that
    decides its witnesses says `¬◇⁰_y ⊤`, which reopening refutes at any stage that has `y`'s
    content. -/
theorem DecidesO.stable {w : World σ N₀} (hdec : DecidesO hO w) {y : VarSymb} {m m' : ℕ}
    {X₀ X : VarType} (h₀ : w.L.base m (.step y .dia) = some X₀)
    (hX : (w.L.base m').wit y = some X) : w.L.base m' (.step y .dia) = some X := by
  rcases hdec m' y X hX with h₁ | hneg
  · exact h₁
  exfalso
  have hK₀ : m ≤ max m' m := le_max_right _ _
  have hKm : m' ≤ max m' m := le_max_left _ _
  have hw : (w.L.ctx (max m' m, 0)).wit y = some X := (w.L.base_mono hKm).wit y X hX
  have hd : w.L.ctx (max m' m, 0) (.step y .dia) = some X := by
    have h₂ : w.L.ctx (max m' m, 0) (.step y .dia) = some X₀ := (w.L.base_mono hK₀) _ _ h₀
    rcases (w.L.ctx (max m' m, 0)).wit_dia y X hw with h | h
    · rw [h] at h₂
      cases h₂
    · exact h
  have hneg' := (World.mem_lift (w := w)
    (show ((m', 0) : ℕ × ℕ) ≤ (max m' m, 0) from ⟨hKm, le_rfl⟩)).mp hneg
  refine w.mcs.bot_not_mem (i := (max m' m, 0)) (World.mem_of_provable (Δ := [_])
    (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hneg') ⟨?_⟩)
  exact .imp_elim (Proof.lookup List.mem_cons_self)
    (Proof.opt_reopen hO .arrow y ⟨X, hw, hd⟩ (ψ := .top) .top_intro)

/-- A child that opened `x` has it opened at every stage of the parent's `□` view. -/
theorem AccO.opened_at {w w' : World σ N₀} (h : AccO hO w w') {x : VarSymb}
    (ho : Opened w w' x) {m : ℕ} {X : VarType} (hX : (bview w m).wit x = some X) :
    w'.L.base m (.step x .dia) = some X := by
  obtain ⟨m₀, X₀, -, hd₀⟩ := ho
  exact h.decides.stable hd₀ ((h.wit m x).trans hX)

/-- A proper child is one level deeper. -/
theorem AccO.depth_ne {w w' : World σ N₀} (h : AccO hO w w') : w'.depth - w.depth ≠ 0 := by
  have := h.depth
  omega

/-! ## No identity readings -/

/-- A world's stages declare no identity reading (no `at` step). -/
def StagesNoAt (w : World σ N₀) : Prop := ∀ i, (w.L.ctx i).NoAt

omit [ModalSys] in
theorem Ctx.NoAt.insert' {Γ : Ctx} (h : Γ.NoAt) (r : Root) (T : VarType) :
    (Γ.insert r T).NoAt := by
  intro v U hv
  by_cases hvr : v = .root r
  · subst hvr
    trivial
  · exact h v U (Ctx.insert_ne_some hv hvr)

omit [ModalSys] in
/-- The stages over a base declaring no identity reading declare none. -/
theorem Ctx.NoAt.stage' {B : Ctx} (h : B.NoAt) (τ : ℕ → VarType) (ρ : ℕ → ℕ) :
    ∀ k, (B.stage τ ρ k).NoAt
  | 0 => h
  | k + 1 => Ctx.NoAt.insert' (Ctx.NoAt.stage' h τ ρ k) _ _

/-- A `□` view of a context reaching no identity reading declares none. -/
theorem Ctx.RefNoAt.boxIn_noAt {Γ : Ctx} (h : Γ.RefNoAt) : Γ.boxIn.NoAt := by
  intro v T hv
  match v with
  | .step u .box => exact ⟨nofun, h u _ (Ctx.boxIn_box hv).2⟩
  | .step u .keep => exact ⟨nofun, h u _ (Ctx.boxIn_keep hv).2.1⟩
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv
  | .step _ .at => cases hv

theorem Ctx.NoAt.optIn' {Γ : Ctx} (h : Γ.NoAt) {y : VarSymb}
    (hy : ∀ X, Γ.wit y = some X → y.NoAt) : (Γ.optIn y).NoAt := by
  intro v T hv
  by_cases hvy : v = .step y .dia
  · subst hvy
    rcases hw : Γ.wit y with _ | X
    · rw [Ctx.optIn_content_none hw] at hv
      exact h _ _ hv
    · exact ⟨nofun, hy X hw⟩
  · rw [Ctx.optIn_ne hvy] at hv
    exact h v T hv

theorem Ctx.NoAt.optIns' {Γ : Ctx} (h : Γ.NoAt) (hy : ∀ y X, Γ.wit y = some X → y.NoAt) :
    ∀ L : List VarSymb, (Γ.optIns L).NoAt
  | [] => h
  | y :: L => Ctx.NoAt.optIn' (Ctx.NoAt.optIns' h hy L) fun X hX =>
      hy y X ((Ctx.optIns_wit Γ L y).symm.trans hX)

/-- The `□` view of a world's diagonal stage, with any witnesses opened, declares no identity
    reading when the world declares none. -/
theorem bview_optIns_noAt {w : World σ N₀} (hna : StagesNoAt w) (m : ℕ) (L : List VarSymb) :
    ((bview w m).optIns L).NoAt :=
  Ctx.NoAt.optIns' (Ctx.RefNoAt.boxIn_noAt (Ctx.RefNoAt.of_noAt (hna (m, m))))
    (fun y _ hy => Ctx.RefNoAt.of_noAt (hna (m, m)) y _ (Ctx.boxIn_wit.mp hy).2) L

/-! ## The arrows -/

variable (hO) in
/-- ⭐**The arrows of the tree with `Opt`**: a proper child (declaring no identity reading where its
    parent declares none), or under T the world itself. -/
def RT (w w' : World σ N₀) : Prop :=
  (AccO hO w w' ∧ (StagesNoAt w → StagesNoAt w')) ∨ (ModalSys.T = true ∧ w' = w)

variable (hO) in
/-- The successors of a world: its proper children and, under T, itself. -/
abbrev SuccO (w : World σ N₀) : Type := Σ w' : World σ N₀, PLift (RT hO w w')

/-- The arrow to a proper child. -/
abbrev SuccO.child {w w' : World σ N₀} (h : AccO hO w w') (hn : StagesNoAt w → StagesNoAt w') :
    SuccO hO w :=
  ⟨w', ⟨Or.inl ⟨h, hn⟩⟩⟩

/-- Under T, the arrow from a world to itself. -/
abbrev SuccO.selfArr (hT : ModalSys.T = true) (w : World σ N₀) : SuccO hO w :=
  ⟨w, ⟨Or.inr ⟨hT, rfl⟩⟩⟩

/-- ⭐A successor at the same depth is the world itself, under T. -/
theorem SuccO.self {w : World σ N₀} (w' : SuccO hO w) (h : w'.1.depth - w.depth = 0) :
    ModalSys.T = true ∧ w'.1 = w := by
  rcases w'.2.down with ha | hs
  · exact absurd h ha.1.depth_ne
  · exact hs

/-- ⭐A deeper successor is a proper child. -/
theorem SuccO.acc {w : World σ N₀} (w' : SuccO hO w) (h : w'.1.depth - w.depth ≠ 0) :
    AccO hO w w'.1 := by
  rcases w'.2.down with ha | ⟨_, he⟩
  · exact ha.1
  · exact (h (by rw [he, Nat.sub_self])).elim

/-- A deeper successor of a world declaring no identity reading declares none. -/
theorem SuccO.noAt {w : World σ N₀} (w' : SuccO hO w) (h : w'.1.depth - w.depth ≠ 0)
    (hna : StagesNoAt w) : StagesNoAt w'.1 := by
  rcases w'.2.down with ha | ⟨_, he⟩
  · exact ha.2 hna
  · exact (h (by rw [he, Nat.sub_self])).elim

/-! ## Children declare no identity reading -/

section Children

variable (hO) [Countable σ.FuncSyms] [Countable σ.RelSyms] (w : World σ N₀) {i : ℕ × ℕ}
  (χ : WFF σ (w.L.ctx i).boxIn 0) (hχ : (⟨i, .box χ⟩ : w.L.sys.Sentence σ) ∉ w.T)

/-- ⭐The `□`-failure child declares no identity reading where its parent declares none. -/
theorem child_noAt (hna : StagesNoAt w) : StagesNoAt (child hO w χ hχ) := fun k =>
  Ctx.NoAt.stage' (bview_optIns_noAt hna k.1 _) _ _ k.2

include hχ in
/-- ⭐**A non-necessary formula fails at some proper successor**, which declares no identity reading
    where its parent declares none. -/
theorem exists_box_failT :
    ∃ (w' : World σ N₀) (ha : AccO hO w w'), (StagesNoAt w → StagesNoAt w') ∧
      (⟨childStage i, WFF.mono (ha.boxIn_le i) χ⟩ : w'.L.sys.Sentence σ) ∉ w'.T :=
  ⟨child hO w χ hχ, child_acc hO w χ hχ, child_noAt hO w χ hχ, child_not hO w χ hχ⟩

end Children

/-- ⭐Under D every world has a proper successor (`D_box` refutes `□⊥`). -/
theorem exists_succT (hO : ModalSys.Opt = true) [Countable σ.FuncSyms] [Countable σ.RelSyms]
    (hD : ModalSys.D = true) (w : World σ N₀) :
    ∃ w' : World σ N₀, AccO hO w w' ∧ (StagesNoAt w → StagesNoAt w') := by
  have hnot : (⟨(0, 0), .box .bot⟩ : w.L.sys.Sentence σ) ∉ w.T := fun h =>
    w.mcs.bot_not_mem (World.mem_of_provable (Δ := [.box .bot])
      (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact h)
      ⟨Proof.D_box hD (Proof.lookup List.mem_cons_self)⟩)
  obtain ⟨w', ha, hn, -⟩ := exists_box_failT hO w (i := (0, 0)) .bot hnot
  exact ⟨w', ha, hn⟩

/-! ## Extents -/

variable (hO) in
/-- ⭐**`x` is realised at the world itself** (under T): identity-present, and the world declares
    no identity reading, so its content there is read at a name. -/
def SelfIn (w : World σ N₀) (x : VarSymb) : Prop :=
  ∃ hT : ModalSys.T = true, TCanon.IdPres hT hO w x ∧ StagesNoAt w

/-- ⭐**The extent of a witness**: the children that opened it, and the world itself when `x` is
    realised there. -/
def extentO (w : World σ N₀) (x : VarSymb) : Set (SuccO hO w) :=
  {w' | (AccO hO w w'.1 ∧ Opened w w'.1 x) ∨ (w'.1 = w ∧ SelfIn hO w x)}

/-- A deeper member of an extent is a child that opened the witness. -/
theorem extentO_child {w : World σ N₀} {x : VarSymb} {w' : SuccO hO w} (hm : w' ∈ extentO w x)
    (hd : w'.1.depth - w.depth ≠ 0) : AccO hO w w'.1 ∧ Opened w w'.1 x := by
  rcases hm with h | ⟨he, _⟩
  · exact h
  · exact (hd (by rw [he, Nat.sub_self])).elim

/-- A member at the same depth is the world itself, with the witness realised there. -/
theorem extentO_self {w : World σ N₀} {x : VarSymb} {w' : SuccO hO w} (hm : w' ∈ extentO w x)
    (hd : w'.1.depth - w.depth = 0) : w'.1 = w ∧ SelfIn hO w x := by
  rcases hm with ⟨ha, _⟩ | h
  · exact absurd hd ha.depth_ne
  · exact h

/-- The `◇_x` view of a stage sits in the child stage of a child that opened `x`: through the `□`
    view with `x` opened, its content declared there (`AccO.opened_at`). -/
theorem extentO_le {w w' : World σ N₀} {x : VarSymb} (ha : AccO hO w w') (ho : Opened w w' x)
    {Γ : Ctx} {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) :
    (Γ.diaIn x).Le (w'.L.ctx (childStage i)) := by
  have hM : (w.L.ctx i).boxIn.Le (bview w (max i.1 i.2)) := (le_diag_max w i).boxIn
  have hopen : ((w.L.ctx i).boxIn.optIns [x]).Le (w'.L.base (max i.1 i.2)) :=
    Ctx.optIns_le_of (hM.trans (ha.le _)) fun y hy X hX => by
      rw [List.mem_singleton.mp hy] at hX ⊢
      exact ha.opened_at ho (hM.wit x X hX)
  exact (e.diaIn x).trans ((Ctx.le_diaIn_boxIn_optIn' hO (hx.imp fun _ h => e.ref h)).trans
    hopen)

/-! ## Reading a possible term at the world itself -/

/-- The identity name chosen for a witness realised at the world itself. -/
noncomputable def SelfIn.name {w : World σ N₀} {x : VarSymb} (hs : SelfIn hO w x) :
    TCanon.IdName hs.1 hO w x :=
  hs.2.1.name

theorem SelfIn.decl {w : World σ N₀} {x : VarSymb} (hs : SelfIn hO w x) {j : ℕ × ℕ}
    (hj : hs.name.i₀ ≤ j) : (w.L.ctx j).ref x = some (.VTypeDia hs.name.A) :=
  (w.L.ctx_le (hs.name.hi.trans hj)).ref hs.name.hx

theorem SelfIn.declName {w : World σ N₀} {x : VarSymb} (hs : SelfIn hO w x) {j : ℕ × ℕ}
    (hj : hs.name.i₀ ≤ j) : (w.L.ctx j).ref (.root (.free hs.name.c)) = some hs.name.A :=
  (w.L.ctx_le hj).ref hs.name.hc

/-- ⭐**A possible term's body read at the world itself**, at a stage past the name: collapsed onto
    `x`'s identity view (`x.dia` to `x.at`), then read at the identity name (`x.at` to the name). -/
noncomputable def selfTermAt {w : World σ N₀} {x : VarSymb} (hs : SelfIn hO w x) {j : ℕ × ℕ}
    (hj : hs.name.i₀ ≤ j) {A : VarType} {a : Ann A} (t : Term σ ((w.L.ctx j).diaIn x) A a) :
    Σ b : Ann A, Term σ (w.L.ctx j) A b :=
  ⟨_, Term.readNames (TCanon.readsNameIn hs.1 hO (hs.2.2 j) (hs.decl hj) (hs.declName hj))
    (Term.collapse (Ctx.collapses_diaIn_optInT hs.1 hO _ (hs.decl hj)) t)⟩

/-- `selfTermAt` commutes with raising the stage. -/
theorem selfTermAt_mono {w : World σ N₀} {x : VarSymb} (hs : SelfIn hO w x) {j k : ℕ × ℕ}
    (hj : hs.name.i₀ ≤ j) (hk : hs.name.i₀ ≤ k) (hjk : j ≤ k) {A : VarType} {a : Ann A}
    (t : Term σ ((w.L.ctx j).diaIn x) A a) :
    Term.mono (w.L.ctx_le hjk) (selfTermAt hs hj t).2 =
      (selfTermAt hs hk (Term.mono ((w.L.ctx_le hjk).diaIn x) t)).2 := by
  change _ = Term.readNames _ (Term.collapse _ (Term.mono ((w.L.ctx_le hjk).diaIn x) t))
  rw [Term.collapse_mono (Ctx.collapses_diaIn_optInT hs.1 hO _ (hs.decl hj))
      (Ctx.collapses_diaIn_optInT hs.1 hO _ (hs.decl hk)) ((w.L.ctx_le hjk).diaIn x)
      ((w.L.ctx_le hjk).optInT x) t,
    Term.readNames_mono (TCanon.readsNameIn hs.1 hO (hs.2.2 j) (hs.decl hj) (hs.declName hj))
      (TCanon.readsNameIn hs.1 hO (hs.2.2 k) (hs.decl hk) (hs.declName hk))
      ((w.L.ctx_le hjk).optInT x) (w.L.ctx_le hjk)]
  rfl

/-- The body of a possible term of a stage, read at the world itself, at the stage joined with the
    name's. -/
noncomputable def selfTerm {w : World σ N₀} {x : VarSymb} (hs : SelfIn hO w x) {Γ : Ctx}
    {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) {A : VarType} {a : Ann A} (t : Term σ (Γ.diaIn x) A a) :
    Σ b : Ann A, Term σ (w.L.ctx (i ⊔ hs.name.i₀)) A b :=
  selfTermAt hs le_sup_right (Term.mono ((e.trans (w.L.ctx_le le_sup_left)).diaIn x) t)

/-- `selfTerm`, raised to a later stage, is `selfTermAt` there. -/
theorem selfTerm_mono {w : World σ N₀} {x : VarSymb} (hs : SelfIn hO w x) {Γ : Ctx}
    {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) {k : ℕ × ℕ} (hk : i ⊔ hs.name.i₀ ≤ k) {A : VarType}
    {a : Ann A} (t : Term σ (Γ.diaIn x) A a) :
    Term.mono (w.L.ctx_le hk) (selfTerm hs e t).2 =
      (selfTermAt hs (le_sup_right.trans hk)
        (Term.mono ((e.trans (w.L.ctx_le (le_sup_left.trans hk))).diaIn x) t)).2 := by
  unfold selfTerm
  rw [selfTermAt_mono hs le_sup_right (le_sup_right.trans hk) hk, Term.mono_mono]

/-! ## Raw objects and denotations -/

variable (hO) in
/-- Raw objects of a type at a world.  No shapes: with `Opt` on, `Here` is the identity view. -/
def RDomO : VarType → World σ N₀ → Type
  | .Var, w => w.D
  | .VTypeOne, _ => PUnit
  | .VTypeProd A B, w => RDomO A w × RDomO B w
  | .VTypeBox A, w => (w' : SuccO hO w) → RDomO A w'.1
  | .VTypeDia A, w => Σ E : Set (SuccO hO w), (w' : E) → RDomO A w'.1.1

variable (hO) in
/-- ⭐**The denotation of a term at a world**, computed at a stage containing its context: a
    necessary term its body at each child and, at the world itself, its body collapsed; a possible
    one its body at each child that opened the witness and, at the world itself, its body read at
    the identity name. -/
noncomputable def rdenO : {A : VarType} → {a : Ann A} → {Γ : Ctx} → (w : World σ N₀) →
    (i : ℕ × ℕ) → Γ.Le (w.L.ctx i) → Term σ Γ A a → RDomO hO A w
  | _, _, _, w, i, e, .var v hv => w.cls i (.var v (e.ref hv))
  | _, _, _, w, i, e, .func f => w.cls i (Term.mono e (.func f))
  | _, _, _, _, _, _, .unit => PUnit.unit
  | _, _, _, w, i, e, .pair s t => (rdenO w i e s, rdenO w i e t)
  | _, _, Γ, w, i, e, .boxtm t => fun w' =>
      match hd : w'.1.depth - w.depth with
      | 0 => rdenO w'.1 i (by rw [(w'.self hd).2]; exact e)
          (Term.collapse (Ctx.collapses_boxIn_self (w'.self hd).1 Γ) t)
      | _ + 1 => rdenO w'.1 (childStage i)
          (e.boxIn.trans ((w'.acc (by omega)).boxIn_le i)) t
  | _, _, _, w, i, e, .diatm x hx t =>
      ⟨extentO w x, fun w' =>
        match hd : w'.1.1.depth - w.depth with
        | 0 => (extentO_self w'.2 hd).1.symm ▸
            rdenO w (i ⊔ (extentO_self w'.2 hd).2.name.i₀) (Ctx.Le.refl _)
              (selfTerm (extentO_self w'.2 hd).2 e t).2
        | _ + 1 => rdenO w'.1.1 (childStage i)
            (extentO_le (extentO_child w'.2 (by omega)).1 (extentO_child w'.2 (by omega)).2 e hx)
            t⟩
  termination_by structural A => A

/-- ⭐At the world itself, a necessary term denotes its body collapsed. -/
theorem rdenO_boxtm_self {A : VarType} {a : Ann A} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ}
    (e : Γ.Le (w.L.ctx i)) (t : Term σ Γ.boxIn A a) (w' : SuccO hO w)
    (h : w'.1.depth - w.depth = 0) :
    rdenO hO w i e (.boxtm t) w' = rdenO hO w'.1 i (by rw [(w'.self h).2]; exact e)
      (Term.collapse (Ctx.collapses_boxIn_self (w'.self h).1 Γ) t) := by
  simp only [rdenO]
  split
  · rfl
  · omega

/-- ⭐At a proper child, a necessary term denotes its body there. -/
theorem rdenO_boxtm_acc {A : VarType} {a : Ann A} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ}
    (e : Γ.Le (w.L.ctx i)) (t : Term σ Γ.boxIn A a) (w' : SuccO hO w)
    (h : w'.1.depth - w.depth ≠ 0) :
    rdenO hO w i e (.boxtm t) w' =
      rdenO hO w'.1 (childStage i) (e.boxIn.trans ((w'.acc h).boxIn_le i)) t := by
  simp only [rdenO]
  split
  · omega
  · rfl

/-- ⭐At the world itself, a possible term whose witness is realised there denotes its body read at
    the identity name. -/
theorem rdenO_diatm_self {A : VarType} {a : Ann A} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ}
    (e : Γ.Le (w.L.ctx i)) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (t : Term σ (Γ.diaIn x) A a) (w' : extentO (hO := hO) w x)
    (hd : w'.1.1.depth - w.depth = 0) :
    (rdenO hO w i e (.diatm x hx t)).2 w' = (extentO_self w'.2 hd).1.symm ▸
      rdenO hO w (i ⊔ (extentO_self w'.2 hd).2.name.i₀) (Ctx.Le.refl _)
        (selfTerm (extentO_self w'.2 hd).2 e t).2 := by
  simp only [rdenO]
  split
  · rfl
  · omega

/-- ⭐At a child that opened the witness, a possible term denotes its body there. -/
theorem rdenO_diatm_acc {A : VarType} {a : Ann A} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ}
    (e : Γ.Le (w.L.ctx i)) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (t : Term σ (Γ.diaIn x) A a) (w' : extentO (hO := hO) w x)
    (hd : w'.1.1.depth - w.depth ≠ 0) :
    (rdenO hO w i e (.diatm x hx t)).2 w' = rdenO hO w'.1.1 (childStage i)
      (extentO_le (extentO_child w'.2 hd).1 (extentO_child w'.2 hd).2 e hx) t := by
  simp only [rdenO]
  split
  · omega
  · rfl

/-- The denotation commutes with weakening. -/
theorem rdenO_mono : ∀ {A : VarType} {a : Ann A} {Γ Γ' : Ctx} (h : Γ.Le Γ') (t : Term σ Γ A a)
    (w : World σ N₀) (i : ℕ × ℕ) (e : Γ'.Le (w.L.ctx i)),
    rdenO hO w i e (Term.mono h t) = rdenO hO w i (h.trans e) t
  | _, _, _, _, _, .var _ _, _, _, _ => rfl
  | _, _, _, _, h, .func f, w, i, e => by
      change w.cls i (Term.mono e (Term.mono h (.func f))) =
        w.cls i (Term.mono (h.trans e) (.func f))
      rw [Term.mono_mono]
  | _, _, _, _, _, .unit, _, _, _ => rfl
  | _, _, _, _, h, .pair s t, w, i, e => Prod.ext (rdenO_mono h s w i e) (rdenO_mono h t w i e)
  | _, _, Γ, Γ', h, .boxtm t, w, i, e => funext fun w' => by
      change rdenO hO w i e (.boxtm (Term.mono h.boxIn t)) w' =
        rdenO hO w i (h.trans e) (.boxtm t) w'
      by_cases hd : w'.1.depth - w.depth = 0
      · rw [rdenO_boxtm_self _ _ _ hd, rdenO_boxtm_self _ _ _ hd,
          Term.collapse_mono (Ctx.collapses_boxIn_self (w'.self hd).1 Γ)
            (Ctx.collapses_boxIn_self (w'.self hd).1 Γ') h.boxIn h t, rdenO_mono]
      · rw [rdenO_boxtm_acc _ _ _ hd, rdenO_boxtm_acc _ _ _ hd, rdenO_mono]
  | _, _, _, _, h, .diatm x hx t, w, i, e => by
      refine congrArg (Sigma.mk (extentO w x)) (funext fun w' => ?_)
      change (rdenO hO w i e (.diatm x (hx.imp fun _ hX => h.ref hX)
          (Term.mono (h.diaIn x) t))).2 w' = (rdenO hO w i (h.trans e) (.diatm x hx t)).2 w'
      by_cases hd : w'.1.1.depth - w.depth = 0
      · rw [rdenO_diatm_self _ _ _ _ hd, rdenO_diatm_self _ _ _ _ hd]
        congr 1
        change rdenO hO w _ _ (selfTermAt _ _ (Term.mono _ (Term.mono (h.diaIn x) t))).2 =
          rdenO hO w _ _ (selfTermAt _ _ (Term.mono _ t)).2
        rw [Term.mono_mono]
      · rw [rdenO_diatm_acc _ _ _ _ hd, rdenO_diatm_acc _ _ _ _ hd, rdenO_mono]
  termination_by structural A => A

/-- The denotation does not depend on the stage it is computed at. -/
theorem rdenO_congr : ∀ {A : VarType} {a : Ann A} {Γ : Ctx} (t : Term σ Γ A a)
    (w : World σ N₀) (i j : ℕ × ℕ) (e : Γ.Le (w.L.ctx i)) (e' : Γ.Le (w.L.ctx j)),
    rdenO hO w i e t = rdenO hO w j e' t
  | _, _, _, .var _ _, w, i, j, _, _ =>
      Quotient.sound (World.TEq_of_lift_eq (w := w) (le_sup_left (b := j))
        (le_sup_right (a := i)) rfl)
  | _, _, _, .func _, w, i, j, _, _ =>
      Quotient.sound (World.TEq_of_lift_eq (w := w) (le_sup_left (b := j))
        (le_sup_right (a := i)) ((Term.mono_mono _ _ _).trans (Term.mono_mono _ _ _).symm))
  | _, _, _, .unit, _, _, _, _, _ => rfl
  | _, _, _, .pair s t, w, i, j, e, e' =>
      Prod.ext (rdenO_congr s w i j e e') (rdenO_congr t w i j e e')
  | _, _, _, .boxtm t, w, i, j, e, e' => funext fun w' => by
      by_cases hd : w'.1.depth - w.depth = 0
      · rw [rdenO_boxtm_self _ _ _ hd, rdenO_boxtm_self _ _ _ hd, rdenO_congr]
      · rw [rdenO_boxtm_acc _ _ _ hd, rdenO_boxtm_acc _ _ _ hd, rdenO_congr]
  | _, _, _, .diatm x hx t, w, i, j, e, e' => by
      refine congrArg (Sigma.mk (extentO w x)) (funext fun w' => ?_)
      change (rdenO hO w i e (.diatm x hx t)).2 w' = (rdenO hO w j e' (.diatm x hx t)).2 w'
      by_cases hd : w'.1.1.depth - w.depth = 0
      · rw [rdenO_diatm_self _ _ _ _ hd, rdenO_diatm_self _ _ _ _ hd]
        congr 1
        set hs := (extentO_self w'.2 hd).2
        have hk₁ : i ⊔ hs.name.i₀ ≤ i ⊔ j ⊔ hs.name.i₀ :=
          sup_le_sup_right le_sup_left _
        have hk₂ : j ⊔ hs.name.i₀ ≤ i ⊔ j ⊔ hs.name.i₀ :=
          sup_le_sup_right le_sup_right _
        calc rdenO hO w _ (Ctx.Le.refl _) (selfTerm hs e t).2
            = rdenO hO w (i ⊔ j ⊔ hs.name.i₀) (Ctx.Le.refl _)
                (Term.mono (w.L.ctx_le hk₁) (selfTerm hs e t).2) :=
              (rdenO_congr _ _ _ _ _ _).trans (rdenO_mono _ _ _ _ _).symm
          _ = rdenO hO w (i ⊔ j ⊔ hs.name.i₀) (Ctx.Le.refl _)
                (Term.mono (w.L.ctx_le hk₂) (selfTerm hs e' t).2) := by
              rw [selfTerm_mono hs e hk₁, selfTerm_mono hs e' hk₂]
          _ = _ := (rdenO_mono _ _ _ _ _).trans (rdenO_congr _ _ _ _ _ _)
      · rw [rdenO_diatm_acc _ _ _ _ hd, rdenO_diatm_acc _ _ _ _ hd]
        exact rdenO_congr _ _ _ _ _ _
  termination_by structural A => A

/-- Stage and embedding both free: the denotation of a term depends only on the term. -/
theorem rdenO_mono' {A : VarType} {a : Ann A} {Γ Γ' : Ctx} (h : Γ.Le Γ') (t : Term σ Γ A a)
    (w : World σ N₀) (i j : ℕ × ℕ) (e : Γ'.Le (w.L.ctx i)) (e' : Γ.Le (w.L.ctx j)) :
    rdenO hO w i e (Term.mono h t) = rdenO hO w j e' t :=
  (rdenO_mono h t w i e).trans (rdenO_congr t w i j _ e')

/-- A base term denotes its class. -/
theorem rdenO_var_mono {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) :
    ∀ u : Term σ Γ .Var .var, rdenO hO w i e u = w.cls i (Term.mono e u)
  | .var _ _ => rfl
  | .func _ => rfl

theorem rdenO_varTerm {Γ : Ctx} (w : World σ N₀) (i : ℕ × ℕ) (e : Γ.Le (w.L.ctx i)) :
    ∀ p : (Σ b : Ann .Var, Term σ Γ .Var b), rdenO hO w i e (varTerm p) = rdenO hO w i e p.2
  | ⟨.var, _⟩ => rfl

theorem rdenO_var_cls {w : World σ N₀} {i : ℕ × ℕ} (t : Term σ (w.L.ctx i) .Var .var) :
    rdenO hO w i (Ctx.Le.refl _) t = w.cls i t := by
  rw [rdenO_var_mono, Term.mono_refl]

/-! ## Definable objects -/

/-- With `Opt` on, a flag that turns it off is absurd. -/
theorem _root_.V12M.ModalSys.opt_absurd (hO : ModalSys.Opt = true) (h : ModalSys.Opt = false) :
    False := by
  rw [hO] at h
  cases h

variable (hO) in
/-- ⭐The raw objects denoted by terms. -/
def DefinableO (A : VarType) (w : World σ N₀) (o : RDomO hO A w) : Prop :=
  ∃ (i : ℕ × ℕ) (a : Ann A) (t : Term σ (w.L.ctx i) A a), rdenO hO w i (Ctx.Le.refl _) t = o

theorem definableO_rden {A : VarType} {a : Ann A} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ}
    (e : Γ.Le (w.L.ctx i)) (t : Term σ Γ A a) : DefinableO hO A w (rdenO hO w i e t) :=
  ⟨i, a, Term.mono e t, by rw [rdenO_mono]⟩

theorem definableO_var {w : World σ N₀} (d : w.D) : DefinableO hO .Var w d :=
  Quotient.inductionOn d fun s => ⟨s.1, .var, s.2, rdenO_var_cls s.2⟩

theorem definableO_unit {w : World σ N₀} (o : RDomO hO .VTypeOne w) :
    DefinableO hO .VTypeOne w o :=
  ⟨(0, 0), .one, .unit, rfl⟩

theorem definableO_fst {A B : VarType} {w : World σ N₀} {o : RDomO hO (.VTypeProd A B) w}
    (h : DefinableO hO (.VTypeProd A B) w o) : DefinableO hO A w o.1 := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | pair s _ => exact ⟨i, _, s, rfl⟩

theorem definableO_snd {A B : VarType} {w : World σ N₀} {o : RDomO hO (.VTypeProd A B) w}
    (h : DefinableO hO (.VTypeProd A B) w o) : DefinableO hO B w o.2 := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | pair _ u => exact ⟨i, _, u, rfl⟩

theorem definableO_pair {A B : VarType} {w : World σ N₀} {o₁ : RDomO hO A w}
    {o₂ : RDomO hO B w} (h₁ : DefinableO hO A w o₁) (h₂ : DefinableO hO B w o₂) :
    DefinableO hO (.VTypeProd A B) w ((o₁, o₂) : RDomO hO (.VTypeProd A B) w) := by
  obtain ⟨i₁, a₁, t₁, rfl⟩ := h₁
  obtain ⟨i₂, a₂, t₂, rfl⟩ := h₂
  exact ⟨i₁ ⊔ i₂, _, .pair (w.liftT le_sup_left t₁) (w.liftT le_sup_right t₂),
    Prod.ext (rdenO_mono' _ _ _ _ _ _ _) (rdenO_mono' _ _ _ _ _ _ _)⟩

/-- A definable raw object transported along an equality of worlds is definable. -/
theorem definableO_cast {A : VarType} {w w' : World σ N₀} (h : w = w') {o : RDomO hO A w}
    (ho : DefinableO hO A w o) : DefinableO hO A w' (h ▸ o) := by
  subst h
  exact ho

theorem definableO_box_apply {A : VarType} {w : World σ N₀} {o : RDomO hO (.VTypeBox A) w}
    (h : DefinableO hO (.VTypeBox A) w o) (w' : SuccO hO w) : DefinableO hO A w'.1 (o w') := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | boxtm b =>
      by_cases hd : w'.1.depth - w.depth = 0
      · rw [rdenO_boxtm_self _ _ _ hd]
        exact definableO_rden _ _
      · rw [rdenO_boxtm_acc _ _ _ hd]
        exact definableO_rden _ _

theorem definableO_dia_apply {A : VarType} {w : World σ N₀} {o : RDomO hO (.VTypeDia A) w}
    (h : DefinableO hO (.VTypeDia A) w o) (w' : o.1) : DefinableO hO A w'.1.1 (o.2 w') := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | diatm x hx b =>
      by_cases hd : w'.1.1.depth - w.depth = 0
      · rw [rdenO_diatm_self _ _ _ _ hd]
        exact definableO_cast _ (definableO_rden _ _)
      · rw [rdenO_diatm_acc _ _ _ _ hd]
        exact definableO_rden _ _

/-! ## The function algebra on raw objects -/

variable (hO) in
/-- ⭐The function algebra on raw objects.  `extract` reads the self arrow; `dup` and `dkeep` need
    4, which is off. -/
noncomputable def rawEvalO :
    {A B : VarType} → GFunc σ A B → (w : World σ N₀) → RDomO hO A w → RDomO hO B w
  | _, _, .id _, _, o => o
  | _, _, .comp g f, w, o => rawEvalO g w (rawEvalO f w o)
  | _, _, .fst, _, o => o.1
  | _, _, .snd, _, o => o.2
  | _, _, .pair f g, w, o => (rawEvalO f w o, rawEvalO g w o)
  | _, _, .unit _, _, _ => PUnit.unit
  | _, _, .func f args, w, o => canonFunc w f (fun k => rawEvalO (args k) w o)
  | _, _, .boxMap f, _, o => fun w' => rawEvalO f w'.1 (o w')
  | _, _, .boxPair _ _, _, o => fun w' => (o.1 w', o.2 w')
  | _, _, .boxUnit, _, _ => fun _ => PUnit.unit
  | _, _, .diaMap f, _, o => ⟨o.1, fun w' => rawEvalO f w'.1.1 (o.2 w')⟩
  | _, _, .strength _ _, _, o => ⟨o.2.1, fun w' => (o.1 w'.1, o.2.2 w')⟩
  | _, _, .extract hT, w, o => o (SuccO.selfArr hT w)
  | _, _, .dup hF, _, _ => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim
  | _, _, .dkeep hF, _, _ => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim

/-- Evaluating a map commutes with transport along an equality of worlds. -/
theorem rawEvalO_transport {A B : VarType} (g : GFunc σ A B) {w₁ w₂ : World σ N₀} (h : w₁ = w₂)
    (o : RDomO hO A w₁) : rawEvalO hO g w₂ (h ▸ o) = h ▸ rawEvalO hO g w₁ o := by
  subst h
  rfl

theorem rdenO_sig {A : VarType} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ} {e : Γ.Le (w.L.ctx i)}
    {p q : Σ b : Ann A, Term σ Γ A b} (h : p = q) : rdenO hO w i e p.2 = rdenO hO w i e q.2 := by
  subst h
  rfl

/-- ⭐Reading a body at the world itself commutes with applying a definable map. -/
theorem selfTerm_applyG {w : World σ N₀} {x : VarSymb} (hs : SelfIn hO w x) {Γ : Ctx}
    {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) {A B : VarType} (g : GFunc σ A B) {a : Ann A}
    (t : Term σ (Γ.diaIn x) A a) :
    selfTerm hs e (applyG g t).2 = applyG g (selfTerm hs e t).2 := by
  simp only [selfTerm, selfTermAt]
  rw [applyG_readNames hO, applyG_collapse, applyG_mono]

/-- ⭐A necessary body moved into a `◇_x` view and read at the world itself denotes its collapse:
    reading at the name leaves it alone (it has no `at` step). -/
theorem rdenO_selfTerm_boxIn {w : World σ N₀} {x : VarSymb} (hs : SelfIn hO w x) {Γ : Ctx}
    {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType}
    {a : Ann A} (b : Term σ Γ.boxIn A a) :
    rdenO hO w (i ⊔ hs.name.i₀) (Ctx.Le.refl _)
        (selfTerm hs e (Term.mono (Ctx.le_boxIn_diaIn Γ x) b)).2 =
      rdenO hO w i e (Term.collapse (Ctx.collapses_boxIn_self hs.1 Γ) b) := by
  have e' : Γ.Le (w.L.ctx (i ⊔ hs.name.i₀)) := e.trans (w.L.ctx_le le_sup_left)
  have hna : Γ.RefNoAt := fun v T hv => Ctx.RefNoAt.of_noAt (hs.2.2 _) v T (e'.ref hv)
  have R₀ : Ctx.ReadsNames (TCanon.nameAt x hs.name.c) 0 Γ (w.L.ctx (i ⊔ hs.name.i₀)) := by
    refine Ctx.ReadsNames.of_raw (fun v T hlp hv => ?_) (fun y X hy => e'.wit y X hy)
      (fun _ y n hyn => ?_)
    · have hr : Γ.ref v = some T := (Ctx.ref_nonproj Γ hlp).trans hv
      rw [VarSymb.readNames_noAt (hna v T hr)]
      exact e'.ref hr
    · obtain ⟨rfl, rfl⟩ := TCanon.nameAt_eq hyn
      obtain ⟨X, hX⟩ := hx
      have h₁ := e'.ref hX
      rw [hs.decl le_sup_right] at h₁
      cases h₁
      exact ⟨_, hX, hs.declName le_sup_right⟩
  simp only [selfTerm, selfTermAt]
  rw [Term.mono_mono, Term.collapse_mono (Ctx.collapses_boxIn_self hs.1 Γ)
      (Ctx.collapses_diaIn_optInT hs.1 hO _ (hs.decl le_sup_right)) _
      (e'.trans (Ctx.le_optInT _ x)) b,
    Term.readNames_mono R₀ _ _ (Ctx.Le.refl _), rdenO_mono]
  exact (rdenO_sig (Term.readNames_noAt R₀ e' hna _)).trans (rdenO_mono' _ _ _ _ _ _ _)

/-- ⭐**Applying a map to a term is evaluating it on the denotation.** -/
theorem rdenO_applyG :
    ∀ {A B : VarType} (g : GFunc σ A B) {Γ : Ctx} {a : Ann A} (t : Term σ Γ A a)
      (w : World σ N₀) (i : ℕ × ℕ) (e : Γ.Le (w.L.ctx i)),
    rdenO hO w i e (applyG g t).2 = rawEvalO hO g w (rdenO hO w i e t)
  | _, _, .id _, _, _, _, _, _, _ => rfl
  | _, _, .comp g f, _, _, t, w, i, e =>
      (rdenO_applyG g _ w i e).trans (congrArg (rawEvalO hO g w) (rdenO_applyG f t w i e))
  | _, _, .fst, _, _, .pair _ _, _, _, _ => rfl
  | _, _, .snd, _, _, .pair _ _, _, _, _ => rfl
  | _, _, .pair f g, _, _, t, w, i, e =>
      Prod.ext (rdenO_applyG f t w i e) (rdenO_applyG g t w i e)
  | _, _, .unit _, _, _, _, _, _, _ => rfl
  | _, _, .func f args, _, _, t, w, i, e => by
      change rdenO hO w i e (.func _) =
        canonFunc w f (fun k => rawEvalO hO (args k) w (rdenO hO w i e t))
      have hk : (fun k => rawEvalO hO (args k) w (rdenO hO w i e t)) =
          fun k => w.cls i (Term.mono e (varTerm (applyG (args k) t))) := by
        funext k
        rw [← rdenO_applyG (args k) t w i e, ← rdenO_varTerm, rdenO_var_mono]
      rw [hk, canonFunc_cls, rdenO_var_mono, Term.mono_fill, Spine.mono_ofFn]
      rfl
  | _, _, .boxMap f, _, _, .boxtm b, w, i, e => funext fun w' => by
      change rdenO hO w i e (.boxtm (applyG f b).2) w' =
        rawEvalO hO f w'.1 (rdenO hO w i e (.boxtm b) w')
      by_cases hd : w'.1.depth - w.depth = 0
      · obtain ⟨⟨w₁, h₁⟩, rfl⟩ : ∃ w₁, w' = w₁ := ⟨w', rfl⟩
        obtain ⟨hT, hw⟩ := SuccO.self ⟨w₁, h₁⟩ hd
        change w₁ = w at hw
        subst hw
        rw [rdenO_boxtm_self _ _ _ hd, rdenO_boxtm_self _ _ _ hd, ← rdenO_applyG f,
          applyG_collapse]
      · rw [rdenO_boxtm_acc _ _ _ hd, rdenO_boxtm_acc _ _ _ hd]
        exact rdenO_applyG f b w'.1 _ _
  | _, _, .boxPair _ _, _, _, .pair (.boxtm b) (.boxtm c), w, i, e => funext fun w' => by
      change rdenO hO w i e (.boxtm (.pair b c)) w' =
        (rdenO hO w i e (.boxtm b) w', rdenO hO w i e (.boxtm c) w')
      by_cases hd : w'.1.depth - w.depth = 0
      · rw [rdenO_boxtm_self _ _ _ hd, rdenO_boxtm_self _ _ _ hd, rdenO_boxtm_self _ _ _ hd]
        rfl
      · rw [rdenO_boxtm_acc _ _ _ hd, rdenO_boxtm_acc _ _ _ hd, rdenO_boxtm_acc _ _ _ hd]
        rfl
  | _, _, .boxUnit, _, _, .unit, _, _, _ => funext fun _ => rfl
  | _, _, .diaMap f, _, _, .diatm x hx c, w, i, e => by
      refine congrArg (Sigma.mk (extentO w x)) (funext fun w' => ?_)
      change (rdenO hO w i e (.diatm x hx (applyG f c).2)).2 w' =
        rawEvalO hO f w'.1.1 ((rdenO hO w i e (.diatm x hx c)).2 w')
      by_cases hd : w'.1.1.depth - w.depth = 0
      · rw [rdenO_diatm_self _ _ _ _ hd, rdenO_diatm_self _ _ _ _ hd, rawEvalO_transport]
        congr 1
        rw [← rdenO_applyG f (selfTerm (extentO_self w'.2 hd).2 e c).2 w _ _]
        exact rdenO_sig (selfTerm_applyG _ e f c)
      · rw [rdenO_diatm_acc _ _ _ _ hd, rdenO_diatm_acc _ _ _ _ hd]
        exact rdenO_applyG f c w'.1.1 _ _
  | _, _, .strength _ _, Γ, _, .pair (.boxtm b) (.diatm x hx c), w, i, e => by
      refine congrArg (Sigma.mk (extentO w x)) (funext fun w' => ?_)
      change (rdenO hO w i e (.diatm x hx (.pair (Term.mono (Ctx.le_boxIn_diaIn Γ x) b) c))).2 w' =
        (rdenO hO w i e (.boxtm b) w'.1, (rdenO hO w i e (.diatm x hx c)).2 w')
      by_cases hd : w'.1.1.depth - w.depth = 0
      · obtain ⟨⟨w₁, h₁⟩, hm⟩ := w'
        obtain ⟨he, hs⟩ := extentO_self hm hd
        change w₁ = w at he
        subst he
        rw [rdenO_diatm_self _ _ _ _ hd, rdenO_diatm_self _ _ _ _ hd, rdenO_boxtm_self _ _ _ hd]
        exact Prod.ext (rdenO_selfTerm_boxIn hs e hx b) rfl
      · rw [rdenO_diatm_acc _ _ _ _ hd, rdenO_diatm_acc _ _ _ _ hd, rdenO_boxtm_acc _ _ _ hd]
        exact Prod.ext (rdenO_mono _ b _ _ _) rfl
  | _, _, .extract hT, _, _, .boxtm b, w, _, e =>
      (rdenO_boxtm_self e b (SuccO.selfArr hT w) (Nat.sub_self _)).symm
  | _, _, .dup hF, _, _, _, _, _, _ => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim
  | _, _, .dkeep hF, _, _, _, _, _, _ =>
      (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim

/-- ⭐Definable objects are closed under the function algebra. -/
theorem definableO_rawEval {A B : VarType} (g : GFunc σ A B) {w : World σ N₀}
    {o : RDomO hO A w} (h : DefinableO hO A w o) : DefinableO hO B w (rawEvalO hO g w o) := by
  obtain ⟨i, a, t, rfl⟩ := h
  exact ⟨i, _, (applyG g t).2, rdenO_applyG g t w i _⟩

end OCanon

end V12M
