import QML.QML_v12m_GKNCut
import QML.QML_v12m_GKToND

/-!
# QML v12m — the formula translation of a tree sequent

A tree sequent is read, node by node, as a **refutation**: at a node its hypotheses and negated
conclusions, and for each child that child's reading behind the edge (`¬□¬` for a `□`-edge,
`◇_x` for a `◇_x`-edge), the node's births bound by `∃` (docs §12.49, `GKN → ND`).

* `conj`, `Seq.at` (a side's formulas at a node), `Tree.children`;
* `closeB` (the births, bound by `∃`), `pack` (behind the edge);
* ⭐`tr D Δ Θ d ρ` (the reading of the node `ρ`, `d` levels deep) and `Pc` (closed: births bound,
  over the edge's view of the parent's context); the root's is the sequent's refutation.
-/

namespace V12M

set_option linter.unusedSectionVars false

variable [ModalSys]

namespace GKN

variable {σ : Signature} {Γ₀ : Ctx}

/-! ## Conjunctions and sides at a node -/

/-- The conjunction of a list. -/
def conj {Γ : Ctx} : List (WFF σ Γ 0) → WFF σ Γ 0
  | [] => .top
  | φ :: L => φ.and (conj L)

theorem mono_conj {Γ Γ' : Ctx} (h : Γ.Le Γ') :
    ∀ L : List (WFF σ Γ 0), WFF.mono h (conj L) = conj (L.map (WFF.mono h))
  | [] => rfl
  | φ :: L => by
      change WFF.and (WFF.mono h φ) (WFF.mono h (conj L)) = _
      rw [mono_conj h L]
      rfl

/-- A side's formulas at a node. -/
def Seq.at {D : Tree} (L : Seq σ Γ₀ D) (ρ : Lab) : List (WFF σ (D.ctxAt Γ₀ ρ) 0) :=
  L.filterMap fun p =>
    if h : p.1 = ρ then some (WFF.mono (Ctx.le_of_eq (congrArg (D.ctxAt Γ₀) h)) p.2) else none

theorem Seq.mem_at {D : Tree} {L : Seq σ Γ₀ D} {ρ : Lab} {φ : WFF σ (D.ctxAt Γ₀ ρ) 0} :
    φ ∈ L.at ρ ↔ (⟨ρ, φ⟩ : LF σ Γ₀ D) ∈ L := by
  unfold Seq.at
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨ρ', ψ⟩, hp, he⟩
    dsimp only at he
    split at he
    · rename_i h
      cases he
      have e := LF.mono_eq (Γ₀ := Γ₀) (D := D) ψ h (Ctx.Le.refl _)
        (Ctx.le_of_eq (congrArg (D.ctxAt Γ₀) h))
      rw [WFF.mono_refl] at e
      rw [← e]
      exact hp
    · cases he
  · intro h
    refine ⟨_, h, ?_⟩
    rw [dif_pos rfl, WFF.mono_refl]

theorem Seq.at_cons_ne {D : Tree} {L : Seq σ Γ₀ D} {ρ : Lab} {p : LF σ Γ₀ D} (h : p.1 ≠ ρ) :
    Seq.at (p :: L) ρ = L.at ρ := by
  unfold Seq.at
  rw [List.filterMap_cons, dif_neg h]

theorem Seq.at_cons_self {D : Tree} {L : Seq σ Γ₀ D} {ρ : Lab} (φ : WFF σ (D.ctxAt Γ₀ ρ) 0) :
    Seq.at (⟨ρ, φ⟩ :: L : Seq σ Γ₀ D) ρ = φ :: L.at ρ := by
  unfold Seq.at
  rw [List.filterMap_cons, dif_pos rfl, WFF.mono_refl]

theorem Seq.at_mono {D D' : Tree} (hk : ∀ τ, (D.ctxAt Γ₀ τ).Le (D'.ctxAt Γ₀ τ))
    (L : Seq σ Γ₀ D) (ρ : Lab) : (Seq.mono hk L).at ρ = (L.at ρ).map (WFF.mono (hk ρ)) := by
  unfold Seq.at Seq.mono
  rw [List.filterMap_map, List.map_filterMap]
  refine List.filterMap_congr fun p _ => ?_
  simp only [Function.comp]
  split
  · rename_i h
    rw [Option.map_some, WFF.mono_mono, WFF.mono_mono]
  · rfl

/-! ## Children -/

/-- The children of a node: the indices of the edges into its child nodes. -/
def Tree.children (D : Tree) (ρ : Lab) : List ℕ :=
  (D.edges.filterMap fun e => match e.1 with
    | k :: ρ' => if ρ' = ρ then some k else none
    | [] => none).dedup

theorem Tree.mem_children {D : Tree} {ρ : Lab} {k : ℕ} :
    k ∈ D.children ρ ↔ D.edge (k :: ρ) ≠ none := by
  unfold Tree.children Tree.edge
  rw [List.mem_dedup, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hk⟩
    intro hn
    rw [Option.map_eq_none_iff, List.find?_eq_none] at hn
    have := hn e he
    obtain ⟨c, ek⟩ := e
    cases c with
    | nil => cases hk
    | cons k' ρ' =>
        dsimp only at hk
        split at hk
        · rename_i h
          cases hk
          subst h
          exact this (by simp)
        · cases hk
  · intro hn
    obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hn
    obtain ⟨x, hx, -⟩ := Option.map_eq_some_iff.mp he
    have hxm := List.mem_of_find?_eq_some hx
    have hx1 : x.1 = k :: ρ := by
      have := List.find?_some hx
      simpa using this
    refine ⟨x, hxm, ?_⟩
    rw [hx1]
    dsimp only
    rw [if_pos rfl]

/-! ## Births and edges -/

open Classical in
/-- The births bound by `∃`, the head innermost. -/
noncomputable def closeB {V : Ctx} : (L : List (Root × VarType)) → WFF σ (V.inserts L) 0 →
    WFF σ V 0
  | [], φ => φ
  | (.free u, T) :: L, φ =>
      closeB L (if h : (V.inserts L).RootFresh (.free u) ∧ (V.inserts L).SlotsFrom 0 then
        .ex T (WFF.bindFree u h.1 h.2 T φ) else .top)
  | (.bnd _, _) :: L, _ => closeB L .top

theorem closeB_cons {V : Ctx} {u : ℕ} {T : VarType} {L : List (Root × VarType)}
    (hu : (V.inserts L).RootFresh (.free u)) (hs : (V.inserts L).SlotsFrom 0)
    (φ : WFF σ (V.inserts ((.free u, T) :: L)) 0) :
    closeB ((.free u, T) :: L) φ = closeB L (.ex T (WFF.bindFree u hu hs T φ)) := by
  change closeB L _ = _
  rw [dif_pos ⟨hu, hs⟩]

open Classical in
/-- The openings closed by `◇⁰`, the head innermost (as `closeB` binds the births). -/
noncomputable def closeO {P : Ctx} :
    (L : List (WitKind × VarSymb)) → WFF σ (P.optInsK L) 0 → WFF σ P 0
  | [], φ => φ
  | o :: L, φ => closeO L (if h : ModalSys.Opt = true ∧ ∃ X, (P.optInsK L).witK o.1 o.2 = some X
      then .optx h.1 o.1 o.2 h.2 φ else .top)

open Classical in
theorem closeO_cons {P : Ctx} {κ : WitKind} {y : VarSymb} {L : List (WitKind × VarSymb)}
    (hO : ModalSys.Opt = true) (hy : ∃ X, (P.optInsK L).witK κ y = some X)
    (φ : WFF σ (P.optInsK ((κ, y) :: L)) 0) :
    closeO ((κ, y) :: L) φ = closeO L (.optx hO κ y hy φ) := by
  change closeO L (dite _ _ _) = _
  rw [dif_pos ⟨hO, hy⟩]

/-- A node's closure: its openings by `◇⁰`, then its births by `∃`. -/
noncomputable def closeN {V : Ctx} (B : List (Root × VarType)) (O : List (WitKind × VarSymb))
    (φ : WFF σ ((V.inserts B).optInsK O) 0) : WFF σ V 0 :=
  closeB B (closeO O φ)

open Classical in
/-- A child's reading behind its edge: `◇_x` for a `◇_x`-edge, `¬□¬` otherwise. -/
noncomputable def pack (D : Tree) (Γ : Ctx) (c : Lab) (φ : WFF σ (D.view c Γ) 0) : WFF σ Γ 0 :=
  match he : D.edge c with
  | some (.dia x) =>
      if hx : ∃ X, Γ.ref x = some (.VTypeDia X) then
        .dia x hx (WFF.mono (Ctx.le_of_eq (Tree.view_dia he)) φ)
      else .top
  | some .box => (WFF.box (Γ := Γ) (WFF.mono (Ctx.le_of_eq (Tree.view_box (Or.inr he))) φ).neg).neg
  | none => (WFF.box (Γ := Γ) (WFF.mono (Ctx.le_of_eq (Tree.view_box (Or.inl he))) φ).neg).neg

theorem pack_dia {D : Tree} {Γ : Ctx} {c : Lab} {x : VarSymb} (he : D.edge c = some (.dia x))
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (φ : WFF σ (D.view c Γ) 0) :
    pack D Γ c φ = .dia x hx (WFF.mono (Ctx.le_of_eq (Tree.view_dia he)) φ) := by
  unfold pack
  split
  · rename_i x' he'
    rw [he] at he'
    cases he'
    rw [dif_pos hx]
  · rename_i he'
    rw [he] at he'
    cases he'
  · rename_i he'
    rw [he] at he'
    cases he'

theorem pack_box {D : Tree} {Γ : Ctx} {c : Lab} (he : D.edge c = none ∨ D.edge c = some .box)
    (φ : WFF σ (D.view c Γ) 0) :
    pack D Γ c φ = (WFF.box (Γ := Γ) (WFF.mono (Ctx.le_of_eq (Tree.view_box he)) φ).neg).neg := by
  unfold pack
  split
  · rename_i x he'
    rcases he with he | he <;> rw [he] at he' <;> cases he'
  · rfl
  · rfl

/-! ## The reading of a tree sequent -/

/-- ⭐**The reading of a node**, `d` levels deep: its hypotheses and negated conclusions, and its
    children's readings behind their edges, each child's births bound. -/
noncomputable def tr (D : Tree) (Δ Θ : Seq σ Γ₀ D) : ℕ → (ρ : Lab) → WFF σ (D.ctxAt Γ₀ ρ) 0
  | 0, ρ => (conj (Δ.at ρ ++ (Θ.at ρ).map WFF.neg)).and .top
  | d + 1, ρ => (conj (Δ.at ρ ++ (Θ.at ρ).map WFF.neg)).and
      (conj ((D.children ρ).map fun k =>
        pack D (D.ctxAt Γ₀ ρ) (k :: ρ)
          (closeN (V := D.view (k :: ρ) (D.ctxAt Γ₀ ρ)) (D.birthsAt (k :: ρ))
            (D.opensAt (k :: ρ)) (tr D Δ Θ d (k :: ρ)))))

/-- The context a node's closed reading lives in: the end sequent's at the root, the edge's view
    of the parent's below. -/
def Vw (D : Tree) (Γ₀ : Ctx) : Lab → Ctx
  | [] => Γ₀
  | k :: ρ => D.view (k :: ρ) (D.ctxAt Γ₀ ρ)

/-- ⭐**The closed reading of a node**: its reading with its births bound. -/
noncomputable def Pc (D : Tree) (Δ Θ : Seq σ Γ₀ D) (d : ℕ) : (ρ : Lab) → WFF σ (Vw D Γ₀ ρ) 0
  | [] => closeN (V := Γ₀) (D.birthsAt []) (D.opensAt []) (tr D Δ Θ d [])
  | k :: ρ => closeN (V := D.view (k :: ρ) (D.ctxAt Γ₀ ρ)) (D.birthsAt (k :: ρ))
      (D.opensAt (k :: ρ)) (tr D Δ Θ d (k :: ρ))

theorem tr_succ (D : Tree) (Δ Θ : Seq σ Γ₀ D) (d : ℕ) (ρ : Lab) :
    tr D Δ Θ (d + 1) ρ = (conj (Δ.at ρ ++ (Θ.at ρ).map WFF.neg)).and
      (conj ((D.children ρ).map fun k => pack D (D.ctxAt Γ₀ ρ) (k :: ρ) (Pc D Δ Θ d (k :: ρ)))) :=
  rfl

theorem tr_zero (D : Tree) (Δ Θ : Seq σ Γ₀ D) (ρ : Lab) :
    tr D Δ Θ 0 ρ = (conj (Δ.at ρ ++ (Θ.at ρ).map WFF.neg)).and .top := rfl

end GKN

/-! ## Natural deduction for the readings -/

namespace GKN

open NDP

variable {σ : Signature}

section ND

variable {Γ : Ctx}

theorem conj_elim {H : List (WFF σ Γ 0)} :
    ∀ {L : List (WFF σ Γ 0)}, Provable H (conj L) → ∀ φ ∈ L, Provable H φ
  | [], _, _, h => absurd h List.not_mem_nil
  | _ :: _, p, φ, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact p.map .and_elim_l
      · exact conj_elim (p.map .and_elim_r) φ h

theorem conj_intro {H : List (WFF σ Γ 0)} :
    ∀ {L : List (WFF σ Γ 0)}, (∀ φ ∈ L, Provable H φ) → Provable H (conj L)
  | [], _ => ⟨.top_intro⟩
  | ψ :: _, h => by
      obtain ⟨p⟩ := h ψ List.mem_cons_self
      obtain ⟨q⟩ := conj_intro fun φ hφ => h φ (List.mem_cons_of_mem _ hφ)
      exact ⟨.and_intro p q⟩

theorem chain {H : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (p : Provable H φ)
    (q : Provable (φ :: H) ψ) : Provable H ψ :=
  mp (lam q) p

theorem or_cases {H : List (WFF σ Γ 0)} {φ ψ χ : WFF σ Γ 0} (p : Provable H (φ.or ψ))
    (q₁ : Provable (φ :: H) χ) (q₂ : Provable (ψ :: H) χ) : Provable H χ :=
  let ⟨p⟩ := p; let ⟨q₁⟩ := q₁; let ⟨q₂⟩ := q₂; ⟨.or_elim p q₁ q₂⟩

theorem orl {H : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (ψ : WFF σ Γ 0) (p : Provable H φ) :
    Provable H (φ.or ψ) :=
  p.map (.or_intro_l ψ)

theorem orr {H : List (WFF σ Γ 0)} (φ : WFF σ Γ 0) {ψ : WFF σ Γ 0} (p : Provable H ψ) :
    Provable H (φ.or ψ) :=
  p.map (.or_intro_r φ)

theorem dne {H : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (p : Provable H φ.neg.neg) : Provable H φ :=
  byContra (mp (sub (fun _ h => List.mem_cons_of_mem _ h) p) (lk List.mem_cons_self))

theorem botE {H : List (WFF σ Γ 0)} (φ : WFF σ Γ 0) (p : Provable H .bot) : Provable H φ :=
  p.map (.bot_elim φ)

/-- A `□`-view formula behind the edge: `¬□¬`. -/
abbrev dpk (A : WFF σ Γ.boxIn 0) : WFF σ Γ 0 := (WFF.box (Γ := Γ) A.neg).neg

/-- ⭐`¬□¬` is monotone and distributes over `∨`, with boxed side hypotheses. -/
theorem dpk_or {H₁ : List (WFF σ Γ.boxIn 0)} {A B₁ B₂ : WFF σ Γ.boxIn 0}
    (p : Provable (A :: H₁) (B₁.or B₂)) :
    Provable (dpk A :: H₁.map fun χ => WFF.box (Γ := Γ) χ) ((dpk B₁).or (dpk B₂)) := by
  refine byContra ?_
  have b₁ : Provable (((dpk B₁).or (dpk B₂)).neg ::
      (dpk A :: H₁.map fun χ => WFF.box (Γ := Γ) χ)) (WFF.box (Γ := Γ) B₁.neg) :=
    byContra (contra (List.mem_cons_of_mem _ List.mem_cons_self) (orl _ (lk List.mem_cons_self)))
  have b₂ : Provable (((dpk B₁).or (dpk B₂)).neg ::
      (dpk A :: H₁.map fun χ => WFF.box (Γ := Γ) χ)) (WFF.box (Γ := Γ) B₂.neg) :=
    byContra (contra (List.mem_cons_of_mem _ List.mem_cons_self) (orr _ (lk List.mem_cons_self)))
  have k : Provable (B₁.neg :: B₂.neg :: H₁) A.neg := by
    refine lam (or_cases (sub (by lsub) p) ?_ ?_)
    · exact contra (by simp) (lk List.mem_cons_self)
    · exact contra (by simp) (lk List.mem_cons_self)
  obtain ⟨k⟩ := k
  refine contra (List.mem_cons_of_mem _ List.mem_cons_self) (dis ⟨Proof.K_box k⟩ ?_)
  intro ℓ hℓ
  simp only [List.map_cons, List.mem_cons] at hℓ
  rcases hℓ with rfl | rfl | hℓ
  · exact b₁
  · exact b₂
  · exact lk (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hℓ))

/-- ⭐`◇_x` is monotone and distributes over `∨`, with `□_x` and `□` side hypotheses. -/
theorem dia_or (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    {Δ₁ : List (WFF σ Γ.boxIn 0)} {Δ₂ : List (WFF σ (Γ.diaIn x) 0)}
    {A B₁ B₂ : WFF σ (Γ.diaIn x) 0}
    (p : Provable (A :: (Δ₂ ++ Δ₁.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))) (B₁.or B₂)) :
    Provable (.dia x hx A :: (Δ₂.map (WFF.boxx x hx) ++ Δ₁.map fun χ => WFF.box (Γ := Γ) χ))
      ((WFF.dia x hx B₁).or (WFF.dia x hx B₂)) := by
  have k : Provable (A :: ((B₁.neg :: B₂.neg :: Δ₂) ++
      Δ₁.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))) .bot :=
    or_cases (sub (by lsub) p) (contra (by simp) (lk List.mem_cons_self))
      (contra (by simp) (lk List.mem_cons_self))
  obtain ⟨k⟩ := k
  refine byContra ((dis ⟨Proof.K_dia x hx (Δ₁ := Δ₁) (Δ₂ := B₁.neg :: B₂.neg :: Δ₂) k⟩ ?_).map
    (.dia_bot x hx))
  intro ℓ hℓ
  simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hℓ
  rcases hℓ with rfl | rfl | rfl | hℓ | hℓ
  · exact lk (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact dis (L := [_]) (boxx_neg x hx List.mem_cons_self) fun ℓ hℓ => by
      rw [List.mem_singleton.mp hℓ]
      exact lam (contra (List.mem_cons_of_mem _ List.mem_cons_self) (orl _ (lk List.mem_cons_self)))
  · exact dis (L := [_]) (boxx_neg x hx List.mem_cons_self) fun ℓ hℓ => by
      rw [List.mem_singleton.mp hℓ]
      exact lam (contra (List.mem_cons_of_mem _ List.mem_cons_self) (orr _ (lk List.mem_cons_self)))
  · exact lk (by simp [hℓ])
  · exact lk (by simp [hℓ])

/-- An existential's witness re-bound: the body proves its own `∃`. -/
theorem ex_self [Γ.NoSlots] {u : ℕ} (hu : Γ.RootFresh (.free u)) (T : VarType)
    {L : List (WFF σ (Γ.insert (.free u) T) 0)} {B : WFF σ (Γ.insert (.free u) T) 0}
    (q : Provable L B) :
    Provable L ((WFF.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T B)).weaken hu.root T) := by
  obtain ⟨q⟩ := q
  exact ⟨Proof.ex_intro T (Term.eta (.root (.free u)) T (Ctx.ref_insert_root Γ _ T))
    (φ := WFF.mono ((Ctx.le_insert hu.root T).insert (.bnd 0) T)
      (WFF.bindFree u hu Ctx.NoSlots.slots T B))
    (Proof.conv ((WFF.openFree_bindFree u hu _ B).symm.trans
      (WFF.instantiate_eta_openFree u hu _ _ _).symm) q)⟩

/-- ⭐`∃` is monotone and distributes over `∨`, with side hypotheses. -/
theorem ex_or [Γ.NoSlots] {u : ℕ} (hu : Γ.RootFresh (.free u)) (T : VarType)
    {H : List (WFF σ Γ 0)} {A B₁ B₂ : WFF σ (Γ.insert (.free u) T) 0}
    (p : Provable (A :: H.map (WFF.weaken hu.root T)) (B₁.or B₂)) :
    Provable (.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T A) :: H)
      ((WFF.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T B₁)).or
        (WFF.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T B₂))) := by
  obtain ⟨q⟩ := or_cases (H := A :: (WFF.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T A) ::
      H).map (WFF.weaken hu.root T)) (sub (by lsub) p)
    (orl _ (ex_self hu T (lk List.mem_cons_self)))
    (orr _ (ex_self hu T (lk List.mem_cons_self)))
  exact ⟨Proof.ex_elim u T hu (Proof.lookup List.mem_cons_self) q⟩

/-! ## Binding the births -/

/-- The births can be bound in turn: each free, fresh for the context of the ones before it. -/
def BOK (V : Ctx) : List (Root × VarType) → Prop
  | [] => V.SlotsFrom 0
  | b :: L => (∃ u, b.1 = .free u) ∧ (V.inserts L).RootFresh b.1 ∧ BOK V L

theorem BOK.slots : ∀ {V : Ctx} {L : List (Root × VarType)}, BOK V L → (V.inserts L).SlotsFrom 0
  | _, [], h => h
  | _, b :: _, ⟨⟨u, hu⟩, _, h⟩ => by
      obtain ⟨r, T⟩ := b
      dsimp only at hu
      subst hu
      exact (BOK.slots h).insertFree u T

theorem BOK.le : ∀ {V : Ctx} {L : List (Root × VarType)}, BOK V L → V.Le (V.inserts L)
  | _, [], _ => Ctx.Le.refl _
  | _, b :: _, ⟨_, hfr, h⟩ => (BOK.le h).trans (Ctx.le_insert hfr.root b.2)

/-- ⭐**Binding the births is monotone and distributes over `∨`**, with side hypotheses. -/
theorem closeB_or : ∀ {V : Ctx} {L : List (Root × VarType)} (hL : BOK V L)
    {H : List (WFF σ V 0)} {A B₁ B₂ : WFF σ (V.inserts L) 0},
    Provable (A :: H.map (WFF.mono hL.le)) (B₁.or B₂) →
    Provable (closeB L A :: H) ((closeB L B₁).or (closeB L B₂))
  | _, [], _, H, _, _, _, p => by
      rw [List.map_congr_left fun ψ _ => WFF.mono_refl _ ψ, List.map_id'] at p
      exact p
  | V, b :: L, hL, H, A, B₁, B₂, p => by
      obtain ⟨⟨u, hu⟩, hfr, hL'⟩ := hL
      obtain ⟨r, T⟩ := b
      dsimp only at hu hfr
      subst hu
      haveI : (V.inserts L).NoSlots := ⟨hL'.slots⟩
      rw [closeB_cons hfr hL'.slots, closeB_cons hfr hL'.slots, closeB_cons hfr hL'.slots]
      refine closeB_or hL' (ex_or hfr T ?_)
      rw [List.map_map]
      refine (congrArg (fun H' => Provable (A :: H') (B₁.or B₂)) ?_).mp p
      refine List.map_congr_left fun ψ _ => ?_
      simp only [Function.comp, WFF.weaken, WFF.mono_mono]

/-- Binding the births keeps a refutation. -/
theorem closeB_bot : ∀ {V : Ctx} {L : List (Root × VarType)} (hL : BOK V L)
    {H : List (WFF σ V 0)} {A : WFF σ (V.inserts L) 0},
    Provable (A :: H.map (WFF.mono hL.le)) .bot → Provable (closeB L A :: H) .bot
  | _, [], _, H, _, p => by
      rw [List.map_congr_left fun ψ _ => WFF.mono_refl _ ψ, List.map_id'] at p
      exact p
  | V, b :: L, hL, H, A, p => by
      obtain ⟨⟨u, hu⟩, hfr, hL'⟩ := hL
      obtain ⟨r, T⟩ := b
      dsimp only at hu hfr
      subst hu
      haveI : (V.inserts L).NoSlots := ⟨hL'.slots⟩
      rw [closeB_cons hfr hL'.slots]
      refine closeB_bot hL' ?_
      have p' : Provable (A :: (WFF.ex T (WFF.bindFree u hfr Ctx.NoSlots.slots T A) ::
          H.map (WFF.mono hL'.le)).map (WFF.weaken hfr.root T)) .bot := by
        have p₁ : Provable (A :: (H.map (WFF.mono hL'.le)).map (WFF.weaken hfr.root T)) .bot := by
          refine (congrArg (fun H' => Provable (A :: H') .bot) ?_).mp p
          rw [List.map_map]
          refine List.map_congr_left fun ψ _ => ?_
          simp only [Function.comp, WFF.weaken, WFF.mono_mono]
        exact sub (by lsub) p₁
      obtain ⟨p'⟩ := p'
      exact ⟨Proof.ex_elim u T hfr (ψ := .bot) (Proof.lookup List.mem_cons_self) p'⟩

/-- ⭐**Weakening commutes with binding the births.** -/
theorem mono_closeB : ∀ {V V' : Ctx} (h : V.Le V') {L : List (Root × VarType)} (_ : BOK V L)
    (_ : BOK V' L) (A : WFF σ (V.inserts L) 0),
    WFF.mono h (closeB L A) = closeB L (WFF.mono (h.inserts L) A)
  | _, _, _, [], _, _, _ => rfl
  | V, V', h, b :: L, hL, hL', A => by
      obtain ⟨⟨u, hu⟩, hfr, hL₁⟩ := hL
      obtain ⟨-, hfr', hL₁'⟩ := hL'
      obtain ⟨r, T⟩ := b
      dsimp only at hu hfr hfr'
      subst hu
      rw [closeB_cons hfr hL₁.slots, closeB_cons hfr' hL₁'.slots, mono_closeB h hL₁ hL₁']
      congr 1
      change WFF.ex T (WFF.mono ((h.inserts L).insert (.bnd 0) T) _) = _
      rw [WFF.mono_bindFree (h.inserts L) hfr hfr' hL₁.slots hL₁'.slots T A]

/-! ## Opening the witnesses -/

/-- `□⁰` of a negation from the negated `◇⁰`. -/
theorem optBox_neg (hO : ModalSys.Opt = true) (κ : WitKind) (y : VarSymb)
    (hy : ∃ X, Γ.witK κ y = some X) {H : List (WFF σ Γ 0)} {B : WFF σ (Γ.optInK κ y) 0}
    (h : (WFF.optx hO κ y hy B).neg ∈ H) : Provable H (WFF.optBox hO κ y hy B.neg) := by
  refine lam ?_
  obtain ⟨q⟩ : Provable [B.neg.neg] B := dne (lk List.mem_cons_self)
  have r : Proof σ Γ (WFF.optx hO κ y hy B.neg.neg ::
      (([] : List (WFF σ (Γ.optInK κ y) 0)).map (WFF.optBox hO κ y hy) ++ []))
      (WFF.optx hO κ y hy B) := Proof.K_opt hO κ y hy (Δ₁ := []) (Δ₂ := []) q
  exact contra (List.mem_cons_of_mem _ h) (sub (by lsub) ⟨r⟩)

/-- ⭐`◇⁰` is monotone and distributes over `∨`, with side hypotheses (no world crossed). -/
theorem opt_or (hO : ModalSys.Opt = true) (κ : WitKind) (y : VarSymb)
    (hy : ∃ X, Γ.witK κ y = some X) {H : List (WFF σ Γ 0)} {A B₁ B₂ : WFF σ (Γ.optInK κ y) 0}
    (p : Provable (A :: H.map (WFF.mono (Ctx.le_optInK Γ κ y))) (B₁.or B₂)) :
    Provable (.optx hO κ y hy A :: H) ((WFF.optx hO κ y hy B₁).or (WFF.optx hO κ y hy B₂)) := by
  have k : Provable (A :: ([B₁.neg, B₂.neg] ++ H.map (WFF.mono (Ctx.le_optInK Γ κ y)))) .bot :=
    or_cases (sub (by lsub) p) (contra (by simp) (lk List.mem_cons_self))
      (contra (by simp) (lk List.mem_cons_self))
  obtain ⟨k⟩ := k
  refine byContra ((dis ⟨Proof.K_opt hO κ y hy (Δ₁ := H) (Δ₂ := [B₁.neg, B₂.neg]) k⟩ ?_).map
    (.opt_bot hO κ y hy))
  intro ℓ hℓ
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons] at hℓ
  rcases hℓ with rfl | rfl | rfl | hℓ
  · exact lk (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact dis (L := [_]) (optBox_neg hO κ y hy List.mem_cons_self) fun ℓ hℓ => by
      rw [List.mem_singleton.mp hℓ]
      exact lam (contra (List.mem_cons_of_mem _ List.mem_cons_self) (orl _ (lk List.mem_cons_self)))
  · exact dis (L := [_]) (optBox_neg hO κ y hy List.mem_cons_self) fun ℓ hℓ => by
      rw [List.mem_singleton.mp hℓ]
      exact lam (contra (List.mem_cons_of_mem _ List.mem_cons_self) (orr _ (lk List.mem_cons_self)))
  · exact lk (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hℓ))

/-- `◇⁰` keeps a refutation. -/
theorem opt_bot' (hO : ModalSys.Opt = true) (κ : WitKind) (y : VarSymb)
    (hy : ∃ X, Γ.witK κ y = some X) {H : List (WFF σ Γ 0)} {A : WFF σ (Γ.optInK κ y) 0}
    (p : Provable (A :: H.map (WFF.mono (Ctx.le_optInK Γ κ y))) .bot) :
    Provable (.optx hO κ y hy A :: H) .bot := by
  obtain ⟨p⟩ := sub (L' := A :: (([] : List (WFF σ (Γ.optInK κ y) 0)) ++
    H.map (WFF.mono (Ctx.le_optInK Γ κ y)))) (by lsub) p
  exact sub (by lsub) ⟨.opt_bot hO κ y hy (Proof.K_opt hO κ y hy (Δ₂ := []) p)⟩


/-- ⭐**Barcan for `◇⁰`**: `◇⁰_y ∃u A ⊢ ∃u ◇⁰_y A`, no world crossed; the body carried along the
    birth's commutation with the opening (`hc`).  By `opt_bot'` against the negated conclusion,
    `∃`-elimination inside the view, and `opt_reopen` there (`y` is opened). -/
theorem opt_ex [Γ.NoSlots] (hO : ModalSys.Opt = true) (κ : WitKind) (y : VarSymb)
    (hy : ∃ X, Γ.witK κ y = some X) {u : ℕ} (T : VarType) (hu : Γ.RootFresh (.free u))
    (hu₁ : (Γ.optInK κ y).RootFresh (.free u))
    (hy' : ∃ X, (Γ.insert (.free u) T).witK κ y = some X)
    (hc : ((Γ.optInK κ y).insert (.free u) T).Le ((Γ.insert (.free u) T).optInK κ y))
    (A : WFF σ ((Γ.optInK κ y).insert (.free u) T) 0) :
    Provable [WFF.optx hO κ y hy (.ex T (WFF.bindFree u hu₁ Ctx.NoSlots.slots T A))]
      (.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T (WFF.optx hO κ y hy' (WFF.mono hc A)))) := by
  obtain ⟨X₀, hX₀⟩ := id hy
  have hle := Ctx.le_optInK Γ κ y
  set B₀ := WFF.optx hO κ y hy' (WFF.mono hc A) with hB₀
  set X := (WFF.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T B₀) : WFF σ Γ 0) with hX
  have hop : ((Γ.optInK κ y).insert (.free u) T).Opened κ y :=
    (Ctx.opened_self hX₀).mono (Ctx.le_insert hu₁.root T)
  have hB : Provable [A] (WFF.mono (hle.insert (.free u) T) B₀) := by
    have r := Proof.opt_reopen hO κ y hop (Proof.lookup (Δ := [A]) List.mem_cons_self)
    refine (congrArg (Provable [A]) ?_).mp ⟨r⟩
    change WFF.optx hO κ y _ (WFF.mono (Ctx.le_optInK _ κ y) A) =
      WFF.optx hO κ y _ (WFF.mono ((hle.insert (.free u) T).optInK κ y) (WFF.mono hc A))
    rw [WFF.mono_mono]
  have hmX : WFF.mono hle X = .ex T (WFF.bindFree u hu₁ Ctx.NoSlots.slots T
      (WFF.mono (hle.insert (.free u) T) B₀)) := by
    change WFF.ex T (WFF.mono (hle.insert (.bnd 0) T) _) = _
    rw [WFF.mono_bindFree hle hu hu₁ Ctx.NoSlots.slots Ctx.NoSlots.slots T B₀]
  have hXw : Provable [A] ((WFF.mono hle X).weaken hu₁.root T) := by
    rw [hmX]
    exact ex_self hu₁ T hB
  refine byContra (sub (by lsub) (opt_bot' hO κ y hy (H := [X.neg]) ?_))
  obtain ⟨q⟩ : Provable (A :: ([WFF.ex T (WFF.bindFree u hu₁ Ctx.NoSlots.slots T A),
      WFF.mono hle X.neg]).map (WFF.weaken hu₁.root T)) .bot :=
    contra (φ := (WFF.mono hle X).weaken hu₁.root T)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (sub (by lsub) hXw)
  exact ⟨Proof.ex_elim u T hu₁ (ψ := .bot) (Proof.lookup List.mem_cons_self) q⟩

end ND

section ND

variable {Γ : Ctx}

/-- ⭐**Closing the openings is monotone and distributes over `∨`**, with side hypotheses. -/
theorem closeO_or : ∀ {P : Ctx} {L : List (WitKind × VarSymb)} (_ : P.OptsEff L)
    {H : List (WFF σ P 0)} {A B₁ B₂ : WFF σ (P.optInsK L) 0},
    Provable (A :: H.map (WFF.mono (Ctx.le_optInsK P L))) (B₁.or B₂) →
    Provable (closeO L A :: H) ((closeO L B₁).or (closeO L B₂))
  | _, [], _, H, _, _, _, p => by
      rw [List.map_congr_left fun ψ _ => WFF.mono_refl _ ψ, List.map_id'] at p
      exact p
  | P, ⟨κ, y⟩ :: L, ⟨hL, hO, hy⟩, H, A, B₁, B₂, p => by
      rw [closeO_cons hO hy, closeO_cons hO hy, closeO_cons hO hy]
      refine closeO_or hL (opt_or hO κ y hy ?_)
      rw [List.map_map]
      refine (congrArg (fun H' => Provable (A :: H') (B₁.or B₂)) ?_).mp p
      refine List.map_congr_left fun ψ _ => ?_
      simp only [Function.comp, WFF.mono_mono]

/-- Closing the openings keeps a refutation. -/
theorem closeO_bot : ∀ {P : Ctx} {L : List (WitKind × VarSymb)} (_ : P.OptsEff L)
    {H : List (WFF σ P 0)} {A : WFF σ (P.optInsK L) 0},
    Provable (A :: H.map (WFF.mono (Ctx.le_optInsK P L))) .bot → Provable (closeO L A :: H) .bot
  | _, [], _, H, _, p => by
      rw [List.map_congr_left fun ψ _ => WFF.mono_refl _ ψ, List.map_id'] at p
      exact p
  | P, ⟨κ, y⟩ :: L, ⟨hL, hO, hy⟩, H, A, p => by
      rw [closeO_cons hO hy]
      refine closeO_bot hL (opt_bot' hO κ y hy ?_)
      rw [List.map_map]
      refine (congrArg (fun H' => Provable (A :: H') .bot) ?_).mp p
      refine List.map_congr_left fun ψ _ => ?_
      simp only [Function.comp, WFF.mono_mono]


/-- ⭐**Barcan for a node's openings**: `closeO L (∃u A) ⊢ ∃u closeO L A`, the body carried along
    the birth's commutation with the openings. -/
theorem closeO_ex : ∀ {P : Ctx} {L : List (WitKind × VarSymb)} (_ : P.OptsEff L) {u : ℕ}
    (T : VarType) (hs : P.SlotsFrom 0) (hu : P.RootFresh (.free u))
    (hu₁ : (P.optInsK L).RootFresh (.free u)) (_ : (P.insert (.free u) T).OptsEff L)
    (hc : ((P.optInsK L).insert (.free u) T).Le ((P.insert (.free u) T).optInsK L))
    (A : WFF σ ((P.optInsK L).insert (.free u) T) 0),
    Provable [closeO L (.ex T (WFF.bindFree u hu₁ (hs.optInsK L) T A))]
      (.ex T (WFF.bindFree u hu hs T (closeO L (WFF.mono hc A))))
  | _, [], _, _, T, _, _, _, _, hc, A => by
      change Provable [WFF.ex T _] (WFF.ex T (WFF.bindFree _ _ _ T (WFF.mono hc A)))
      rw [WFF.mono_refl]
      exact lk List.mem_cons_self
  | P, ⟨κ, y⟩ :: L, ⟨hL, hO, hy⟩, u, T, hs, hu, hu₁, ⟨hL', _, hy'⟩, hc, A => by
      have hsQ := hs.optInsK L
      haveI : (P.optInsK L).NoSlots := ⟨hsQ⟩
      have huQ : (P.optInsK L).RootFresh (.free u) :=
        Ctx.RootFresh.of_le (Ctx.le_optInK _ κ y) hu₁
      have hyQ : ∃ X, ((P.optInsK L).insert (.free u) T).witK κ y = some X :=
        hy.imp fun _ h => (Ctx.le_insert huQ.root T).witK h
      have hc₁ := Ctx.insert_optInK_le huQ T κ y
      have hcL := Ctx.insert_optInsK_le hu T L
      have s₁ := opt_ex hO κ y hy T huQ hu₁ hyQ hc₁ A
      have s₂ : Provable [closeO L (WFF.optx hO κ y hy
          (.ex T (WFF.bindFree u hu₁ (hs.optInsK ((κ, y) :: L)) T A)))]
          (closeO L (.ex T (WFF.bindFree u huQ hsQ T (WFF.optx hO κ y hyQ (WFF.mono hc₁ A))))) :=
        or_cases (closeO_or hL (H := []) (orl _ s₁)) (lk List.mem_cons_self)
          (lk List.mem_cons_self)
      have ih := closeO_ex hL T hs hu huQ hL' hcL (WFF.optx hO κ y hyQ (WFF.mono hc₁ A))
      have e : WFF.mono hcL (WFF.optx hO κ y hyQ (WFF.mono hc₁ A)) =
          WFF.optx hO κ y hy' (WFF.mono hc A) := by
        change WFF.optx hO κ y _ (WFF.mono (hcL.optInK κ y) (WFF.mono hc₁ A)) = _
        rw [WFF.mono_mono]
      rw [e] at ih
      rw [closeO_cons hO hy, closeO_cons hO hy']
      exact chain s₂ (sub (by lsub) ih)

end ND

/-- ⭐**Weakening commutes with closing the openings.** -/
theorem mono_closeO : ∀ {P P' : Ctx} (h : P.Le P') {L : List (WitKind × VarSymb)}
    (_ : P.OptsEff L) (_ : P'.OptsEff L) (A : WFF σ (P.optInsK L) 0),
    WFF.mono h (closeO L A) = closeO L (WFF.mono (h.optInsK L) A)
  | _, _, _, [], _, _, _ => rfl
  | P, P', h, ⟨κ, y⟩ :: L, ⟨hL, hO, hy⟩, ⟨hL', _, hy'⟩, A => by
      rw [closeO_cons hO hy, closeO_cons hO hy', mono_closeO h hL hL']
      rfl

/-- A node's closure is well formed: the births bind, the openings take effect. -/
def NOK (V : Ctx) (B : List (Root × VarType)) (O : List (WitKind × VarSymb)) : Prop :=
  BOK V B ∧ (V.inserts B).OptsEff O

theorem NOK.le {V : Ctx} {B : List (Root × VarType)} {O : List (WitKind × VarSymb)}
    (h : NOK V B O) : V.Le ((V.inserts B).optInsK O) :=
  h.1.le.trans (Ctx.le_optInsK _ O)

section ND

theorem closeN_or {V : Ctx} {B : List (Root × VarType)} {O : List (WitKind × VarSymb)}
    (hN : NOK V B O) {H : List (WFF σ V 0)} {A B₁ B₂ : WFF σ ((V.inserts B).optInsK O) 0}
    (p : Provable (A :: H.map (WFF.mono hN.le)) (B₁.or B₂)) :
    Provable (closeN B O A :: H) ((closeN B O B₁).or (closeN B O B₂)) := by
  refine closeB_or hN.1 (closeO_or hN.2 ?_)
  rw [List.map_map]
  refine (congrArg (fun H' => Provable (A :: H') (B₁.or B₂)) ?_).mp p
  refine List.map_congr_left fun ψ _ => ?_
  simp only [Function.comp, WFF.mono_mono]

theorem closeN_bot {V : Ctx} {B : List (Root × VarType)} {O : List (WitKind × VarSymb)}
    (hN : NOK V B O) {H : List (WFF σ V 0)} {A : WFF σ ((V.inserts B).optInsK O) 0}
    (p : Provable (A :: H.map (WFF.mono hN.le)) .bot) : Provable (closeN B O A :: H) .bot := by
  refine closeB_bot hN.1 (closeO_bot hN.2 ?_)
  rw [List.map_map]
  refine (congrArg (fun H' => Provable (A :: H') .bot) ?_).mp p
  refine List.map_congr_left fun ψ _ => ?_
  simp only [Function.comp, WFF.mono_mono]

end ND

theorem mono_closeN {V V' : Ctx} (h : V.Le V') {B : List (Root × VarType)}
    {O : List (WitKind × VarSymb)} (hN : NOK V B O) (hN' : NOK V' B O)
    (A : WFF σ ((V.inserts B).optInsK O) 0) :
    WFF.mono h (closeN B O A) = closeN B O (WFF.mono ((h.inserts B).optInsK O) A) := by
  unfold closeN
  rw [mono_closeB h hN.1 hN'.1, mono_closeO _ hN.2 hN'.2]

section ND

variable {Γ : Ctx}

/-! ## Behind the edge -/

theorem prov_cast {W W' : Ctx} (e : W = W') {L : List (WFF σ W 0)} {φ : WFF σ W 0}
    (p : Provable L φ) :
    Provable (L.map (WFF.mono (Ctx.le_of_eq e))) (WFF.mono (Ctx.le_of_eq e) φ) := by
  subst e
  rw [List.map_congr_left fun ψ _ => WFF.mono_refl _ ψ, List.map_id', WFF.mono_refl]
  exact p

theorem dpk_bot {A : WFF σ Γ.boxIn 0} (p : Provable [A] .bot) : Provable [dpk A] .bot := by
  obtain ⟨q⟩ := lam p
  exact contra List.mem_cons_self (sub (fun _ h => absurd h List.not_mem_nil) ⟨Proof.K_box q⟩)

/-- ⭐**Behind the edge is monotone and distributes over `∨`.** -/
theorem pack_or {D : Tree} {c : Lab}
    (hw : ∀ x, D.edge c = some (.dia x) → ∃ X, Γ.ref x = some (.VTypeDia X))
    {A B₁ B₂ : WFF σ (D.view c Γ) 0} (p : Provable [A] (B₁.or B₂)) :
    Provable [pack D Γ c A] ((pack D Γ c B₁).or (pack D Γ c B₂)) := by
  cases he : D.edge c with
  | none =>
      simp only [pack_box (Or.inl he)]
      exact dpk_or (H₁ := []) (prov_cast (Tree.view_box (Or.inl he)) p)
  | some e =>
      cases e with
      | box =>
          simp only [pack_box (Or.inr he)]
          exact dpk_or (H₁ := []) (prov_cast (Tree.view_box (Or.inr he)) p)
      | dia x =>
          have hx := hw x he
          simp only [pack_dia he hx]
          exact dia_or x hx (Δ₁ := []) (Δ₂ := []) (prov_cast (Tree.view_dia he) p)

theorem pack_mono {D : Tree} {c : Lab}
    (hw : ∀ x, D.edge c = some (.dia x) → ∃ X, Γ.ref x = some (.VTypeDia X))
    {A B : WFF σ (D.view c Γ) 0} (p : Provable [A] B) : Provable [pack D Γ c A] (pack D Γ c B) :=
  or_cases (pack_or hw (orl B p)) (lk List.mem_cons_self) (lk List.mem_cons_self)

theorem pack_bot {D : Tree} {c : Lab}
    (hw : ∀ x, D.edge c = some (.dia x) → ∃ X, Γ.ref x = some (.VTypeDia X))
    {A : WFF σ (D.view c Γ) 0} (p : Provable [A] .bot) : Provable [pack D Γ c A] .bot := by
  cases he : D.edge c with
  | none =>
      simp only [pack_box (Or.inl he)]
      exact dpk_bot (prov_cast (Tree.view_box (Or.inl he)) p)
  | some e =>
      cases e with
      | box =>
          simp only [pack_box (Or.inr he)]
          exact dpk_bot (prov_cast (Tree.view_box (Or.inr he)) p)
      | dia x =>
          have hx := hw x he
          simp only [pack_dia he hx]
          obtain ⟨q⟩ := prov_cast (Tree.view_dia he) p
          exact ⟨.dia_bot x hx (Proof.K_dia x hx (Δ₁ := []) (Δ₂ := []) q)⟩

end ND

/-- ⭐**Weakening commutes with the edge.** -/
theorem mono_pack {D D' : Tree} {Γ Γ' : Ctx} (h : Γ.Le Γ') {c : Lab}
    (he : D'.edge c = D.edge c) (h' : (D.view c Γ).Le (D'.view c Γ'))
    (hw : ∀ x, D.edge c = some (.dia x) → ∃ X, Γ.ref x = some (.VTypeDia X))
    (φ : WFF σ (D.view c Γ) 0) :
    WFF.mono h (pack D Γ c φ) = pack D' Γ' c (WFF.mono h' φ) := by
  cases hd : D.edge c with
  | none =>
      rw [pack_box (Or.inl hd), pack_box (Or.inl (he.trans hd))]
      change WFF.imp (WFF.box (WFF.imp (WFF.mono h.boxIn (WFF.mono _ φ)) .bot)) .bot = _
      rw [WFF.mono_mono, WFF.mono_mono]
  | some e =>
      cases e with
      | box =>
          rw [pack_box (Or.inr hd), pack_box (Or.inr (he.trans hd))]
          change WFF.imp (WFF.box (WFF.imp (WFF.mono h.boxIn (WFF.mono _ φ)) .bot)) .bot = _
          rw [WFF.mono_mono, WFF.mono_mono]
      | dia x =>
          have hx := hw x hd
          rw [pack_dia hd hx, pack_dia (he.trans hd) (hx.imp fun _ hX => h.ref hX)]
          change WFF.dia x _ (WFF.mono (h.diaIn x) (WFF.mono _ φ)) = _
          rw [WFF.mono_mono, WFF.mono_mono]

/-! ## Binding a node's births -/

theorem bok_of {V : Ctx} (hV : V.SlotsFrom 0) :
    ∀ {L : List (Root × VarType)}, L.Pairwise (fun b b' => b.1 ≠ b'.1) →
      (∀ b ∈ L, V.RootFresh b.1) → (∀ b ∈ L, ∃ u, b.1 = .free u) → BOK V L
  | [], _, _, _ => hV
  | b :: L, hp, hf, hu => by
      obtain ⟨hb, hp⟩ := List.pairwise_cons.mp hp
      exact ⟨hu b List.mem_cons_self,
        (hf b List.mem_cons_self).inserts L fun b' hm => (hb b' hm).symm,
        bok_of hV hp (fun b' h => hf b' (List.mem_cons_of_mem _ h))
          (fun b' h => hu b' (List.mem_cons_of_mem _ h))⟩

theorem Tree.vw_slots {D : Tree} (h0 : Γ₀.SlotsFrom 0) (hok : D.OK Γ₀) :
    ∀ ρ, (Vw D Γ₀ ρ).SlotsFrom 0
  | [] => h0
  | k :: ρ => by
      change (D.view (k :: ρ) (D.ctxAt Γ₀ ρ)).SlotsFrom 0
      have := Tree.ctxAt_slots h0 hok ρ
      unfold Tree.view
      split
      · exact this.diaIn _
      · exact this.boxIn

/-- A node's births can be bound over the context its closed reading lives in. -/
theorem Tree.bok {D : Tree} (h0 : Γ₀.SlotsFrom 0) (hok : D.OK Γ₀) (ρ : Lab) :
    BOK (Vw D Γ₀ ρ) (D.birthsAt ρ) := by
  refine bok_of (Tree.vw_slots h0 hok ρ) (Tree.birthsAt_pairwise hok ρ) (fun b hm => ?_)
    fun b hm => hok.free _ (Tree.mem_birthsAt.mp hm)
  have hb := Tree.mem_birthsAt.mp hm
  cases ρ with
  | nil => exact hok.fresh _ hb
  | cons k ρ =>
      have hfr : (D.ctxAt Γ₀ ρ).RootFresh b.1 := by
        refine Tree.fresh_branch (hok.fresh _ hb) ρ fun b' hb' hs he => ?_
        have := hok.uniq b' hb' _ hb he
        rw [this] at hs
        have := hs.length_le
        simp at this
      change (D.view (k :: ρ) (D.ctxAt Γ₀ ρ)).RootFresh b.1
      unfold Tree.view
      split
      · exact hfr.diaIn _
      · exact hfr.boxIn

/-- A node's closure is well formed over the context its closed reading lives in. -/
theorem Tree.nok {D : Tree} (h0 : Γ₀.SlotsFrom 0) (hok : D.OK Γ₀) (ρ : Lab) :
    NOK (Vw D Γ₀ ρ) (D.birthsAt ρ) (D.opensAt ρ) :=
  ⟨Tree.bok h0 hok ρ, by
    cases ρ with
    | nil => exact hok.eff []
    | cons k ρ => exact hok.eff (k :: ρ)⟩

/-! ## ⭐From a node to the root, across a grown tree -/

open NDP

/-- The readings of two trees agree at a node: the same formulas (weakened), children, edges
    into them and births. -/
structure Ag {D D' : Tree} (Δ Θ : Seq σ Γ₀ D) (Δ' Θ' : Seq σ Γ₀ D')
    (hk : ∀ ρ, (D.ctxAt Γ₀ ρ).Le (D'.ctxAt Γ₀ ρ)) (ρ : Lab) : Prop where
  left : Δ'.at ρ = (Δ.at ρ).map (WFF.mono (hk ρ))
  right : Θ'.at ρ = (Θ.at ρ).map (WFF.mono (hk ρ))
  children : D'.children ρ = D.children ρ
  edge : ∀ k, D'.edge (k :: ρ) = D.edge (k :: ρ)
  births : D'.birthsAt ρ = D.birthsAt ρ
  opens : D'.opensAt ρ = D.opensAt ρ

/-- The closed reading of the smaller tree, weakened, proves the bigger tree's. -/
def Claim {D D' : Tree} (Δ Θ : Seq σ Γ₀ D) (Δ' Θ' : Seq σ Γ₀ D')
    (hV : ∀ ρ, (Vw D Γ₀ ρ).Le (Vw D' Γ₀ ρ)) (f : ℕ) (ρ : Lab) : Prop :=
  Provable [WFF.mono (hV ρ) (Pc D Δ Θ f ρ)] (Pc D' Δ' Θ' f ρ)

theorem closed_of {V V' : Ctx} (hVV : V.Le V') {L L' : List (Root × VarType)} (hL : L' = L)
    {O O' : List (WitKind × VarSymb)} (hO : O' = O) (hb : NOK V L O) (hb' : NOK V' L' O')
    {A : WFF σ ((V.inserts L).optInsK O) 0} {B : WFF σ ((V'.inserts L').optInsK O') 0}
    (hA : ((V.inserts L).optInsK O).Le ((V'.inserts L').optInsK O'))
    (p : Provable [WFF.mono hA A] B) :
    Provable [WFF.mono hVV (closeN L O A)] (closeN L' O' B) := by
  subst hL
  subst hO
  rw [mono_closeN hVV hb hb' A]
  exact or_cases (closeN_or hb' (H := []) (orl B p)) (lk List.mem_cons_self)
    (lk List.mem_cons_self)

section Cross

variable {D D' : Tree} {Δ Θ : Seq σ Γ₀ D} {Δ' Θ' : Seq σ Γ₀ D'}
  {hk : ∀ ρ, (D.ctxAt Γ₀ ρ).Le (D'.ctxAt Γ₀ ρ)} {hV : ∀ ρ, (Vw D Γ₀ ρ).Le (Vw D' Γ₀ ρ)}

theorem claim_of_tr (h0 : Γ₀.SlotsFrom 0) (hok : D.OK Γ₀) (hok' : D'.OK Γ₀) {ρ : Lab}
    (hb : D'.birthsAt ρ = D.birthsAt ρ) (ho : D'.opensAt ρ = D.opensAt ρ) {f : ℕ}
    (p : Provable [WFF.mono (hk ρ) (tr D Δ Θ f ρ)] (tr D' Δ' Θ' f ρ)) :
    Claim Δ Θ Δ' Θ' hV f ρ := by
  cases ρ with
  | nil =>
      exact closed_of (hV []) hb ho (Tree.nok h0 hok []) (Tree.nok h0 hok' []) (hk []) p
  | cons k ρ =>
      exact closed_of (hV (k :: ρ)) hb ho (Tree.nok h0 hok _) (Tree.nok h0 hok' _) (hk (k :: ρ))
        p

theorem content_eq {ρ : Lab} (ag : Ag Δ Θ Δ' Θ' hk ρ) :
    Δ'.at ρ ++ (Θ'.at ρ).map WFF.neg =
      (Δ.at ρ ++ (Θ.at ρ).map WFF.neg).map (WFF.mono (hk ρ)) := by
  rw [ag.left, ag.right, List.map_append, List.map_map, List.map_map]
  rfl

theorem step0 {ρ : Lab} (ag : Ag Δ Θ Δ' Θ' hk ρ) :
    Provable [WFF.mono (hk ρ) (tr D Δ Θ 0 ρ)] (tr D' Δ' Θ' 0 ρ) := by
  have e : WFF.mono (hk ρ) (tr D Δ Θ 0 ρ) = tr D' Δ' Θ' 0 ρ := by
    rw [tr_zero, tr_zero, content_eq ag]
    change WFF.and (WFF.mono _ (conj _)) .top = _
    rw [mono_conj]
  rw [e]
  exact lk List.mem_cons_self

theorem stepS (hW : D.WitOK Γ₀) {ρ : Lab} (ag : Ag Δ Θ Δ' Θ' hk ρ) {f : ℕ}
    (hc : ∀ j ∈ D.children ρ, Claim Δ Θ Δ' Θ' hV f (j :: ρ)) :
    Provable [WFF.mono (hk ρ) (tr D Δ Θ (f + 1) ρ)] (tr D' Δ' Θ' (f + 1) ρ) := by
  rw [tr_succ, tr_succ, content_eq ag, ag.children]
  change Provable [WFF.and (WFF.mono _ (conj _)) (WFF.mono _ (conj _))] _
  rw [mono_conj, mono_conj, List.map_map]
  have hY : Provable [conj ((D.children ρ).map (WFF.mono (hk ρ) ∘ fun k =>
        pack D (D.ctxAt Γ₀ ρ) (k :: ρ) (Pc D Δ Θ f (k :: ρ))))]
      (conj ((D.children ρ).map fun k => pack D' (D'.ctxAt Γ₀ ρ) (k :: ρ)
        (Pc D' Δ' Θ' f (k :: ρ)))) := by
    refine conj_intro fun z hz => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
    have h₁ := conj_elim (lk List.mem_cons_self : Provable [conj ((D.children ρ).map
      (WFF.mono (hk ρ) ∘ fun k => pack D (D.ctxAt Γ₀ ρ) (k :: ρ) (Pc D Δ Θ f (k :: ρ))))] _) _
      (List.mem_map_of_mem (f := WFF.mono (hk ρ) ∘ fun k =>
        pack D (D.ctxAt Γ₀ ρ) (k :: ρ) (Pc D Δ Θ f (k :: ρ))) hj)
    simp only [Function.comp] at h₁
    rw [mono_pack (hk ρ) (ag.edge j) (hV (j :: ρ)) (fun x he => hW j ρ x he)] at h₁
    refine chain h₁ (sub (fun _ h => by
      rw [List.mem_singleton.mp h]; exact List.mem_cons_self) ?_)
    refine pack_mono (fun x he => ?_) (hc j hj)
    rw [ag.edge j] at he
    exact (hW j ρ x he).imp fun _ hX => (hk ρ).ref hX
  obtain ⟨y⟩ := chain ((lk List.mem_cons_self).map .and_elim_r)
    (sub (fun _ h => by rw [List.mem_singleton.mp h]; exact List.mem_cons_self) hY)
  exact ⟨.and_intro (.and_elim_l (Proof.lookup List.mem_cons_self)) y⟩

/-- ⭐**Where the whole subtree agrees, the claim holds**, at any depth. -/
theorem claim_sub (h0 : Γ₀.SlotsFrom 0) (hok : D.OK Γ₀) (hok' : D'.OK Γ₀) (hW : D.WitOK Γ₀) :
    ∀ f ρ, (∀ σ', ρ <:+ σ' → Ag Δ Θ Δ' Θ' hk σ') → Claim Δ Θ Δ' Θ' hV f ρ
  | 0, ρ, hA => claim_of_tr h0 hok hok' (hA ρ (List.suffix_refl _)).births
      (hA ρ (List.suffix_refl _)).opens
      (step0 (hA ρ (List.suffix_refl _)))
  | f + 1, ρ, hA => claim_of_tr h0 hok hok' (hA ρ (List.suffix_refl _)).births
      (hA ρ (List.suffix_refl _)).opens
      (stepS hW (hA ρ (List.suffix_refl _)) fun j _ =>
        claim_sub h0 hok hok' hW f (j :: ρ) fun σ' hσ =>
          hA σ' ((List.suffix_cons j ρ).trans hσ))

theorem off_sub {τ : Lab} {k j : ℕ} {ρ : Lab} (hτ : (k :: ρ) <:+ τ) (hj : j ≠ k) :
    ∀ σ', (j :: ρ) <:+ σ' → ¬ τ <:+ σ' := by
  intro σ' h₁ h₂
  have h₃ : (j :: ρ) <:+ τ := List.suffix_of_suffix_length_le h₁ h₂ (by
    have := hτ.length_le
    simp only [List.length_cons] at this ⊢
    omega)
  have h₄ := List.suffix_of_suffix_length_le h₃ hτ (by simp)
  have := h₄.eq_of_length (by simp)
  exact hj (List.cons.inj this).1

/-- ⭐**From the hole to the root**: agreement off the hole's subtree and the claim at the hole
    give the claim at the root. -/
theorem claim_path (h0 : Γ₀.SlotsFrom 0) (hok : D.OK Γ₀) (hok' : D'.OK Γ₀) (hW : D.WitOK Γ₀)
    {d : ℕ} : ∀ τ : Lab, τ.length ≤ d → (∀ σ', ¬ τ <:+ σ' → Ag Δ Θ Δ' Θ' hk σ') →
      Claim Δ Θ Δ' Θ' hV (d - τ.length) τ → Claim Δ Θ Δ' Θ' hV d []
  | [], _, _, hole => hole
  | k :: ρ, hd, hA, hole => by
      have hd' : ρ.length ≤ d := by simp only [List.length_cons] at hd; omega
      have hf : d - ρ.length = (d - (k :: ρ).length) + 1 := by
        simp only [List.length_cons] at hd ⊢; omega
      refine claim_path h0 hok hok' hW ρ hd'
        (fun σ' hσ => hA σ' fun h => hσ ((List.suffix_cons k ρ).trans h)) ?_
      rw [hf]
      have agρ := hA ρ fun h => by have := h.length_le; simp at this
      refine claim_of_tr h0 hok hok' agρ.births agρ.opens (stepS (hV := hV) hW agρ fun j _ => ?_)
      by_cases hj : j = k
      · subst hj
        exact hole
      · exact claim_sub h0 hok hok' hW _ _ fun σ' hσ =>
          hA σ' (off_sub (List.suffix_refl _) hj σ' hσ)

end Cross

/-! ## From a node to the root, over the same tree: disjunctions and refutations -/

/-- Every node on the branch to `τ` has an edge into it. -/
def Tree.Reach (D : Tree) (τ : Lab) : Prop := ∀ k ρ, (k :: ρ) <:+ τ → D.edge (k :: ρ) ≠ none

section Same

variable {D : Tree}

theorem andI {Γ : Ctx} {H : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (p : Provable H φ)
    (q : Provable H ψ) : Provable H (φ.and ψ) :=
  let ⟨p⟩ := p; let ⟨q⟩ := q; ⟨.and_intro p q⟩

theorem tr_congr {Δ Θ Δ₁ Θ₁ : Seq σ Γ₀ D} :
    ∀ f ρ, (∀ σ', ρ <:+ σ' → Δ₁.at σ' = Δ.at σ' ∧ Θ₁.at σ' = Θ.at σ') →
      tr D Δ₁ Θ₁ f ρ = tr D Δ Θ f ρ
  | 0, ρ, h => by rw [tr_zero, tr_zero, (h ρ (List.suffix_refl _)).1, (h ρ (List.suffix_refl _)).2]
  | f + 1, ρ, h => by
      rw [tr_succ, tr_succ, (h ρ (List.suffix_refl _)).1, (h ρ (List.suffix_refl _)).2]
      refine congrArg (WFF.and _) (congrArg conj (List.map_congr_left fun j _ => ?_))
      have e := tr_congr f (j :: ρ) fun σ' hσ => h σ' ((List.suffix_cons j ρ).trans hσ)
      change pack _ _ _ (closeN _ _ (tr D Δ₁ Θ₁ f (j :: ρ))) =
        pack _ _ _ (closeN _ _ (tr D Δ Θ f (j :: ρ)))
      rw [e]

theorem Pc_congr {Δ Θ Δ₁ Θ₁ : Seq σ Γ₀ D} {f : ℕ} {ρ : Lab}
    (h : ∀ σ', ρ <:+ σ' → Δ₁.at σ' = Δ.at σ' ∧ Θ₁.at σ' = Θ.at σ') :
    Pc D Δ₁ Θ₁ f ρ = Pc D Δ Θ f ρ := by
  cases ρ with
  | nil =>
      change closeN _ _ (tr D Δ₁ Θ₁ f []) = closeN _ _ (tr D Δ Θ f [])
      rw [tr_congr f [] h]
  | cons k ρ =>
      change closeN _ _ (tr D Δ₁ Θ₁ f (k :: ρ)) = closeN _ _ (tr D Δ Θ f (k :: ρ))
      rw [tr_congr f (k :: ρ) h]

theorem closed_or_tr (h0 : Γ₀.SlotsFrom 0) (hok : D.OK Γ₀) {ρ : Lab} {f : ℕ}
    {Δ Θ Δ₁ Θ₁ Δ₂ Θ₂ : Seq σ Γ₀ D}
    (p : Provable [tr D Δ Θ f ρ] ((tr D Δ₁ Θ₁ f ρ).or (tr D Δ₂ Θ₂ f ρ))) :
    Provable [Pc D Δ Θ f ρ] ((Pc D Δ₁ Θ₁ f ρ).or (Pc D Δ₂ Θ₂ f ρ)) := by
  cases ρ with
  | nil => exact closeN_or (Tree.nok h0 hok []) (H := []) p
  | cons k ρ => exact closeN_or (Tree.nok h0 hok _) (H := []) p

theorem closed_bot_tr (h0 : Γ₀.SlotsFrom 0) (hok : D.OK Γ₀) {ρ : Lab} {f : ℕ}
    {Δ Θ : Seq σ Γ₀ D} (p : Provable [tr D Δ Θ f ρ] .bot) : Provable [Pc D Δ Θ f ρ] .bot := by
  cases ρ with
  | nil => exact closeN_bot (Tree.nok h0 hok []) (H := []) p
  | cons k ρ => exact closeN_bot (Tree.nok h0 hok _) (H := []) p

theorem conj_map_or {Γ : Ctx} {g g₁ g₂ : ℕ → WFF σ Γ 0} {k : ℕ}
    (hk : Provable [g k] ((g₁ k).or (g₂ k))) (he : ∀ j, j ≠ k → g₁ j = g j ∧ g₂ j = g j)
    (L : List ℕ) : Provable [conj (L.map g)] ((conj (L.map g₁)).or (conj (L.map g₂))) := by
  by_cases hkL : k ∈ L
  · have gk : Provable [conj (L.map g)] (g k) :=
      conj_elim (lk List.mem_cons_self) _ (List.mem_map_of_mem hkL)
    have hall : ∀ (i : Fin 2) (gi : ℕ → WFF σ Γ 0), (∀ j, j ≠ k → gi j = g j) →
        Provable [gi k, conj (L.map g)] (conj (L.map gi)) := fun _ gi hgi =>
      conj_intro fun z hz => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
        by_cases hjk : j = k
        · subst hjk
          exact lk List.mem_cons_self
        · rw [hgi j hjk]
          exact sub (by lsub) (conj_elim (lk List.mem_cons_self) _ (List.mem_map_of_mem hj))
    exact or_cases (chain gk (sub (by lsub) hk))
      (orl _ (hall 0 g₁ fun j h => (he j h).1)) (orr _ (hall 1 g₂ fun j h => (he j h).2))
  · have e₁ : L.map g₁ = L.map g :=
      List.map_congr_left fun j hj => (he j fun h => hkL (h ▸ hj)).1
    rw [e₁]
    exact orl _ (lk List.mem_cons_self)

theorem and_or {Γ : Ctx} {C X X₁ X₂ : WFF σ Γ 0} (p : Provable [X] (X₁.or X₂)) :
    Provable [C.and X] ((C.and X₁).or (C.and X₂)) :=
  or_cases (chain ((lk List.mem_cons_self).map .and_elim_r) (sub (by lsub) p))
    (orl _ (andI ((lk (List.mem_cons_of_mem _ List.mem_cons_self)).map .and_elim_l)
      (lk List.mem_cons_self)))
    (orr _ (andI ((lk (List.mem_cons_of_mem _ List.mem_cons_self)).map .and_elim_l)
      (lk List.mem_cons_self)))

/-- The three sides agree off a node's subtree. -/
def Agree3 (Δ Θ Δ₁ Θ₁ Δ₂ Θ₂ : Seq σ Γ₀ D) (τ : Lab) : Prop :=
  ∀ σ', ¬ τ <:+ σ' →
    (Δ₁.at σ' = Δ.at σ' ∧ Θ₁.at σ' = Θ.at σ') ∧ (Δ₂.at σ' = Δ.at σ' ∧ Θ₂.at σ' = Θ.at σ')

/-- ⭐**A disjunction at the hole is one at the root**, over the same tree. -/
theorem or_path (h0 : Γ₀.SlotsFrom 0) (hok : D.OK Γ₀) (hW : D.WitOK Γ₀)
    {Δ Θ Δ₁ Θ₁ Δ₂ Θ₂ : Seq σ Γ₀ D} {d : ℕ} :
    ∀ τ : Lab, τ.length ≤ d → Agree3 Δ Θ Δ₁ Θ₁ Δ₂ Θ₂ τ →
      Provable [Pc D Δ Θ (d - τ.length) τ]
        ((Pc D Δ₁ Θ₁ (d - τ.length) τ).or (Pc D Δ₂ Θ₂ (d - τ.length) τ)) →
      Provable [Pc D Δ Θ d []] ((Pc D Δ₁ Θ₁ d []).or (Pc D Δ₂ Θ₂ d []))
  | [], _, _, hole => hole
  | k :: ρ, hd, hA, hole => by
      have hd' : ρ.length ≤ d := by simp only [List.length_cons] at hd; omega
      have hf : d - ρ.length = (d - (k :: ρ).length) + 1 := by
        simp only [List.length_cons] at hd ⊢; omega
      refine or_path h0 hok hW ρ hd'
        (fun σ' hσ => hA σ' fun h => hσ ((List.suffix_cons k ρ).trans h)) ?_
      rw [hf]
      have agρ := hA ρ fun h => by have := h.length_le; simp at this
      refine closed_or_tr h0 hok ?_
      rw [tr_succ, tr_succ, tr_succ, agρ.1.1, agρ.1.2, agρ.2.1, agρ.2.2]
      refine and_or (conj_map_or (pack_or (fun x he => hW k ρ x he) hole) (fun j hj => ?_) _)
      have hsub : ∀ σ', (j :: ρ) <:+ σ' → ¬ (k :: ρ) <:+ σ' :=
        off_sub (List.suffix_refl _) hj
      exact ⟨congrArg _ (Pc_congr fun σ' hσ => (hA σ' (hsub σ' hσ)).1),
        congrArg _ (Pc_congr fun σ' hσ => (hA σ' (hsub σ' hσ)).2)⟩

/-- ⭐**A refutation at a reachable hole is one at the root.** -/
theorem bot_path (h0 : Γ₀.SlotsFrom 0) (hok : D.OK Γ₀) (hW : D.WitOK Γ₀)
    {Δ Θ : Seq σ Γ₀ D} {d : ℕ} :
    ∀ τ : Lab, τ.length ≤ d → D.Reach τ → Provable [Pc D Δ Θ (d - τ.length) τ] .bot →
      Provable [Pc D Δ Θ d []] .bot
  | [], _, _, hole => hole
  | k :: ρ, hd, hr, hole => by
      have hd' : ρ.length ≤ d := by simp only [List.length_cons] at hd; omega
      have hf : d - ρ.length = (d - (k :: ρ).length) + 1 := by
        simp only [List.length_cons] at hd ⊢; omega
      refine bot_path h0 hok hW ρ hd'
        (fun j ρ' h => hr j ρ' (h.trans (List.suffix_cons k ρ))) ?_
      rw [hf]
      refine closed_bot_tr h0 hok ?_
      rw [tr_succ]
      have hk : k ∈ D.children ρ := Tree.mem_children.mpr (hr k ρ (List.suffix_refl _))
      exact chain (conj_elim ((lk List.mem_cons_self).map .and_elim_r) _
        (List.mem_map_of_mem (f := fun k => pack D (D.ctxAt Γ₀ ρ) (k :: ρ)
          (Pc D Δ Θ (d - (k :: ρ).length) (k :: ρ))) hk))
        (sub (by lsub) (pack_bot (fun x he => hW k ρ x he) hole))

end Same

end GKN

end V12M
