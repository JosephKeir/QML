import QML.QML_v12m_CanonShape

/-!
# QML v12m — the canonical model: domains and denotations

* The **base domain** of a world: its base-typed terms, at any stage, up to equality in its
  theory (`World.D`).
* **Raw objects** (`RDom`), by recursion on the type: base objects, pairs, a raw object at every
  successor (`□`, the world itself included under T), an extent with a raw object at each of its
  worlds and a shape (`◇`, `RPos`).  The shape is stored, not computed: the canonical model's
  shapes have to follow the laws of `Model`, which a raw object's extent and contents do not
  determine (docs §10.34).  `rawShape` reads the shape of any raw object.
* The **denotation** of a term (`rden`): a variable or a function term is its class; `□t` gives at
  a successor `d + 1` levels deeper the denotation there of `t` shifted `d` times
  (`rden_boxtm_far`; under 4 this is what `□(shift t)` gives from a proper successor on the way,
  `rden_boxtm_step`), and at the world itself the denotation of `t` collapsed (`rden_boxtm_self`);
  `◇_x t` has the extent of `x`, at each of its worlds the denotation of `t` there, and as shape
  the term's symbolic shape in the canonical shape environment (`termShp`, `cEnv`).  Shifting
  and collapsing keep the type, so this is a recursion on the type.  It does not depend on the
  stage it is computed at (`rden_congr`) and commutes with weakening (`rden_mono`).
* **Definable** raw objects are the denotations of terms; they are closed under the components of
  pairs, the values of necessary objects and the contents of possible ones.
-/

namespace V12M

variable [ModalSys]

namespace Canon

variable {σ : Signature} {N₀ : ℕ}

namespace World

variable (w : World σ N₀)

/-- Base-typed terms at some stage. -/
abbrev BTerm : Type := Σ i : ℕ × ℕ, Term σ (w.L.ctx i) .Var .var

/-- A term moved to a later stage. -/
def liftT {i j : ℕ × ℕ} (h : i ≤ j) {A : VarType} {a : Ann A} (t : Term σ (w.L.ctx i) A a) :
    Term σ (w.L.ctx j) A a :=
  Term.mono (w.L.ctx_le h) t

theorem liftT_liftT {i j k : ℕ × ℕ} (h₁ : i ≤ j) (h₂ : j ≤ k) {A : VarType} {a : Ann A}
    (t : Term σ (w.L.ctx i) A a) : w.liftT h₂ (w.liftT h₁ t) = w.liftT (h₁.trans h₂) t :=
  Term.mono_mono _ _ t


/-- Two base terms are equal in the theory. -/
def TEq (s t : w.BTerm) : Prop :=
  (⟨s.1 ⊔ t.1, .eq (w.liftT le_sup_left s.2) (w.liftT le_sup_right t.2)⟩ :
    w.L.sys.Sentence σ) ∈ w.T

variable {w}

theorem TEq_iff {s t : w.BTerm} {K : ℕ × ℕ} (hs : s.1 ≤ K) (ht : t.1 ≤ K) :
    w.TEq s t ↔ (⟨K, .eq (w.liftT hs s.2) (w.liftT ht t.2)⟩ : w.L.sys.Sentence σ) ∈ w.T := by
  unfold TEq
  rw [mem_lift (sup_le hs ht)]
  change (⟨K, .eq (w.liftT (sup_le hs ht) (w.liftT le_sup_left s.2))
    (w.liftT (sup_le hs ht) (w.liftT le_sup_right t.2))⟩ : w.L.sys.Sentence σ) ∈ w.T ↔ _
  rw [liftT_liftT, liftT_liftT]

theorem TEq_refl (s : w.BTerm) : w.TEq s s :=
  (TEq_iff le_rfl le_rfl).mpr (mem_of_provable (Δ := []) (fun _ h => absurd h List.not_mem_nil)
    ⟨Proof.eq_intro _⟩)

theorem TEq_symm {s t : w.BTerm} (h : w.TEq s t) : w.TEq t s := by
  have h' := (TEq_iff (K := s.1 ⊔ t.1) le_sup_left le_sup_right).mp h
  refine (TEq_iff le_sup_right le_sup_left).mpr (mem_of_provable (Δ := [_])
    (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact h') ?_)
  exact ⟨Proof.eq_symm_base (Proof.lookup List.mem_cons_self)⟩

theorem TEq_trans {s t u : w.BTerm} (h₁ : w.TEq s t) (h₂ : w.TEq t u) : w.TEq s u := by
  have hs : s.1 ≤ s.1 ⊔ t.1 ⊔ u.1 := le_sup_left.trans le_sup_left
  have ht : t.1 ≤ s.1 ⊔ t.1 ⊔ u.1 := le_sup_right.trans le_sup_left
  have hu : u.1 ≤ s.1 ⊔ t.1 ⊔ u.1 := le_sup_right
  have h₁' := (TEq_iff hs ht).mp h₁
  have h₂' := (TEq_iff ht hu).mp h₂
  refine (TEq_iff hs hu).mpr (mem_of_provable
    (Δ := [WFF.eq (w.liftT hs s.2) (w.liftT ht t.2), WFF.eq (w.liftT ht t.2) (w.liftT hu u.2)])
    (fun ψ hψ => ?_) ?_)
  · rcases List.mem_cons.mp hψ with rfl | hψ
    · exact h₁'
    · rw [List.mem_singleton.mp hψ]
      exact h₂'
  · exact ⟨Proof.eq_trans_base (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩

/-- Terms with the same lift to a common stage are equal in the theory. -/
theorem TEq_of_lift_eq {s t : w.BTerm} {K : ℕ × ℕ} (hs : s.1 ≤ K) (ht : t.1 ≤ K)
    (h : w.liftT hs s.2 = w.liftT ht t.2) : w.TEq s t := by
  have hr := TEq_refl (w := w) ⟨K, w.liftT hs s.2⟩
  rw [TEq_iff le_rfl le_rfl] at hr
  refine (TEq_iff hs ht).mpr ?_
  have e : w.liftT (le_refl K) (w.liftT hs s.2) = w.liftT hs s.2 := Term.mono_refl _ _
  rw [e] at hr
  rw [← h]
  exact hr

variable (w)

def setoid : Setoid w.BTerm := ⟨w.TEq, ⟨TEq_refl, TEq_symm, TEq_trans⟩⟩

/-- ⭐The base domain. -/
def D : Type := Quotient w.setoid

/-- The class of a base term. -/
def cls (i : ℕ × ℕ) (t : Term σ (w.L.ctx i) .Var .var) : w.D := Quotient.mk w.setoid ⟨i, t⟩

variable {w}

theorem cls_eq_iff {i j : ℕ × ℕ} {s : Term σ (w.L.ctx i) .Var .var}
    {t : Term σ (w.L.ctx j) .Var .var} {K : ℕ × ℕ} (hi : i ≤ K) (hj : j ≤ K) :
    w.cls i s = w.cls j t ↔
      (⟨K, .eq (w.liftT hi s) (w.liftT hj t)⟩ : w.L.sys.Sentence σ) ∈ w.T :=
  Quotient.eq.trans (TEq_iff (s := ⟨i, s⟩) (t := ⟨j, t⟩) hi hj)

theorem cls_lift {i j : ℕ × ℕ} (h : i ≤ j) (t : Term σ (w.L.ctx i) .Var .var) :
    w.cls j (w.liftT h t) = w.cls i t :=
  Quotient.sound (TEq_of_lift_eq (s := ⟨j, w.liftT h t⟩) (t := ⟨i, t⟩) le_rfl h
    (Term.mono_mono _ _ _))

end World

/-! ## Iterated shifts -/

omit [ModalSys] in
/-- An annotation shifted `n` times, innermost first. -/
def _root_.V12M.Ann.shiftIter : ℕ → {A : VarType} → Ann A → Ann A
  | 0, _, a => a
  | n + 1, _, a => Ann.shiftIter n (a.shift 0)

/-- A `□` body moved `n` views further in (under 4 when `n ≠ 0`), innermost first. -/
def _root_.V12M.Term.shiftIter : (n : ℕ) → (n ≠ 0 → ModalSys.Four = true) → {Γ : Ctx} →
    {A : VarType} → {a : Ann A} → Term σ Γ.boxIn A a →
    Term σ (Ctx.boxIter (n + 1) Γ) A (Ann.shiftIter n a)
  | 0, _, _, _, _, t => t
  | n + 1, hF, Γ, _, _, t =>
      Term.shiftIter n (fun _ => hF (Nat.succ_ne_zero n)) (Γ := Γ.boxIn)
        (Term.shift (Ctx.shifts_boxIn_boxIn (hF (Nat.succ_ne_zero n)) Γ) t)

theorem _root_.V12M.Term.shiftIter_mono : ∀ (n : ℕ) (hF : n ≠ 0 → ModalSys.Four = true)
    {Γ Γ' : Ctx} (h : Γ.Le Γ') {A : VarType} {a : Ann A} (t : Term σ Γ.boxIn A a),
    Term.shiftIter n hF (Term.mono h.boxIn t) =
      Term.mono (Ctx.Le.boxIter (n + 1) h) (Term.shiftIter n hF t)
  | 0, _, _, _, _, _, _, _ => rfl
  | n + 1, hF, Γ, Γ', h, _, _, t => by
      have hF' := hF (Nat.succ_ne_zero n)
      change Term.shiftIter n (fun _ => hF') (Term.shift (Ctx.shifts_boxIn_boxIn hF' Γ')
        (Term.mono h.boxIn t)) = _
      rw [Term.shift_mono (Ctx.shifts_boxIn_boxIn hF' Γ) (Ctx.shifts_boxIn_boxIn hF' Γ') h.boxIn
        h.boxIn.boxIn t]
      exact Term.shiftIter_mono n (fun _ => hF') h.boxIn _

/-- A `◇_x` body moved `n` views further in, its witness kept at each (under 4 without shapes when
    `n ≠ 0`): what a member of `x`'s extent kept `n` times reads (`KeepExt`), as `Term.shiftIter`
    is what a far successor reads of a `□` body. -/
def _root_.V12M.Term.shiftDia : (n : ℕ) → KeepOK n → {Γ : Ctx} → {x : VarSymb} →
    {A : VarType} → {a : Ann A} → Term σ (Γ.diaIn x) A a →
    Term σ ((Ctx.boxIter n Γ).diaIn (VarSymb.keepIter n x)) A (Ann.shiftIter n a)
  | 0, _, _, _, _, _, t => t
  | n + 1, hK, Γ, x, _, _, t =>
      Term.shiftDia n (fun _ => hK (Nat.succ_ne_zero n)) (Γ := Γ.boxIn) (x := .step x .keep)
        (Term.shift (Ctx.shifts_diaIn_keep (hK (Nat.succ_ne_zero n)).1
          (hK (Nat.succ_ne_zero n)).2 Γ x) t)

theorem _root_.V12M.Term.shiftDia_mono : ∀ (n : ℕ) (hK : KeepOK n) {Γ Γ' : Ctx} (h : Γ.Le Γ')
    {x : VarSymb} {A : VarType} {a : Ann A} (t : Term σ (Γ.diaIn x) A a),
    Term.shiftDia n hK (Term.mono (h.diaIn x) t) =
      Term.mono ((Ctx.Le.boxIter n h).diaIn _) (Term.shiftDia n hK t)
  | 0, _, _, _, _, _, _, _, _ => rfl
  | n + 1, hK, Γ, Γ', h, x, _, _, t => by
      have hF := (hK (Nat.succ_ne_zero n)).1
      have hnS := (hK (Nat.succ_ne_zero n)).2
      change Term.shiftDia n (fun _ => hK (Nat.succ_ne_zero n))
        (Term.shift (Ctx.shifts_diaIn_keep hF hnS Γ' x) (Term.mono (h.diaIn x) t)) = _
      rw [Term.shift_mono (Ctx.shifts_diaIn_keep hF hnS Γ x) (Ctx.shifts_diaIn_keep hF hnS Γ' x)
        (h.diaIn x) (h.boxIn.diaIn _) t]
      exact Term.shiftDia_mono n _ h.boxIn _

/-! ## Raw objects -/

/-- ⭐A raw possible object: an extent, a raw object at each of its worlds, and, under T, its
    **shape**, which the canonical model stores rather than computes (docs §10.34).  Gated as
    `Model.posFull` is: without T, objects with one section are one object. -/
structure RPos (w : World σ N₀) (A : VarType) (C : Succ w → Type) where
  E : Set (Succ w)
  c : (w' : E) → C w'.1
  tag : ModalSys.T = true → CShape w (.VTypeDia A)

theorem RPos.congr_cont {w : World σ N₀} {A : VarType} {C : Succ w → Type} {E : Set (Succ w)}
    {c c' : (w' : E) → C w'.1} {τ τ' : ModalSys.T = true → CShape w (.VTypeDia A)} (hc : c = c')
    (hτ : ∀ hT, τ hT = τ' hT) :
    (⟨E, c, τ⟩ : RPos w A C) = ⟨E, c', τ'⟩ := by
  subst hc
  obtain rfl : τ = τ' := funext hτ
  rfl

/-- Raw objects of a type at a world. -/
def RDom : VarType → World σ N₀ → Type
  | .Var, w => w.D
  | .VTypeOne, _ => PUnit
  | .VTypeProd A B, w => RDom A w × RDom B w
  | .VTypeBox A, w => (w' : Succ w) → RDom A w'.1
  | .VTypeDia A, w => RPos w A fun w' => RDom A w'.1

/-- ⭐Under T, the shape of a raw object: the stored shapes of its possible objects, arranged as its
    type arranges them — `Frame.domShape` for raw objects. -/
def rawShape (hT : ModalSys.T = true) : {A : VarType} → {w : World σ N₀} → RDom A w → CShape w A
  | .Var, _, _ => .var
  | .VTypeOne, _, _ => .one
  | .VTypeProd _ _, _, o => .prod (rawShape hT o.1) (rawShape hT o.2)
  | .VTypeBox _, _, o =>
      .box (Arrows.transposeShp (F := arrows σ N₀) (Root := fun _ => VarSymb) fun s =>
        rawShape hT (o s))
  | .VTypeDia _, _, o => o.3 hT
/-- Under strong T, the view term a realised witness's content is read from at the world itself:
    the view term realised by the chosen term of the realisation (`WFF.realiseAt`'s term form).
    Both terms are lifted to one stage. -/
theorem realisedLe (w : World σ N₀) {x : VarSymb} (hr : w.Realised x) {Γ : Ctx} {i : ℕ × ℕ}
    (e : Γ.Le (w.L.ctx i)) :
    (Γ.diaIn x).Le ((w.L.ctx (i ⊔ hr.data.i₀)).diaIn x) :=
  (e.trans (w.L.ctx_le le_sup_left)).diaIn x

/-- So it is declared at the stage where both it and the term live.  Through `RealDatum.hdeclOf`,
    so that this survives realisedness being read off the theory (§2d, step 4), where a stage
    order on the datum is not available. -/
theorem realisedDecl {w : World σ N₀} {x : VarSymb} (hr : w.Realised x) {Γ : Ctx} {i : ℕ × ℕ}
    (e : Γ.Le (w.L.ctx i)) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) :
    (w.L.ctx (i ⊔ hr.data.i₀)).ref x = some (.VTypeDia hr.data.A) :=
  hr.data.hdeclOf _ (hx.imp fun _ h => (w.L.ctx_le le_sup_left).ref (e.ref h))

noncomputable def realisedTerm (w : World σ N₀) {x : VarSymb} (hr : w.Realised x) {Γ : Ctx}
    {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType}
    {a : Ann A} (t : Term σ (Γ.diaIn x) A a) :
    Σ b : Ann A, Term σ (w.L.ctx (i ⊔ hr.data.i₀)) A b :=
  ⟨_, Term.realiseAtA hr.data.hT x (realisedDecl hr e hx)
    (Term.mono (w.L.ctx_le le_sup_right) hr.data.t₀) (Term.mono (realisedLe w hr e) t)⟩

/-- ⭐The denotation of a term at a world, computed at a stage containing its context. -/
noncomputable def rden : {A : VarType} → {a : Ann A} → {Γ : Ctx} → (w : World σ N₀) →
    (i : ℕ × ℕ) → Γ.Le (w.L.ctx i) → Term σ Γ A a → RDom A w
  | _, _, _, w, i, e, .var v hv => w.cls i (.var v (e.ref hv))
  | _, _, _, w, i, e, .func f => w.cls i (Term.mono e (.func f))
  | _, _, _, _, _, _, .unit => PUnit.unit
  | _, _, _, w, i, e, .pair s t => (rden w i e s, rden w i e t)
  | _, _, Γ, w, i, e, .boxtm t => fun w' =>
      match hd : w'.1.depth - w.depth with
      | 0 => rden w'.1 i (by rw [(w'.self hd).2]; exact e)
          (Term.collapse (Ctx.collapses_boxIn_self (w'.self hd).1 Γ) t)
      | d + 1 =>
          rden w'.1 (childIter (d + 1) i) (w'.chainLe hd e) (Term.shiftIter d (w'.four hd) t)
  | _, _, Γ, w, i, e, .diatm x hx t =>
      ⟨extent w x, fun w' =>
        match hd : w'.1.1.depth - w.depth with
        | 0 => ((extent_self w'.2 hd).1).symm ▸
            rden w (i ⊔ ((extent_self w'.2 hd).2).data.i₀) (Ctx.Le.refl _)
              (realisedTerm w (extent_self w'.2 hd).2 e hx t).2
        | k + 1 => rden w'.1.1 (childIter (k + 1) i) (extent_leK w'.2 hd e)
            (Term.shiftDia k (extent_far w'.2 hd).1 t),
        fun _ => Model.termShp (cEnv Γ w) 0 (.diatm x hx t)⟩
  termination_by structural A => A

/-- At the world itself, a necessary term denotes its body collapsed. -/
theorem rden_boxtm_self {A : VarType} {a : Ann A} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ}
    (e : Γ.Le (w.L.ctx i)) (t : Term σ Γ.boxIn A a) (w' : Succ w)
    (h : w'.1.depth - w.depth = 0) :
    rden w i e (.boxtm t) w' = rden w'.1 i (by rw [(w'.self h).2]; exact e)
      (Term.collapse (Ctx.collapses_boxIn_self (w'.self h).1 Γ) t) := by
  simp only [rden]
  split
  · rfl
  · omega

/-- At a successor `d + 1` levels deeper, a necessary term denotes its body shifted `d` times. -/
theorem rden_boxtm_far {A : VarType} {a : Ann A} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ}
    (e : Γ.Le (w.L.ctx i)) (t : Term σ Γ.boxIn A a) (w' : Succ w) {d : ℕ}
    (h : w'.1.depth - w.depth = d + 1) :
    rden w i e (.boxtm t) w' =
      rden w'.1 (childIter (d + 1) i) (w'.chainLe h e) (Term.shiftIter d (w'.four h) t) := by
  simp only [rden]
  split
  · omega
  · rename_i d' hd'
    obtain rfl : d' = d := by omega
    rfl

/-- At a proper successor, a necessary term denotes its body there. -/
theorem rden_boxtm_acc {A : VarType} {a : Ann A} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ}
    (e : Γ.Le (w.L.ctx i)) (t : Term σ Γ.boxIn A a) (w' : Succ w)
    (h : w'.1.depth - w.depth = 1) :
    rden w i e (.boxtm t) w' =
      rden w'.1 (childStage i) (e.boxIn.trans ((w'.acc h).boxIn_le i)) t :=
  rden_boxtm_far e t w' (d := 0) h

/-- Under 4, at a far successor a necessary term denotes what its body shifted denotes from a
    proper successor on the way. -/
theorem rden_boxtm_step {A : VarType} {a : Ann A} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ}
    (hF : ModalSys.Four = true) (e : Γ.Le (w.L.ctx i)) (t : Term σ Γ.boxIn A a) (w' : Succ w)
    {u : World σ N₀} (hu : Acc' w u) (hr : R u w'.1) (hd : w'.1.depth - u.depth ≠ 0) :
    rden w i e (.boxtm t) w' =
      rden u (childStage i) (e.boxIn.trans (hu.boxIn_le i))
        (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) t)) ⟨w'.1, ⟨hr⟩⟩ := by
  obtain ⟨d, hd'⟩ : ∃ d, w'.1.depth - u.depth = d + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_ne_zero hd).symm⟩
  have hw : w'.1.depth - w.depth = d + 1 + 1 := by
    have := hu.1
    omega
  exact (rden_boxtm_far e t w' hw).trans (rden_boxtm_far _ _ ⟨w'.1, ⟨hr⟩⟩ hd').symm

/-- ⭐At a member `k + 1` levels deeper — kept `k` times — a possible term denotes there its body
    shifted `k` times. -/
theorem rden_diatm_far {A : VarType} {a : Ann A} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ}
    (e : Γ.Le (w.L.ctx i)) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (t : Term σ (Γ.diaIn x) A a) (w' : (extent w x)) {k : ℕ}
    (hd : w'.1.1.depth - w.depth = k + 1) :
    (rden w i e (.diatm x hx t)).2 w' =
      rden w'.1.1 (childIter (k + 1) i) (extent_leK w'.2 hd e)
        (Term.shiftDia k (extent_far w'.2 hd).1 t) := by
  simp only [rden]
  split
  · omega
  · rename_i k' hd'
    obtain rfl : k' = k := by omega
    rfl

/-- At a proper successor, a possible term denotes its body there. -/
theorem rden_diatm_acc {A : VarType} {a : Ann A} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ}
    (e : Γ.Le (w.L.ctx i)) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (t : Term σ (Γ.diaIn x) A a) (w' : (extent w x)) (hd : w'.1.1.depth - w.depth = 1) :
    (rden w i e (.diatm x hx t)).2 w' =
      rden w'.1.1 (childStage i) ((e.diaIn x).trans (extent_le w'.2 hd i)) t :=
  rden_diatm_far e hx t w' (k := 0) hd

/-- The same, for a membership proof given separately and at any embedding of the view. -/
theorem rden_diatm_acc' {A : VarType} {a : Ann A} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ}
    (e : Γ.Le (w.L.ctx i)) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (t : Term σ (Γ.diaIn x) A a) (v : Succ w) (hv : v ∈ (rden w i e (.diatm x hx t)).1)
    (hd : v.1.depth - w.depth = 1) (le : (Γ.diaIn x).Le (v.1.L.ctx (childStage i))) :
    (rden w i e (.diatm x hx t)).2 ⟨v, hv⟩ = rden v.1 (childStage i) le t :=
  rden_diatm_far e hx t ⟨v, hv⟩ (k := 0) hd

/-- ⭐At the world itself, a possible term whose witness is realised denotes its body realised. -/
theorem rden_diatm_self {A : VarType} {a : Ann A} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ}
    (e : Γ.Le (w.L.ctx i)) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (t : Term σ (Γ.diaIn x) A a) (w' : (extent w x)) (hd : w'.1.1.depth - w.depth = 0) :
    (rden w i e (.diatm x hx t)).2 w' =
      ((extent_self w'.2 hd).1).symm ▸ rden w (i ⊔ ((extent_self w'.2 hd).2).data.i₀)
        (Ctx.Le.refl _) (realisedTerm w (extent_self w'.2 hd).2 e hx t).2 := by
  simp only [rden]
  split
  · rfl
  · omega

/-- ⭐Under 4 without shapes, at a member past a proper successor `u`, a possible term denotes
    what its body shifted denotes from `u`, as a possible term of the kept witness — what
    `four_dia` says of the theory (`rden_boxtm_step` for `◇`). -/
theorem rden_diatm_step (hF : ModalSys.Four = true) (hnS : ModalSys.shaped = false)
    {A : VarType} {a : Ann A} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ}
    (e : Γ.Le (w.L.ctx i)) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (t : Term σ (Γ.diaIn x) A a) (w' : (extent w x)) {u : World σ N₀} (hu : Acc' w u)
    (hr : R u w'.1.1) :
    (rden w i e (.diatm x hx t)).2 w' =
      (rden u (childStage i) (e.boxIn.trans (hu.boxIn_le i))
        (.diatm (.step x .keep) (Ctx.exists_keep_dia hF hnS hx)
          (Term.shift (Ctx.shifts_diaIn_keep hF hnS Γ x) t))).2
        ⟨⟨w'.1.1, ⟨hr⟩⟩, (extent_keep hF hnS hu ⟨w'.1.1, ⟨hr⟩⟩).mp w'.2⟩ := by
  have hnT := ModalSys.T_false_of_unshaped hnS
  obtain ⟨_, h₀, _⟩ := Succ.chain (⟨w'.1.1, ⟨hr⟩⟩ : Succ u)
  obtain ⟨k, hk⟩ : ∃ k, w'.1.1.depth - u.depth = k + 1 := by
    rcases h : w'.1.1.depth - u.depth with _ | k
    · rw [h₀ h] at hnT
      cases hnT
    · exact ⟨k, rfl⟩
  have hw : w'.1.1.depth - w.depth = k + 1 + 1 := by
    have := hu.1
    omega
  rw [rden_diatm_far e hx t w' hw, rden_diatm_far _ _ _ _ hk]
  rfl

theorem rden_sigma {A : VarType} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i))
    {p q : Σ b : Ann A, Term σ Γ A b} (h : p = q) : rden w i e p.2 = rden w i e q.2 := by
  subst h
  rfl

/-- Transporting a raw object along an equation of worlds respects equality. -/
theorem rden_transport_congr {w₁ w₂ : World σ N₀} (hw : w₁ = w₂) {A : VarType}
    {u v : RDom A w₁} (h : u = v) : hw ▸ u = hw ▸ v := by
  cases hw
  exact h

/-- Realising a weakened view term is weakening its realisation. -/
theorem realisedTerm_mono {w : World σ N₀} {x : VarSymb} (hr : w.Realised x) {Γ Γ' : Ctx}
    (h : Γ.Le Γ') {i : ℕ × ℕ} (e : Γ'.Le (w.L.ctx i))
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (hx' : ∃ X, Γ'.ref x = some (.VTypeDia X))
    {A : VarType} {a : Ann A} (t : Term σ (Γ.diaIn x) A a) :
    realisedTerm w hr e hx' (Term.mono (h.diaIn x) t) = realisedTerm w hr (h.trans e) hx t := by
  have key : Term.mono (realisedLe w hr e) (Term.mono (h.diaIn x) t) =
      Term.mono (realisedLe w hr (h.trans e)) t := by
    rw [Term.mono_mono]
  exact congrArg (fun u => (⟨_, Term.realiseAtA hr.data.hT x (realisedDecl hr e hx')
    (Term.mono (w.L.ctx_le le_sup_right) hr.data.t₀) u⟩ :
      Σ b : Ann A, Term σ (w.L.ctx (i ⊔ hr.data.i₀)) A b)) key

/-- The denotation commutes with weakening. -/
theorem rden_mono : ∀ {A : VarType} {a : Ann A} {Γ Γ' : Ctx} (h : Γ.Le Γ') (t : Term σ Γ A a)
    (w : World σ N₀) (i : ℕ × ℕ) (e : Γ'.Le (w.L.ctx i)),
    rden w i e (Term.mono h t) = rden w i (h.trans e) t
  | _, _, _, _, _, .var _ _, _, _, _ => rfl
  | _, _, _, _, h, .func f, w, i, e => by
      change w.cls i (Term.mono e (Term.mono h (.func f))) =
        w.cls i (Term.mono (h.trans e) (.func f))
      rw [Term.mono_mono]
  | _, _, _, _, _, .unit, _, _, _ => rfl
  | _, _, _, _, h, .pair s t, w, i, e => Prod.ext (rden_mono h s w i e) (rden_mono h t w i e)
  | _, _, Γ, Γ', h, .boxtm t, w, i, e => funext fun w' => by
      change rden w i e (.boxtm (Term.mono h.boxIn t)) w' = _
      rcases hd : w'.1.depth - w.depth with _ | d
      · rw [rden_boxtm_self e _ w' hd, rden_boxtm_self (h.trans e) t w' hd,
          Term.collapse_mono (Ctx.collapses_boxIn_self (w'.self hd).1 Γ)
            (Ctx.collapses_boxIn_self (w'.self hd).1 Γ') h.boxIn h t]
        exact rden_mono h _ w'.1 i _
      · rw [rden_boxtm_far e _ w' hd, rden_boxtm_far (h.trans e) t w' hd,
          Term.shiftIter_mono d _ h t]
        exact rden_mono _ _ w'.1 _ _
  | _, _, Γ, Γ', h, .diatm x hx t, w, i, e =>
      RPos.congr_cont (E := extent w x) (C := fun w' => RDom _ w'.1)
        (c := (rden w i e (.diatm x (hx.imp fun _ hh => h.ref hh)
          (Term.mono (h.diaIn x) t))).2) (c' := (rden w i (h.trans e) (.diatm x hx t)).2)
        (funext fun w' => by
          rcases hd : w'.1.1.depth - w.depth with _ | k
          · rw [rden_diatm_self _ _ _ w' hd, rden_diatm_self _ _ _ w' hd]
            exact rden_transport_congr _ (rden_sigma _
              (realisedTerm_mono _ h e hx (hx.imp fun _ hh => h.ref hh) t))
          · rw [rden_diatm_far _ _ _ w' hd, rden_diatm_far _ _ _ w' hd, Term.shiftDia_mono _ _ h]
            exact rden_mono _ _ w'.1.1 _ _)
        fun _ => (Model.termShp_mono (h := h) (ρ := cEnv Γ w) (ρ' := cEnv Γ' w) (fun _ _ _ => rfl) 0
          (.diatm x hx t))
  termination_by structural A => A

/-- Transporting a pair of raw objects along an equation of worlds is the pair of transports. -/
theorem rden_transport_world {w₁ w₂ : World σ N₀} (hw : w₁ = w₂) {Γ : Ctx} {i : ℕ × ℕ}
    (e : Γ.Le (w₁.L.ctx i)) (e2 : Γ.Le (w₂.L.ctx i)) {A : VarType} {a : Ann A} (t : Term σ Γ A a) :
    hw ▸ rden w₁ i e t = rden w₂ i e2 t := by
  cases hw
  rfl

theorem rden_transport_pair {w₁ w₂ : World σ N₀} (hw : w₁ = w₂) {A B : VarType}
    (u : RDom A w₁) (v : RDom B w₁) :
    (hw ▸ ((u, v) : RDom (.VTypeProd A B) w₁) : RDom (.VTypeProd A B) w₂) = (hw ▸ u, hw ▸ v) := by
  cases hw
  rfl

/-- The denotation does not depend on the stage it is computed at. -/
theorem rden_congr : ∀ {A : VarType} {a : Ann A} {Γ : Ctx} (t : Term σ Γ A a)
    (w : World σ N₀) (i j : ℕ × ℕ) (e : Γ.Le (w.L.ctx i)) (e' : Γ.Le (w.L.ctx j)),
    rden w i e t = rden w j e' t
  | _, _, _, .var _ _, w, i, j, _, _ =>
      Quotient.sound (World.TEq_of_lift_eq (w := w) (le_sup_left (b := j))
        (le_sup_right (a := i)) rfl)
  | _, _, _, .func _, w, i, j, _, _ =>
      Quotient.sound (World.TEq_of_lift_eq (w := w) (le_sup_left (b := j))
        (le_sup_right (a := i)) ((Term.mono_mono _ _ _).trans (Term.mono_mono _ _ _).symm))
  | _, _, _, .unit, _, _, _, _, _ => rfl
  | _, _, _, .pair s t, w, i, j, e, e' =>
      Prod.ext (rden_congr s w i j e e') (rden_congr t w i j e e')
  | _, _, _, .boxtm t, w, i, j, e, e' => funext fun w' => by
      rcases h : w'.1.depth - w.depth with _ | d
      · rw [rden_boxtm_self e t w' h, rden_boxtm_self e' t w' h]
        exact rden_congr _ w'.1 i j _ _
      · rw [rden_boxtm_far e t w' h, rden_boxtm_far e' t w' h]
        exact rden_congr _ w'.1 _ _ _ _
  | _, _, _, .diatm x hx t, w, i, j, e, e' =>
      RPos.congr_cont (E := extent w x) (C := fun w' => RDom _ w'.1)
        (c := (rden w i e (.diatm x hx t)).2)
        (c' := (rden w j e' (.diatm x hx t)).2)
        (funext fun w' => by
        rcases hd : w'.1.1.depth - w.depth with _ | k
        · rw [rden_diatm_self _ _ _ w' hd, rden_diatm_self _ _ _ w' hd]
          refine rden_transport_congr _ ?_
          have hr := (extent_self w'.2 hd).2
          have h₁ : (w.L.ctx (i ⊔ hr.data.i₀)).Le
              (w.L.ctx ((i ⊔ hr.data.i₀) ⊔ (j ⊔ hr.data.i₀))) := w.L.ctx_le le_sup_left
          have h₂ : (w.L.ctx (j ⊔ hr.data.i₀)).Le
              (w.L.ctx ((i ⊔ hr.data.i₀) ⊔ (j ⊔ hr.data.i₀))) := w.L.ctx_le le_sup_right
          have key : Term.mono h₁ (realisedTerm w hr e hx t).2 =
              Term.mono h₂ (realisedTerm w hr e' hx t).2 := by
            simp only [realisedTerm]
            rw [Term.mono_realiseAtA hr.data.hT _
                (hcA' := hr.data.hdeclOf _ (hx.imp fun _ h =>
                  (w.L.ctx_le (le_sup_left.trans le_sup_left)).ref (e.ref h))),
              Term.mono_realiseAtA hr.data.hT _
                (hcA' := hr.data.hdeclOf _ (hx.imp fun _ h =>
                  (w.L.ctx_le (le_sup_left.trans le_sup_left)).ref (e.ref h))),
              Term.mono_mono, Term.mono_mono, Term.mono_mono, Term.mono_mono]
          calc rden w (i ⊔ hr.data.i₀) (Ctx.Le.refl _) (realisedTerm w hr e hx t).2
              = rden w _ h₁ (realisedTerm w hr e hx t).2 := rden_congr _ w _ _ _ _
            _ = rden w _ (Ctx.Le.refl _) (Term.mono h₁ (realisedTerm w hr e hx t).2) :=
                (rden_mono h₁ _ w _ (Ctx.Le.refl _)).symm
            _ = rden w _ (Ctx.Le.refl _) (Term.mono h₂ (realisedTerm w hr e' hx t).2) := by
                rw [key]
            _ = rden w _ h₂ (realisedTerm w hr e' hx t).2 := rden_mono h₂ _ w _ (Ctx.Le.refl _)
            _ = rden w (j ⊔ hr.data.i₀) (Ctx.Le.refl _) (realisedTerm w hr e' hx t).2 :=
                rden_congr _ w _ _ _ _
        · rw [rden_diatm_far _ _ _ w' hd, rden_diatm_far _ _ _ w' hd]
          exact rden_congr _ w'.1.1 _ _ _ _) fun _ => rfl
  termination_by structural A => A


/-- The denotations of the η-expansions of an address in two nested contexts agree. -/
theorem rden_eta_le {Γ₁ Γ₂ : Ctx} (h : Γ₁.Le Γ₂) {w : World σ N₀} {i j : ℕ × ℕ}
    (e₁ : Γ₁.Le (w.L.ctx i)) (e₂ : Γ₂.Le (w.L.ctx j)) (v : VarSymb) (T : VarType)
    (p₁ : Γ₁.ref v = some T) (p₂ : Γ₂.ref v = some T) :
    rden w i e₁ (Term.eta (σ := σ) v T p₁) = rden w j e₂ (Term.eta v T p₂) := by
  rw [show Term.eta (σ := σ) v T p₂ = Term.mono h (Term.eta v T p₁) from
    (Term.mono_eta h v T p₁).symm, rden_mono]
  exact rden_congr _ _ _ _ _ _

/-! ## The stored shapes are the symbolic ones -/

/-- `d + 1` levels deeper, a `□` body read through `succAddr` has the shape of its `d`-fold
    shift. -/
theorem termShp_shiftIter_cEnv (w : World σ N₀) :
    ∀ (d : ℕ) (hF : d ≠ 0 → ModalSys.Four = true) {Γ : Ctx} {A : VarType} {a : Ann A}
      (t : Term σ Γ.boxIn A a),
      Model.termShp (cEnv (Ctx.boxIter (d + 1) Γ) w) 0 (Term.shiftIter d hF t) =
        Model.termShp (canonEnvF Γ.boxIn w (VarSymb.shiftIter d)) 0 t
  | 0, _, _, _, _, _ => rfl
  | d + 1, hF, Γ, _, _, t => by
      have hF' := hF (Nat.succ_ne_zero d)
      refine (termShp_shiftIter_cEnv w d (fun _ => hF') (Γ := Γ.boxIn)
        (Term.shift (Ctx.shifts_boxIn_boxIn hF' Γ) t)).trans ?_
      refine Model.termShp_shift ?_ t
      intro v T hv
      rw [canonEnvF_ref _ _ (fun v s hs => VarSymb.shiftIter_proj (d + 1) v s hs),
        canonEnvF_ref _ _ (fun v s hs => VarSymb.shiftIter_proj d v s hs)]
      rfl

/-- ⭐**The stored shape is the symbolic one**: a term's denotation has the shape `termShp` computes
    for it in the canonical shape environment.  For a `◇` term this is `rden`'s definition.  A `□`
    term's values sit at the successors, where the environment pushed into `□` is the successor's
    own read through `succAddr` (`cEnv_boxPush`) — what collapsing the body (at the world itself)
    and shifting it (further on) need. -/
theorem rawShape_rden (hT : ModalSys.T = true) : ∀ {A : VarType} {a : Ann A} {Γ : Ctx}
    (w : World σ N₀) (i : ℕ × ℕ) (e : Γ.Le (w.L.ctx i)) (t : Term σ Γ A a),
    rawShape hT (rden w i e t) = Model.termShp (cEnv Γ w) 0 t
  | _, _, _, _, _, _, .var _ _ => rfl
  | _, _, _, _, _, _, .func _ => rfl
  | _, _, _, _, _, _, .unit => rfl
  | _, _, _, w, i, e, .pair s t => by
      change Shp.prod (rawShape hT (rden w i e s)) (rawShape hT (rden w i e t)) = _
      rw [rawShape_rden hT w i e s, rawShape_rden hT w i e t]
      rfl
  | _, _, Γ, w, i, e, .boxtm t => by
      change Shp.box (Arrows.transposeShp (F := arrows σ N₀) (Root := fun _ => VarSymb) fun s =>
          rawShape hT (rden w i e (.boxtm t) s)) =
        Shp.box (Model.termShp ((cEnv Γ w).boxPush 0) (0 + 1) t)
      rw [Model.termShp_transpose ((cEnv Γ w).boxPush 0)
        (fun s => canonEnvF Γ.boxIn s.1 (succAddr w s.1)) 0 (cEnv_boxPush Γ w) t]
      refine congrArg Shp.box (congrArg _ (funext fun s => ?_))
      rcases hd : s.1.depth - w.depth with _ | d
      · rw [rden_boxtm_self e t s hd, rawShape_rden hT, termShp_collapse_cEnv (Succ.self s hd).1,
          show succAddr w s.1 = fun v => v.collapse 0 from funext (succAddr_zero hd)]
      · rw [rden_boxtm_far e t s hd, rawShape_rden hT, termShp_shiftIter_cEnv,
          show succAddr w s.1 = VarSymb.shiftIter d from funext (succAddr_succ hd)]
  | _, _, _, _, _, _, .diatm _ _ _ => rfl
  termination_by structural A => A

/-- The realised content of a pair is the pair of realised contents. -/
theorem rden_realisedTerm_pair {w : World σ N₀} {x : VarSymb} (hr : w.Realised x) {Γ : Ctx}
    {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A B : VarType}
    {a : Ann A} {b : Ann B}
    (s : Term σ (Γ.diaIn x) A a) (t : Term σ (Γ.diaIn x) B b) :
    rden w (i ⊔ hr.data.i₀) (Ctx.Le.refl _) (realisedTerm w hr e hx (Term.pair s t)).2 =
      ((rden w (i ⊔ hr.data.i₀) (Ctx.Le.refl _) (realisedTerm w hr e hx s).2,
        rden w (i ⊔ hr.data.i₀) (Ctx.Le.refl _) (realisedTerm w hr e hx t).2) :
        RDom (.VTypeProd A B) w) :=
  rfl

/-- ⭐The realised content of a term of the `□` view is what the term denotes here: realisation
    collapses it, so the witness plays no part. -/
theorem rden_realisedTerm_mono_boxIn {w : World σ N₀} {x : VarSymb} (hr : w.Realised x) {Γ : Ctx}
    {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType}
    {a : Ann A} (b : Term σ Γ.boxIn A a) :
    rden w (i ⊔ hr.data.i₀) (Ctx.Le.refl _)
        (realisedTerm w hr e hx (Term.mono (Ctx.le_boxIn_diaIn Γ x) b)).2 =
      rden w i e (Term.collapse (Ctx.collapses_boxIn_self hr.T Γ) b) := by
  have hle : Γ.boxIn.Le (w.L.ctx (i ⊔ hr.data.i₀)).boxIn :=
    (e.trans (w.L.ctx_le le_sup_left)).boxIn
  have hcomb : Term.mono (realisedLe w hr e) (Term.mono (Ctx.le_boxIn_diaIn Γ x) b) =
      Term.mono (Ctx.le_boxIn_diaIn (w.L.ctx (i ⊔ hr.data.i₀)) x) (Term.mono hle b) := by
    rw [Term.mono_mono, Term.mono_mono]
  simp only [realisedTerm]
  rw [hcomb, rden_sigma _ (Term.realiseAtA_mono_boxIn hr.data.hT x
      (realisedDecl hr e hx) _ (Term.mono hle b)),
    Term.collapse_mono (Ctx.collapses_boxIn_self hr.T Γ)
      (Ctx.collapses_boxIn_self hr.data.hT (w.L.ctx (i ⊔ hr.data.i₀))) hle
      (e.trans (w.L.ctx_le le_sup_left)) b,
    rden_mono]
  exact rden_congr _ _ _ _ _ _

/-- A base term denotes its class. -/
theorem rden_var_cls {w : World σ N₀} {i : ℕ × ℕ} :
    ∀ (t : Term σ (w.L.ctx i) .Var .var), rden w i (Ctx.Le.refl _) t = w.cls i t
  | .var _ _ => rfl
  | .func f => by
      change w.cls i (Term.mono (Ctx.Le.refl _) (.func f)) = _
      rw [Term.mono_refl]

/-! ## Definable objects -/

/-- ⭐The raw objects denoted by terms. -/
def Definable (A : VarType) (w : World σ N₀) (o : RDom A w) : Prop :=
  ∃ (i : ℕ × ℕ) (a : Ann A) (t : Term σ (w.L.ctx i) A a), rden w i (Ctx.Le.refl _) t = o

theorem definable_rden {A : VarType} {a : Ann A} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ}
    (e : Γ.Le (w.L.ctx i)) (t : Term σ Γ A a) : Definable A w (rden w i e t) :=
  ⟨i, a, Term.mono e t, by rw [rden_mono]⟩

theorem definable_var {w : World σ N₀} (d : w.D) : Definable .Var w d :=
  Quotient.inductionOn d fun s => ⟨s.1, .var, s.2, rden_var_cls s.2⟩

theorem definable_unit {w : World σ N₀} (o : RDom .VTypeOne w) : Definable .VTypeOne w o :=
  ⟨(0, 0), .one, .unit, rfl⟩

theorem definable_fst {A B : VarType} {w : World σ N₀} {o : RDom (.VTypeProd A B) w}
    (h : Definable (.VTypeProd A B) w o) : Definable A w o.1 := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | pair s _ => exact ⟨i, _, s, rfl⟩

theorem definable_snd {A B : VarType} {w : World σ N₀} {o : RDom (.VTypeProd A B) w}
    (h : Definable (.VTypeProd A B) w o) : Definable B w o.2 := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | pair _ u => exact ⟨i, _, u, rfl⟩

theorem definable_pair {A B : VarType} {w : World σ N₀} {o₁ : RDom A w} {o₂ : RDom B w}
    (h₁ : Definable A w o₁) (h₂ : Definable B w o₂) :
    Definable (.VTypeProd A B) w ((o₁, o₂) : RDom (.VTypeProd A B) w) := by
  obtain ⟨i₁, a₁, t₁, rfl⟩ := h₁
  obtain ⟨i₂, a₂, t₂, rfl⟩ := h₂
  refine ⟨i₁ ⊔ i₂, _, .pair (w.liftT le_sup_left t₁) (w.liftT le_sup_right t₂), Prod.ext ?_ ?_⟩
  · change rden w (i₁ ⊔ i₂) _ (Term.mono _ t₁) = _
    rw [rden_mono]
    exact rden_congr _ _ _ _ _ _
  · change rden w (i₁ ⊔ i₂) _ (Term.mono _ t₂) = _
    rw [rden_mono]
    exact rden_congr _ _ _ _ _ _

theorem definable_box_apply {A : VarType} {w : World σ N₀} {o : RDom (.VTypeBox A) w}
    (h : Definable (.VTypeBox A) w o) (w' : Succ w) : Definable A w'.1 (o w') := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | boxtm b =>
      rcases hd : w'.1.depth - w.depth with _ | d
      · rw [rden_boxtm_self _ b w' hd]
        exact definable_rden _ _
      · rw [rden_boxtm_far _ b w' hd]
        exact definable_rden _ _

/-- Definability transports along an equation of worlds. -/
theorem definable_transport {w₁ w₂ : World σ N₀} (hw : w₁ = w₂) {A : VarType} {u : RDom A w₁}
    (h : Definable A w₁ u) : Definable A w₂ (hw ▸ u) := by
  cases hw
  exact h

theorem definable_dia_apply {A : VarType} {w : World σ N₀} {o : RDom (.VTypeDia A) w}
    (h : Definable (.VTypeDia A) w o) (w' : o.1) : Definable A w'.1.1 (o.2 w') := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | diatm x hx b =>
      rcases hd : w'.1.1.depth - w.depth with _ | k
      · rw [rden_diatm_self _ _ _ w' hd]
        exact definable_transport _ (definable_rden _ _)
      · rw [rden_diatm_far _ _ _ w' hd]
        exact definable_rden _ _


/-! ## Faithfulness: the denotation respects a provable equality

At a `◇`-free type, two terms the theory equates denote alike.  This is what naming an object by an
address buys (§2d): the realising term of a datum may be replaced by `η b` exactly because the two
denote the same thing.  The `□` case travels to the successors, so it is split off as
⭐`rden_eqRec_far`, taking the type-level induction hypothesis as a parameter — the same shape as
`interp_box_far` on the model side. -/

/-- A base term's denotation is its class, at any embedding. -/
theorem rden_base_cls {w : World σ N₀} {Γ : Ctx} {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) :
    ∀ (t : Term σ Γ .Var .var), rden w i e t = w.cls i (Term.mono e t)
  | .var _ _ => rfl
  | .func _ => rfl

/-- ⭐**Faithfulness at a proper successor**: a necessary equation in the theory makes the two
    necessary terms denote alike `d + 1` steps in.  At `d = 0` this is the first successor's
    necessary contents; beyond it, `Proof.four_box` pushes the equation one step further each time,
    as `interp_box_far` does on the model side. -/
theorem rden_eqRec_far {A : VarType}
    (IH : ∀ {Γ : Ctx} {a : Ann A} (t s : Term σ Γ A a) {w : World σ N₀} {i : ℕ × ℕ}
      (e : Γ.Le (w.L.ctx i)),
      (⟨i, eqRec A (Term.mono e t) (Term.mono e s)⟩ : w.L.sys.Sentence σ) ∈ w.T →
      rden w i e t = rden w i e s) :
    ∀ (d : ℕ) {Γ : Ctx} {a : Ann A} (t s : Term σ Γ.boxIn A a) {w : World σ N₀} {i : ℕ × ℕ}
      (e : Γ.Le (w.L.ctx i)),
      (⟨i, .box (eqRec A (Term.mono e.boxIn t) (Term.mono e.boxIn s))⟩ :
        w.L.sys.Sentence σ) ∈ w.T →
      ∀ (w' : Succ w), w'.1.depth - w.depth = d + 1 →
        rden w i e (.boxtm t) w' = rden w i e (.boxtm s) w'
  | 0, _, _, t, s, w, i, e, hmem, w', hd => by
      rw [rden_boxtm_acc e t w' hd, rden_boxtm_acc e s w' hd]
      refine IH t s _ ?_
      have hb := (w'.acc hd).2.2.1 i (eqRec A (Term.mono e.boxIn t) (Term.mono e.boxIn s))
        (childStage i) ((w'.acc hd).boxIn_le i) hmem
      rwa [eqRec_mono, Term.mono_mono, Term.mono_mono] at hb
  | d + 1, Γ, _, t, s, w, i, e, hmem, w', hd => by
      obtain ⟨u, hu, hr, hd'⟩ := w'.split hd
      have hF : ModalSys.Four = true := w'.four hd (Nat.succ_ne_zero d)
      rw [rden_boxtm_step hF e t w' hu hr (by omega), rden_boxtm_step hF e s w' hu hr (by omega)]
      refine rden_eqRec_far IH d _ _ (e.boxIn.trans (hu.boxIn_le i)) ?_ ⟨w'.1, ⟨hr⟩⟩ hd'
      have h4 : (⟨i, .box (.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF _) Ctx.NoSlots.slots
          (eqRec A (Term.mono e.boxIn t) (Term.mono e.boxIn s))))⟩ :
          w.L.sys.Sentence σ) ∈ w.T :=
        World.mem_of_provable (Δ := [.box (eqRec A (Term.mono e.boxIn t) (Term.mono e.boxIn s))])
          (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hmem)
          ⟨Proof.four_box hF (Proof.lookup List.mem_cons_self)⟩
      have hb := hu.2.2.1 i _ (childStage i) (hu.boxIn_le i) h4
      simp only [eqRec_shift, WFF.mono, eqRec_mono,
        Term.shift_mono (Ctx.shifts_boxIn_boxIn hF Γ) (Ctx.shifts_boxIn_boxIn hF (w.L.ctx i))
          e.boxIn e.boxIn.boxIn, Term.mono_mono] at hb
      exact hb


/-- ⭐**Faithfulness**: at a `◇`-free type, two terms the theory equates denote alike.  Base by
    `World.cls_eq_iff`, `𝟙` trivially, `×` componentwise, and `□` at each successor — the world
    itself by `Proof.T_box`, a proper one by `rden_eqRec_far`.  There is no `◇` case, and none is
    wanted: equality there is a `□_x` inside a witness's own extent, and `Here` — what faithfulness
    is for — is `◇`-free (§2d). -/
theorem rden_eqRec : ∀ (A : VarType), A.diaFree = true →
    ∀ {Γ : Ctx} {a : Ann A} (t s : Term σ Γ A a) (w : World σ N₀) (i : ℕ × ℕ)
      (e : Γ.Le (w.L.ctx i)),
      (⟨i, eqRec A (Term.mono e t) (Term.mono e s)⟩ : w.L.sys.Sentence σ) ∈ w.T →
      rden w i e t = rden w i e s
  | .Var, _, _, .var, t, s, w, i, e, h => by
      rw [eqRec_Var] at h
      rw [rden_base_cls e t, rden_base_cls e s, World.cls_eq_iff (le_refl i) (le_refl i)]
      change (⟨i, WFF.eq (Term.mono (w.L.ctx_le (le_refl i)) (Term.mono e t))
        (Term.mono (w.L.ctx_le (le_refl i)) (Term.mono e s))⟩ : w.L.sys.Sentence σ) ∈ w.T
      rw [Term.mono_mono, Term.mono_mono]
      exact h
  | .VTypeOne, _, _, .one, .unit, .unit, _, _, _, _ => rfl
  | .VTypeProd A B, hAB, _, .prod _ _, .pair t₁ t₂, .pair s₁ s₂, w, i, e, h => by
      simp only [VarType.diaFree, Bool.and_eq_true] at hAB
      have h' := (w.mcs.and_mem_iff (φ := eqRec A (Term.mono e t₁) (Term.mono e s₁))
        (ψ := eqRec B (Term.mono e t₂) (Term.mono e s₂))).mp h
      exact Prod.ext (rden_eqRec A hAB.1 t₁ s₁ w i e h'.1)
        (rden_eqRec B hAB.2 t₂ s₂ w i e h'.2)
  | .VTypeBox A, hA, Γ, .box _, .boxtm t, .boxtm s, w, i, e, h => by
      funext w'
      obtain ⟨w₁, hw₁⟩ := w'
      rcases hd : w₁.depth - w.depth with _ | d
      · obtain ⟨hT, hw⟩ := Succ.self ⟨w₁, hw₁⟩ hd
        change w₁ = w at hw
        subst hw
        rw [rden_boxtm_self e t ⟨w₁, hw₁⟩ hd, rden_boxtm_self e s ⟨w₁, hw₁⟩ hd]
        refine rden_eqRec A hA _ _ _ i _ ?_
        have hb := World.mem_of_provable
          (Δ := [.box (eqRec A (Term.mono e.boxIn t) (Term.mono e.boxIn s))])
          (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact h)
          ⟨Proof.T_box hT (Proof.lookup List.mem_cons_self)⟩
        rw [eqRec_collapse,
          Term.collapse_mono (Ctx.collapses_boxIn_self hT Γ)
            (Ctx.collapses_boxIn_self hT (w₁.L.ctx i)) e.boxIn e,
          Term.collapse_mono (Ctx.collapses_boxIn_self hT Γ)
            (Ctx.collapses_boxIn_self hT (w₁.L.ctx i)) e.boxIn e] at hb
        exact hb
      · exact rden_eqRec_far
          (fun {_} {_} t' s' {_} {_} e' h' => rden_eqRec A hA t' s' _ _ e' h') d t s e h
          ⟨w₁, hw₁⟩ hd

end Canon

end V12M
