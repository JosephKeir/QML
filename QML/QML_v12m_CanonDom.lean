import QML.QML_v12m_CanonWorld

/-!
# QML v12m — the canonical model: domains and denotations

* The **base domain** of a world: its base-typed terms, at any stage, up to equality in its
  theory (`World.D`).
* **Raw objects** (`RDom`), by recursion on the type: base objects, pairs, a raw object at every
  successor (`□`, the world itself included under T), an extent with a raw object at each of its
  worlds (`◇`).
* The **denotation** of a term (`rden`): a variable or a function term is its class; `□t` gives at
  a successor `d + 1` levels deeper the denotation there of `t` shifted `d` times
  (`rden_boxtm_far`; under 4 this is what `□(shift t)` gives from a proper successor on the way,
  `rden_boxtm_step`), and at the world itself the denotation of `t` collapsed (`rden_boxtm_self`);
  `◇_x t` has the extent of `x` and at each of its worlds the denotation of `t` there.  Shifting
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

variable {w}

theorem mem_lift {i j : ℕ × ℕ} (h : i ≤ j) {φ : WFF σ (w.L.ctx i) 0} :
    (⟨i, φ⟩ : w.L.sys.Sentence σ) ∈ w.T ↔
      (⟨j, WFF.mono (w.L.ctx_le h) φ⟩ : w.L.sys.Sentence σ) ∈ w.T :=
  (w.mcs.mem_lift_iff h).symm

/-- Membership from a proof at one stage. -/
theorem mem_of_provable {i : ℕ × ℕ} {Δ : List (WFF σ (w.L.ctx i) 0)} {φ : WFF σ (w.L.ctx i) 0}
    (hΔ : ∀ ψ ∈ Δ, (⟨i, ψ⟩ : w.L.sys.Sentence σ) ∈ w.T) (p : Provable Δ φ) :
    (⟨i, φ⟩ : w.L.sys.Sentence σ) ∈ w.T :=
  w.mcs.closed (StageSys.derives_of_mems hΔ p)

variable (w)

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

/-! ## Raw objects -/

/-- Raw objects of a type at a world. -/
def RDom : VarType → World σ N₀ → Type
  | .Var, w => w.D
  | .VTypeOne, _ => PUnit
  | .VTypeProd A B, w => RDom A w × RDom B w
  | .VTypeBox A, w => (w' : Succ w) → RDom A w'.1
  | .VTypeDia A, w => Σ E : Set (Succ w), (w' : E) → RDom A w'.1.1

/-- ⭐The denotation of a term at a world, computed at a stage containing its context. -/
def rden : {A : VarType} → {a : Ann A} → {Γ : Ctx} → (w : World σ N₀) → (i : ℕ × ℕ) →
    Γ.Le (w.L.ctx i) → Term σ Γ A a → RDom A w
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
  | _, _, _, w, i, e, .diatm x _ t =>
      ⟨extent w x, fun w' => rden w'.1.1 (childStage i) ((e.diaIn x).trans (extent_le w'.2 i)) t⟩
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
        (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) t)) ⟨w'.1, hr⟩ := by
  obtain ⟨d, hd'⟩ : ∃ d, w'.1.depth - u.depth = d + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_ne_zero hd).symm⟩
  have hw : w'.1.depth - w.depth = d + 1 + 1 := by
    have := hu.1
    omega
  exact (rden_boxtm_far e t w' hw).trans (rden_boxtm_far _ _ ⟨w'.1, hr⟩ hd').symm

theorem rden_sigma {A : VarType} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i))
    {p q : Σ b : Ann A, Term σ Γ A b} (h : p = q) : rden w i e p.2 = rden w i e q.2 := by
  subst h
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
  | _, _, _, .diatm _ _ t, _, i, j, _, _ =>
      congrArg (Sigma.mk _) (funext fun w' => rden_congr t w'.1.1 (childStage i) (childStage j) _ _)
  termination_by structural A => A

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
  | _, _, _, _, h, .diatm x _ t, _, i, _ =>
      congrArg (Sigma.mk _) (funext fun w' => rden_mono (h.diaIn x) t w'.1.1 (childStage i) _)
  termination_by structural A => A

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

theorem definable_dia_apply {A : VarType} {w : World σ N₀} {o : RDom (.VTypeDia A) w}
    (h : Definable (.VTypeDia A) w o) (w' : o.1) : Definable A w'.1.1 (o.2 w') := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | diatm x hx b => exact definable_rden _ b

end Canon

end V12M
