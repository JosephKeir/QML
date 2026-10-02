import QML.QML_v12m_BFair
import QML.QML_v12m_CanonFunc

/-!
# QML v12m — B's canonical model: worlds

A **world** of the canonical model for B is what a node of the chain becomes in the limit: at each
stage `i` a list of variable types `l i` (growing by prefixing), a maximal consistent theory
`M i` over them (growing), and Henkin witnesses for existentials and failing universals.

As in the staged canonical model (`QML_v12m_CanonDom`): the base domain is the base-typed terms at
any stage up to provable equality (`BWorld.D`), and the signature acts on classes
(`BWorld.canonFunc`, `BWorld.canonRel`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-- ⭐A world of the canonical model for B. -/
structure BWorld (σ : Signature) where
  l : ℕ → List VarType
  suf : ∀ {i j : ℕ}, i ≤ j → l i <:+ l j
  M : ∀ i, Set (WFF σ (ctxOf (l i)) 0)
  mcs : ∀ i, Theory.IsMCS (M i)
  sub : ∀ {i j : ℕ} (h : i ≤ j) (φ : WFF σ (ctxOf (l i)) 0), φ ∈ M i →
    WFF.mono (ctxOf_le_of_suffix (suf h)) φ ∈ M j
  /-- Henkin witnessing at a **declared root** (the network declares a fresh variable), which
      naming a `Here` atom's content needs (`Canon.RootWitnessed`); `BWorld.exW_term` is the
      term form. -/
  exW : ∀ {i : ℕ} {A : VarType} {ψ : WFF σ ((ctxOf (l i)).insert (.bnd 0) A) 1},
    .ex A ψ ∈ M i → ∃ (j : ℕ) (hij : i ≤ j) (c : ℕ)
      (hc : (ctxOf (l j)).ref (.root (.free c)) = some A),
      WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free c)) A hc)
        (WFF.mono ((ctxOf_le_of_suffix (suf hij)).insert _ A) ψ) ∈ M j
  allW : ∀ {i : ℕ} {A : VarType} {ψ : WFF σ ((ctxOf (l i)).insert (.bnd 0) A) 1},
    (WFF.all A ψ).neg ∈ M i → ∃ (j : ℕ) (hij : i ≤ j) (a : Ann A) (t : Term σ (ctxOf (l j)) A a),
      (WFF.instantiate Ctx.NoSlots.slots t
        (WFF.mono ((ctxOf_le_of_suffix (suf hij)).insert _ A) ψ)).neg ∈ M j

namespace BWorld

variable (w : BWorld σ)

/-- The context at a stage. -/
abbrev ctx (i : ℕ) : Ctx := ctxOf (w.l i)

theorem le {i j : ℕ} (h : i ≤ j) : (w.ctx i).Le (w.ctx j) := ctxOf_le_of_suffix (w.suf h)

/-- Henkin witnessing with a term: a declared root's η-expansion. -/
theorem exW_term {i : ℕ} {A : VarType} {ψ : WFF σ ((ctxOf (w.l i)).insert (.bnd 0) A) 1}
    (h : .ex A ψ ∈ w.M i) : ∃ (j : ℕ) (hij : i ≤ j) (a : Ann A) (t : Term σ (ctxOf (w.l j)) A a),
      WFF.instantiate Ctx.NoSlots.slots t
        (WFF.mono ((ctxOf_le_of_suffix (w.suf hij)).insert _ A) ψ) ∈ w.M j := by
  obtain ⟨j, hij, c, hc, hm⟩ := w.exW h
  exact ⟨j, hij, _, _, hm⟩

variable {w}

theorem mem_lift {i j : ℕ} (h : i ≤ j) {φ : WFF σ (w.ctx i) 0} :
    φ ∈ w.M i ↔ WFF.mono (w.le h) φ ∈ w.M j :=
  ⟨w.sub h φ, fun hφ => mem_of_mono_mem (w.le h) (w.mcs i) (w.mcs j) (w.sub h) hφ⟩

/-- Membership does not depend on how a formula is weakened to a stage. -/
theorem mem_mono_congr {Γ : Ctx} {i j : ℕ} (hi : Γ.Le (w.ctx i)) (hj : Γ.Le (w.ctx j))
    {φ : WFF σ Γ 0} : WFF.mono hi φ ∈ w.M i ↔ WFF.mono hj φ ∈ w.M j := by
  rw [mem_lift (le_max_left i j), mem_lift (w := w) (le_max_right i j), WFF.mono_mono,
    WFF.mono_mono]

theorem mem_of_provable {i : ℕ} {Δ : List (WFF σ (w.ctx i) 0)} {φ : WFF σ (w.ctx i) 0}
    (hΔ : ∀ ψ ∈ Δ, ψ ∈ w.M i) (p : Provable Δ φ) : φ ∈ w.M i :=
  (w.mcs i).closed ⟨Δ, hΔ, p⟩

variable (w)

/-- Base-typed terms at some stage. -/
abbrev BTerm : Type := Σ i : ℕ, Term σ (w.ctx i) .Var .var

/-- A term moved to a later stage. -/
def liftT {i j : ℕ} (h : i ≤ j) {A : VarType} {a : Ann A} (t : Term σ (w.ctx i) A a) :
    Term σ (w.ctx j) A a :=
  Term.mono (w.le h) t

theorem liftT_liftT {i j k : ℕ} (h₁ : i ≤ j) (h₂ : j ≤ k) {A : VarType} {a : Ann A}
    (t : Term σ (w.ctx i) A a) : w.liftT h₂ (w.liftT h₁ t) = w.liftT (h₁.trans h₂) t :=
  Term.mono_mono _ _ t

/-- Two base terms are equal in the theory. -/
def TEq (s t : w.BTerm) : Prop :=
  WFF.eq (w.liftT (le_max_left s.1 t.1) s.2) (w.liftT (le_max_right s.1 t.1) t.2) ∈
    w.M (max s.1 t.1)

variable {w}

theorem TEq_iff {s t : w.BTerm} {K : ℕ} (hs : s.1 ≤ K) (ht : t.1 ≤ K) :
    w.TEq s t ↔ WFF.eq (w.liftT hs s.2) (w.liftT ht t.2) ∈ w.M K := by
  unfold TEq
  rw [mem_lift (max_le hs ht)]
  change WFF.eq (w.liftT (max_le hs ht) (w.liftT _ s.2)) (w.liftT (max_le hs ht) (w.liftT _ t.2))
    ∈ w.M K ↔ _
  rw [liftT_liftT, liftT_liftT]

theorem TEq_refl (s : w.BTerm) : w.TEq s s :=
  (TEq_iff le_rfl le_rfl).mpr (mem_of_provable (Δ := []) (fun _ h => absurd h List.not_mem_nil)
    ⟨Proof.eq_intro _⟩)

theorem TEq_symm {s t : w.BTerm} (h : w.TEq s t) : w.TEq t s := by
  have h' := (TEq_iff (K := max s.1 t.1) (le_max_left _ _) (le_max_right _ _)).mp h
  refine (TEq_iff (le_max_right _ _) (le_max_left _ _)).mpr (mem_of_provable (Δ := [_])
    (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact h') ?_)
  exact ⟨Proof.eq_symm_base (Proof.lookup List.mem_cons_self)⟩

theorem TEq_trans {s t u : w.BTerm} (h₁ : w.TEq s t) (h₂ : w.TEq t u) : w.TEq s u := by
  have hs : s.1 ≤ max (max s.1 t.1) u.1 := (le_max_left _ _).trans (le_max_left _ _)
  have ht : t.1 ≤ max (max s.1 t.1) u.1 := (le_max_right _ _).trans (le_max_left _ _)
  have hu : u.1 ≤ max (max s.1 t.1) u.1 := le_max_right _ _
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
theorem TEq_of_lift_eq {s t : w.BTerm} {K : ℕ} (hs : s.1 ≤ K) (ht : t.1 ≤ K)
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
def cls (i : ℕ) (t : Term σ (w.ctx i) .Var .var) : w.D := Quotient.mk w.setoid ⟨i, t⟩

variable {w}

theorem cls_eq_iff {i j : ℕ} {s : Term σ (w.ctx i) .Var .var} {t : Term σ (w.ctx j) .Var .var}
    {K : ℕ} (hi : i ≤ K) (hj : j ≤ K) :
    w.cls i s = w.cls j t ↔ WFF.eq (w.liftT hi s) (w.liftT hj t) ∈ w.M K :=
  Quotient.eq.trans (TEq_iff (s := ⟨i, s⟩) (t := ⟨j, t⟩) hi hj)

theorem cls_lift {i j : ℕ} (h : i ≤ j) (t : Term σ (w.ctx i) .Var .var) :
    w.cls j (w.liftT h t) = w.cls i t :=
  Quotient.sound (TEq_of_lift_eq (s := ⟨j, w.liftT h t⟩) (t := ⟨i, t⟩) le_rfl h
    (Term.mono_mono _ _ _))

/-! ## The signature on classes -/

omit [ModalSys] in
/-- A common stage for finitely many stages. -/
def stageSup {n : ℕ} (f : Fin n → ℕ) : ℕ := Finset.univ.sup f

omit [ModalSys] in
theorem le_stageSup {n : ℕ} (f : Fin n → ℕ) (k : Fin n) : f k ≤ stageSup f :=
  Finset.le_sup (Finset.mem_univ k)

variable (w)

/-- Representatives of classes, at a common stage. -/
noncomputable def outArgs {n : ℕ} (args : Fin n → w.D) :
    Fin n → Term σ (w.ctx (stageSup fun k => (args k).out.1)) .Var .var :=
  fun k => w.liftT (le_stageSup (fun k => (args k).out.1) k) (args k).out.2

/-- ⭐The canonical interpretation of a function symbol. -/
noncomputable def canonFunc (f : σ.FuncSyms) (args : Fin (σ.funcArity f) → w.D) : w.D :=
  w.cls (stageSup fun k => (args k).out.1)
    (.func ((Spine.ofFn (w.outArgs args)).fill (.F ⟨f, rfl⟩)))

/-- ⭐The canonical interpretation of a relation symbol. -/
noncomputable def canonRel (r : σ.RelSyms) (args : Fin (σ.relArity r) → w.D) : Prop :=
  WFF.atom ((Spine.ofFn (w.outArgs args)).fillR (.R ⟨r, rfl⟩)) ∈
    w.M (stageSup fun k => (args k).out.1)

variable {w}

theorem outArgs_eq {n : ℕ} {i : ℕ} (ts : Fin n → Term σ (w.ctx i) .Var .var)
    (K : ℕ) (hs : (stageSup fun k => (w.cls i (ts k)).out.1) ≤ K) (hi : i ≤ K) (k : Fin n) :
    WFF.eq (w.liftT hs (w.outArgs (fun k => w.cls i (ts k)) k)) (w.liftT hi (ts k)) ∈ w.M K := by
  have h := Quotient.out_eq (s := w.setoid) (w.cls i (ts k))
  have h' : w.TEq (w.cls i (ts k)).out ⟨i, ts k⟩ := Quotient.exact h
  rw [TEq_iff ((le_stageSup _ k).trans hs) hi] at h'
  unfold outArgs
  rw [liftT_liftT]
  exact h'

theorem canonFunc_cls (f : σ.FuncSyms) {i : ℕ}
    (ts : Fin (σ.funcArity f) → Term σ (w.ctx i) .Var .var) :
    w.canonFunc f (fun k => w.cls i (ts k)) =
      w.cls i (.func ((Spine.ofFn ts).fill (.F ⟨f, rfl⟩))) := by
  unfold canonFunc
  set s := stageSup fun k => (w.cls i (ts k)).out.1
  refine (cls_eq_iff (K := max s i) (le_max_left _ _) (le_max_right _ _)).mpr ?_
  change WFF.eq (Term.mono _ (.func ((Spine.ofFn (w.outArgs _)).fill (.F ⟨f, rfl⟩))))
    (Term.mono _ (.func ((Spine.ofFn ts).fill (.F ⟨f, rfl⟩)))) ∈ w.M (max s i)
  rw [Term.mono_fill, Term.mono_fill, Spine.mono_ofFn, Spine.mono_ofFn]
  refine mem_of_provable (Δ := List.ofFn fun k => WFF.eq
      (w.liftT (le_max_left s i) (w.outArgs (fun k => w.cls i (ts k)) k))
      (w.liftT (le_max_right s i) (ts k)))
    (fun ψ hψ => ?_) ⟨Proof.spineCong _ _ _ fun k => Proof.lookup (List.mem_ofFn.mpr ⟨k, rfl⟩)⟩
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hψ
  exact outArgs_eq ts _ (le_max_left _ _) (le_max_right _ _) k

theorem canonRel_cls (r : σ.RelSyms) {i : ℕ}
    (ts : Fin (σ.relArity r) → Term σ (w.ctx i) .Var .var) :
    w.canonRel r (fun k => w.cls i (ts k)) ↔
      WFF.atom ((Spine.ofFn ts).fillR (.R ⟨r, rfl⟩)) ∈ w.M i := by
  unfold canonRel
  set s := stageSup fun k => (w.cls i (ts k)).out.1
  rw [mem_lift (le_max_left s i), mem_lift (w := w) (le_max_right s i),
    WFF.mono_fillR, WFF.mono_fillR, Spine.mono_ofFn, Spine.mono_ofFn]
  have heqs : ∀ k, WFF.eq (w.liftT (le_max_left s i) (w.outArgs (fun k => w.cls i (ts k)) k))
      (w.liftT (le_max_right s i) (ts k)) ∈ w.M (max s i) :=
    outArgs_eq ts _ (le_max_left _ _) (le_max_right _ _)
  constructor
  · intro h
    refine mem_of_provable (Δ := _ :: List.ofFn fun k => WFF.eq
        (w.liftT (le_max_left s i) (w.outArgs (fun k => w.cls i (ts k)) k))
        (w.liftT (le_max_right s i) (ts k)))
      (fun ψ hψ => ?_) ⟨Proof.spineRelCong _ _ _ fun k =>
        Proof.lookup (List.mem_ofFn.mpr ⟨k, rfl⟩)⟩
    · rcases List.mem_cons.mp hψ with rfl | hψ
      · exact h
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hψ
        exact heqs k
  · intro h
    refine mem_of_provable (Δ := _ :: List.ofFn fun k => WFF.eq
        (w.liftT (le_max_left s i) (w.outArgs (fun k => w.cls i (ts k)) k))
        (w.liftT (le_max_right s i) (ts k)))
      (fun ψ hψ => ?_) ⟨Proof.spineRelCong _ _ _ fun k =>
        Proof.eq_symm_base (Proof.lookup (List.mem_ofFn.mpr ⟨k, rfl⟩))⟩
    · rcases List.mem_cons.mp hψ with rfl | hψ
      · exact h
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hψ
        exact heqs k

end BWorld

end BArrow

end V12M
