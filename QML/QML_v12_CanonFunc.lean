import QML.QML_v12_CanonDom
import QML.QML_v12_LeibnizCong

/-!
# QML v12 — the canonical model: the function algebra

* Argument spines from functions (`Spine.ofFn`), their values (`interpFunc_fill`,
  `relSat_fillR`), and **congruence**: provably equal arguments give provably equal
  applications and equivalent atoms (`Proof.spineCong`, `Proof.spineRelCong`).
* The canonical interpretation of the signature on classes (`canonFunc`, `canonRel`), computed on
  representatives, and its value on classes of terms at one stage (`canonFunc_cls`,
  `canonRel_cls`).
* Raw evaluation of the function algebra (`rawEval`), syntactic application of a definable map to a
  term (`applyG`), and ⭐`rden_applyG`: the denotation of the applied term is the evaluation.  So
  definable objects are closed under the function algebra (`definable_rawEval`).
-/

namespace V12

/-! ## Spines from functions -/

/-- The spine of the arguments `ts 0, ts 1, …`. -/
def Spine.ofFn {σ : Signature} {Δ : Ctx} : {n : ℕ} → (Fin n → Term σ Δ .Var .var) → Spine σ Δ n
  | 0, _ => .nil
  | _ + 1, ts => .cons (ts 0) (Spine.ofFn fun k => ts k.succ)

theorem Spine.mono_ofFn {σ : Signature} {Δ Δ' : Ctx} (h : Δ.Le Δ') :
    ∀ {n : ℕ} (ts : Fin n → Term σ Δ .Var .var),
      (Spine.ofFn ts).mono h = Spine.ofFn (fun k => Term.mono h (ts k))
  | 0, _ => rfl
  | _ + 1, ts => congrArg (Spine.cons _) (Spine.mono_ofFn h (fun k => ts k.succ))

theorem Term.mono_fill {σ : Signature} {Δ Δ' : Ctx} (h : Δ.Le Δ') :
    ∀ {n : ℕ} (S : Spine σ Δ n) (f : Func σ Δ n),
      Term.mono h (.func (S.fill f)) = .func ((S.mono h).fill (Func.mono h f))
  | _, .nil, _ => rfl
  | _, .cons t S, f => Term.mono_fill h S (.eval f t)

theorem WFF.mono_fillR {σ : Signature} {Δ Δ' : Ctx} (h : Δ.Le Δ') :
    ∀ {n : ℕ} (S : Spine σ Δ n) (ρ : Rel σ Δ n),
      WFF.mono h (.atom (S.fillR ρ) : WFF σ Δ 0) = .atom ((S.mono h).fillR (Rel.mono h ρ))
  | _, .nil, _ => rfl
  | _, .cons t S, ρ => WFF.mono_fillR h S (.eval ρ t)

namespace Model

variable {σ : Signature} {M : Model.{u} σ}

theorem interpFunc_fill {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) :
    ∀ {n : ℕ} (ts : Fin n → Term σ Δ .Var .var) (g : Func σ Δ n),
      interpFunc env ((Spine.ofFn ts).fill g) Fin.elim0 =
        interpFunc env g (fun k => interp env (ts k))
  | 0, _, g => congrArg (interpFunc env g) (funext fun k => k.elim0)
  | n + 1, ts, g => by
      change interpFunc env ((Spine.ofFn fun k => ts k.succ).fill (.eval g (ts 0))) Fin.elim0 = _
      rw [interpFunc_fill env (fun k => ts k.succ) (.eval g (ts 0))]
      change interpFunc env g (Fin.cons (interp env (ts 0)) fun k => interp env (ts k.succ)) = _
      congr 1
      funext k
      cases k using Fin.cases <;> simp

theorem relSat_fillR {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) :
    ∀ {n : ℕ} (ts : Fin n → Term σ Δ .Var .var) (ρ : Rel σ Δ n),
      relSat env ((Spine.ofFn ts).fillR ρ) Fin.elim0 ↔
        relSat env ρ (fun k => interp env (ts k))
  | 0, ts, ρ => by
      have e : (fun k => interp env (ts k)) = (Fin.elim0 : Fin 0 → M.frame.D w) :=
        funext fun k => k.elim0
      rw [e]
      rfl
  | n + 1, ts, ρ => by
      change relSat env ((Spine.ofFn fun k => ts k.succ).fillR (.eval ρ (ts 0))) Fin.elim0 ↔ _
      rw [relSat_fillR env (fun k => ts k.succ) (.eval ρ (ts 0))]
      change relSat env ρ (Fin.cons (interp env (ts 0)) fun k => interp env (ts k.succ)) ↔ _
      have e : (Fin.cons (interp env (ts 0)) fun k => interp env (ts k.succ) : Fin (n + 1) → _) =
          fun k => interp env (ts k) := by
        funext k
        cases k using Fin.cases <;> simp
      rw [e]

end Model

/-! ## Congruence -/

/-- Provably equal arguments give provably equal applications. -/
def Proof.spineCong {σ : Signature} {Δ : Ctx} [Δ.NoSlots] {E : List (WFF σ Δ 0)} :
    ∀ {n : ℕ} (S S' : Fin n → Term σ Δ .Var .var) (G : Func σ Δ n),
      (∀ k, Proof σ Δ E (.eq (S k) (S' k))) →
      Proof σ Δ E (.eq (.func ((Spine.ofFn S).fill G)) (.func ((Spine.ofFn S').fill G)))
  | 0, _, _, _, _ => Proof.eq_intro _
  | _ + 1, S, S', G, h =>
      have p₁ := Proof.spineCong (fun k => S k.succ) (fun k => S' k.succ) (.eval G (S 0))
        (fun k => h k.succ)
      have p₂ := Proof.eq_elim (φ := WFF.eq (Term.mono holeLe (.func ((Spine.ofFn S).fill G)))
          (Term.func ((Spine.cons hole ((Spine.ofFn fun k => S' k.succ).mono holeLe)).fill
            (Func.mono holeLe G))))
        (S 0) (S' 0) (h 0)
        (Proof.conv (instantiate_funcHole _ _ G (S 0)).symm p₁)
      Proof.conv (instantiate_funcHole _ _ G (S' 0)) p₂

/-- Provably equal arguments give equivalent atoms. -/
def Proof.spineRelCong {σ : Signature} {Δ : Ctx} [Δ.NoSlots] {E : List (WFF σ Δ 0)} :
    ∀ {n : ℕ} (S S' : Fin n → Term σ Δ .Var .var) (ρ : Rel σ Δ n),
      (∀ k, Proof σ Δ E (.eq (S k) (S' k))) →
      Proof σ Δ (.atom ((Spine.ofFn S).fillR ρ) :: E) (.atom ((Spine.ofFn S').fillR ρ))
  | 0, _, _, _, _ => Proof.lookup List.mem_cons_self
  | _ + 1, S, S', ρ, h =>
      have p₁ := Proof.spineRelCong (fun k => S k.succ) (fun k => S' k.succ) (.eval ρ (S 0))
        (fun k => h k.succ)
      have p₂ := Proof.eq_elim
          (φ := WFF.atom ((Spine.cons hole ((Spine.ofFn fun k => S' k.succ).mono holeLe)).fillR
            (Rel.mono holeLe ρ)))
        (S 0) (S' 0) (Proof.weak _ (h 0))
        (Proof.conv (instantiate_relHole _ ρ (S 0)).symm p₁)
      Proof.conv (instantiate_relHole _ ρ (S' 0)) p₂

namespace Canon

variable {σ : Signature} {N₀ : ℕ}

/-! ## The signature on classes -/

/-- A common stage for finitely many stages. -/
def stageSup {n : ℕ} (f : Fin n → ℕ × ℕ) : ℕ × ℕ := Finset.univ.sup f

theorem le_stageSup {n : ℕ} (f : Fin n → ℕ × ℕ) (k : Fin n) : f k ≤ stageSup f :=
  Finset.le_sup (Finset.mem_univ k)

/-- Representatives of classes, at a common stage. -/
noncomputable def World.outArgs (w : World σ N₀) {n : ℕ} (args : Fin n → w.D) :
    Fin n → Term σ (w.L.ctx (stageSup fun k => (args k).out.1)) .Var .var :=
  fun k => w.liftT (le_stageSup (fun k => (args k).out.1) k) (args k).out.2

/-- ⭐The canonical interpretation of a function symbol. -/
noncomputable def canonFunc (w : World σ N₀) (f : σ.FuncSyms)
    (args : Fin (σ.funcArity f) → w.D) : w.D :=
  w.cls (stageSup fun k => (args k).out.1)
    (.func ((Spine.ofFn (w.outArgs args)).fill (.F ⟨f, rfl⟩)))

/-- ⭐The canonical interpretation of a relation symbol. -/
noncomputable def canonRel (w : World σ N₀) (r : σ.RelSyms)
    (args : Fin (σ.relArity r) → w.D) : Prop :=
  (⟨stageSup fun k => (args k).out.1, .atom ((Spine.ofFn (w.outArgs args)).fillR (.R ⟨r, rfl⟩))⟩ :
    w.L.sys.Sentence σ) ∈ w.T

/-- The representatives of classes of terms at one stage are equal to them, at a common stage. -/
theorem outArgs_eq {w : World σ N₀} {n : ℕ} {i : ℕ × ℕ} (ts : Fin n → Term σ (w.L.ctx i) .Var .var)
    (K : ℕ × ℕ) (hs : (stageSup fun k => (w.cls i (ts k)).out.1) ≤ K) (hi : i ≤ K) (k : Fin n) :
    (⟨K, .eq (w.liftT hs (w.outArgs (fun k => w.cls i (ts k)) k)) (w.liftT hi (ts k))⟩ :
      w.L.sys.Sentence σ) ∈ w.T := by
  have h := Quotient.out_eq (s := w.setoid) (w.cls i (ts k))
  have h' : w.TEq (w.cls i (ts k)).out ⟨i, ts k⟩ := Quotient.exact h
  rw [World.TEq_iff ((le_stageSup _ k).trans hs) hi] at h'
  unfold World.outArgs
  rw [World.liftT_liftT]
  exact h'

theorem canonFunc_cls {w : World σ N₀} (f : σ.FuncSyms) {i : ℕ × ℕ}
    (ts : Fin (σ.funcArity f) → Term σ (w.L.ctx i) .Var .var) :
    canonFunc w f (fun k => w.cls i (ts k)) =
      w.cls i (.func ((Spine.ofFn ts).fill (.F ⟨f, rfl⟩))) := by
  unfold canonFunc
  set s := stageSup fun k => (w.cls i (ts k)).out.1
  refine (World.cls_eq_iff (K := s ⊔ i) le_sup_left le_sup_right).mpr ?_
  change (⟨s ⊔ i, .eq (Term.mono _ (.func ((Spine.ofFn (w.outArgs _)).fill (.F ⟨f, rfl⟩))))
    (Term.mono _ (.func ((Spine.ofFn ts).fill (.F ⟨f, rfl⟩))))⟩ : w.L.sys.Sentence σ) ∈ w.T
  rw [Term.mono_fill, Term.mono_fill, Spine.mono_ofFn, Spine.mono_ofFn]
  refine World.mem_of_provable (Δ := List.ofFn fun k => WFF.eq
      (w.liftT le_sup_left (w.outArgs (fun k => w.cls i (ts k)) k)) (w.liftT le_sup_right (ts k)))
    (fun ψ hψ => ?_) ⟨Proof.spineCong _ _ _ fun k => Proof.lookup (List.mem_ofFn.mpr ⟨k, rfl⟩)⟩
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hψ
  exact outArgs_eq ts _ le_sup_left le_sup_right k

theorem canonRel_cls {w : World σ N₀} (r : σ.RelSyms) {i : ℕ × ℕ}
    (ts : Fin (σ.relArity r) → Term σ (w.L.ctx i) .Var .var) :
    canonRel w r (fun k => w.cls i (ts k)) ↔
      (⟨i, .atom ((Spine.ofFn ts).fillR (.R ⟨r, rfl⟩))⟩ : w.L.sys.Sentence σ) ∈ w.T := by
  unfold canonRel
  set s := stageSup fun k => (w.cls i (ts k)).out.1
  rw [World.mem_lift (le_sup_left : s ≤ s ⊔ i), World.mem_lift (le_sup_right : i ≤ s ⊔ i),
    WFF.mono_fillR, WFF.mono_fillR, Spine.mono_ofFn, Spine.mono_ofFn]
  have heqs : ∀ k, (⟨s ⊔ i, .eq (w.liftT le_sup_left (w.outArgs (fun k => w.cls i (ts k)) k))
      (w.liftT le_sup_right (ts k))⟩ : w.L.sys.Sentence σ) ∈ w.T :=
    outArgs_eq ts _ le_sup_left le_sup_right
  constructor
  · intro h
    refine World.mem_of_provable (Δ := _ :: List.ofFn fun k => WFF.eq
        (w.liftT le_sup_left (w.outArgs (fun k => w.cls i (ts k)) k)) (w.liftT le_sup_right (ts k)))
      (fun ψ hψ => ?_) ⟨Proof.spineRelCong _ _ _ fun k =>
        Proof.lookup (List.mem_ofFn.mpr ⟨k, rfl⟩)⟩
    · rcases List.mem_cons.mp hψ with rfl | hψ
      · exact h
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hψ
        exact heqs k
  · intro h
    refine World.mem_of_provable (Δ := _ :: List.ofFn fun k => WFF.eq
        (w.liftT le_sup_left (w.outArgs (fun k => w.cls i (ts k)) k)) (w.liftT le_sup_right (ts k)))
      (fun ψ hψ => ?_) ⟨Proof.spineRelCong _ _ _ fun k =>
        Proof.eq_symm_base (Proof.lookup (List.mem_ofFn.mpr ⟨k, rfl⟩))⟩
    · rcases List.mem_cons.mp hψ with rfl | hψ
      · exact h
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hψ
        exact heqs k

/-! ## Raw evaluation and application -/

/-- ⭐The function algebra on raw objects. -/
noncomputable def rawEval : {A B : VarType} → GFunc σ A B → (w : World σ N₀) → RDom A w → RDom B w
  | _, _, .id _, _, o => o
  | _, _, .comp g f, w, o => rawEval g w (rawEval f w o)
  | _, _, .fst, _, o => o.1
  | _, _, .snd, _, o => o.2
  | _, _, .pair f g, w, o => (rawEval f w o, rawEval g w o)
  | _, _, .unit _, _, _ => PUnit.unit
  | _, _, .func f args, w, o => canonFunc w f (fun k => rawEval (args k) w o)
  | _, _, .boxMap f, _, o => fun w' => rawEval f w'.1 (o w')
  | _, _, .boxPair _ _, _, o => fun w' => (o.1 w', o.2 w')
  | _, _, .boxUnit, _, _ => fun _ => PUnit.unit
  | _, _, .diaMap f, _, o => ⟨o.1, fun w' => rawEval f w'.1.1 (o.2 w')⟩
  | _, _, .strength _ _, _, o => ⟨o.2.1, fun w' => (o.1 w'.1, o.2.2 w')⟩

/-- A base-typed term with its (only possible) annotation. -/
def varTerm {Γ : Ctx} : (Σ b : Ann .Var, Term σ Γ .Var b) → Term σ Γ .Var .var
  | ⟨.var, t⟩ => t

/-- A definable map applied to a term. -/
def applyG : {A B : VarType} → GFunc σ A B → {Γ : Ctx} → {a : Ann A} → Term σ Γ A a →
    Σ b : Ann B, Term σ Γ B b
  | _, _, .id _, _, _, t => ⟨_, t⟩
  | _, _, .comp g f, _, _, t => applyG g (applyG f t).2
  | _, _, .fst, _, _, .pair s _ => ⟨_, s⟩
  | _, _, .snd, _, _, .pair _ u => ⟨_, u⟩
  | _, _, .pair f g, _, _, t => ⟨_, .pair (applyG f t).2 (applyG g t).2⟩
  | _, _, .unit _, _, _, _ => ⟨.one, .unit⟩
  | _, _, .func f args, _, _, t =>
      ⟨.var, .func ((Spine.ofFn fun k => varTerm (applyG (args k) t)).fill (.F ⟨f, rfl⟩))⟩
  | _, _, .boxMap f, _, _, .boxtm b => ⟨_, .boxtm (applyG f b).2⟩
  | _, _, .boxPair _ _, _, _, .pair (.boxtm b) (.boxtm c) => ⟨_, .boxtm (.pair b c)⟩
  | _, _, .boxUnit, _, _, .unit => ⟨_, .boxtm .unit⟩
  | _, _, .diaMap f, _, _, .diatm x hx c => ⟨_, .diatm x hx (applyG f c).2⟩
  | _, _, .strength _ _, Γ, _, .pair (.boxtm b) (.diatm x hx c) =>
      ⟨_, .diatm x hx (.pair (Term.mono (Ctx.le_boxIn_diaIn Γ x) b) c)⟩

theorem rden_varTerm {Γ : Ctx} (w : World σ N₀) (i : ℕ × ℕ) (e : Γ.Le (w.L.ctx i)) :
    ∀ p : (Σ b : Ann .Var, Term σ Γ .Var b), rden w i e (varTerm p) = rden w i e p.2
  | ⟨.var, _⟩ => rfl

theorem rden_var_mono {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) :
    ∀ u : Term σ Γ .Var .var, rden w i e u = w.cls i (Term.mono e u)
  | .var _ _ => rfl
  | .func _ => rfl

/-- ⭐The denotation of an applied map is its raw evaluation. -/
theorem rden_applyG : ∀ {A B : VarType} (g : GFunc σ A B) {Γ : Ctx} {a : Ann A}
    (t : Term σ Γ A a) (w : World σ N₀) (i : ℕ × ℕ) (e : Γ.Le (w.L.ctx i)),
    rden w i e (applyG g t).2 = rawEval g w (rden w i e t)
  | _, _, .id _, _, _, _, _, _, _ => rfl
  | _, _, .comp g f, _, _, t, w, i, e =>
      (rden_applyG g _ w i e).trans (congrArg (rawEval g w) (rden_applyG f t w i e))
  | _, _, .fst, _, _, .pair _ _, _, _, _ => rfl
  | _, _, .snd, _, _, .pair _ _, _, _, _ => rfl
  | _, _, .pair f g, _, _, t, w, i, e => Prod.ext (rden_applyG f t w i e) (rden_applyG g t w i e)
  | _, _, .unit _, _, _, _, _, _, _ => rfl
  | _, _, .func f args, _, _, t, w, i, e => by
      change rden w i e (.func _) = canonFunc w f (fun k => rawEval (args k) w (rden w i e t))
      have hk : (fun k => rawEval (args k) w (rden w i e t)) =
          fun k => w.cls i (Term.mono e (varTerm (applyG (args k) t))) := by
        funext k
        rw [← rden_applyG (args k) t w i e, ← rden_varTerm, rden_var_mono]
      rw [hk, canonFunc_cls, rden_var_mono, Term.mono_fill, Spine.mono_ofFn]
      rfl
  | _, _, .boxMap f, _, _, .boxtm b, _, i, _ =>
      funext fun w' => rden_applyG f b w'.1 (childStage i) _
  | _, _, .boxPair _ _, _, _, .pair (.boxtm _) (.boxtm _), _, _, _ => rfl
  | _, _, .boxUnit, _, _, .unit, _, _, _ => rfl
  | _, _, .diaMap f, _, _, .diatm _ _ c, _, i, _ =>
      congrArg (Sigma.mk _) (funext fun w' => rden_applyG f c w'.1.1 (childStage i) _)
  | _, _, .strength _ _, _, _, .pair (.boxtm _) (.diatm _ _ _), _, _, _ =>
      congrArg (Sigma.mk _) (funext fun _ => Prod.ext (rden_mono _ _ _ _ _) rfl)

/-- ⭐Definable objects are closed under the function algebra. -/
theorem definable_rawEval {A B : VarType} (g : GFunc σ A B) {w : World σ N₀} {o : RDom A w}
    (h : Definable A w o) : Definable B w (rawEval g w o) := by
  obtain ⟨i, a, t, rfl⟩ := h
  exact ⟨i, _, (applyG g t).2, rden_applyG g t w i _⟩

end Canon

end V12
