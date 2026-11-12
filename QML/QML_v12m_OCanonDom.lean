import QML.QML_v12m_OCanonChild
import QML.QML_v12m_CanonFunc

/-!
# QML v12m — the canonical tree with `Opt` on: domains and denotations

The successors of a world are its proper `Opt` children (`AccO`); with `Opt` on, T and 4 are off,
so there are no others (docs §12.22).

* `Opened w w' x`: the child `w'` of `w` opened the witness `x` — its content `x.dia` is declared in
  `w'`'s base.  ⭐Opened at one stage means opened at every stage where `x` is a witness
  (`AccO.opened_at`): otherwise the child's theory says `¬◇⁰_x ⊤` there, which reopening refutes.
* `extentO w x`: the children that opened `x`.  The `◇_x` view of a stage sits in such a child
  (`extentO_le`), through the `□` view with `x` opened.
* `RDomO`, `rdenO`: raw objects (no shapes: T is off) and the denotation of a term at a world, with
  weakening (`rdenO_mono`) and stage independence (`rdenO_congr`).
-/

namespace V12M

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
    (⟨(m, 0), (WFF.optx hO y ⟨X, hX⟩ .top).neg⟩ : w.L.sys.Sentence σ) ∈ w.T

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
    (Proof.opt_reopen hO y ⟨X, hw, hd⟩ (ψ := .top) .top_intro)

/-- A child that opened `x` has it opened at every stage of the parent's `□` view. -/
theorem AccO.opened_at {w w' : World σ N₀} (h : AccO hO w w') {x : VarSymb}
    (ho : Opened w w' x) {m : ℕ} {X : VarType} (hX : (bview w m).wit x = some X) :
    w'.L.base m (.step x .dia) = some X := by
  obtain ⟨m₀, X₀, -, hd₀⟩ := ho
  exact h.decides.stable hd₀ ((h.wit m x).trans hX)


variable (hO) in
/-- The successors of a world: its proper `Opt` children. -/
abbrev SuccO (w : World σ N₀) : Type := Σ w' : World σ N₀, PLift (AccO hO w w')

/-- ⭐**The extent of a witness**: the children that opened it. -/
def extentO (w : World σ N₀) (x : VarSymb) : Set (SuccO hO w) := {w' | Opened w w'.1 x}

/-- The `◇_x` view of a stage sits in the child stage of a member of `x`'s extent: through the `□`
    view with `x` opened, its content declared there (`AccO.opened_at`). -/
theorem extentO_le {w : World σ N₀} {x : VarSymb} {w' : SuccO hO w} (hm : w' ∈ extentO w x)
    {Γ : Ctx} {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) :
    (Γ.diaIn x).Le (w'.1.L.ctx (childStage i)) := by
  have hM : (w.L.ctx i).boxIn.Le (bview w (max i.1 i.2)) := (le_diag_max w i).boxIn
  have hopen : ((w.L.ctx i).boxIn.optIns [x]).Le (w'.1.L.base (max i.1 i.2)) :=
    Ctx.optIns_le_of (hM.trans (w'.2.down.le _)) fun y hy X hX => by
      rw [List.mem_singleton.mp hy] at hX ⊢
      exact w'.2.down.opened_at hm (hM.wit x X hX)
  exact (e.diaIn x).trans ((Ctx.le_diaIn_boxIn_optIn' hO (hx.imp fun _ h => e.ref h)).trans
    hopen)

/-! ## Raw objects and denotations -/

variable (hO) in
/-- Raw objects of a type at a world.  No shapes: T is off under `Opt`. -/
def RDomO : VarType → World σ N₀ → Type
  | .Var, w => w.D
  | .VTypeOne, _ => PUnit
  | .VTypeProd A B, w => RDomO A w × RDomO B w
  | .VTypeBox A, w => (w' : SuccO hO w) → RDomO A w'.1
  | .VTypeDia A, w => Σ E : Set (SuccO hO w), (w' : E) → RDomO A w'.1.1

variable (hO) in
/-- ⭐**The denotation of a term at a world**, computed at a stage containing its context: a
    necessary term its body at each child, a possible one its body at each child that opened the
    witness. -/
noncomputable def rdenO : {A : VarType} → {a : Ann A} → {Γ : Ctx} → (w : World σ N₀) →
    (i : ℕ × ℕ) → Γ.Le (w.L.ctx i) → Term σ Γ A a → RDomO hO A w
  | _, _, _, w, i, e, .var v hv => w.cls i (.var v (e.ref hv))
  | _, _, _, w, i, e, .func f => w.cls i (Term.mono e (.func f))
  | _, _, _, _, _, _, .unit => PUnit.unit
  | _, _, _, w, i, e, .pair s t => (rdenO w i e s, rdenO w i e t)
  | _, _, _, _, i, e, .boxtm t => fun w' =>
      rdenO w'.1 (childStage i) (e.boxIn.trans (w'.2.down.boxIn_le i)) t
  | _, _, _, w, i, e, .diatm x hx t =>
      ⟨extentO w x, fun w' => rdenO w'.1.1 (childStage i) (extentO_le w'.2 e hx) t⟩
  termination_by structural A => A

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
  | _, _, _, _, h, .boxtm t, w, i, e => funext fun w' => rdenO_mono h.boxIn t w'.1 _ _
  | _, _, _, _, h, .diatm x _ t, w, i, e =>
      congrArg (Sigma.mk (extentO w x)) (funext fun w' => rdenO_mono (h.diaIn x) t w'.1.1 _ _)
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
  | _, _, _, .boxtm t, _, _, _, _, _ => funext fun w' => rdenO_congr t w'.1 _ _ _ _
  | _, _, _, .diatm x _ t, w, _, _, _, _ =>
      congrArg (Sigma.mk (extentO w x)) (funext fun w' => rdenO_congr t w'.1.1 _ _ _ _)
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

theorem definableO_box_apply {A : VarType} {w : World σ N₀} {o : RDomO hO (.VTypeBox A) w}
    (h : DefinableO hO (.VTypeBox A) w o) (w' : SuccO hO w) : DefinableO hO A w'.1 (o w') := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | boxtm b => exact definableO_rden _ b

theorem definableO_dia_apply {A : VarType} {w : World σ N₀} {o : RDomO hO (.VTypeDia A) w}
    (h : DefinableO hO (.VTypeDia A) w o) (w' : o.1) : DefinableO hO A w'.1.1 (o.2 w') := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | diatm x hx b => exact definableO_rden _ b

/-! ## The function algebra on raw objects -/

variable (hO) in
/-- ⭐The function algebra on raw objects.  `extract`, `dup` and `dkeep` need T or 4, both off. -/
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
  | _, _, .extract hT, _, _ => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_T hT)).elim
  | _, _, .dup hF, _, _ => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim
  | _, _, .dkeep hF, _, _ => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim

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
  | _, _, .boxMap f, _, _, .boxtm b, _, _, _ => funext fun w' => rdenO_applyG f b w'.1 _ _
  | _, _, .boxPair _ _, _, _, .pair (.boxtm _) (.boxtm _), _, _, _ => rfl
  | _, _, .boxUnit, _, _, .unit, _, _, _ => rfl
  | _, _, .diaMap f, _, _, .diatm x _ c, w, _, _ =>
      congrArg (Sigma.mk (extentO w x)) (funext fun w' => rdenO_applyG f c w'.1.1 _ _)
  | _, _, .strength _ _, _, _, .pair (.boxtm b) (.diatm x _ _), w, _, _ =>
      congrArg (Sigma.mk (extentO w x)) (funext fun w' => Prod.ext (rdenO_mono _ b _ _ _) rfl)
  | _, _, .extract hT, _, _, _, _, _, _ => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_T hT)).elim
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
