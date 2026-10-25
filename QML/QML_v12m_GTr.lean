import QML.QML_v12m_GCanonLift
import QML.QML_v12m_CanonTerm

/-!
# QML v12m — translations: substitutions, shifts and weakenings in sequence

A path's translation (`pTr`) is not one substitution: each step keeps (a shift) before it
substitutes, and a shift is not a substitution (a substitution's witness index map is uniform,
while a shift's index depends on the depth).  Under T the world's own arrow collapses, and a
realisation abstracts, collapses and substitutes.  So translations are kept as **chains** (`GTr`).

* `app`, `appF`: a chain applied to a term, a function term.
* `box`, `dia`, `idx`: the chain inside `□`, inside `◇_x`, and where it sends a witness.
* It commutes with the term formers (`app_boxtm`, `app_diatm`, `app_pair`, `app_func`), with
  definable maps (`applyG_app`), and its `◇_x` view agrees with its `□` view on the `□` part
  (`dia_box_mono`); under T, with collapsing its `□` view (`app_collapse`).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

variable {σ : Signature}

/-- ⭐A translation: substitutions, shifts and weakenings in sequence. -/
inductive GTr (σ : Signature) : Ctx → Ctx → Type
  | nil (Γ : Ctx) : GTr σ Γ Γ
  | sub {ι : VarSymb → VarSymb} {Γ Δ Δ' : Ctx} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
      (hc : Subst.Coh ι Γ θ) (C : GTr σ Δ Δ') : GTr σ Γ Δ'
  | sh {k : ℕ} {Γ Γ' Δ : Ctx} (h : Ctx.Shifts k Γ Γ') (C : GTr σ Γ' Δ) : GTr σ Γ Δ
  | mono {Γ Γ' Δ : Ctx} (h : Γ.Le Γ') (C : GTr σ Γ' Δ) : GTr σ Γ Δ
  | col {k : ℕ} {Γ Γ' Δ : Ctx} (h : Ctx.Collapses k Γ Γ') (C : GTr σ Γ' Δ) : GTr σ Γ Δ

namespace GTr

/-- A chain applied to a term. -/
def app : {Γ Δ : Ctx} → GTr σ Γ Δ → {T : VarType} → {a : Ann T} → Term σ Γ T a →
    Σ b : Ann T, Term σ Δ T b
  | _, _, .nil _, _, _, t => ⟨_, t⟩
  | _, _, .sub (ι := ι) θ hθ hc C, _, _, t => C.app (Term.subst ι θ hθ hc t)
  | _, _, .sh h C, _, _, t => C.app (Term.shift h t)
  | _, _, .mono h C, _, _, t => C.app (Term.mono h t)
  | _, _, .col h C, _, _, t => C.app (Term.collapse h t)

/-- A chain applied to a function term. -/
def appF : {Γ Δ : Ctx} → GTr σ Γ Δ → {n : ℕ} → Func σ Γ n → Func σ Δ n
  | _, _, .nil _, _, f => f
  | _, _, .sub (ι := ι) θ hθ hc C, _, f => C.appF (Func.subst ι θ hθ hc f)
  | _, _, .sh h C, _, f => C.appF (Func.shift h f)
  | _, _, .mono h C, _, f => C.appF (Func.mono h f)
  | _, _, .col h C, _, f => C.appF (Func.collapse h f)

/-- The chain inside `□`. -/
def box : {Γ Δ : Ctx} → GTr σ Γ Δ → GTr σ Γ.boxIn Δ.boxIn
  | _, _, .nil _ => .nil _
  | _, _, .sub θ hθ hc C => .sub θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) C.box
  | _, _, .sh h C => .sh h.boxIn C.box
  | _, _, .mono h C => .mono h.boxIn C.box
  | _, _, .col h C => .col h.boxIn C.box

/-- Where the chain sends a witness. -/
def idx : {Γ Δ : Ctx} → GTr σ Γ Δ → VarSymb → VarSymb
  | _, _, .nil _, x => x
  | _, _, .sub (ι := ι) _ _ _ C, x => C.idx (ι x)
  | _, _, .sh (k := k) _ C, x => C.idx (x.shift k)
  | _, _, .mono _ C, x => C.idx x
  | _, _, .col (k := k) _ C, x => C.idx (x.collapse k)

theorem idx_decl : ∀ {Γ Δ : Ctx} (C : GTr σ Γ Δ) {x : VarSymb},
    (∃ X, Γ.ref x = some (.VTypeDia X)) → ∃ X, Δ.ref (C.idx x) = some (.VTypeDia X)
  | _, _, .nil _, _, hx => hx
  | _, _, .sub _ hθ hc C, x, hx =>
      C.idx_decl (hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) (hc x _ hX []))
  | _, _, .sh h C, x, hx => C.idx_decl (hx.imp fun _ hX => h x _ hX)
  | _, _, .mono h C, _, hx => C.idx_decl (hx.imp fun _ hX => h.ref hX)
  | _, _, .col h C, x, hx => C.idx_decl (hx.imp fun _ hX => h x _ hX)

/-- The chain inside `◇_x`. -/
def dia : {Γ Δ : Ctx} → (C : GTr σ Γ Δ) → (x : VarSymb) →
    (∃ X, Γ.ref x = some (.VTypeDia X)) → GTr σ (Γ.diaIn x) (Δ.diaIn (C.idx x))
  | _, _, .nil _, _, _ => .nil _
  | _, _, .sub (ι := ι) θ hθ hc C, x, hx =>
      .sub (θ.dia x (ι x)) (Subst.ok_dia hθ hx (hx.elim fun _ hX => hc x _ hX []))
        (Subst.coh_dia hθ hc hx)
        (C.dia (ι x) (hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) (hc x _ hX [])))
  | _, _, .sh (k := k) h C, x, hx =>
      .sh (h.diaIn x) (C.dia (x.shift k) (hx.imp fun _ hX => h x _ hX))
  | _, _, .mono h C, x, hx => .mono (h.diaIn x) (C.dia x (hx.imp fun _ hX => h.ref hX))
  | _, _, .col (k := k) h C, x, hx =>
      .col (h.diaIn x) (C.dia (x.collapse k) (hx.imp fun _ hX => h x _ hX))

/-- One chain after another. -/
def comp : {Γ Δ Δ' : Ctx} → GTr σ Γ Δ → GTr σ Δ Δ' → GTr σ Γ Δ'
  | _, _, _, .nil _, D => D
  | _, _, _, .sub θ hθ hc C, D => .sub θ hθ hc (C.comp D)
  | _, _, _, .sh h C, D => .sh h (C.comp D)
  | _, _, _, .mono h C, D => .mono h (C.comp D)
  | _, _, _, .col h C, D => .col h (C.comp D)

theorem app_sigma {Γ Δ : Ctx} (C : GTr σ Γ Δ) {T : VarType} {p q : Σ b : Ann T, Term σ Γ T b}
    (h : p = q) : C.app p.2 = C.app q.2 := by
  subst h
  rfl

theorem app_comp : ∀ {Γ Δ Δ' : Ctx} (C : GTr σ Γ Δ) (D : GTr σ Δ Δ') {T : VarType} {a : Ann T}
    (t : Term σ Γ T a), (C.comp D).app t = D.app (C.app t).2
  | _, _, _, .nil _, _, _, _, _ => rfl
  | _, _, _, .sub _ _ _ C, D, _, _, _ => app_comp C D _
  | _, _, _, .sh _ C, D, _, _, _ => app_comp C D _
  | _, _, _, .mono _ C, D, _, _, _ => app_comp C D _
  | _, _, _, .col _ C, D, _, _, _ => app_comp C D _

theorem app_boxtm : ∀ {Γ Δ : Ctx} (C : GTr σ Γ Δ) {A : VarType} {a : Ann A}
    (X : Term σ Γ.boxIn A a), C.app (.boxtm X) = ⟨_, .boxtm (C.box.app X).2⟩
  | _, _, .nil _, _, _, _ => rfl
  | _, _, .sub _ _ _ C, _, _, _ => app_boxtm C _
  | _, _, .sh _ C, _, _, _ => app_boxtm C _
  | _, _, .mono _ C, _, _, _ => app_boxtm C _
  | _, _, .col _ C, _, _, _ => app_boxtm C _

theorem app_diatm : ∀ {Γ Δ : Ctx} (C : GTr σ Γ Δ) {A : VarType} {a : Ann A} (x : VarSymb)
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (X : Term σ (Γ.diaIn x) A a),
    C.app (.diatm x hx X) = ⟨_, .diatm (C.idx x) (C.idx_decl hx) (C.dia x hx |>.app X).2⟩
  | _, _, .nil _, _, _, _, _, _ => rfl
  | _, _, .sub (ι := ι) _ _ _ C, _, _, x, _, _ => app_diatm C (ι x) _ _
  | _, _, .sh (k := k) _ C, _, _, x, _, _ => app_diatm C (x.shift k) _ _
  | _, _, .mono _ C, _, _, x, _, _ => app_diatm C x _ _
  | _, _, .col (k := k) _ C, _, _, x, _, _ => app_diatm C (x.collapse k) _ _

theorem app_pair : ∀ {Γ Δ : Ctx} (C : GTr σ Γ Δ) {A B : VarType} {a : Ann A} {b : Ann B}
    (s : Term σ Γ A a) (t : Term σ Γ B b),
    C.app (.pair s t) = ⟨_, .pair (C.app s).2 (C.app t).2⟩
  | _, _, .nil _, _, _, _, _, _, _ => rfl
  | _, _, .sub _ _ _ C, _, _, _, _, _, _ => app_pair C _ _
  | _, _, .sh _ C, _, _, _, _, _, _ => app_pair C _ _
  | _, _, .mono _ C, _, _, _, _, _, _ => app_pair C _ _
  | _, _, .col _ C, _, _, _, _, _, _ => app_pair C _ _

theorem app_func : ∀ {Γ Δ : Ctx} (C : GTr σ Γ Δ) (f : Func σ Γ 0),
    C.app (.func f) = ⟨.var, .func (C.appF f)⟩
  | _, _, .nil _, _ => rfl
  | _, _, .sub _ _ _ C, _ => app_func C _
  | _, _, .sh _ C, _ => app_func C _
  | _, _, .mono _ C, _ => app_func C _
  | _, _, .col _ C, _ => app_func C _

theorem appF_F : ∀ {Γ Δ : Ctx} (C : GTr σ Γ Δ) {n : ℕ} (f : {f : σ.FuncSyms // σ.funcArity f = n}),
    C.appF (.F f) = .F f
  | _, _, .nil _, _, _ => rfl
  | _, _, .sub _ _ _ C, _, _ => appF_F C _
  | _, _, .sh _ C, _, _ => appF_F C _
  | _, _, .mono _ C, _, _ => appF_F C _
  | _, _, .col _ C, _, _ => appF_F C _

theorem appF_eval : ∀ {Γ Δ : Ctx} (C : GTr σ Γ Δ) {n : ℕ} (g : Func σ Γ (n + 1))
    (t : Term σ Γ .Var .var), C.appF (.eval g t) = .eval (C.appF g) (Canon.varTerm (C.app t))
  | _, _, .nil _, _, _, _ => rfl
  | _, _, .sub _ _ _ C, _, _, _ => appF_eval C _ _
  | _, _, .sh _ C, _, _, _ => appF_eval C _ _
  | _, _, .mono _ C, _, _, _ => appF_eval C _ _
  | _, _, .col _ C, _, _, _ => appF_eval C _ _

/-- ⭐A chain commutes with applying a definable map. -/
theorem applyG_app {A B : VarType} (g : GFunc σ A B) : ∀ {Γ Δ : Ctx} (C : GTr σ Γ Δ)
    {a : Ann A} (t : Term σ Γ A a),
    Canon.applyG g (C.app t).2 = C.app (Canon.applyG g t).2
  | _, _, .nil _, _, _ => rfl
  | _, _, .sub θ hθ hc C, _, t =>
      (applyG_app g C _).trans (C.app_sigma (Canon.applyG_subst g θ hθ hc t))
  | _, _, .sh h C, _, t => (applyG_app g C _).trans (C.app_sigma (Canon.applyG_shift g h t))
  | _, _, .mono h C, _, t => (applyG_app g C _).trans (C.app_sigma (Canon.applyG_mono g h t))
  | _, _, .col h C, _, t =>
      (applyG_app g C _).trans (C.app_sigma (Canon.applyG_collapse g h t))

/-- ⭐A chain's `◇_x` view agrees with its `□` view on the `□` part. -/
theorem dia_box_mono : ∀ {Γ Δ : Ctx} (C : GTr σ Γ Δ) (x : VarSymb)
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (Y : Term σ Γ.boxIn A a),
    (C.dia x hx).app (Term.mono (Ctx.le_boxIn_diaIn Γ x) Y) =
      ⟨_, Term.mono (Ctx.le_boxIn_diaIn Δ (C.idx x)) (C.box.app Y).2⟩
  | _, _, .nil _, _, _, _, _, _ => rfl
  | _, _, .sub (ι := ι) θ hθ hc C, x, hx, _, _, Y =>
      ((C.dia (ι x) _).app_sigma (congrArg (Sigma.mk _)
        (Canon.Term.subst_dia_mono θ hθ hc hx (hx.elim fun _ hX => hc x _ hX []) Y))).trans
        (dia_box_mono C (ι x) _ _)
  | _, _, .sh (k := k) (Γ' := Γ') h C, x, _, _, _, Y =>
      ((C.dia (x.shift k) _).app_sigma (congrArg (Sigma.mk _)
        (Term.shift_mono h.boxIn (h.diaIn x) (Ctx.le_boxIn_diaIn _ x)
          (Ctx.le_boxIn_diaIn Γ' (x.shift k)) Y))).trans (dia_box_mono C (x.shift k) _ _)
  | _, _, .mono (Γ' := Γ') h C, x, _, _, _, Y =>
      ((C.dia x _).app_sigma (congrArg (Sigma.mk _)
        ((Term.mono_mono _ _ Y).trans (Term.mono_mono _ _ Y).symm :
          Term.mono (h.diaIn x) (Term.mono (Ctx.le_boxIn_diaIn _ x) Y) =
            Term.mono (Ctx.le_boxIn_diaIn Γ' x) (Term.mono h.boxIn Y)))).trans
        (dia_box_mono C x _ _)
  | _, _, .col (k := k) (Γ' := Γ') h C, x, _, _, _, Y =>
      ((C.dia (x.collapse k) _).app_sigma (congrArg (Sigma.mk _)
        (Term.collapse_mono h.boxIn (h.diaIn x) (Ctx.le_boxIn_diaIn _ x)
          (Ctx.le_boxIn_diaIn Γ' (x.collapse k)) Y))).trans (dia_box_mono C (x.collapse k) _ _)

/-- ⭐**Under T a chain commutes with collapsing its `□` view**: a substitution by
    `Term.collapse_subst` (its `□` view corresponds, `Subst.corr_box_self`), a shift by
    `Term.shift_collapse`, a weakening by `Term.collapse_mono`, a collapse by
    `Term.collapse_collapse`. -/
theorem app_collapse (hT : ModalSys.T = true) : ∀ {Γ Δ : Ctx} (C : GTr σ Γ Δ) {A : VarType}
    {a : Ann A} (Y : Term σ Γ.boxIn A a),
    C.app (Term.collapse (Ctx.collapses_boxIn_self hT Γ) Y) =
      ⟨_, Term.collapse (Ctx.collapses_boxIn_self hT Δ) (C.box.app Y).2⟩
  | _, _, .nil _, _, _, _ => rfl
  | _, _, .sub θ hθ hc C, _, _, Y =>
      (C.app_sigma (Term.collapse_subst (Ctx.collapses_boxIn_self hT _)
        (Ctx.collapses_boxIn_self hT _) θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) θ hθ hc
        (Subst.corr_box_self hT hθ) Y).symm).trans (app_collapse hT C _)
  | _, _, .sh (k := k) h C, _, _, Y =>
      (C.app_sigma (Term.shift_collapse (k := k) (m := 0) h.boxIn
        (Ctx.collapses_boxIn_self hT _) (Ctx.collapses_boxIn_self hT _) h Y).symm).trans
        (app_collapse hT C _)
  | _, _, .mono h C, _, _, Y =>
      (C.app_sigma (congrArg (Sigma.mk _) (Term.collapse_mono (Ctx.collapses_boxIn_self hT _)
        (Ctx.collapses_boxIn_self hT _) h.boxIn h Y)).symm).trans (app_collapse hT C _)
  | _, _, .col (k := k) h C, _, _, Y =>
      (C.app_sigma (Term.collapse_collapse (k := k) (m := 0) h.boxIn
        (Ctx.collapses_boxIn_self hT _) (Ctx.collapses_boxIn_self hT _) h Y).symm).trans
        (app_collapse hT C _)

end GTr

end GArrow

end V12M
