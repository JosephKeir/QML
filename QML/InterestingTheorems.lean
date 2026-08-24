import QML.QML_Full_v8
import QML.SubstitutionLemmas
import QML.Freshness
import QML.CastLemmas

def empty_VarCtx : VarCtx := ⟨∅, fun v vinempty ↦ False.elim (Finset.notMem_empty v vinempty)⟩

-- Lets `freshness` close leaves over the empty base context.
@[simp] theorem empty_VarCtx_fst : empty_VarCtx.fst = ∅ := rfl

def not_in_empty_VarCtx (x : VarSymb) : x ∉ VarCtx_to_VarSymbs empty_VarCtx := by
  intro xin
  simp only [VarCtx_to_VarSymbs, empty_VarCtx, Finset.image_empty, Finset.notMem_empty] at xin

theorem firstPairVar_none_of_no_pair {V : VarCtx}
    (h : ∀ (z : VarSymb) (V1 V2 : VarType),
        (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∉ V.1) :
    V.firstPairVar = none := by
  cases hf : V.firstPairVar with
  | none => rfl
  | some val => exact absurd val.2 (h val.1.1 val.1.2.1 val.1.2.2)


-- `P` is a unary predicate in the *empty* context; each quantifier weakens it into
-- its own singleton context.  Keeping `P` context-free is what lets the hypothesis
-- bind `y` while the consequence binds `x` (no shared symbol ⇒ no α-renaming).

/-- `□(∀y. P y)`. -/
def Barcan_universal_hypothesis {y : VarSymb} (σ : Signature) (P : Rel σ empty_VarCtx 1)
    : WFF σ empty_VarCtx :=
  WFF.box (W := empty_VarCtx)
    (WFF.all ⟨y, .Var⟩ (hx := not_in_empty_VarCtx y)
      (WFF.atom (Rel.eval (Rel.ctx_ext ⟨y, .Var⟩ (not_in_empty_VarCtx y) P)
        (Term.var ⟨y, Finset.mem_insert_self _ _⟩))))
    (by simp [VarCtx_box, empty_VarCtx]) (by simp [empty_VarCtx])

/-- `∀x:□Var. □(P x)`. -/
def Barcan_universal_consequence {x : VarSymb} (σ : Signature) (P : Rel σ empty_VarCtx 1)
    : WFF σ empty_VarCtx :=
  WFF.all ⟨x, .VTypeBox .Var⟩ (hx := not_in_empty_VarCtx x)
    (WFF.box (W := VarCtx_insert ⟨x, .VTypeBox .Var⟩ empty_VarCtx (not_in_empty_VarCtx x))
      (WFF.atom (Rel.eval (Rel.ctx_ext ⟨x, .Var⟩ (not_in_empty_VarCtx x) P)
        (Term.var ⟨x, Finset.mem_insert_self _ _⟩)))
      (by simp [VarCtx_box, VarCtx_insert, empty_VarCtx, Finset.image_singleton])
      (by intro p hp hbox
          simp_all [VarCtx_box, VarCtx_insert, empty_VarCtx, Finset.image_singleton,
            Finset.mem_singleton]))

def converse_Barcan_universal {x y : VarSymb} (hxy : x ≠ y) (σ : Signature) (P : Rel σ empty_VarCtx 1) :
    Proof σ empty_VarCtx {Barcan_universal_hypothesis (y := y) σ P} (Barcan_universal_consequence (x := x) σ P) := by
  refine Proof.all_intro ⟨x, .VTypeBox .Var⟩ (not_in_empty_VarCtx x) ?_
  let W := VarCtx_insert ⟨x, .VTypeBox .Var⟩ empty_VarCtx (not_in_empty_VarCtx x)
  let V := VarCtx_insert ⟨x, .Var⟩ empty_VarCtx (not_in_empty_VarCtx x)
  have hsub : (VarCtx_box V).fst ⊆ W.fst := by
    simp [V, W, VarCtx_box, VarCtx_insert, empty_VarCtx, Finset.image_singleton]
  have h_no_box_extras : ∀ p ∈ W.fst, p.2.isBox = true → p ∈ (VarCtx_box V).fst := by
    intro p hp hbox
    simp_all [V, W, VarCtx_box, VarCtx_insert, empty_VarCtx, Finset.image_singleton,
      Finset.mem_singleton]
  -- The (empty-context) inner universal `∀y. P y`, and its weakening into V = {x : Var}.
  let Py : Rel σ (VarCtx_insert ⟨y, .Var⟩ empty_VarCtx (not_in_empty_VarCtx y)) 1 :=
    Rel.ctx_ext ⟨y, .Var⟩ (not_in_empty_VarCtx y) P
  let y' := Term.var (σ := σ) (V := VarCtx_insert ⟨y, .Var⟩ empty_VarCtx (not_in_empty_VarCtx y))
              ⟨y, Finset.mem_insert_self _ _⟩
  let h_inner_inner : WFF σ empty_VarCtx :=
    WFF.all (σ := σ) ⟨y, .Var⟩ (hx := not_in_empty_VarCtx y) (.atom (Rel.eval Py y'))
  let h_inner := WFF.ctx_ext ⟨x, .Var⟩ (not_in_empty_VarCtx x) h_inner_inner
  have simplifying : WFF.ctx_ext_Finset ⟨x, .VTypeBox .Var⟩ (not_in_empty_VarCtx x) {Barcan_universal_hypothesis (y := y) σ P}
       = WFF.box_Finset (σ := σ) hsub h_no_box_extras {h_inner} := by
    simp only [Barcan_universal_hypothesis, WFF.ctx_ext_Finset, WFF.box_Finset, h_inner,
      h_inner_inner, Finset.image_singleton, Finset.singleton_inj]
    simp only [WFF.ctx_ext, Py, y']
  rw [simplifying]
  apply Proof.K_box hsub h_no_box_extras
  -- Residual goal:  Proof σ V {h_inner} (WFF.atom ((P wk-x).eval (var x))), with
  -- h_inner = ctx_ext ⟨x,.Var⟩ (∀y. (P wk-y).eval (var y)).  Since x ≠ y there is NO
  -- α-rename, so h_inner is `WFF.all ⟨y,.Var⟩ (…)`; instantiate it at witness (var x)
  -- via `all_elim`, then discharge the resulting substitution equality (below).
  have hy_V : y ∉ VarCtx_to_VarSymbs V := by simp only [V]; freshness
  -- Expose the weakened hypothesis as `∀y. …` (no α-rename since x ≠ y) and instantiate
  -- it at witness `x` via `all_elim`; the whole `Proof` structure is now in place.
  change Proof σ V {h_inner} _
  simp only [h_inner, h_inner_inner, WFF.ctx_ext]
  rw [dif_neg hxy]
  let x' : Term σ V .Var := Term.var ⟨x, Finset.mem_insert_self _ _⟩
  refine cast (congrArg (Proof σ V _) ?_)
    (Proof.all_elim ⟨y, .Var⟩ hy_V x' (Proof.ax (Finset.mem_singleton_self _)))
  have hpf_yx : (VarCtx_insert ⟨y, .Var⟩ V hy_V).firstPairVar = none := by
    apply firstPairVar_none_of_no_pair; intro z V1 V2 hmem
    simp [V, VarCtx_insert, empty_VarCtx, Finset.mem_insert, Finset.mem_singleton] at hmem
  rw [WFF.cast_atom, WFF.substVar_atom hy_V x' hpf_yx]
  congr 1
  -- Residual Rel equality.  Distribute `ctx_ext ⟨x⟩` over the eval, commute to lift
  -- `ctx_ext ⟨y⟩` outermost; then `simp` pushes/cancels the transports (cast library),
  -- distributes `ctx_rest`, and applies the vacuous lemma; the `var y ↦ var x` closes it.
  have hpf_empty : empty_VarCtx.firstPairVar = none :=
    firstPairVar_none_of_no_pair (fun z V1 V2 hmem => absurd hmem (Finset.notMem_empty _))
  have hcomm := Rel.ctx_ext_comm (σ := σ) (V := empty_VarCtx) (x := x) (y := y)
      hpf_empty (not_in_empty_VarCtx y) (not_in_empty_VarCtx x)
      (by freshness) (by freshness) P
  simp only [Py, y', Rel.ctx_ext, Term.ctx_ext]
  rw [hcomm]
  simp only [Rel.cast_eval, Rel.cast_cancel, Rel.ctx_rest, Rel.ctx_rest_ctx_ext]
  congr 1
  rw [Term.cast_var]
  conv_lhs => unfold Term.ctx_rest
  split_ifs with h_eq
  · rfl
  · exact absurd (congrArg (fun a => (a, VarType.Var)) (cast_subtype_val _ _)) h_eq

/-- `∃x:♢Var. ♢_x(P x)`. -/
def Barcan_existential_hypothesis {x : VarSymb} (σ : Signature) (P : Rel σ empty_VarCtx 1)
    : WFF σ empty_VarCtx :=
  WFF.ex ⟨x, .VTypeDia .Var⟩ (hx := not_in_empty_VarCtx x)
    (WFF.dia (W := VarCtx_insert ⟨x, .VTypeDia .Var⟩ empty_VarCtx (not_in_empty_VarCtx x))
      ⟨x, .Var⟩ (not_in_empty_VarCtx x)
      (WFF.atom (Rel.eval (Rel.ctx_ext ⟨x, .Var⟩ (not_in_empty_VarCtx x) P)
        (Term.var ⟨x, Finset.mem_insert_self _ _⟩)))
      (by simp [VarCtx_dia, VarCtx_box, VarCtx_insert, empty_VarCtx])
      (by intro p hp hbox
          simp_all [VarCtx_box, VarCtx_dia, VarCtx_insert, empty_VarCtx,
            Finset.mem_singleton]))

/-- `∃z:♢Var. ♢_z (∃y. P y)`. -/
def Barcan_existential_consequence {y z : VarSymb} {hyz : y ≠ z} (σ : Signature)
  (P : Rel σ empty_VarCtx 1)
    : WFF σ (empty_VarCtx) :=
    WFF.ex ⟨z, .VTypeDia .Var⟩ (hx := by simp)
      (WFF.dia (W := VarCtx_insert ⟨z, .VTypeDia .Var⟩ empty_VarCtx (by simp)) ⟨z, .Var⟩
      (hx := not_in_empty_VarCtx z)
        (WFF.ex ⟨y, .Var⟩ (hx := by simp [hyz])
          (WFF.atom (Rel.eval (Rel.ctx_ext ⟨y, .Var⟩ (by simp [hyz]) (Rel.ctx_ext ⟨z, .Var⟩
          (by simp) P))
            (Term.var ⟨y, Finset.mem_insert_self _ _⟩))))
    (by freshness) (by freshness))

def converse_Barcan_existential {x y z: VarSymb} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (σ : Signature) (P : Rel σ empty_VarCtx 1) :
    Proof σ empty_VarCtx {Barcan_existential_hypothesis (x := x) σ P} (Barcan_existential_consequence (y := y) (z := z) (hyz := hyz) σ P) := by
  -- first show x, P(x) ⊢ P(x)
  have PvdashP : Proof σ (VarCtx_insert ⟨x, .Var⟩ empty_VarCtx (by simp))
          {(WFF.atom (Rel.eval (Rel.ctx_ext ⟨x, .Var⟩ _ P)
            (Term.var ⟨x, Finset.mem_insert_self _ _⟩)))}
          (WFF.atom (Rel.eval (Rel.ctx_ext ⟨x, .Var⟩ (by simp) P)
            (Term.var ⟨x, Finset.mem_insert_self _ _⟩)))
        := by
          apply Proof.ax
          exact Finset.mem_singleton.mpr rfl

  -- next show x, P(x) ⊢ ∃ y P(y)
  -- have : (WFF.atom (Rel.eval (Rel.ctx_ext ⟨x, .Var⟩ (by simp) P)
  --          (Term.var ⟨x, Finset.mem_insert_self _ _⟩)))



  -- apply Proof.ex_intro at PvdashP
  -- next, show ♢x, ♢_x P(x) ⊢ ♢_x ∃ y P(y)
  -- next, show ♢x, ♢_x P(x) ⊢ ∃ z ♢_z ∃ y P(y)
  -- finally, show ∃ x:♢Var, ♢_x P(x) ⊢ ∃ z ♢_z ∃ y P(y)

def necessity_of_identity_consequence (x : VarSymb) {σ : Signature} :
    WFF σ (VarCtx_insert ⟨x, .VTypeDia .Var⟩ empty_VarCtx (by simp))
  := (WFF.imp (.dia
      (W := VarCtx_insert ⟨x, .VTypeDia .Var⟩ empty_VarCtx (by simp))
      (V := empty_VarCtx)
      ⟨x, .Var⟩ (by simp)
      (WFF.imp (.eq (Term.var ⟨x, (by simp [VarCtx_insert])⟩)
        (Term.var ⟨x, (by simp [VarCtx_insert])⟩)) .bot)
      (by freshness) (by freshness)) .bot)


def necessity_of_identity {x : VarSymb} (σ : Signature) :
    Proof σ (VarCtx_insert ⟨x, .VTypeDia .Var⟩ empty_VarCtx (by simp))
      {} (necessity_of_identity_consequence x)
  := sorry
  -- first show that x ⊢ x = x
  -- next show x, ¬(x = x) ⊢ ⊥
  -- next apply dia: ♢x, ♢_x ¬(x = x) ⊢ ♢_x ⊥
  -- show that ♢_x ⊥ ⊢ ⊥
  -- finally use MP to show ♢x ⊢ ¬♢_x ¬(x = x), i.e. ♢x ⊢ □_x (x = x)
  -- interpretation: if x is a contingent object then it is necessarily (when it exists) equal to itself
  -- this is the actual way Kripke wanted necessity of identity interpreted

-- def box_x_intro :
  -- from a proof that x, Γ ⊢ φ, show ♢x, □Γ ⊢ □_x φ
  -- first assume x, Γ ⊢ φ
  -- show that x, Γ, ¬φ ⊢ ⊥
  -- apply ♢_x: ♢x, □Γ, ♢_x ¬φ ⊢ ♢_x ⊥
  -- next use dia_bot: ♢x, □Γ, ♢_x ¬φ ⊢ ⊥
  -- finally use →intro and def of □_x: ♢x, □Γ ⊢ □_x φ

-- def dia_intro :
  -- from a proof that x, Γ, ψ ⊢ φ, show □x, □Γ, ♢Ψ ⊢ ♢φ
  -- first assume x, Γ, ψ ⊢ φ
  -- show that x, Γ, ψ, ¬φ ⊢ ⊥
  -- use →intro to show x, Γ, ¬φ ⊢ ¬ψ
  -- apply □: □x, □Γ, □¬φ ⊢ □¬ψ
  -- next show  □x, □Γ, □¬φ, ¬□¬ψ ⊢ ⊥
  -- apply →intro: □x, □Γ, ¬□¬ψ ⊢ ¬□¬φ
  -- finally use def of ♢: □x, □Γ, ♢ψ ⊢ ♢φ

-- def converse_Barcan_universal_restricted
  -- show ∀z:♢Var, □_z ∀y P(y) ⊢ ∀x:♢Var, □_x P(x)
  -- this follows from quantifier exchange, the def of □_x, and the existential version of the CBF

-- def converse_Barcan_existential_restricted
  -- show ∃x:□Var, ♢P(x) ⊢ ♢∃x, P(x)
  -- this follows from quantifier exchange, the def of ♢, and the universal version of the CBF
