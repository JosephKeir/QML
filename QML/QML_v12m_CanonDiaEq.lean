import QML.QML_v12m_CanonWorld
import QML.QML_v12m_ViewEq
import QML.QML_v12m_EqDia

/-!
# QML v12m — the canonical model: addresses the theory identifies

The `◇`-types' equality (§2d) is a comparison across *witnesses*, so in the canonical model it is a
relation between **addresses**: `World.PEq w i x y` says the world's theory contains `η x ≐ η y` at
stage `i`.  This file establishes what the extent needs of it:

* it is an equivalence relation on the `◇`-typed addresses of a stage (⭐`PEq.refl`, ⭐`PEq.symm`,
  ⭐`PEq.trans`), from `Proof.diaEq_intro` and the derived `eqRec_symm`/`eqRec_trans` at `◇`-type
  together with closure of a maximal consistent theory under provability;
* it does not depend on the stage it is read at (⭐`PEq.lift`, ⭐`PEq.of_lift`), because an
  η-expansion moved to a later stage is the η-expansion there (`Term.mono_eta`).

The extent taken up to `PEq` comes next.
-/

namespace V12M

variable [ModalSys]

namespace Canon

variable {σ : Signature} {N₀ : ℕ}

namespace World

/-- ⭐Two `◇`-typed addresses of a stage that the world's theory identifies: `η x ≐ η y`. -/
def PEq (w : World σ N₀) (i : ℕ × ℕ) {A : VarType} {x y : VarSymb}
    (hx : (w.L.ctx i).ref x = some (.VTypeDia A))
    (hy : (w.L.ctx i).ref y = some (.VTypeDia A)) : Prop :=
  (⟨i, WFF.diaEq (Term.eta x (.VTypeDia A) hx) (Term.eta y (.VTypeDia A) hy)⟩ :
    w.L.sys.Sentence σ) ∈ w.T

variable {w : World σ N₀} {i j : ℕ × ℕ} {A : VarType} {x y z : VarSymb}

/-- The equation `PEq` asserts, as a formula of the stage. -/
abbrev peqWFF (hx : (w.L.ctx i).ref x = some (.VTypeDia A))
    (hy : (w.L.ctx i).ref y = some (.VTypeDia A)) : WFF σ (w.L.ctx i) 0 :=
  WFF.diaEq (Term.eta x (.VTypeDia A) hx) (Term.eta y (.VTypeDia A) hy)

/-- ⭐Reflexivity. -/
theorem PEq.refl (hx : (w.L.ctx i).ref x = some (.VTypeDia A)) : w.PEq i hx hx :=
  mem_of_provable (Δ := []) (fun _ h => absurd h List.not_mem_nil) ⟨.diaEq_intro _⟩

/-- ⭐Symmetry, by the derived symmetry of the defined equality at `◇`-type. -/
theorem PEq.symm (hx : (w.L.ctx i).ref x = some (.VTypeDia A))
    (hy : (w.L.ctx i).ref y = some (.VTypeDia A)) (h : w.PEq i hx hy) : w.PEq i hy hx :=
  mem_of_provable (Δ := [peqWFF hx hy])
    (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact h)
    ⟨Proof.conv (eqRec_dia _ _)
      (Proof.eqRec_symm (.VTypeDia A) (Proof.conv (eqRec_dia _ _).symm
        (Proof.lookup List.mem_cons_self)))⟩

/-- ⭐Transitivity, likewise. -/
theorem PEq.trans (hx : (w.L.ctx i).ref x = some (.VTypeDia A))
    (hy : (w.L.ctx i).ref y = some (.VTypeDia A))
    (hz : (w.L.ctx i).ref z = some (.VTypeDia A))
    (h₁ : w.PEq i hx hy) (h₂ : w.PEq i hy hz) : w.PEq i hx hz :=
  mem_of_provable (Δ := [peqWFF hx hy, peqWFF hy hz])
    (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ'
      · exact h₁
      · rw [List.mem_singleton.mp hψ']; exact h₂)
    ⟨Proof.conv (eqRec_dia _ _)
      (Proof.eqRec_trans (.VTypeDia A)
        (Proof.conv (eqRec_dia _ _).symm (Proof.lookup List.mem_cons_self))
        (Proof.conv (eqRec_dia _ _).symm
          (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))))⟩

/-- Moving the equation to a later stage changes nothing: an η-expansion moved is the η-expansion
    there. -/
theorem peqWFF_mono (hij : i ≤ j) (hx : (w.L.ctx i).ref x = some (.VTypeDia A))
    (hy : (w.L.ctx i).ref y = some (.VTypeDia A)) :
    WFF.mono (w.L.ctx_le hij) (peqWFF hx hy) =
      peqWFF ((w.L.ctx_le hij).ref hx) ((w.L.ctx_le hij).ref hy) := by
  change WFF.diaEq (Term.mono _ (Term.eta x _ hx)) (Term.mono _ (Term.eta y _ hy)) = _
  rw [Term.mono_eta, Term.mono_eta]

/-- ⭐`PEq` at a later stage. -/
theorem PEq.lift (hij : i ≤ j) (hx : (w.L.ctx i).ref x = some (.VTypeDia A))
    (hy : (w.L.ctx i).ref y = some (.VTypeDia A)) (h : w.PEq i hx hy) :
    w.PEq j ((w.L.ctx_le hij).ref hx) ((w.L.ctx_le hij).ref hy) := by
  have h' := (mem_lift hij (φ := peqWFF hx hy)).mp h
  rwa [peqWFF_mono hij hx hy] at h'

/-- ⭐And back: the stage it is read at does not matter. -/
theorem PEq.of_lift (hij : i ≤ j) (hx : (w.L.ctx i).ref x = some (.VTypeDia A))
    (hy : (w.L.ctx i).ref y = some (.VTypeDia A))
    (h : w.PEq j ((w.L.ctx_le hij).ref hx) ((w.L.ctx_le hij).ref hy)) : w.PEq i hx hy := by
  refine (mem_lift hij (φ := peqWFF hx hy)).mpr ?_
  rw [peqWFF_mono hij hx hy]
  exact h


/-! ## The identification, read anywhere in the language -/

/-- ⭐Two addresses the world's theory identifies, at whatever stage declares them both.  Stage-free,
    because the extent must be: `rden` does not depend on the stage it is computed at. -/
def PEqW (w : World σ N₀) (x y : VarSymb) : Prop :=
  ∃ (j : ℕ × ℕ) (A : VarType) (hx : (w.L.ctx j).ref x = some (.VTypeDia A))
    (hy : (w.L.ctx j).ref y = some (.VTypeDia A)), w.PEq j hx hy

theorem PEqW.of_peq (hx : (w.L.ctx i).ref x = some (.VTypeDia A))
    (hy : (w.L.ctx i).ref y = some (.VTypeDia A)) (h : w.PEq i hx hy) : w.PEqW x y :=
  ⟨i, A, hx, hy, h⟩

theorem PEqW.refl (hx : (w.L.ctx i).ref x = some (.VTypeDia A)) : w.PEqW x x :=
  ⟨i, A, hx, hx, PEq.refl hx⟩

theorem PEqW.symm (h : w.PEqW x y) : w.PEqW y x := by
  obtain ⟨j, A, hx, hy, h⟩ := h
  exact ⟨j, A, hy, hx, PEq.symm hx hy h⟩

/-- A declaration keeps its type at a later stage. -/
theorem declType_eq {j k : ℕ × ℕ} (hjk : j ≤ k) {B : VarType}
    (h : (w.L.ctx j).ref x = some (.VTypeDia A)) (h' : (w.L.ctx k).ref x = some (.VTypeDia B)) :
    A = B := by
  have h₁ := (w.L.ctx_le hjk).ref h
  rw [h'] at h₁
  simp only [Option.some.injEq, VarType.VTypeDia.injEq] at h₁
  exact h₁.symm

theorem PEqW.trans (h₁ : w.PEqW x y) (h₂ : w.PEqW y z) : w.PEqW x z := by
  obtain ⟨j, A, hx, hy, hxy⟩ := h₁
  obtain ⟨k, B, hy', hz, hyz⟩ := h₂
  have hAB : A = B :=
    declType_eq (w := w) (x := y) (le_sup_left : j ≤ j ⊔ k) hy
      ((w.L.ctx_le (le_sup_right : k ≤ j ⊔ k)).ref hy')
  subst hAB
  refine ⟨j ⊔ k, A, (w.L.ctx_le (le_sup_left : j ≤ j ⊔ k)).ref hx,
    (w.L.ctx_le (le_sup_right : k ≤ j ⊔ k)).ref hz, ?_⟩
  refine PEq.trans _ ((w.L.ctx_le (le_sup_left : j ≤ j ⊔ k)).ref hy) _
    (PEq.lift (le_sup_left : j ≤ j ⊔ k) hx hy hxy) ?_
  have hyy : (w.L.ctx_le (le_sup_left : j ≤ j ⊔ k)).ref hy =
      (w.L.ctx_le (le_sup_right : k ≤ j ⊔ k)).ref hy' := rfl
  rw [hyy]
  exact PEq.lift (le_sup_right : k ≤ j ⊔ k) hy' hz hyz

/-! ## The extent, up to the identification -/

/-- ⭐The extent of `x` taken up to provable `≐` (§2d): the successors in the extent of any address
    the theory identifies with `x`.  Under the identity identification this is the old extent
    (`extent_subset_upTo` one way, `PEqW.refl` the other). -/
def extentUpTo (w : World σ N₀) (x : VarSymb) : Set (Succ w) :=
  {w' | ∃ y, w.PEqW x y ∧ w' ∈ extent w y}

theorem extent_subset_upTo (hx : (w.L.ctx i).ref x = some (.VTypeDia A)) {w' : Succ w}
    (h : w' ∈ extent w x) : w' ∈ w.extentUpTo x :=
  ⟨x, PEqW.refl hx, h⟩

/-- ⭐The extent is invariant: what the theory identifies has one extent. -/
theorem extentUpTo_congr (h : w.PEqW x y) : w.extentUpTo x = w.extentUpTo y := by
  apply Set.eq_of_subset_of_subset
  · exact fun w' ⟨z, hz, hmem⟩ => ⟨z, PEqW.trans (PEqW.symm h) hz, hmem⟩
  · exact fun w' ⟨z, hz, hmem⟩ => ⟨z, PEqW.trans h hz, hmem⟩

/-! ## A child has only one tag -/

/-- ⭐A child world's language *is* one view, so the witness it is a view of is determined: the
    content address of the tag is declared there and no other `.dia`-address is.  This is what makes
    the content function on the union well defined. -/
theorem DiaView.inj {w w' : World σ N₀} {y z : VarSymb} {i : ℕ × ℕ} {A : VarType}
    (hy : (w.L.ctx i).ref y = some (.VTypeDia A)) (h₁ : DiaView y w w') (h₂ : DiaView z w w') :
    y = z := by
  have hd : (w.L.ctx i).Le (w.L.ctx (max i.1 i.2, max i.1 i.2)) :=
    w.L.le_diag (le_max_left _ _) (le_max_right _ _)
  have hy' : (w.L.ctx (max i.1 i.2, max i.1 i.2)).ref y = some (.VTypeDia A) := hd.ref hy
  have he : (w.L.ctx (max i.1 i.2, max i.1 i.2)).diaIn y =
      (w.L.ctx (max i.1 i.2, max i.1 i.2)).diaIn z := by
    rw [← h₁ (max i.1 i.2), h₂ (max i.1 i.2)]
  have h3 := congrFun he (.step y .dia)
  change (if y = y then (match (w.L.ctx (max i.1 i.2, max i.1 i.2)).ref y with
      | some (.VTypeDia X) => some X | _ => none) else none) =
    (if y = z then (match (w.L.ctx (max i.1 i.2, max i.1 i.2)).ref z with
      | some (.VTypeDia X) => some X | _ => none) else none) at h3
  rw [if_pos (rfl : y = y), hy'] at h3
  split_ifs at h3 with hyz
  · exact hyz

/-! ## Reading a member of the union -/

/-- A member of the union is the world itself or one level deeper, as before. -/
theorem extentUpTo_cases {w : World σ N₀} {x : VarSymb} {w' : Succ w}
    (hw' : w' ∈ w.extentUpTo x) :
    (w'.1.depth - w.depth = 1 ∧ ∃ y, w.PEqW x y ∧ DiaView y w w'.1 ∧ BoxxContents y w w'.1) ∨
      (w'.1.depth - w.depth = 0 ∧ w'.1 = w ∧ ∃ y, w.PEqW x y ∧ w.Realised y) := by
  obtain ⟨y, hxy, hmem⟩ := hw'
  rcases extent_cases hmem with ⟨hd, hv, hb⟩ | ⟨hd, he, hr⟩
  · exact Or.inl ⟨hd, y, hxy, hv, hb⟩
  · exact Or.inr ⟨hd, he, y, hxy, hr⟩

/-- ⭐A proper member comes with its tag. -/
theorem extentUpTo_proper {w : World σ N₀} {x : VarSymb} {w' : Succ w}
    (hw' : w' ∈ w.extentUpTo x) (hd : w'.1.depth - w.depth ≠ 0) :
    w'.1.depth - w.depth = 1 ∧
      ∃ y, w.PEqW x y ∧ DiaView y w w'.1 ∧ BoxxContents y w w'.1 := by
  rcases extentUpTo_cases hw' with h | ⟨h, -⟩
  · exact h
  · exact absurd h hd

/-- ⭐A member at this depth is the world itself, and then some address the theory identifies with
    `x` is realised. -/
theorem extentUpTo_self {w : World σ N₀} {x : VarSymb} {w' : Succ w}
    (hw' : w' ∈ w.extentUpTo x) (hd : w'.1.depth - w.depth = 0) :
    w'.1 = w ∧ ∃ y, w.PEqW x y ∧ w.Realised y := by
  rcases extentUpTo_cases hw' with ⟨h, -⟩ | ⟨-, h⟩
  · omega
  · exact h

theorem extentUpTo_dist {w : World σ N₀} {x : VarSymb} {w' : Succ w}
    (hw' : w' ∈ w.extentUpTo x) (hd : w'.1.depth - w.depth ≠ 0) : w'.1.depth - w.depth = 1 :=
  (extentUpTo_proper hw' hd).1

/-- ⭐The view of the tag embeds in the child's language, which is what the renamed body is read
    through. -/
theorem extentUpTo_le {w : World σ N₀} {y : VarSymb} {w' : Succ w}
    (hv : DiaView y w w'.1) (i : ℕ × ℕ) :
    ((w.L.ctx i).diaIn y).Le (w'.1.L.ctx (childStage i)) :=
  hv.le (le_max_left _ _) (le_max_right _ _) 0

/-! ## The transfer, in the theory of a world -/

/-- ⭐What the world's theory holds `□_x`-necessary it holds `□_z`-necessary of the renamed formula,
    when it identifies `x` and `z` (`Proof.boxx_reView` plus closure under provability).  This is
    what lets a child tagged `z` serve as a member of `x`'s extent. -/
theorem boxx_mem_reView {A : VarType} {x z : VarSymb}
    (hx : (w.L.ctx i).ref x = some (.VTypeDia A)) (hz : (w.L.ctx i).ref z = some (.VTypeDia A))
    (hcl : Ctx.ViewClean (w.L.ctx i) x)
    (hclI : Ctx.ViewClean ((w.L.ctx i).insert (.bnd 0) (.VTypeDia A)) x)
    (hpe : w.PEq i hx hz) (φ : WFF σ ((w.L.ctx i).diaIn x) 0)
    (h : (⟨i, WFF.boxx x ⟨A, hx⟩ φ⟩ : w.L.sys.Sentence σ) ∈ w.T) :
    (⟨i, WFF.boxx z ⟨A, hz⟩ (WFF.reView hx hz hcl φ)⟩ : w.L.sys.Sentence σ) ∈ w.T :=
  mem_of_provable (Δ := [peqWFF hx hz, WFF.boxx x ⟨A, hx⟩ φ])
    (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ'
      · exact hpe
      · rw [List.mem_singleton.mp hψ']
        exact h)
    ⟨Proof.boxx_reView hx hz hcl hclI φ⟩
end World

end Canon

end V12M
