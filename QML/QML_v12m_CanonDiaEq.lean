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


/-! ## The class's realised member

The self part of the extent is unioned over the `≐`-class like the proper part, so the content it
carries has to come from a member of the class **chosen by the class, not by the address**:
`Classical.choose` on `∃ y, PEqW x y ∧ Realised y` would depend on `x`, and two identified addresses
would then get different contents, which is exactly what the union is for.  So take the *least*
realised root index in the class — a realised address is always a bare free root
(`World.RealData.hx`), and the predicate's extension depends only on the class, so the least witness
does too (`classRepIdx_congr`).
-/

/-- `c` names a realised member of `x`'s class. -/
def RealHere (w : World σ N₀) (x : VarSymb) (c : ℕ) : Prop :=
  w.PEqW x (.root (.free c)) ∧ w.Realised (.root (.free c))

theorem exists_realHere {w : World σ N₀} {x : VarSymb}
    (h : ∃ y, w.PEqW x y ∧ w.Realised y) : ∃ c, RealHere w x c := by
  obtain ⟨y, hpe, hr⟩ := h
  exact ⟨hr.data.c, hr.data.hx ▸ hpe, hr.data.hx ▸ hr⟩

open Classical in
/-- ⭐The class's canonical realised member, as an index. -/
noncomputable def classRepIdx (w : World σ N₀) (x : VarSymb)
    (h : ∃ y, w.PEqW x y ∧ w.Realised y) : ℕ :=
  Nat.find (exists_realHere h)

/-- ⭐The class's canonical realised member. -/
noncomputable def classRep (w : World σ N₀) (x : VarSymb)
    (h : ∃ y, w.PEqW x y ∧ w.Realised y) : VarSymb :=
  .root (.free (classRepIdx w x h))

open Classical in
theorem classRep_peq {w : World σ N₀} {x : VarSymb} (h : ∃ y, w.PEqW x y ∧ w.Realised y) :
    w.PEqW x (classRep w x h) :=
  (Nat.find_spec (exists_realHere h)).1

open Classical in
theorem classRep_realised {w : World σ N₀} {x : VarSymb} (h : ∃ y, w.PEqW x y ∧ w.Realised y) :
    w.Realised (classRep w x h) :=
  (Nat.find_spec (exists_realHere h)).2

open Classical in
/-- ⭐**The choice is a function of the class**: identified addresses have the same predicate up to
    `PEqW.trans`, so the same least witness.  This is what makes the self part of the extent, and
    the content it carries, invariant under the theory's identification. -/
theorem classRepIdx_congr {w : World σ N₀} {x x' : VarSymb} (hxx : w.PEqW x x')
    (h : ∃ y, w.PEqW x y ∧ w.Realised y) (h' : ∃ y, w.PEqW x' y ∧ w.Realised y) :
    classRepIdx w x h = classRepIdx w x' h' := by
  refine le_antisymm (Nat.find_le ⟨?_, ?_⟩) (Nat.find_le ⟨?_, ?_⟩)
  · exact hxx.trans (Nat.find_spec (exists_realHere h')).1
  · exact (Nat.find_spec (exists_realHere h')).2
  · exact hxx.symm.trans (Nat.find_spec (exists_realHere h)).1
  · exact (Nat.find_spec (exists_realHere h)).2

theorem classRep_congr {w : World σ N₀} {x x' : VarSymb} (hxx : w.PEqW x x')
    (h : ∃ y, w.PEqW x y ∧ w.Realised y) (h' : ∃ y, w.PEqW x' y ∧ w.Realised y) :
    classRep w x h = classRep w x' h' := by
  rw [classRep, classRep, classRepIdx_congr hxx h h']

/-! ## The extent, up to the theory's identification -/

/-- ⭐The extent of the possible object named by `x`, with its **proper** part taken up to provable
    `≐` (§2d): the successors whose language is the view of some address the theory identifies with
    `x` and which hold everything that address holds `□`-necessarily; and — under strong T — the
    world itself when `x` is realised.

    A child world is tagged by exactly one witness (`DiaView.inj`), so the union is unambiguous.
    ⭐**Both parts are unioned** (2026-09-27): the self clause asks for *some* address the theory
    identifies with `x` to be realised, not for `x` itself, which is what makes `extent_congr`
    unconditional.  `World.real` stays the chain's bookkeeping — it need not be `≐`-invariant,
    because the content read at the self point comes from the **class's** realised member
    (`classRep`), not from `x`'s own datum, and that choice is a function of the class
    (`classRep_congr`).  So the realising term is still a chain witness's, with its `hstage`, and
    `interp_canon`'s induction is untouched. -/
def extent (w : World σ N₀) (x : VarSymb) : Set (Succ w) :=
  {w' | (∃ y, w.PEqW x y ∧ w'.1.depth = w.depth + 1 ∧ DiaView y w w'.1 ∧
      BoxxContents y w w'.1) ∨ (w'.1 = w ∧ ∃ y, w.PEqW x y ∧ w.Realised y)}

/-- A member of the extent is the world itself or one level deeper; a proper one comes with its
    **tag**. -/
theorem extent_cases {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x) :
    (w'.1.depth - w.depth = 1 ∧ ∃ y, w.PEqW x y ∧ DiaView y w w'.1 ∧ BoxxContents y w w'.1) ∨
      (w'.1.depth - w.depth = 0 ∧ w'.1 = w ∧ ∃ y, w.PEqW x y ∧ w.Realised y) := by
  rcases hw' with ⟨y, hpe, hd, hv, hb⟩ | ⟨he, hr⟩
  · exact Or.inl ⟨by omega, y, hpe, hv, hb⟩
  · exact Or.inr ⟨by rw [he]; omega, he, hr⟩

/-- ⭐A member one level deeper is a proper one, with its tag. -/
theorem extent_proper {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth ≠ 0) :
    w'.1.depth - w.depth = 1 ∧ ∃ y, w.PEqW x y ∧ DiaView y w w'.1 ∧ BoxxContents y w w'.1 := by
  rcases extent_cases hw' with h | ⟨h, _⟩
  · exact h
  · exact absurd h hd

/-- A member at this depth is the world itself, and then some address of the class is realised. -/
theorem extent_self {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth = 0) : w'.1 = w ∧ ∃ y, w.PEqW x y ∧ w.Realised y := by
  rcases extent_cases hw' with ⟨h, -⟩ | ⟨-, h⟩
  · omega
  · exact h

theorem extent_dist {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth ≠ 0) : w'.1.depth - w.depth = 1 :=
  (extent_proper hw' hd).1

theorem extent_acc {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth ≠ 0) : Acc' w w'.1 :=
  w'.acc (extent_dist hw' hd)

/-- ⭐The view of the **tag** embeds in the child's language; a body written in the `x`-view is read
    there through the renaming `x ↦ y`. -/
theorem extent_le {w w₂ : World σ N₀} {y : VarSymb} (hv : DiaView y w w₂) (i : ℕ × ℕ) :
    ((w.L.ctx i).diaIn y).Le (w₂.L.ctx (childStage i)) :=
  hv.le (le_max_left _ _) (le_max_right _ _) 0

/-- The world itself is in the extent of a realised address — `x` is its own class member, its
    declaration coming from the datum (`World.Realised.decl`). -/
theorem self_mem_extent {w : World σ N₀} {x : VarSymb} (h : w.Realised x) :
    (⟨w, ⟨R.refl h.T w⟩⟩ : Succ w) ∈ extent w x :=
  Or.inr ⟨rfl, x, h.decl.elim fun _ h' => h'.elim fun _ hr => World.PEqW.refl hr, h⟩

/-- The same at an address the class's realised member is identified with. -/
theorem self_mem_extent_of_peq {w : World σ N₀} {x y : VarSymb} (hpe : w.PEqW x y)
    (h : w.Realised y) :
    (⟨w, ⟨R.refl h.T w⟩⟩ : Succ w) ∈ extent w x :=
  Or.inr ⟨rfl, y, hpe, h⟩

/-- A child tagged by `y` is in the extent of `y` itself. -/
theorem mem_extent_of_tag {w : World σ N₀} {y : VarSymb} {A : VarType} {i : ℕ × ℕ}
    (hy : (w.L.ctx i).ref y = some (.VTypeDia A)) {w' : Succ w} (hdep : w'.1.depth = w.depth + 1)
    (hv : DiaView y w w'.1) (hb : BoxxContents y w w'.1) : w' ∈ extent w y :=
  Or.inl ⟨y, World.PEqW.refl hy, hdep, hv, hb⟩

/-- ⭐**What the union is for**: addresses the theory identifies have the same extent, with no side
    condition (2026-09-27).  Both clauses quantify over the class, so both transport by
    `PEqW.trans` — the self clause exactly as the proper one does. -/
theorem extent_congr {w : World σ N₀} {x y : VarSymb} (h : w.PEqW x y) :
    extent w x = extent w y := by
  apply Set.eq_of_subset_of_subset
  · rintro w' (⟨z, hz, hd, hv, hb⟩ | ⟨he, z, hz, hr⟩)
    · exact Or.inl ⟨z, World.PEqW.trans (World.PEqW.symm h) hz, hd, hv, hb⟩
    · exact Or.inr ⟨he, z, World.PEqW.trans (World.PEqW.symm h) hz, hr⟩
  · rintro w' (⟨z, hz, hd, hv, hb⟩ | ⟨he, z, hz, hr⟩)
    · exact Or.inl ⟨z, World.PEqW.trans h hz, hd, hv, hb⟩
    · exact Or.inr ⟨he, z, World.PEqW.trans h hz, hr⟩

/-! ## Reading the identification, and the tag of a member -/

namespace World

/-- A stage declaring both addresses of an identification. -/
noncomputable def PEqW.st {w : World σ N₀} {x y : VarSymb} (h : w.PEqW x y) : ℕ × ℕ := h.choose

/-- Their shared content type there. -/
noncomputable def PEqW.ty {w : World σ N₀} {x y : VarSymb} (h : w.PEqW x y) : VarType :=
  h.choose_spec.choose

theorem PEqW.refX {w : World σ N₀} {x y : VarSymb} (h : w.PEqW x y) :
    (w.L.ctx h.st).ref x = some (.VTypeDia h.ty) :=
  h.choose_spec.choose_spec.choose

theorem PEqW.refY {w : World σ N₀} {x y : VarSymb} (h : w.PEqW x y) :
    (w.L.ctx h.st).ref y = some (.VTypeDia h.ty) :=
  h.choose_spec.choose_spec.choose_spec.choose

theorem PEqW.peq {w : World σ N₀} {x y : VarSymb} (h : w.PEqW x y) :
    w.PEq h.st h.refX h.refY :=
  h.choose_spec.choose_spec.choose_spec.choose_spec

end World

/-- ⭐The tag of a proper member of an extent: the witness its language is the view of. -/
noncomputable def tagOf {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth ≠ 0) : VarSymb :=
  (extent_proper hw' hd).2.choose

theorem peqw_tagOf {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth ≠ 0) : w.PEqW x (tagOf hw' hd) :=
  (extent_proper hw' hd).2.choose_spec.1

theorem diaView_tagOf {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth ≠ 0) : DiaView (tagOf hw' hd) w w'.1 :=
  (extent_proper hw' hd).2.choose_spec.2.1

theorem boxxContents_tagOf {w : World σ N₀} {x : VarSymb} {w' : Succ w} (hw' : w' ∈ extent w x)
    (hd : w'.1.depth - w.depth ≠ 0) : BoxxContents (tagOf hw' hd) w w'.1 :=
  (extent_proper hw' hd).2.choose_spec.2.2


/-- ⭐The body of a `◇`-term, read in the **tag's** view: moved to a stage declaring both witnesses
    and renamed along `x ↦ y` there.  Cleanliness comes from the world's flatness, so this needs no
    side condition. -/
noncomputable def tagBody (w : World σ N₀) {Γ : Ctx} {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i))
    {x y : VarSymb} (hpe : w.PEqW x y) {A : VarType} {a : Ann A} (t : Term σ (Γ.diaIn x) A a) :
    Σ b : Ann A, Term σ ((w.L.ctx (i ⊔ hpe.st)).diaIn y) A b :=
  ⟨_, Term.reView ((w.L.ctx_le (le_sup_right : hpe.st ≤ i ⊔ hpe.st)).ref hpe.refX)
      ((w.L.ctx_le (le_sup_right : hpe.st ≤ i ⊔ hpe.st)).ref hpe.refY)
      ((w.L.flatCtx (i ⊔ hpe.st)).viewClean
        ((w.L.ctx_le (le_sup_right : hpe.st ≤ i ⊔ hpe.st)).ref hpe.refX))
      (Term.mono ((e.trans (w.L.ctx_le (le_sup_left : i ≤ i ⊔ hpe.st))).diaIn x) t)⟩

/-- The tag is declared at the stage the body is read at. -/
theorem refY_sup {w : World σ N₀} {i : ℕ × ℕ} {x y : VarSymb} (hpe : w.PEqW x y) :
    ∃ X, (w.L.ctx (i ⊔ hpe.st)).ref y = some (.VTypeDia X) :=
  ⟨hpe.ty, (w.L.ctx_le (le_sup_right : hpe.st ≤ i ⊔ hpe.st)).ref hpe.refY⟩

/-- Reading the body in the tag's view absorbs a weakening of the term's context. -/
theorem tagBody_mono {w : World σ N₀} {Γ Γ' : Ctx} (h : Γ.Le Γ') {i : ℕ × ℕ}
    (e : Γ'.Le (w.L.ctx i)) {x y : VarSymb} (hpe : w.PEqW x y) {A : VarType} {a : Ann A}
    (t : Term σ (Γ.diaIn x) A a) :
    tagBody w e hpe (Term.mono (h.diaIn x) t) = tagBody w (h.trans e) hpe t :=
  congrArg (Sigma.mk _) (congrArg (Term.reView _ _ _) (Term.mono_mono _ _ t))



/-- The declarations and cleanliness the tagged reading uses, at the stage it reads at. -/
theorem World.PEqW.refXs {w : World σ N₀} {x y : VarSymb} (hpe : w.PEqW x y) (i : ℕ × ℕ) :
    (w.L.ctx (i ⊔ hpe.st)).ref x = some (.VTypeDia hpe.ty) :=
  (w.L.ctx_le (le_sup_right : hpe.st ≤ i ⊔ hpe.st)).ref hpe.refX

theorem World.PEqW.refYs {w : World σ N₀} {x y : VarSymb} (hpe : w.PEqW x y) (i : ℕ × ℕ) :
    (w.L.ctx (i ⊔ hpe.st)).ref y = some (.VTypeDia hpe.ty) :=
  (w.L.ctx_le (le_sup_right : hpe.st ≤ i ⊔ hpe.st)).ref hpe.refY

theorem World.PEqW.clean {w : World σ N₀} {x y : VarSymb} (hpe : w.PEqW x y) (i : ℕ × ℕ) :
    Ctx.ViewClean (w.L.ctx (i ⊔ hpe.st)) x :=
  (w.L.flatCtx (i ⊔ hpe.st)).viewClean (hpe.refXs i)

/-- ⭐A view **formula**, read in the tag's view: the formula-level `tagBody`, and what the truth
    lemma's `◇` case says holds at a tagged successor. -/
noncomputable def tagWFF (w : World σ N₀) {i : ℕ × ℕ} {x y : VarSymb} (hpe : w.PEqW x y)
    (χ : WFF σ ((w.L.ctx i).diaIn x) 0) : WFF σ ((w.L.ctx (i ⊔ hpe.st)).diaIn y) 0 :=
  WFF.reView (hpe.refXs i) (hpe.refYs i) (hpe.clean i)
    (WFF.mono ((w.L.ctx_le (le_sup_left : i ≤ i ⊔ hpe.st)).diaIn x) χ)

/-- Reading a pair in the tag's view is reading its components there. -/
theorem tagBody_pair {w : World σ N₀} {Γ : Ctx} {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i))
    {x y : VarSymb} (hpe : w.PEqW x y) {A B : VarType} {a : Ann A} {b : Ann B}
    (s : Term σ (Γ.diaIn x) A a) (t : Term σ (Γ.diaIn x) B b) :
    tagBody w e hpe (Term.pair s t) =
      ⟨_, Term.pair (tagBody w e hpe s).2 (tagBody w e hpe t).2⟩ := rfl

/-- ⭐A body lifted from the `□`-part is read in the tag's view as itself: the renaming touches only
    the content address. -/
theorem tagBody_mono_boxIn {w : World σ N₀} {Γ : Ctx} {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i))
    {x y : VarSymb} (hpe : w.PEqW x y) {A : VarType} {a : Ann A} (b : Term σ Γ.boxIn A a) :
    tagBody w e hpe (Term.mono (Ctx.le_boxIn_diaIn Γ x) b) =
      ⟨a, Term.mono (Ctx.le_boxIn_diaIn (w.L.ctx (i ⊔ hpe.st)) y)
        (Term.mono (e.trans (w.L.ctx_le (le_sup_left : i ≤ i ⊔ hpe.st))).boxIn b)⟩ := by
  have hcomb : Term.mono ((e.trans (w.L.ctx_le (le_sup_left : i ≤ i ⊔ hpe.st))).diaIn x)
        (Term.mono (Ctx.le_boxIn_diaIn Γ x) b) =
      Term.mono (Ctx.le_boxIn_diaIn (w.L.ctx (i ⊔ hpe.st)) x)
        (Term.mono (e.trans (w.L.ctx_le (le_sup_left : i ≤ i ⊔ hpe.st))).boxIn b) := by
    rw [Term.mono_mono, Term.mono_mono]
  simp only [tagBody]
  rw [hcomb]
  exact Term.reView_mono_boxIn _ _ _ _
/-- Reading the body in the tag's view commutes with moving to a later stage — this is where
    `Term.reView_mono` earns its keep, and it is what makes `rden` stage-independent. -/
theorem tagBody_stage {w : World σ N₀} {Γ : Ctx} {i k : ℕ × ℕ} (hik : i ≤ k)
    (e : Γ.Le (w.L.ctx i)) {x y : VarSymb} (hpe : w.PEqW x y) {A : VarType} {a : Ann A}
    (t : Term σ (Γ.diaIn x) A a) :
    Term.mono ((w.L.ctx_le (sup_le_sup_right hik hpe.st)).diaIn y) (tagBody w e hpe t).2 =
      (tagBody w (e.trans (w.L.ctx_le hik)) hpe t).2 := by
  simp only [tagBody]
  rw [Term.reView_mono (w.L.ctx_le (sup_le_sup_right hik hpe.st))
    (hcl' := (w.L.flatCtx (k ⊔ hpe.st)).viewClean
      ((w.L.ctx_le (le_sup_right : hpe.st ≤ k ⊔ hpe.st)).ref hpe.refX)), Term.mono_mono]

end Canon

end V12M
