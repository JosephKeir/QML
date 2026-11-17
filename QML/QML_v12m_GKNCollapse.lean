import QML.QML_v12m_GKNSubst
import QML.QML_v12m_GKCollapse

/-!
# QML v12m — `GKN`: collapsing a child onto its parent (T, docs §12.50 item (v))

T's principal cut reductions (`boxR` against `TL`, `diaT` against `diaL`) need a derivation over a
tree with a child `c = k :: τ` turned into one with `c`'s subtree **folded into `τ`**: `c`'s
formulas collapsed onto `τ` (`WFF.collapse` at level 0), those below it collapsed one level deeper
each, the rest of the tree weakened.  The tree form of `GK.collapseD`; Brünnler's admissible
structural rule for T in deep sequents.

* `cmap τ k g`: the label map, `lmap g` with the step into `c` deleted (`c` goes where `τ`
  goes).
* `EdgeKind.col`, `colOpen`: an edge and an opening collapsed at a depth (a `◇_x`-edge follows its
  witness; at `c` an arrow opening becomes an identity opening).
* `CSetup`: the conditions, as `TMap`'s; ⭐`CSetup.ctx`: every node's context goes into its
  image's, by inclusion off `c`'s subtree and by `Ctx.Collapses` (at the depth below `c`) on it.
* `CSetup.addBirth`, `CSetup.addOpen`, `CSetup.addEdge`: the setup as both trees grow.
* `CSetup.F`, `CSetup.lf`: a formula at a node sent to its image (collapsed on `c`'s subtree,
  weakened off it); `CSetup.lf_mono_sub`: images of weakened sides.
* ⭐`GKN.collapse`: a derivation over the source tree gives one over the target of every
  formula's image (heights not kept).  Rules at `τ` into `c` become T's: `boxL` becomes `TL`,
  `foldR` becomes `diaT`, `diaR` becomes `diaT` then `reopenR`; under `c` each rule goes to itself,
  collapsed (`WFF.collapse_collapse` for `TL` and `diaT`, `Ctx.Collapses.opened` for `reopenR`).
-/

namespace V12M

set_option linter.unusedSectionVars false

variable [ModalSys]

/-! ## Collapses, weakened -/

namespace Ctx

theorem Collapses.mono_right {k : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx} (h : Collapses k Γ₁ Γ₂) (l : Γ₂.Le Γ₃) :
    Collapses k Γ₁ Γ₃ :=
  ⟨h.hT, fun v T hv => l.ref (h v T hv), fun y X hy =>
    ⟨fun h0 => l.witT ((h.wit y X hy).1 h0), fun k' hk => l.wit _ _ ((h.wit y X hy).2 k' hk)⟩⟩

theorem Collapses.mono_left {k : ℕ} {Γ₀ Γ₁ Γ₂ : Ctx} (l : Γ₀.Le Γ₁) (h : Collapses k Γ₁ Γ₂) :
    Collapses k Γ₀ Γ₂ :=
  ⟨h.hT, fun v T hv => h v T (l.ref hv), fun y X hy => h.wit y X (l.wit y X hy)⟩

/-- Declarations the target holds already. -/
theorem Collapses.inserts_of {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Collapses k Γ₁ Γ₂) :
    ∀ {L : List (Root × VarType)}, L.Pairwise (fun b b' => b.1 ≠ b'.1) →
      (∀ b ∈ L, Γ₁.RootFresh b.1) → (∀ b ∈ L, Γ₂ (.root b.1) = some b.2) →
      Collapses k (Γ₁.inserts L) Γ₂
  | [], _, _, _ => h
  | b :: L, hp, hf, hL => by
      obtain ⟨hb, hp⟩ := List.pairwise_cons.mp hp
      have ih := Collapses.inserts_of h hp (fun b' h' => hf b' (List.mem_cons_of_mem _ h'))
        (fun b' h' => hL b' (List.mem_cons_of_mem _ h'))
      have hfr : (Γ₁.inserts L).RootFresh b.1 :=
        (hf b List.mem_cons_self).inserts L fun b' hm => (hb b' hm).symm
      exact (ih.insert hfr b.2).mono_right
        (Ctx.insert_le_of (Ctx.Le.refl Γ₂) (hL b List.mem_cons_self))

end Ctx

namespace GKN

theorem EdgeKind.compat_refl' : ∀ e : EdgeKind, e.Compat e
  | .box => trivial
  | .dia _ => rfl

/-- An edge collapsed below a node at depth `d`: a `◇_x`-edge follows its witness. -/
def EdgeKind.col (d : ℕ) : EdgeKind → EdgeKind
  | .box => .box
  | .dia x => .dia (x.collapse d)

/-- An opening collapsed at depth `d`: at the collapsed child an arrow opening becomes an
    identity opening (`Ctx.Collapses.optIn_zero`); further in its witness collapses. -/
def colOpen (d : ℕ) : WitKind × VarSymb → WitKind × VarSymb
  | (.ident, y) => (.ident, y.collapse d)
  | (.arrow, y) => match d with
    | 0 => (.ident, y)
    | d + 1 => (.arrow, y.collapse d)

/-- ⭐**Opening a collapsed view** where the target opens the collapsed opening. -/
theorem _root_.V12M.Ctx.Collapses.optInK_of (hO : ModalSys.Opt = true) {d : ℕ} {Γ₁ Γ₂ : Ctx}
    (h : Ctx.Collapses d Γ₁ Γ₂) {κ : WitKind} {y : VarSymb} {X : VarType}
    (hw : Γ₁.witK κ y = some X) (hop : Γ₂.Opened (colOpen d (κ, y)).1 (colOpen d (κ, y)).2) :
    Ctx.Collapses d (Γ₁.optInK κ y) Γ₂ := by
  cases κ with
  | arrow =>
      cases d with
      | zero => exact (h.optIn_zero hO hw).mono_right (Ctx.optInK_le_of (κ := .ident)
          (Ctx.Le.refl _) hop)
      | succ d => exact (h.optIn_succ hw).mono_right (Ctx.optInK_le_of (κ := .arrow)
          (Ctx.Le.refl _) hop)
  | ident => exact (h.optInT hw).mono_right (Ctx.optInK_le_of (κ := .ident) (Ctx.Le.refl _) hop)

theorem _root_.V12M.Ctx.Collapses.optInsK_of (hO : ModalSys.Opt = true) {d : ℕ} {Γ₁ Γ₂ : Ctx}
    (h : Ctx.Collapses d Γ₁ Γ₂) :
    ∀ {L : List (WitKind × VarSymb)}, Γ₁.OptsEff L →
      (∀ o ∈ L, Γ₂.Opened (colOpen d o).1 (colOpen d o).2) →
      Ctx.Collapses d (Γ₁.optInsK L) Γ₂
  | [], _, _ => h
  | _ :: _, ⟨he, _, _, hX⟩, hop =>
      (Ctx.Collapses.optInsK_of hO h he fun o h' => hop o (List.mem_cons_of_mem _ h')).optInK_of
        hO hX (hop _ List.mem_cons_self)

/-- ⭐**The label map collapsing `c = k :: τ` onto `τ`**: child indices by `g` (as `lmap g`),
    and the step into `c` deleted, so `c` goes where `τ` goes. -/
def cmap (τ : Lab) (k : ℕ) (g : Lab → ℕ → ℕ) : Lab → Lab
  | [] => []
  | j :: ρ => if j :: ρ = k :: τ then cmap τ k g ρ else g ρ j :: cmap τ k g ρ

/-- A node's depth below `c = k :: τ`. -/
abbrev cdepth (τ : Lab) (ρ : Lab) : ℕ := ρ.length - (τ.length + 1)

theorem cmap_c (τ : Lab) (k : ℕ) (g : Lab → ℕ → ℕ) : cmap τ k g (k :: τ) = cmap τ k g τ := by
  simp [cmap]

theorem cmap_cons {τ : Lab} {k : ℕ} {g : Lab → ℕ → ℕ} {j : ℕ} {ρ : Lab} (h : j :: ρ ≠ k :: τ) :
    cmap τ k g (j :: ρ) = g ρ j :: cmap τ k g ρ := by
  simp only [cmap, if_neg h]

theorem ne_c_of_under {τ ρ : Lab} {k : ℕ} (h : (k :: τ) <:+ ρ) (j : ℕ) : j :: ρ ≠ k :: τ :=
  fun e => by
    have := h.length_le
    rw [← (List.cons.inj e).2] at this
    simp at this

theorem cdepth_cons {τ ρ : Lab} {k : ℕ} (h : (k :: τ) <:+ ρ) (j : ℕ) :
    cdepth τ (j :: ρ) = cdepth τ ρ + 1 := by
  have := h.length_le
  simp only [cdepth, List.length_cons] at this ⊢
  omega

theorem cdepth_c (τ : Lab) (k : ℕ) : cdepth τ (k :: τ) = 0 := by simp [cdepth]

/-- ⭐**The collapse conditions**: the target satisfies the invariant; off `c`'s subtree edges,
    births and openings go to themselves (edges fitting, openings opened); on it, edges and
    openings go to their collapses at the image, births to the image; `c`'s own `◇_x`-edge
    asks `x` opened at `τ` (identity kind); the target's names are the source's. -/
structure CSetup (Γ₀ : Ctx) (τ : Lab) (k : ℕ) (g : Lab → ℕ → ℕ) (S S' : Tree) : Prop where
  ok : S'.OK Γ₀
  hT : ModalSys.T = true
  hO : ModalSys.Opt = true
  edge_off : ∀ c e, S.edge c = some e → ¬ (k :: τ) <:+ c →
    ∃ e', S'.edge (cmap τ k g c) = some e' ∧ e.Fits (S'.ctxAt Γ₀ (cmap τ k g c)) e'
  edge_under : ∀ j ρ e, S.edge (j :: ρ) = some e → (k :: τ) <:+ ρ →
    S'.edge (cmap τ k g (j :: ρ)) = some (e.col (cdepth τ ρ))
  edge_c : ∀ x, S.edge (k :: τ) = some (.dia x) → (S'.ctxAt Γ₀ (cmap τ k g τ)).Opened .ident x
  birth : ∀ ρ b, b ∈ S.birthsAt ρ → b ∈ S'.birthsAt (cmap τ k g ρ)
  opens_off : ∀ ρ, ¬ (k :: τ) <:+ ρ → ∀ o ∈ S.opensAt ρ,
    (S'.ctxAt Γ₀ (cmap τ k g ρ)).Opened o.1 o.2
  opens_under : ∀ ρ, (k :: τ) <:+ ρ → ∀ o ∈ S.opensAt ρ,
    (S'.ctxAt Γ₀ (cmap τ k g ρ)).Opened (colOpen (cdepth τ ρ) o).1 (colOpen (cdepth τ ρ) o).2
  names : ∀ b ∈ S'.births, ∃ b₀ ∈ S.births, b₀.2.1 = b.2.1
  hc : S.edge (k :: τ) ≠ none

namespace CSetup

variable {Γ₀ : Ctx} {τ : Lab} {k : ℕ} {g : Lab → ℕ → ℕ} {S S' : Tree}

/-- A node's births, collapsed onto its image. -/
theorem births_col (cs : CSetup Γ₀ τ k g S S') (hS : S.OK Γ₀) {d : ℕ} {V W : Ctx}
    (ρ : Lab) (hV : Ctx.Collapses d V W) (hW : W.Le (S'.ctxAt Γ₀ (cmap τ k g ρ)))
    (hfr : ∀ b ∈ S.birthsAt ρ, V.RootFresh b.1) :
    Ctx.Collapses d (V.inserts (S.birthsAt ρ)) (S'.ctxAt Γ₀ (cmap τ k g ρ)) :=
  (hV.mono_right hW).inserts_of (Tree.birthsAt_pairwise hS ρ) hfr
    fun b hb => Tree.ctxAt_root cs.ok (cs.birth ρ b hb)

/-- ⭐**Every node's context goes into its image's**: by inclusion off `c`'s subtree, collapsed
    at its depth below `c` on it. -/
theorem ctx (cs : CSetup Γ₀ τ k g S S') (hS : S.OK Γ₀) (hW : S.WitOK Γ₀) :
    ∀ ρ, (¬ (k :: τ) <:+ ρ → (S.ctxAt Γ₀ ρ).Le (S'.ctxAt Γ₀ (cmap τ k g ρ))) ∧
      ((k :: τ) <:+ ρ →
        Ctx.Collapses (cdepth τ ρ) (S.ctxAt Γ₀ ρ) (S'.ctxAt Γ₀ (cmap τ k g ρ)))
  | [] => by
      refine ⟨fun _ => ?_, fun h => absurd h.length_le (by simp)⟩
      have hΞ : Γ₀.Le (S'.ctxAt Γ₀ []) := by
        simp only [Tree.ctxAt]
        exact (Ctx.le_inserts _ (Tree.birthsAt_pairwise cs.ok _)
          fun b hb => cs.ok.fresh _ (Tree.mem_birthsAt.mp hb)).trans (Ctx.le_optInsK _ _)
      simp only [Tree.ctxAt]
      exact Ctx.optInsK_le_of _
        (Ctx.inserts_le_of _ hΞ fun b hb => Tree.ctxAt_root cs.ok (cs.birth [] b hb))
        (cs.opens_off [] (fun h => absurd h.length_le (by simp)))
  | j :: ρ => by
      obtain ⟨ihL, ihC⟩ := ctx cs hS hW ρ
      by_cases hc : j :: ρ = k :: τ
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hc
        refine ⟨fun h => absurd (List.suffix_refl _) h, fun _ => ?_⟩
        have hoff : ¬ (j :: ρ) <:+ ρ := fun h' => by have := h'.length_le; simp at this
        have hL := ihL hoff
        -- the collapsed view
        have hV : Ctx.Collapses 0 (S.view (j :: ρ) (S.ctxAt Γ₀ ρ))
            (S'.ctxAt Γ₀ (cmap ρ j g ρ)) := by
          cases he : S.edge (j :: ρ) with
          | none =>
              rw [Tree.view_box (Or.inl he)]
              exact (Ctx.collapses_boxIn_self cs.hT _).mono_right hL
          | some e =>
              cases e with
              | box =>
                  rw [Tree.view_box (Or.inr he)]
                  exact (Ctx.collapses_boxIn_self cs.hT _).mono_right hL
              | dia x =>
                  rw [Tree.view_dia he]
                  obtain ⟨X, hX⟩ := hW j ρ x he
                  exact ((Ctx.collapses_diaIn_optInT cs.hT cs.hO _ (hL.ref hX)).mono_left
                    (hL.diaIn x)).mono_right
                    (Ctx.optInK_le_of (κ := .ident) (Ctx.Le.refl _) (cs.edge_c x he))
        rw [cmap_c, cdepth_c]
        have hB := cs.births_col hS (j :: ρ) hV (by rw [cmap_c]; exact Ctx.Le.refl _)
          fun b hb => Tree.view_fresh hS j ρ hb
        rw [cmap_c] at hB
        rw [Tree.ctxAt_eq_pre]
        refine hB.optInsK_of cs.hO (hS.eff (j :: ρ)) fun o ho => ?_
        have := cs.opens_under (j :: ρ) (List.suffix_refl _) o ho
        rwa [cmap_c, cdepth_c] at this
      · by_cases hu : (k :: τ) <:+ ρ
        · refine ⟨fun h => absurd (hu.trans (List.suffix_cons j ρ)) h, fun _ => ?_⟩
          have hC := ihC hu
          rw [cmap_cons (ne_c_of_under hu j), cdepth_cons hu]
          have hV : Ctx.Collapses (cdepth τ ρ + 1) (S.view (j :: ρ) (S.ctxAt Γ₀ ρ))
              ((S'.view (g ρ j :: cmap τ k g ρ) (S'.ctxAt Γ₀ (cmap τ k g ρ)))) := by
            cases he : S.edge (j :: ρ) with
            | none =>
                rw [Tree.view_box (Or.inl he)]
                exact hC.boxIn.mono_right (Tree.boxIn_le_view _ _)
            | some e =>
                have he' := cs.edge_under j ρ e he hu
                rw [cmap_cons (ne_c_of_under hu j)] at he'
                cases e with
                | box =>
                    rw [Tree.view_box (Or.inr he)]
                    exact hC.boxIn.mono_right (Tree.boxIn_le_view _ _)
                | dia x =>
                    rw [Tree.view_dia he, Tree.view_dia he']
                    exact hC.diaIn x
          have hB := cs.births_col hS (j :: ρ) hV
            (by rw [cmap_cons (ne_c_of_under hu j)]; exact Tree.view_le_ctxAt cs.ok _ _)
            fun b hb => Tree.view_fresh hS j ρ hb
          rw [cmap_cons (ne_c_of_under hu j)] at hB
          rw [Tree.ctxAt_eq_pre]
          refine hB.optInsK_of cs.hO (hS.eff (j :: ρ)) fun o ho => ?_
          have := cs.opens_under (j :: ρ) (hu.trans (List.suffix_cons j ρ)) o ho
          rwa [cmap_cons (ne_c_of_under hu j), cdepth_cons hu] at this
        · have hoff : ¬ (k :: τ) <:+ (j :: ρ) := fun h => by
            rcases List.suffix_cons_iff.mp h with h | h
            · exact hc h.symm
            · exact hu h
          refine ⟨fun _ => ?_, fun h => absurd h hoff⟩
          have hL := ihL hu
          have e₁ := cmap_cons (τ := τ) (k := k) (g := g) hc
          have hv : (S.view (j :: ρ) (S.ctxAt Γ₀ ρ)).Le (S'.ctxAt Γ₀ (cmap τ k g (j :: ρ))) := by
            rw [e₁]
            exact Tree.view_le_of hL (Tree.view_le_ctxAt cs.ok (g ρ j) (cmap τ k g ρ))
              (Tree.ctxAt_wit S' (g ρ j) (cmap τ k g ρ)) fun e he => by
                obtain ⟨e', he', hf⟩ := cs.edge_off _ e he hoff
                rw [e₁] at he' hf
                exact ⟨e', he', hf⟩
          have hO' := cs.opens_off (j :: ρ) hoff
          have hb' : ∀ b ∈ S.birthsAt (j :: ρ),
              (S'.ctxAt Γ₀ (cmap τ k g (j :: ρ))) (.root b.1) = some b.2 :=
            fun b hb => Tree.ctxAt_root cs.ok (cs.birth (j :: ρ) b hb)
          simp only [Tree.ctxAt]
          exact Ctx.optInsK_le_of _ (Ctx.inserts_le_of _ hv hb') hO'

end CSetup

/-! ## The setup as the tree grows -/

theorem cmap_setIdx_off {τ : Lab} {k : ℕ} (g : Lab → ℕ → ℕ) {σ' : Lab} {j j' : ℕ} :
    ∀ ρ, ¬ (j :: σ') <:+ ρ → cmap τ k (setIdx g σ' j j') ρ = cmap τ k g ρ
  | [], _ => rfl
  | i :: ρ, h => by
      have hρ : ¬ (j :: σ') <:+ ρ := fun h' => h (h'.trans (List.suffix_cons i ρ))
      have hne : ¬ (ρ = σ' ∧ i = j) := fun ⟨h₁, h₂⟩ => h (by subst h₁ h₂; exact List.suffix_refl _)
      simp only [cmap]
      rw [cmap_setIdx_off g ρ hρ]
      split
      · rfl
      · unfold setIdx
        rw [if_neg hne]

theorem cmap_setIdx_new {τ : Lab} {k : ℕ} (g : Lab → ℕ → ℕ) {σ' : Lab} {j j' : ℕ}
    (h : j :: σ' ≠ k :: τ) : cmap τ k (setIdx g σ' j j') (j :: σ') = j' :: cmap τ k g σ' := by
  rw [cmap_cons h, cmap_setIdx_off g σ' (fun h' => by have := h'.length_le; simp at this)]
  unfold setIdx
  rw [if_pos ⟨rfl, rfl⟩]

namespace CSetup

variable {Γ₀ : Ctx} {τ : Lab} {k : ℕ} {g : Lab → ℕ → ℕ} {S S' : Tree}

theorem fresh (cs : CSetup Γ₀ τ k g S S') {r : Root} (hr : S.Fresh Γ₀ r) : S'.Fresh Γ₀ r :=
  ⟨hr.ctx, fun b hb he => by
    obtain ⟨b₀, hb₀, he₀⟩ := cs.names b hb
    exact hr.births b₀ hb₀ (he₀.trans he)⟩

/-- ⭐**The setup survives a birth**, at the node's image, under the same name. -/
theorem addBirth (cs : CSetup Γ₀ τ k g S S') {u : ℕ} (hu : S.Fresh Γ₀ (.free u)) (σ' : Lab)
    (T : VarType) :
    CSetup Γ₀ τ k g (S.addBirth σ' (.free u) T) (S'.addBirth (cmap τ k g σ') (.free u) T) := by
  have hk := Tree.ctxAt_addBirth (Γ₀ := Γ₀) (cs.fresh hu) (cmap τ k g σ') T
  refine ⟨cs.ok.addBirth (cs.fresh hu) _ T, cs.hT, cs.hO, fun c e he hc => ?_, cs.edge_under,
    fun x he => (cs.edge_c x he).mono (hk _), fun ρ b hb => ?_,
    fun ρ hρ o ho => (cs.opens_off ρ hρ o ho).mono (hk _),
    fun ρ hρ o ho => (cs.opens_under ρ hρ o ho).mono (hk _), fun b hb => ?_, cs.hc⟩
  · obtain ⟨e', he', hf⟩ := cs.edge_off c e he hc
    exact ⟨e', he', hf.mono (hk _)⟩
  · rw [Tree.birthsAt_addBirth] at hb ⊢
    split_ifs at hb with hσ
    · subst hσ
      rw [if_pos rfl]
      rcases List.mem_cons.mp hb with rfl | hb
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (cs.birth _ b hb)
    · have := cs.birth ρ b hb
      split_ifs
      · exact List.mem_cons_of_mem _ this
      · exact this
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨(σ', .free u, T), List.mem_cons_self, rfl⟩
    · obtain ⟨b₀, hb₀, he⟩ := cs.names b hb
      exact ⟨b₀, List.mem_cons_of_mem _ hb₀, he⟩

/-- The opening a node's opening goes to: itself off `c`'s subtree, collapsed on it. -/
def openImg (τ : Lab) (k : ℕ) (ρ : Lab) (o : WitKind × VarSymb) : WitKind × VarSymb :=
  if (k :: τ) <:+ ρ then colOpen (cdepth τ ρ) o else o

/-- A source witness gives the target's witness for the image opening. -/
theorem wit_img (cs : CSetup Γ₀ τ k g S S') (hS : S.OK Γ₀) (hW : S.WitOK Γ₀) {ρ : Lab}
    {κ : WitKind} {y : VarSymb} {X : VarType} (hX : (S.ctxAt Γ₀ ρ).witK κ y = some X) :
    (S'.ctxAt Γ₀ (cmap τ k g ρ)).witK (openImg τ k ρ (κ, y)).1 (openImg τ k ρ (κ, y)).2 =
      some X := by
  unfold openImg
  split_ifs with hu
  · have hC := (cs.ctx hS hW ρ).2 hu
    cases κ with
    | ident => exact hC.witT hX
    | arrow =>
        cases hd : cdepth τ ρ with
        | zero =>
            rw [hd] at hC
            exact (hC.wit y X hX).1 rfl
        | succ d =>
            rw [hd] at hC
            exact (hC.wit y X hX).2 d rfl
  · exact ((cs.ctx hS hW ρ).1 hu).witK hX

/-- ⭐**The setup survives an opening** that takes effect, its image opened at the node's
    image. -/
theorem addOpen (cs : CSetup Γ₀ τ k g S S') (hS : S.OK Γ₀) (hW : S.WitOK Γ₀) {σ' : Lab}
    {κ : WitKind} {y : VarSymb} {X : VarType} (hX : (S.ctxAt Γ₀ σ').witK κ y = some X) :
    CSetup Γ₀ τ k g (S.addOpen σ' κ y)
      (S'.addOpen (cmap τ k g σ') (openImg τ k σ' (κ, y)).1 (openImg τ k σ' (κ, y)).2) := by
  have hk := Tree.ctxAt_addOpen (D := S') (Γ₀ := Γ₀) (cmap τ k g σ')
    (openImg τ k σ' (κ, y)).1 (openImg τ k σ' (κ, y)).2
  have hwX := cs.wit_img hS hW hX
  have hnew : ((S'.addOpen (cmap τ k g σ') (openImg τ k σ' (κ, y)).1
      (openImg τ k σ' (κ, y)).2).ctxAt Γ₀ (cmap τ k g σ')).Opened
      (openImg τ k σ' (κ, y)).1 (openImg τ k σ' (κ, y)).2 := by
    rw [Tree.ctxAt_addOpen_self]
    exact Ctx.opened_self hwX
  have hnew' : ∀ o', o' = openImg τ k σ' (κ, y) →
      ((S'.addOpen (cmap τ k g σ') (openImg τ k σ' (κ, y)).1
        (openImg τ k σ' (κ, y)).2).ctxAt Γ₀ (cmap τ k g σ')).Opened o'.1 o'.2 :=
    fun o' e => by subst e; exact hnew
  refine ⟨cs.ok.addOpen cs.hO hwX, cs.hT, cs.hO, fun c e he hc => ?_, cs.edge_under,
    fun x he => (cs.edge_c x he).mono (hk _), cs.birth, fun ρ hρ o ho => ?_,
    fun ρ hρ o ho => ?_, cs.names, cs.hc⟩
  · obtain ⟨e', he', hf⟩ := cs.edge_off c e he hc
    exact ⟨e', he', hf.mono (hk _)⟩
  · rw [Tree.opensAt_addOpen] at ho
    split_ifs at ho with hσ
    · subst hσ
      rcases List.mem_cons.mp ho with rfl | ho
      · exact hnew' _ (by simp [openImg, hρ])
      · exact (cs.opens_off _ hρ o ho).mono (hk _)
    · exact (cs.opens_off ρ hρ o ho).mono (hk _)
  · rw [Tree.opensAt_addOpen] at ho
    split_ifs at ho with hσ
    · subst hσ
      rcases List.mem_cons.mp ho with rfl | ho
      · exact hnew' _ (by simp [openImg, hρ])
      · exact (cs.opens_under _ hρ o ho).mono (hk _)
    · exact (cs.opens_under ρ hρ o ho).mono (hk _)

/-- The edge a new child's edge goes to: itself off `c`'s subtree, collapsed on it. -/
def edgeImg (τ : Lab) (k : ℕ) (σ' : Lab) (e : EdgeKind) : EdgeKind :=
  if (k :: τ) <:+ σ' then e.col (cdepth τ σ') else e

/-- ⭐**The setup survives a new child**: the source's vacant, the target's fresh, its edge
    collapsed on `c`'s subtree. -/
theorem addEdge {Δ Θ : Seq σ Γ₀ S} {Δ' Θ' : Seq σ Γ₀ S'} (cs : CSetup Γ₀ τ k g S S')
    {σ' : Lab} {j j' : ℕ} (hv : Vacant S (j :: σ') Δ Θ)
    (hv' : Vacant S' (j' :: cmap τ k g σ') Δ' Θ') (e : EdgeKind)
    (hne : j :: σ' ≠ k :: τ) :
    CSetup Γ₀ τ k (setIdx g σ' j j') (S.addEdge (j :: σ') e)
      (S'.addEdge (j' :: cmap τ k g σ') (edgeImg τ k σ' e)) := by
  have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) (hv'.edge _ (List.suffix_refl _)) (edgeImg τ k σ' e)
  have hnew := cmap_setIdx_new (τ := τ) (k := k) g hne (j' := j')
  have hoff : ∀ ρ, ¬ (j :: σ') <:+ ρ → cmap τ k (setIdx g σ' j j') ρ = cmap τ k g ρ :=
    cmap_setIdx_off g
  have hcS : ¬ (j :: σ') <:+ (k :: τ) := fun h => cs.hc (hv.edge _ h)
  have hτ : ¬ (j :: σ') <:+ τ := fun h => hcS (h.trans (List.suffix_cons k τ))
  have hvac : ∀ c e₁, S'.edge (cmap τ k g c) = some e₁ →
      cmap τ k g c ≠ j' :: cmap τ k g σ' := fun c e₁ he₁ heq => by
    rw [heq, hv'.edge _ (List.suffix_refl _)] at he₁
    cases he₁
  refine ⟨cs.ok.addEdge (hv'.edge _ (List.suffix_refl _)) _, cs.hT, cs.hO, fun c e₁ he₁ hc₁ => ?_,
    fun j₁ ρ e₁ he₁ hu => ?_, fun x he => ?_, fun ρ b hb => ?_, fun ρ hρ o ho => ?_,
    fun ρ hρ o ho => ?_, cs.names, ?_⟩
  · rw [Tree.edge_addEdge] at he₁
    split_ifs at he₁ with hcj
    · cases he₁
      subst hcj
      have hσ : ¬ (k :: τ) <:+ σ' := fun h => hc₁ (h.trans (List.suffix_cons j σ'))
      refine ⟨e, ?_, .of_compat (EdgeKind.compat_refl' e)⟩
      rw [hnew, Tree.edge_addEdge, if_pos rfl]
      unfold edgeImg
      rw [if_neg hσ]
    · have hoffc : ¬ (j :: σ') <:+ c := fun hs => by rw [hv.edge c hs] at he₁; cases he₁
      obtain ⟨e', he', hf⟩ := cs.edge_off c e₁ he₁ hc₁
      rw [hoff c hoffc]
      refine ⟨e', ?_, hf.mono (hk _)⟩
      rw [Tree.edge_addEdge, if_neg (hvac c e' he')]
      exact he'
  · rw [Tree.edge_addEdge] at he₁
    split_ifs at he₁ with hcj
    · cases he₁
      obtain ⟨rfl, rfl⟩ := List.cons.inj hcj
      rw [hnew, Tree.edge_addEdge, if_pos rfl]
      unfold edgeImg
      rw [if_pos hu]
    · have hoffc : ¬ (j :: σ') <:+ (j₁ :: ρ) := fun hs => by
        rw [hv.edge _ hs] at he₁; cases he₁
      have he' := cs.edge_under j₁ ρ e₁ he₁ hu
      rw [hoff _ hoffc, Tree.edge_addEdge, if_neg (hvac _ _ he')]
      exact he'
  · rw [Tree.edge_addEdge, if_neg (fun h => hcS (by simp [h]))] at he
    rw [hoff τ hτ]
    exact (cs.edge_c x he).mono (hk _)
  · rw [hoff ρ (hv.births _ (Tree.mem_birthsAt.mp hb))]
    exact cs.birth ρ b hb
  · rw [hoff ρ (hv.not_opensAt ho)]
    exact (cs.opens_off ρ hρ o ho).mono (hk _)
  · rw [hoff ρ (hv.not_opensAt ho)]
    exact (cs.opens_under ρ hρ o ho).mono (hk _)
  · rw [Tree.edge_addEdge]
    split_ifs
    · exact Option.some_ne_none _
    · exact cs.hc

end CSetup


/-! ## Formulas at nodes, collapsed -/

theorem _root_.V12M.WFF.collapse_level {σ : Signature} {k k' : ℕ} {Γ₁ Γ₂ : Ctx} {d : ℕ}
    (e : k = k') (h : Ctx.Collapses k Γ₁ Γ₂) (h' : Ctx.Collapses k' Γ₁ Γ₂)
    (hs : Γ₁.SlotsFrom d) (φ : WFF σ Γ₁ d) : WFF.collapse h hs φ = WFF.collapse h' hs φ := by
  subst e
  rfl

/-- A witness, collapsed: of its collapsed opening's kind. -/
theorem _root_.V12M.Ctx.Collapses.witK_col {d : ℕ} {Γ₁ Γ₂ : Ctx} (C : Ctx.Collapses d Γ₁ Γ₂)
    {κ : WitKind} {y : VarSymb} {X : VarType} (hw : Γ₁.witK κ y = some X) :
    Γ₂.witK (colOpen d (κ, y)).1 (colOpen d (κ, y)).2 = some X := by
  cases κ with
  | arrow =>
      cases d with
      | zero => exact (C.wit y X hw).1 rfl
      | succ d => exact (C.wit y X hw).2 d rfl
  | ident => exact C.witT hw

/-- A witness's view, collapsed onto its collapsed opening's view. -/
theorem _root_.V12M.Ctx.Collapses.optInKC (hO : ModalSys.Opt = true) {d : ℕ} {Γ₁ Γ₂ : Ctx}
    (C : Ctx.Collapses d Γ₁ Γ₂) {κ : WitKind} {y : VarSymb} {X : VarType}
    (hw : Γ₁.witK κ y = some X) :
    Ctx.Collapses d (Γ₁.optInK κ y) (Γ₂.optInK (colOpen d (κ, y)).1 (colOpen d (κ, y)).2) := by
  cases κ with
  | arrow =>
      cases d with
      | zero => exact C.optIn_zero hO hw
      | succ d => exact C.optIn_succ hw
  | ident => exact C.optInT hw

/-- ⭐**An opened witness stays opened under a collapse**, as its collapsed opening. -/
theorem _root_.V12M.Ctx.Collapses.opened (hO : ModalSys.Opt = true) {d : ℕ} {Γ₁ Γ₂ : Ctx}
    (C : Ctx.Collapses d Γ₁ Γ₂) {κ : WitKind} {y : VarSymb} (h : Γ₁.Opened κ y) :
    Γ₂.Opened (colOpen d (κ, y)).1 (colOpen d (κ, y)).2 := by
  obtain ⟨X, hX, hXd⟩ := h
  refine ⟨X, C.witK_col hX, ?_⟩
  cases κ with
  | arrow =>
      have := C (.step y .dia) X ((Ctx.ref_nonproj _ rfl).trans hXd)
      cases d with
      | zero => rwa [VarSymb.collapse_dia_zero_opt hO, Ctx.ref_nonproj _ rfl] at this
      | succ d => rwa [VarSymb.collapse_level_succ rfl, Ctx.ref_nonproj _ rfl] at this
  | ident =>
      have := C (.step y .at) X ((Ctx.ref_nonproj _ rfl).trans hXd)
      rwa [VarSymb.collapse_at, Ctx.ref_nonproj _ rfl] at this

/-- Collapsing `◇⁰_y ψ` is `◇⁰` of the collapsed opening, of `ψ` collapsed onto its view. -/
theorem _root_.V12M.WFF.collapse_optx {σ : Signature} (hO : ModalSys.Opt = true) {d : ℕ}
    {Γ₁ Γ₂ : Ctx} (C : Ctx.Collapses d Γ₁ Γ₂) (hs : Γ₁.SlotsFrom 0) {κ : WitKind} {y : VarSymb}
    {X : VarType} (hw : Γ₁.witK κ y = some X) (hy : ∃ X, Γ₁.witK κ y = some X)
    (ψ : WFF σ (Γ₁.optInK κ y) 0) (hs' : (Γ₁.optInK κ y).SlotsFrom 0) :
    WFF.collapse C hs (.optx hO κ y hy ψ) = .optx hO (colOpen d (κ, y)).1 (colOpen d (κ, y)).2
      ⟨X, C.witK_col hw⟩ (WFF.collapse (C.optInKC hO hw) hs' ψ) := by
  cases κ with
  | arrow => cases d <;> rfl
  | ident => rfl

/-- Collapsing a fold one level in is folding the collapse. -/
theorem _root_.V12M.WFF.collapse_fold_succ {σ : Signature} (hO : ModalSys.Opt = true) {d : ℕ}
    {Γ₁ Γ₂ : Ctx} (C : Ctx.Collapses d Γ₁ Γ₂) (hs : Γ₁.SlotsFrom 0) (x : VarSymb)
    (hx : ∃ X, Γ₁.ref x = some (.VTypeDia X))
    (hx' : ∃ X, Γ₂.ref (x.collapse d) = some (.VTypeDia X)) (θ : WFF σ (Γ₁.diaIn x) 0) :
    WFF.collapse C.boxIn hs.boxIn (WFF.fold hO x hx θ) =
      WFF.fold hO (x.collapse d) hx' (WFF.collapse (C.diaIn x) (hs.diaIn x) θ) := by
  obtain ⟨X, hX⟩ := id hx
  unfold WFF.fold
  exact congrArg (WFF.optx hO .arrow (x.collapse d) _)
    (WFF.collapse_mono (C.diaIn x) (C.boxIn.optIn_succ (Ctx.boxIn_wit.mpr ⟨hO, hX⟩)) _ _ _ _ θ)

/-- ⭐A collapse of a weakening at a node is a weakening of a collapse, labels and levels
    agreeing. -/
theorem LF.col_eq {σ : Signature} {Γ₀ : Ctx} {D : Tree} {A A' B : Ctx} {d d' : ℕ} {a a' : Lab}
    (e : a = a') (ed : d = d') (h : Ctx.Collapses d A' (D.ctxAt Γ₀ a)) (hs : A'.SlotsFrom 0)
    (l : A.Le A') (h₀ : Ctx.Collapses d' A B) (hs₀ : A.SlotsFrom 0) (l' : B.Le (D.ctxAt Γ₀ a'))
    (φ : WFF σ A 0) :
    (⟨a, WFF.collapse h hs (WFF.mono l φ)⟩ : LF σ Γ₀ D) =
      ⟨a', WFF.mono l' (WFF.collapse h₀ hs₀ φ)⟩ := by
  subst e ed
  exact congrArg (Sigma.mk a) (WFF.collapse_mono h₀ h l l' hs₀ hs φ)

theorem off_cons {τ ν : Lab} {k i : ℕ} (hu : ¬ (k :: τ) <:+ ν) (hne : i :: ν ≠ k :: τ) :
    ¬ (k :: τ) <:+ (i :: ν) := fun h => by
  rcases List.suffix_cons_iff.mp h with h | h
  · exact hne h.symm
  · exact hu h

namespace CSetup

variable {σ : Signature} {Γ₀ : Ctx} {τ : Lab} {k : ℕ} {g : Lab → ℕ → ℕ} {S S' : Tree}

/-- ⭐**A formula at a node, into its image**: collapsed under `c`, weakened elsewhere. -/
noncomputable def F (cs : CSetup Γ₀ τ k g S S') (h0 : Γ₀.SlotsFrom 0) (hS : S.OK Γ₀)
    (hW : S.WitOK Γ₀) (ρ : Lab) (φ : WFF σ (S.ctxAt Γ₀ ρ) 0) :
    WFF σ (S'.ctxAt Γ₀ (cmap τ k g ρ)) 0 :=
  if h : (k :: τ) <:+ ρ then WFF.collapse ((cs.ctx hS hW ρ).2 h) (Tree.ctxAt_slots h0 hS ρ) φ
  else WFF.mono ((cs.ctx hS hW ρ).1 h) φ

/-- A formula at a node, collapsed onto its image. -/
noncomputable def lf (cs : CSetup Γ₀ τ k g S S') (h0 : Γ₀.SlotsFrom 0) (hS : S.OK Γ₀)
    (hW : S.WitOK Γ₀) (p : LF σ Γ₀ S) : LF σ Γ₀ S' :=
  ⟨cmap τ k g p.1, cs.F h0 hS hW p.1 p.2⟩

variable (cs : CSetup Γ₀ τ k g S S') (h0 : Γ₀.SlotsFrom 0) (hS : S.OK Γ₀) (hW : S.WitOK Γ₀)

theorem lf_mk (ρ : Lab) (φ : WFF σ (S.ctxAt Γ₀ ρ) 0) :
    cs.lf h0 hS hW ⟨ρ, φ⟩ = ⟨cmap τ k g ρ, cs.F h0 hS hW ρ φ⟩ := rfl

theorem mem_lf {L : Seq σ Γ₀ S} {ρ : Lab} {φ : WFF σ (S.ctxAt Γ₀ ρ) 0} (h : ⟨ρ, φ⟩ ∈ L) :
    (⟨cmap τ k g ρ, cs.F h0 hS hW ρ φ⟩ : LF σ Γ₀ S') ∈ L.map (cs.lf h0 hS hW) :=
  List.mem_map_of_mem (f := cs.lf h0 hS hW) h

theorem F_off {ρ : Lab} (hu : ¬ (k :: τ) <:+ ρ) (φ : WFF σ (S.ctxAt Γ₀ ρ) 0) :
    cs.F h0 hS hW ρ φ = WFF.mono ((cs.ctx hS hW ρ).1 hu) φ := dif_neg hu

theorem F_under {ρ : Lab} (hu : (k :: τ) <:+ ρ) (φ : WFF σ (S.ctxAt Γ₀ ρ) 0) :
    cs.F h0 hS hW ρ φ = WFF.collapse ((cs.ctx hS hW ρ).2 hu) (Tree.ctxAt_slots h0 hS ρ) φ :=
  dif_pos hu

theorem F_top (ρ : Lab) : cs.F h0 hS hW ρ (.top : WFF σ _ 0) = .top := by
  unfold F; split <;> rfl

theorem F_bot (ρ : Lab) : cs.F h0 hS hW ρ (.bot : WFF σ _ 0) = .bot := by
  unfold F; split <;> rfl

theorem F_and (ρ : Lab) (φ ψ : WFF σ (S.ctxAt Γ₀ ρ) 0) :
    cs.F h0 hS hW ρ (φ.and ψ) = (cs.F h0 hS hW ρ φ).and (cs.F h0 hS hW ρ ψ) := by
  unfold F; split <;> rfl

theorem F_or (ρ : Lab) (φ ψ : WFF σ (S.ctxAt Γ₀ ρ) 0) :
    cs.F h0 hS hW ρ (φ.or ψ) = (cs.F h0 hS hW ρ φ).or (cs.F h0 hS hW ρ ψ) := by
  unfold F; split <;> rfl

theorem F_imp (ρ : Lab) (φ ψ : WFF σ (S.ctxAt Γ₀ ρ) 0) :
    cs.F h0 hS hW ρ (φ.imp ψ) = (cs.F h0 hS hW ρ φ).imp (cs.F h0 hS hW ρ ψ) := by
  unfold F; split <;> rfl

theorem F_atom (ρ : Lab) {P : WFF σ (S.ctxAt Γ₀ ρ) 0} (hP : P.IsAtom) :
    (cs.F h0 hS hW ρ P).IsAtom := by
  unfold F
  split
  · exact hP.collapse
  · exact isAtom_mono hP

/-- ⭐**Growing both trees**: the images of a weakened side are the weakened images, where the
    label map agrees on its nodes. -/
theorem lf_mono_sub {g₂ : Lab → ℕ → ℕ} {S₂ S₂' : Tree} (cs₂ : CSetup Γ₀ τ k g₂ S₂ S₂')
    (hS₂ : S₂.OK Γ₀) (hW₂ : S₂.WitOK Γ₀) (hk : ∀ ρ, (S.ctxAt Γ₀ ρ).Le (S₂.ctxAt Γ₀ ρ))
    (hk' : ∀ ρ, (S'.ctxAt Γ₀ ρ).Le (S₂'.ctxAt Γ₀ ρ)) {L : Seq σ Γ₀ S} {L' : Seq σ Γ₀ S'}
    (hL : L.map (cs.lf h0 hS hW) ⊆ L') (hl : ∀ p ∈ L, cmap τ k g₂ p.1 = cmap τ k g p.1) :
    (Seq.mono hk L).map (cs₂.lf h0 hS₂ hW₂) ⊆ Seq.mono hk' L' := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  have hm := hL (List.mem_map_of_mem (f := cs.lf h0 hS hW) hp)
  have := List.mem_map_of_mem (f := fun p : LF σ Γ₀ S' =>
    (⟨p.1, WFF.mono (hk' p.1) p.2⟩ : LF σ Γ₀ S₂')) hm
  refine (congrArg (· ∈ Seq.mono hk' L') ?_).mpr this
  obtain ⟨ρ, φ⟩ := p
  change (⟨cmap τ k g₂ ρ, cs₂.F h0 hS₂ hW₂ ρ (WFF.mono (hk ρ) φ)⟩ : LF σ Γ₀ S₂') =
    ⟨cmap τ k g ρ, WFF.mono (hk' _) (cs.F h0 hS hW ρ φ)⟩
  by_cases hu : (k :: τ) <:+ ρ
  · rw [cs₂.F_under h0 hS₂ hW₂ hu, cs.F_under h0 hS hW hu]
    exact LF.col_eq (hl _ hp) rfl _ _ _ _ _ _ φ
  · rw [cs₂.F_off h0 hS₂ hW₂ hu, cs.F_off h0 hS hW hu]
    exact LF.mono_mono_eq φ (hl _ hp) _ _ _ _

end CSetup

open CSetup in
/-- ⭐**Collapsing a child onto its parent across a derivation** (docs §12.50 item (v)): a
    derivation over the source tree gives one over the target tree, of every formula's image. -/
theorem collapse {σ : Signature} {Γ₀ : Ctx} [Γ₀.Presented] (h0 : Γ₀.SlotsFrom 0) {n : ℕ}
    {D : Tree} {Δ Θ : Seq σ Γ₀ D} (p : GKN σ Γ₀ n D Δ Θ) :
    ∀ (hS : D.OK Γ₀) (hW : D.WitOK Γ₀) {τ : Lab} {k : ℕ} {g : Lab → ℕ → ℕ} {S' : Tree}
      (cs : CSetup Γ₀ τ k g D S') (Δ' Θ' : Seq σ Γ₀ S'),
      Δ.map (cs.lf h0 hS hW) ⊆ Δ' → Θ.map (cs.lf h0 hS hW) ⊆ Θ' → ∃ m, GKN σ Γ₀ m S' Δ' Θ' := by
  induction p with
  | ax ρ P hP h₁ h₂ =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      exact ⟨0, .ax _ _ (cs.F_atom h0 hS hW ρ hP) (hΔ (cs.mem_lf h0 hS hW h₁))
        (hΘ (cs.mem_lf h0 hS hW h₂))⟩
  | botL ρ h =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have := hΔ (cs.mem_lf h0 hS hW h)
      rw [cs.F_bot] at this
      exact ⟨0, .botL _ this⟩
  | topR ρ h =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have := hΘ (cs.mem_lf h0 hS hW h)
      rw [cs.F_top] at this
      exact ⟨0, .topR _ this⟩
  | @andL n D Δ Θ ρ φ ψ h _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have hm := hΔ (cs.mem_lf h0 hS hW h)
      rw [cs.F_and] at hm
      obtain ⟨m, d⟩ := ih hS hW cs (⟨_, cs.F h0 hS hW ρ φ⟩ :: ⟨_, cs.F h0 hS hW ρ ψ⟩ :: Δ') Θ'
        (List.cons_subset_cons _ (List.cons_subset_cons _ hΔ)) hΘ
      exact ⟨m + 1, .andL _ hm d⟩
  | @andR n D Δ Θ ρ φ ψ h _ _ ih₁ ih₂ =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have hm := hΘ (cs.mem_lf h0 hS hW h)
      rw [cs.F_and] at hm
      obtain ⟨m₁, d₁⟩ := ih₁ hS hW cs Δ' (⟨_, cs.F h0 hS hW ρ φ⟩ :: Θ') hΔ
        (List.cons_subset_cons _ hΘ)
      obtain ⟨m₂, d₂⟩ := ih₂ hS hW cs Δ' (⟨_, cs.F h0 hS hW ρ ψ⟩ :: Θ') hΔ
        (List.cons_subset_cons _ hΘ)
      exact ⟨max m₁ m₂ + 1, .andR _ hm (d₁.mono_height (le_max_left _ _))
        (d₂.mono_height (le_max_right _ _))⟩
  | @orL n D Δ Θ ρ φ ψ h _ _ ih₁ ih₂ =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have hm := hΔ (cs.mem_lf h0 hS hW h)
      rw [cs.F_or] at hm
      obtain ⟨m₁, d₁⟩ := ih₁ hS hW cs (⟨_, cs.F h0 hS hW ρ φ⟩ :: Δ') Θ'
        (List.cons_subset_cons _ hΔ) hΘ
      obtain ⟨m₂, d₂⟩ := ih₂ hS hW cs (⟨_, cs.F h0 hS hW ρ ψ⟩ :: Δ') Θ'
        (List.cons_subset_cons _ hΔ) hΘ
      exact ⟨max m₁ m₂ + 1, .orL _ hm (d₁.mono_height (le_max_left _ _))
        (d₂.mono_height (le_max_right _ _))⟩
  | @orR n D Δ Θ ρ φ ψ h _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have hm := hΘ (cs.mem_lf h0 hS hW h)
      rw [cs.F_or] at hm
      obtain ⟨m, d⟩ := ih hS hW cs Δ' (⟨_, cs.F h0 hS hW ρ φ⟩ :: ⟨_, cs.F h0 hS hW ρ ψ⟩ :: Θ')
        hΔ (List.cons_subset_cons _ (List.cons_subset_cons _ hΘ))
      exact ⟨m + 1, .orR _ hm d⟩
  | @impL n D Δ Θ ρ φ ψ h _ _ ih₁ ih₂ =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have hm := hΔ (cs.mem_lf h0 hS hW h)
      rw [cs.F_imp] at hm
      obtain ⟨m₁, d₁⟩ := ih₁ hS hW cs Δ' (⟨_, cs.F h0 hS hW ρ φ⟩ :: Θ') hΔ
        (List.cons_subset_cons _ hΘ)
      obtain ⟨m₂, d₂⟩ := ih₂ hS hW cs (⟨_, cs.F h0 hS hW ρ ψ⟩ :: Δ') Θ'
        (List.cons_subset_cons _ hΔ) hΘ
      exact ⟨max m₁ m₂ + 1, .impL _ hm (d₁.mono_height (le_max_left _ _))
        (d₂.mono_height (le_max_right _ _))⟩
  | @impR n D Δ Θ ρ φ ψ h _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have hm := hΘ (cs.mem_lf h0 hS hW h)
      rw [cs.F_imp] at hm
      obtain ⟨m, d⟩ := ih hS hW cs (⟨_, cs.F h0 hS hW ρ φ⟩ :: Δ') (⟨_, cs.F h0 hS hW ρ ψ⟩ :: Θ')
        (List.cons_subset_cons _ hΔ) (List.cons_subset_cons _ hΘ)
      exact ⟨m + 1, .impR _ hm d⟩
  | @allL n D Δ Θ ν hs T φ a t h _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have hs' := Tree.ctxAt_slots h0 cs.ok (cmap τ k g ν)
      have hm := hΔ (cs.mem_lf h0 hS hW h)
      by_cases hu : (k :: τ) <:+ ν
      · have C := (cs.ctx hS hW ν).2 hu
        haveI : (D.ctxAt Γ₀ ν).NoSlots := ⟨hs⟩
        haveI : (S'.ctxAt Γ₀ (cmap τ k g ν)).NoSlots := ⟨hs'⟩
        rw [cs.F_under h0 hS hW hu] at hm
        have e₁ := congrArg (Sigma.mk (β := fun ρ => WFF σ (S'.ctxAt Γ₀ ρ) 0) (cmap τ k g ν))
          (WFF.collapse_instantiate C t φ)
        rw [← cs.F_under h0 hS hW hu, ← cs.lf_mk] at e₁
        obtain ⟨m, d⟩ := ih hS hW cs _ Θ' (cons_sub e₁ hΔ) hΘ
        exact ⟨m + 1, .allL _ Ctx.NoSlots.slots T _ hm d⟩
      · have L := (cs.ctx hS hW ν).1 hu
        rw [cs.F_off h0 hS hW hu] at hm
        have e₁ : cs.lf h0 hS hW ⟨ν, WFF.instantiate hs t φ⟩ = ⟨cmap τ k g ν,
            WFF.instantiate hs' (Term.mono L t) (WFF.mono (L.insert (.bnd 0) T) φ)⟩ := by
          rw [cs.lf_mk, cs.F_off h0 hS hW hu]
          exact congrArg (Sigma.mk _) (WFF.mono_instantiate L hs hs' t _)
        obtain ⟨m, d⟩ := ih hS hW cs _ Θ' (cons_sub e₁ hΔ) hΘ
        exact ⟨m + 1, .allL _ hs' T _ hm d⟩
  | @exR n D Δ Θ ν hs T φ a t h _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have hs' := Tree.ctxAt_slots h0 cs.ok (cmap τ k g ν)
      have hm := hΘ (cs.mem_lf h0 hS hW h)
      by_cases hu : (k :: τ) <:+ ν
      · have C := (cs.ctx hS hW ν).2 hu
        haveI : (D.ctxAt Γ₀ ν).NoSlots := ⟨hs⟩
        haveI : (S'.ctxAt Γ₀ (cmap τ k g ν)).NoSlots := ⟨hs'⟩
        rw [cs.F_under h0 hS hW hu] at hm
        have e₁ := congrArg (Sigma.mk (β := fun ρ => WFF σ (S'.ctxAt Γ₀ ρ) 0) (cmap τ k g ν))
          (WFF.collapse_instantiate C t φ)
        rw [← cs.F_under h0 hS hW hu, ← cs.lf_mk] at e₁
        obtain ⟨m, d⟩ := ih hS hW cs Δ' _ hΔ (cons_sub e₁ hΘ)
        exact ⟨m + 1, .exR _ Ctx.NoSlots.slots T _ hm d⟩
      · have L := (cs.ctx hS hW ν).1 hu
        rw [cs.F_off h0 hS hW hu] at hm
        have e₁ : cs.lf h0 hS hW ⟨ν, WFF.instantiate hs t φ⟩ = ⟨cmap τ k g ν,
            WFF.instantiate hs' (Term.mono L t) (WFF.mono (L.insert (.bnd 0) T) φ)⟩ := by
          rw [cs.lf_mk, cs.F_off h0 hS hW hu]
          exact congrArg (Sigma.mk _) (WFF.mono_instantiate L hs hs' t _)
        obtain ⟨m, d⟩ := ih hS hW cs Δ' _ hΔ (cons_sub e₁ hΘ)
        exact ⟨m + 1, .exR _ hs' T _ hm d⟩
  | @ref n D Δ Θ ν t _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      by_cases hu : (k :: τ) <:+ ν
      · have C := (cs.ctx hS hW ν).2 hu
        have e₁ : cs.lf h0 hS hW ⟨ν, .eq t t⟩ =
            ⟨cmap τ k g ν, .eq (Term.collapse C t) (Term.collapse C t)⟩ := by
          rw [cs.lf_mk, cs.F_under h0 hS hW hu]
          rfl
        obtain ⟨m, d⟩ := ih hS hW cs _ Θ' (cons_sub e₁ hΔ) hΘ
        exact ⟨m + 1, .ref _ _ d⟩
      · have L := (cs.ctx hS hW ν).1 hu
        have e₁ : cs.lf h0 hS hW ⟨ν, .eq t t⟩ =
            ⟨cmap τ k g ν, .eq (Term.mono L t) (Term.mono L t)⟩ := by
          rw [cs.lf_mk, cs.F_off h0 hS hW hu]
          rfl
        obtain ⟨m, d⟩ := ih hS hW cs _ Θ' (cons_sub e₁ hΔ) hΘ
        exact ⟨m + 1, .ref _ _ d⟩
  | @repl n D Δ Θ ν hs P hP t s h₁ h₂ _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have hs' := Tree.ctxAt_slots h0 cs.ok (cmap τ k g ν)
      have hm₁ := hΔ (cs.mem_lf h0 hS hW h₁)
      have hm₂ := hΔ (cs.mem_lf h0 hS hW h₂)
      by_cases hu : (k :: τ) <:+ ν
      · have C := (cs.ctx hS hW ν).2 hu
        haveI : (D.ctxAt Γ₀ ν).NoSlots := ⟨hs⟩
        haveI : (S'.ctxAt Γ₀ (cmap τ k g ν)).NoSlots := ⟨hs'⟩
        rw [cs.F_under h0 hS hW hu] at hm₁ hm₂
        rw [WFF.collapse_instantiate C t P] at hm₂
        have e₁ := congrArg (Sigma.mk (β := fun ρ => WFF σ (S'.ctxAt Γ₀ ρ) 0) (cmap τ k g ν))
          (WFF.collapse_instantiate C s P)
        rw [← cs.F_under h0 hS hW hu, ← cs.lf_mk] at e₁
        obtain ⟨m, d⟩ := ih hS hW cs _ Θ' (cons_sub e₁ hΔ) hΘ
        exact ⟨m + 1, .repl _ Ctx.NoSlots.slots hP.collapse (Term.collapse C t)
          (Term.collapse C s) hm₁ hm₂ d⟩
      · have L := (cs.ctx hS hW ν).1 hu
        rw [cs.F_off h0 hS hW hu] at hm₁ hm₂
        rw [WFF.mono_instantiate L hs hs' t _] at hm₂
        have e₁ : cs.lf h0 hS hW ⟨ν, WFF.instantiate hs s P⟩ = ⟨cmap τ k g ν,
            WFF.instantiate hs' (Term.mono L s) (WFF.mono (L.insert (.bnd 0) .Var) P)⟩ := by
          rw [cs.lf_mk, cs.F_off h0 hS hW hu]
          exact congrArg (Sigma.mk _) (WFF.mono_instantiate L hs hs' s _)
        obtain ⟨m, d⟩ := ih hS hW cs _ Θ' (cons_sub e₁ hΔ) hΘ
        exact ⟨m + 1, .repl _ hs' (isAtom_mono (h := L.insert (.bnd 0) .Var) hP) (Term.mono L t)
          (Term.mono L s) hm₁ hm₂ d⟩
  | @allR n D Δ Θ ν hs u T hu φ hle h _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have hs' := Tree.ctxAt_slots h0 cs.ok (cmap τ k g ν)
      have hu' := cs.fresh hu
      have cs₂ := cs.addBirth hu ν T
      have hS₂ := hS.addBirth hu ν T
      have hW₂ := hW.addBirth hu ν T
      have hk := Tree.ctxAt_addBirth hu ν T
      have hk' := Tree.ctxAt_addBirth hu' (cmap τ k g ν) T
      have hle' := Tree.insert_le_addBirth hu' (cmap τ k g ν) T
      have hm := hΘ (cs.mem_lf h0 hS hW h)
      have hsub : ∀ {L : Seq σ Γ₀ D} {L' : Seq σ Γ₀ S'}, L.map (cs.lf h0 hS hW) ⊆ L' →
          (Seq.mono hk L).map (cs₂.lf h0 hS₂ hW₂) ⊆ Seq.mono hk' L' :=
        fun hL => cs.lf_mono_sub h0 hS hW cs₂ hS₂ hW₂ hk hk' hL fun _ _ => rfl
      by_cases hu₀ : (k :: τ) <:+ ν
      · have C := (cs.ctx hS hW ν).2 hu₀
        haveI : (D.ctxAt Γ₀ ν).NoSlots := ⟨hs⟩
        haveI : (S'.ctxAt Γ₀ (cmap τ k g ν)).NoSlots := ⟨hs'⟩
        rw [cs.F_under h0 hS hW hu₀] at hm
        have hm' : (⟨cmap τ k g ν, .all T (WFF.bindFree u (hu'.at _) Ctx.NoSlots.slots T
            (WFF.collapse (C.insert (hu.at ν) T) (hs.insertFree u T) φ))⟩ : LF σ Γ₀ S') ∈ Θ' := by
          rw [← WFF.collapse_bindFree C (hu.at ν) (hu'.at _) T φ]
          exact hm
        have e₁ : cs₂.lf h0 hS₂ hW₂ ⟨ν, WFF.mono hle φ⟩ = ⟨cmap τ k g ν, WFF.mono hle'
            (WFF.collapse (C.insert (hu.at ν) T) (hs.insertFree u T) φ)⟩ := by
          rw [cs₂.lf_mk, cs₂.F_under h0 hS₂ hW₂ hu₀]
          exact LF.col_eq rfl rfl _ _ _ _ _ _ φ
        obtain ⟨m, d⟩ := ih hS₂ hW₂ cs₂ _ _ (hsub hΔ) (cons_sub e₁ (hsub hΘ))
        exact ⟨m + 1, .allR _ hs' u T hu' hle' hm' d⟩
      · have L := (cs.ctx hS hW ν).1 hu₀
        rw [cs.F_off h0 hS hW hu₀] at hm
        have hm' : (⟨cmap τ k g ν, .all T (WFF.bindFree u (hu'.at _) hs' T
            (WFF.mono (L.insert (.free u) T) φ))⟩ : LF σ Γ₀ S') ∈ Θ' := by
          rw [← WFF.mono_bindFree L (hu.at ν) (hu'.at _) hs hs' T φ]
          exact hm
        have e₁ : cs₂.lf h0 hS₂ hW₂ ⟨ν, WFF.mono hle φ⟩ = ⟨cmap τ k g ν, WFF.mono hle'
            (WFF.mono (L.insert (.free u) T) φ)⟩ := by
          rw [cs₂.lf_mk, cs₂.F_off h0 hS₂ hW₂ hu₀]
          exact LF.mono_mono_eq φ rfl _ _ _ _
        obtain ⟨m, d⟩ := ih hS₂ hW₂ cs₂ _ _ (hsub hΔ) (cons_sub e₁ (hsub hΘ))
        exact ⟨m + 1, .allR _ hs' u T hu' hle' hm' d⟩
  | @exL n D Δ Θ ν hs u T hu φ hle h _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have hs' := Tree.ctxAt_slots h0 cs.ok (cmap τ k g ν)
      have hu' := cs.fresh hu
      have cs₂ := cs.addBirth hu ν T
      have hS₂ := hS.addBirth hu ν T
      have hW₂ := hW.addBirth hu ν T
      have hk := Tree.ctxAt_addBirth hu ν T
      have hk' := Tree.ctxAt_addBirth hu' (cmap τ k g ν) T
      have hle' := Tree.insert_le_addBirth hu' (cmap τ k g ν) T
      have hm := hΔ (cs.mem_lf h0 hS hW h)
      have hsub : ∀ {L : Seq σ Γ₀ D} {L' : Seq σ Γ₀ S'}, L.map (cs.lf h0 hS hW) ⊆ L' →
          (Seq.mono hk L).map (cs₂.lf h0 hS₂ hW₂) ⊆ Seq.mono hk' L' :=
        fun hL => cs.lf_mono_sub h0 hS hW cs₂ hS₂ hW₂ hk hk' hL fun _ _ => rfl
      by_cases hu₀ : (k :: τ) <:+ ν
      · have C := (cs.ctx hS hW ν).2 hu₀
        haveI : (D.ctxAt Γ₀ ν).NoSlots := ⟨hs⟩
        haveI : (S'.ctxAt Γ₀ (cmap τ k g ν)).NoSlots := ⟨hs'⟩
        rw [cs.F_under h0 hS hW hu₀] at hm
        have hm' : (⟨cmap τ k g ν, .ex T (WFF.bindFree u (hu'.at _) Ctx.NoSlots.slots T
            (WFF.collapse (C.insert (hu.at ν) T) (hs.insertFree u T) φ))⟩ : LF σ Γ₀ S') ∈ Δ' := by
          rw [← WFF.collapse_bindFree C (hu.at ν) (hu'.at _) T φ]
          exact hm
        have e₁ : cs₂.lf h0 hS₂ hW₂ ⟨ν, WFF.mono hle φ⟩ = ⟨cmap τ k g ν, WFF.mono hle'
            (WFF.collapse (C.insert (hu.at ν) T) (hs.insertFree u T) φ)⟩ := by
          rw [cs₂.lf_mk, cs₂.F_under h0 hS₂ hW₂ hu₀]
          exact LF.col_eq rfl rfl _ _ _ _ _ _ φ
        obtain ⟨m, d⟩ := ih hS₂ hW₂ cs₂ _ _ (cons_sub e₁ (hsub hΔ)) (hsub hΘ)
        exact ⟨m + 1, .exL _ hs' u T hu' hle' hm' d⟩
      · have L := (cs.ctx hS hW ν).1 hu₀
        rw [cs.F_off h0 hS hW hu₀] at hm
        have hm' : (⟨cmap τ k g ν, .ex T (WFF.bindFree u (hu'.at _) hs' T
            (WFF.mono (L.insert (.free u) T) φ))⟩ : LF σ Γ₀ S') ∈ Δ' := by
          rw [← WFF.mono_bindFree L (hu.at ν) (hu'.at _) hs hs' T φ]
          exact hm
        have e₁ : cs₂.lf h0 hS₂ hW₂ ⟨ν, WFF.mono hle φ⟩ = ⟨cmap τ k g ν, WFF.mono hle'
            (WFF.mono (L.insert (.free u) T) φ)⟩ := by
          rw [cs₂.lf_mk, cs₂.F_off h0 hS₂ hW₂ hu₀]
          exact LF.mono_mono_eq φ rfl _ _ _ _
        obtain ⟨m, d⟩ := ih hS₂ hW₂ cs₂ _ _ (cons_sub e₁ (hsub hΔ)) (hsub hΘ)
        exact ⟨m + 1, .exL _ hs' u T hu' hle' hm' d⟩
  | @boxR n D Δ Θ ν i φ hv hle h _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      obtain ⟨i', hv'⟩ := exists_vacant (cmap τ k g ν) S' Δ' Θ'
      have hnone := hv.edge _ (List.suffix_refl _)
      have hnone' := hv'.edge _ (List.suffix_refl _)
      have hne : i :: ν ≠ k :: τ := fun e => cs.hc (e ▸ hnone)
      have cs₂ := cs.addEdge hv hv' .box hne
      have eI : edgeImg τ k ν .box = .box := by unfold edgeImg; split <;> rfl
      rw [eI] at cs₂
      have hS₂ := hS.addEdge hnone .box
      have hW₂ := hW.addEdge hnone .box fun _ _ _ _ he => by cases he
      have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hnone EdgeKind.box
      have hk' := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hnone' EdgeKind.box
      have hle' := Tree.boxIn_le_addEdge (Γ₀ := Γ₀) hnone' hv'.birthsAt hv'.opensAt
      have hsub : ∀ {L : Seq σ Γ₀ D} {L' : Seq σ Γ₀ S'}, (∀ p ∈ L, ¬ (i :: ν) <:+ p.1) →
          L.map (cs.lf h0 hS hW) ⊆ L' →
          (Seq.mono hk L).map (cs₂.lf h0 hS₂ hW₂) ⊆ Seq.mono hk' L' :=
        fun hL hL' => cs.lf_mono_sub h0 hS hW cs₂ hS₂ hW₂ hk hk' hL'
          fun p hp => cmap_setIdx_off g p.1 (hL p hp)
      have hm := hΘ (cs.mem_lf h0 hS hW h)
      by_cases hu : (k :: τ) <:+ ν
      · have C := (cs.ctx hS hW ν).2 hu
        rw [cs.F_under h0 hS hW hu] at hm
        have e₁ : cs₂.lf h0 hS₂ hW₂ ⟨i :: ν, WFF.mono hle φ⟩ = ⟨i' :: cmap τ k g ν,
            WFF.mono hle' (WFF.collapse C.boxIn (Tree.ctxAt_slots h0 hS ν).boxIn φ)⟩ := by
          rw [cs₂.lf_mk, cs₂.F_under h0 hS₂ hW₂ (hu.trans (List.suffix_cons i ν))]
          exact LF.col_eq (cmap_setIdx_new g hne) (cdepth_cons hu i) _ _ _ _ _ _ φ
        obtain ⟨m, d⟩ := ih hS₂ hW₂ cs₂ _ _ (hsub hv.left hΔ) (cons_sub e₁ (hsub hv.right hΘ))
        exact ⟨m + 1, .boxR _ i' hv' hle' hm d⟩
      · have L := (cs.ctx hS hW ν).1 hu
        rw [cs.F_off h0 hS hW hu] at hm
        have e₁ : cs₂.lf h0 hS₂ hW₂ ⟨i :: ν, WFF.mono hle φ⟩ = ⟨i' :: cmap τ k g ν,
            WFF.mono hle' (WFF.mono L.boxIn φ)⟩ := by
          rw [cs₂.lf_mk, cs₂.F_off h0 hS₂ hW₂ (off_cons hu hne)]
          exact LF.mono_mono_eq φ (cmap_setIdx_new g hne) _ _ _ _
        obtain ⟨m, d⟩ := ih hS₂ hW₂ cs₂ _ _ (hsub hv.left hΔ) (cons_sub e₁ (hsub hv.right hΘ))
        exact ⟨m + 1, .boxR _ i' hv' hle' hm d⟩
  | @serial n D Δ Θ hD ν i hv _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      obtain ⟨i', hv'⟩ := exists_vacant (cmap τ k g ν) S' Δ' Θ'
      have hnone := hv.edge _ (List.suffix_refl _)
      have hnone' := hv'.edge _ (List.suffix_refl _)
      have hne : i :: ν ≠ k :: τ := fun e => cs.hc (e ▸ hnone)
      have cs₂ := cs.addEdge hv hv' .box hne
      have eI : edgeImg τ k ν .box = .box := by unfold edgeImg; split <;> rfl
      rw [eI] at cs₂
      have hS₂ := hS.addEdge hnone .box
      have hW₂ := hW.addEdge hnone .box fun _ _ _ _ he => by cases he
      have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hnone EdgeKind.box
      have hk' := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hnone' EdgeKind.box
      obtain ⟨m, d⟩ := ih hS₂ hW₂ cs₂ _ _
        (cs.lf_mono_sub h0 hS hW cs₂ hS₂ hW₂ hk hk' hΔ
          fun p hp => cmap_setIdx_off g p.1 (hv.left p hp))
        (cs.lf_mono_sub h0 hS hW cs₂ hS₂ hW₂ hk hk' hΘ
          fun p hp => cmap_setIdx_off g p.1 (hv.right p hp))
      exact ⟨m + 1, .serial hD _ i' hv' d⟩
  | @diaL n D Δ Θ ν i x hx ψ hv hle h _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      obtain ⟨i', hv'⟩ := exists_vacant (cmap τ k g ν) S' Δ' Θ'
      have hnone := hv.edge _ (List.suffix_refl _)
      have hnone' := hv'.edge _ (List.suffix_refl _)
      have hne : i :: ν ≠ k :: τ := fun e => cs.hc (e ▸ hnone)
      have hS₂ := hS.addEdge hnone (.dia x)
      have hW₂ := hW.addEdge hnone (.dia x) fun j ρ y hj he => by
        cases hj
        cases he
        exact hx
      have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hnone (EdgeKind.dia x)
      have hm := hΔ (cs.mem_lf h0 hS hW h)
      by_cases hu : (k :: τ) <:+ ν
      · have C := (cs.ctx hS hW ν).2 hu
        have cs₂ := cs.addEdge hv hv' (.dia x) hne
        have eI : edgeImg τ k ν (.dia x) = .dia (x.collapse (cdepth τ ν)) := by
          unfold edgeImg
          rw [if_pos hu]
          rfl
        rw [eI] at cs₂
        have hk' := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hnone' (EdgeKind.dia (x.collapse (cdepth τ ν)))
        have hle' := Tree.diaIn_le_addEdge (Γ₀ := Γ₀) hnone' hv'.birthsAt hv'.opensAt
          (x.collapse (cdepth τ ν))
        rw [cs.F_under h0 hS hW hu] at hm
        have e₁ : cs₂.lf h0 hS₂ hW₂ ⟨i :: ν, WFF.mono hle ψ⟩ = ⟨i' :: cmap τ k g ν,
            WFF.mono hle' (WFF.collapse (C.diaIn x) ((Tree.ctxAt_slots h0 hS ν).diaIn x) ψ)⟩ := by
          rw [cs₂.lf_mk, cs₂.F_under h0 hS₂ hW₂ (hu.trans (List.suffix_cons i ν))]
          exact LF.col_eq (cmap_setIdx_new g hne) (cdepth_cons hu i) _ _ _ _ _ _ ψ
        obtain ⟨m, d⟩ := ih hS₂ hW₂ cs₂ _ _
          (cons_sub e₁ (cs.lf_mono_sub h0 hS hW cs₂ hS₂ hW₂ hk hk' hΔ
            fun p hp => cmap_setIdx_off g p.1 (hv.left p hp)))
          (cs.lf_mono_sub h0 hS hW cs₂ hS₂ hW₂ hk hk' hΘ
            fun p hp => cmap_setIdx_off g p.1 (hv.right p hp))
        exact ⟨m + 1, .diaL _ i' _ _ hv' hle' hm d⟩
      · have L := (cs.ctx hS hW ν).1 hu
        have cs₂ := cs.addEdge hv hv' (.dia x) hne
        have eI : edgeImg τ k ν (.dia x) = .dia x := by
          unfold edgeImg
          rw [if_neg hu]
        rw [eI] at cs₂
        have hk' := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hnone' (EdgeKind.dia x)
        have hle' := Tree.diaIn_le_addEdge (Γ₀ := Γ₀) hnone' hv'.birthsAt hv'.opensAt x
        rw [cs.F_off h0 hS hW hu] at hm
        have e₁ : cs₂.lf h0 hS₂ hW₂ ⟨i :: ν, WFF.mono hle ψ⟩ = ⟨i' :: cmap τ k g ν,
            WFF.mono hle' (WFF.mono (L.diaIn x) ψ)⟩ := by
          rw [cs₂.lf_mk, cs₂.F_off h0 hS₂ hW₂ (off_cons hu hne)]
          exact LF.mono_mono_eq ψ (cmap_setIdx_new g hne) _ _ _ _
        obtain ⟨m, d⟩ := ih hS₂ hW₂ cs₂ _ _
          (cons_sub e₁ (cs.lf_mono_sub h0 hS hW cs₂ hS₂ hW₂ hk hk' hΔ
            fun p hp => cmap_setIdx_off g p.1 (hv.left p hp)))
          (cs.lf_mono_sub h0 hS hW cs₂ hS₂ hW₂ hk hk' hΘ
            fun p hp => cmap_setIdx_off g p.1 (hv.right p hp))
        exact ⟨m + 1, .diaL _ i' _ _ hv' hle' hm d⟩
  | @boxL n D Δ Θ ν i e χ he hle h _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have hm := hΔ (cs.mem_lf h0 hS hW h)
      by_cases hc' : i :: ν = k :: τ
      · obtain ⟨hik, hντ⟩ := List.cons.inj hc'
        subst k
        subst τ
        have hoff : ¬ (i :: ν) <:+ ν := Tree.not_suffix_cons i ν
        have L := (cs.ctx hS hW ν).1 hoff
        have hs := Tree.ctxAt_slots h0 hS ν
        have hs' := Tree.ctxAt_slots h0 cs.ok (cmap ν i g ν)
        rw [cs.F_off h0 hS hW hoff] at hm
        have e₁ : cs.lf h0 hS hW ⟨i :: ν, WFF.mono hle χ⟩ = ⟨cmap ν i g ν,
            WFF.collapse (Ctx.collapses_boxIn_self cs.hT _) hs'.boxIn (WFF.mono L.boxIn χ)⟩ := by
          rw [cs.lf_mk, cs.F_under h0 hS hW (List.suffix_refl _)]
          exact (LF.col_eq (cmap_c ν i g) (cdepth_c ν i) _ _ hle
            (Ctx.collapses_boxIn_self cs.hT _) hs.boxIn L χ).trans
            (LF.col_eq rfl rfl _ _ L.boxIn (Ctx.collapses_boxIn_self cs.hT _) hs.boxIn L χ).symm
        obtain ⟨m, d⟩ := ih hS hW cs _ Θ' (cons_sub e₁ hΔ) hΘ
        exact ⟨m + 1, .TL cs.hT _ hs' hm d⟩
      · have hle' := Tree.boxIn_le_child cs.ok (g ν i) (cmap τ k g ν)
        by_cases hu : (k :: τ) <:+ ν
        · have C := (cs.ctx hS hW ν).2 hu
          have he' := cs.edge_under i ν e he hu
          rw [cmap_cons (ne_c_of_under hu i)] at he'
          rw [cs.F_under h0 hS hW hu] at hm
          have e₁ : cs.lf h0 hS hW ⟨i :: ν, WFF.mono hle χ⟩ = ⟨g ν i :: cmap τ k g ν,
              WFF.mono hle' (WFF.collapse C.boxIn (Tree.ctxAt_slots h0 hS ν).boxIn χ)⟩ := by
            rw [cs.lf_mk, cs.F_under h0 hS hW (hu.trans (List.suffix_cons i ν))]
            exact LF.col_eq (cmap_cons (ne_c_of_under hu i)) (cdepth_cons hu i) _ _ _ _ _ _ χ
          obtain ⟨m, d⟩ := ih hS hW cs _ Θ' (cons_sub e₁ hΔ) hΘ
          exact ⟨m + 1, .boxL _ (g ν i) _ he' hle' hm d⟩
        · have L := (cs.ctx hS hW ν).1 hu
          have hoff := off_cons hu hc'
          obtain ⟨e', he', -⟩ := cs.edge_off _ e he hoff
          rw [cmap_cons hc'] at he'
          rw [cs.F_off h0 hS hW hu] at hm
          have e₁ : cs.lf h0 hS hW ⟨i :: ν, WFF.mono hle χ⟩ = ⟨g ν i :: cmap τ k g ν,
              WFF.mono hle' (WFF.mono L.boxIn χ)⟩ := by
            rw [cs.lf_mk, cs.F_off h0 hS hW hoff]
            exact LF.mono_mono_eq χ (cmap_cons hc') _ _ _ _
          obtain ⟨m, d⟩ := ih hS hW cs _ Θ' (cons_sub e₁ hΔ) hΘ
          exact ⟨m + 1, .boxL _ (g ν i) e' he' hle' hm d⟩
  | @diaR n D Δ Θ ν i e x hx θ he hf hle h _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have hm := hΘ (cs.mem_lf h0 hS hW h)
      by_cases hc' : i :: ν = k :: τ
      · obtain ⟨hik, hντ⟩ := List.cons.inj hc'
        subst k
        subst τ
        have hoff : ¬ (i :: ν) <:+ ν := Tree.not_suffix_cons i ν
        have L := (cs.ctx hS hW ν).1 hoff
        have hs := Tree.ctxAt_slots h0 hS ν
        have hs' := Tree.ctxAt_slots h0 cs.ok (cmap ν i g ν)
        obtain ⟨X, hX⟩ := id hx
        have hY : (S'.ctxAt Γ₀ (cmap ν i g ν)).ref x = some (.VTypeDia X) := L.ref hX
        have Cc : Ctx.Collapses 0 (D.ctxAt Γ₀ (i :: ν)) (S'.ctxAt Γ₀ (cmap ν i g ν)) := by
          have := (cs.ctx hS hW (i :: ν)).2 (List.suffix_refl _)
          rwa [cmap_c, cdepth_c] at this
        have hop : (S'.ctxAt Γ₀ (cmap ν i g ν)).Opened .ident x := by
          rcases hf with hf | ⟨x', hx', ho⟩
          · cases e with
            | box => exact hf.elim
            | dia z =>
                change x = z at hf
                subst hf
                exact cs.edge_c x he
          · cases hx'
            exact Cc.opened cs.hO ho
        have l₂ : ((D.ctxAt Γ₀ ν).optInT x).Le (S'.ctxAt Γ₀ (cmap ν i g ν)) :=
          Ctx.optInK_le_of (κ := .ident) L hop
        have h₀ := Ctx.collapses_diaIn_optInT cs.hT cs.hO (D.ctxAt Γ₀ ν) hX
        have h₀' := Ctx.collapses_diaIn_optInT cs.hT cs.hO (S'.ctxAt Γ₀ (cmap ν i g ν)) hY
        rw [cs.F_off h0 hS hW hoff] at hm
        have e₁ : cs.lf h0 hS hW ⟨i :: ν, WFF.mono hle θ⟩ =
            ⟨cmap ν i g ν, WFF.mono l₂ (WFF.collapse h₀ (hs.diaIn x) θ)⟩ := by
          rw [cs.lf_mk, cs.F_under h0 hS hW (List.suffix_refl _)]
          exact LF.col_eq (cmap_c ν i g) (cdepth_c ν i) _ _ _ _ _ _ θ
        obtain ⟨m, d⟩ := ih hS hW cs Δ' (_ :: ⟨cmap ν i g ν, WFF.optx cs.hO .ident x
            ⟨X, Ctx.witT_of cs.hT cs.hO hY⟩
            (WFF.collapse h₀' (hs'.diaIn x) (WFF.mono (L.diaIn x) θ))⟩ :: Θ') hΔ
          (cons_sub e₁ (List.subset_cons_of_subset _ hΘ))
        have hmψ : (⟨cmap ν i g ν, WFF.optx cs.hO .ident x (hop.imp fun _ h => h.1)
            (WFF.mono (Ctx.le_optInK _ .ident x) (WFF.mono l₂ (WFF.collapse h₀ (hs.diaIn x) θ)))⟩ :
              LF σ Γ₀ S') ∈ ⟨cmap ν i g ν, WFF.optx cs.hO .ident x
                ⟨X, Ctx.witT_of cs.hT cs.hO hY⟩
                (WFF.collapse h₀' (hs'.diaIn x) (WFF.mono (L.diaIn x) θ))⟩ :: Θ' := by
          have E : WFF.mono (Ctx.le_optInK _ .ident x) (WFF.mono l₂
              (WFF.collapse h₀ (hs.diaIn x) θ)) =
              WFF.collapse h₀' (hs'.diaIn x) (WFF.mono (L.diaIn x) θ) := by
            rw [WFF.mono_mono, WFF.collapse_mono h₀ h₀' (L.diaIn x) (L.optInT x) _ _ θ]
          rw [E]
          exact List.mem_cons_self
        exact ⟨m + 2, .diaT cs.hT cs.hO _ hs' x ⟨X, hY⟩ hm (.reopenR cs.hO _ .ident x hop hmψ d)⟩
      · by_cases hu : (k :: τ) <:+ ν
        · have C := (cs.ctx hS hW ν).2 hu
          have hu₁ := hu.trans (List.suffix_cons i ν)
          have C₁ : Ctx.Collapses (cdepth τ ν + 1) (D.ctxAt Γ₀ (i :: ν))
              (S'.ctxAt Γ₀ (g ν i :: cmap τ k g ν)) := by
            have := (cs.ctx hS hW (i :: ν)).2 hu₁
            rwa [cmap_cons (ne_c_of_under hu i), cdepth_cons hu i] at this
          have he' := cs.edge_under i ν e he hu
          rw [cmap_cons (ne_c_of_under hu i)] at he'
          have hf' : (EdgeKind.dia (x.collapse (cdepth τ ν))).Fits
              (S'.ctxAt Γ₀ (g ν i :: cmap τ k g ν)) (e.col (cdepth τ ν)) := by
            rcases hf with hf | ⟨x', hx', ho⟩
            · cases e with
              | box => exact hf.elim
              | dia z =>
                  change x = z at hf
                  subst hf
                  exact .inl rfl
            · cases hx'
              exact .inr ⟨_, rfl, C₁.opened cs.hO ho⟩
          have hle' := Tree.diaIn_le_fit cs.ok he' hf'
          rw [cs.F_under h0 hS hW hu] at hm
          have e₁ : cs.lf h0 hS hW ⟨i :: ν, WFF.mono hle θ⟩ = ⟨g ν i :: cmap τ k g ν,
              WFF.mono hle' (WFF.collapse (C.diaIn x) ((Tree.ctxAt_slots h0 hS ν).diaIn x) θ)⟩ := by
            rw [cs.lf_mk, cs.F_under h0 hS hW hu₁]
            exact LF.col_eq (cmap_cons (ne_c_of_under hu i)) (cdepth_cons hu i) _ _ _ _ _ _ θ
          obtain ⟨m, d⟩ := ih hS hW cs Δ' _ hΔ (cons_sub e₁ hΘ)
          exact ⟨m + 1, .diaR _ (g ν i) _ _ _ he' hf' hle' hm d⟩
        · have L := (cs.ctx hS hW ν).1 hu
          have hoff := off_cons hu hc'
          have L₁ := (cs.ctx hS hW (i :: ν)).1 hoff
          obtain ⟨e', he', hc₁⟩ := cs.edge_off _ e he hoff
          have hf' : (EdgeKind.dia x).Fits (S'.ctxAt Γ₀ (cmap τ k g (i :: ν))) e' := by
            rcases hf with hf | ⟨x', hx', ho⟩
            · cases e with
              | box => exact hf.elim
              | dia z =>
                  change x = z at hf
                  subst hf
                  exact hc₁
            · cases hx'
              exact .inr ⟨x, rfl, ho.mono L₁⟩
          rw [cmap_cons hc'] at he' hf'
          have hle' := Tree.diaIn_le_fit cs.ok he' hf'
          rw [cs.F_off h0 hS hW hu] at hm
          have e₁ : cs.lf h0 hS hW ⟨i :: ν, WFF.mono hle θ⟩ = ⟨g ν i :: cmap τ k g ν,
              WFF.mono hle' (WFF.mono (L.diaIn x) θ)⟩ := by
            rw [cs.lf_mk, cs.F_off h0 hS hW hoff]
            exact LF.mono_mono_eq θ (cmap_cons hc') _ _ _ _
          obtain ⟨m, d⟩ := ih hS hW cs Δ' _ hΔ (cons_sub e₁ hΘ)
          exact ⟨m + 1, .diaR _ (g ν i) e' x _ he' hf' hle' hm d⟩
  | @foldR n D Δ Θ hO' ν i e x hx θ he hle h _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have hm := hΘ (cs.mem_lf h0 hS hW h)
      by_cases hc' : i :: ν = k :: τ
      · obtain ⟨hik, hντ⟩ := List.cons.inj hc'
        subst k
        subst τ
        have hoff : ¬ (i :: ν) <:+ ν := Tree.not_suffix_cons i ν
        have L := (cs.ctx hS hW ν).1 hoff
        have hs := Tree.ctxAt_slots h0 hS ν
        have hs' := Tree.ctxAt_slots h0 cs.ok (cmap ν i g ν)
        haveI : (D.ctxAt Γ₀ ν).NoSlots := ⟨hs⟩
        obtain ⟨X, hX⟩ := id hx
        have hY : (S'.ctxAt Γ₀ (cmap ν i g ν)).ref x = some (.VTypeDia X) := L.ref hX
        have h₀ := Ctx.collapses_diaIn_optInT cs.hT cs.hO (D.ctxAt Γ₀ ν) hX
        have h₀' := Ctx.collapses_diaIn_optInT cs.hT cs.hO (S'.ctxAt Γ₀ (cmap ν i g ν)) hY
        rw [cs.F_off h0 hS hW hoff] at hm
        have e₁ : cs.lf h0 hS hW ⟨i :: ν, WFF.mono hle (WFF.fold hO' x hx θ)⟩ =
            ⟨cmap ν i g ν, WFF.optx cs.hO .ident x ⟨X, Ctx.witT_of cs.hT cs.hO hY⟩
              (WFF.collapse h₀' (hs'.diaIn x) (WFF.mono (L.diaIn x) θ))⟩ := by
          rw [cs.lf_mk, cs.F_under h0 hS hW (List.suffix_refl _)]
          refine (LF.col_eq (cmap_c ν i g) (cdepth_c ν i) _ _ hle
            (Ctx.collapses_boxIn_self cs.hT _) hs.boxIn L _).trans ?_
          refine (congrArg (fun φ => (⟨cmap ν i g ν, WFF.mono L φ⟩ : LF σ Γ₀ S'))
            (WFF.collapse_fold cs.hT hO' x hx θ)).trans ?_
          exact congrArg (Sigma.mk _) (congrArg (WFF.optx cs.hO .ident x _)
            (WFF.collapse_mono h₀ h₀' (L.diaIn x) (L.optInT x) _ _ θ).symm)
        obtain ⟨m, d⟩ := ih hS hW cs Δ' _ hΔ (cons_sub e₁ hΘ)
        exact ⟨m + 1, .diaT cs.hT cs.hO _ hs' x ⟨X, hY⟩ hm d⟩
      · have hle' := Tree.boxIn_le_child cs.ok (g ν i) (cmap τ k g ν)
        by_cases hu : (k :: τ) <:+ ν
        · have C := (cs.ctx hS hW ν).2 hu
          have hs := Tree.ctxAt_slots h0 hS ν
          have hx' : ∃ X, (S'.ctxAt Γ₀ (cmap τ k g ν)).ref (x.collapse (cdepth τ ν)) =
              some (.VTypeDia X) := hx.imp fun _ hX => C x _ hX
          have he' := cs.edge_under i ν e he hu
          rw [cmap_cons (ne_c_of_under hu i)] at he'
          rw [cs.F_under h0 hS hW hu] at hm
          have e₁ : cs.lf h0 hS hW ⟨i :: ν, WFF.mono hle (WFF.fold hO' x hx θ)⟩ =
              ⟨g ν i :: cmap τ k g ν, WFF.mono hle'
                (WFF.fold hO' (x.collapse (cdepth τ ν)) hx'
                  (WFF.collapse (C.diaIn x) (hs.diaIn x) θ))⟩ := by
            rw [cs.lf_mk, cs.F_under h0 hS hW (hu.trans (List.suffix_cons i ν)),
              ← WFF.collapse_fold_succ hO' C hs x hx hx' θ]
            exact LF.col_eq (cmap_cons (ne_c_of_under hu i)) (cdepth_cons hu i) _ _ _ _ _ _ _
          obtain ⟨m, d⟩ := ih hS hW cs Δ' _ hΔ (cons_sub e₁ hΘ)
          exact ⟨m + 1, .foldR hO' _ (g ν i) _ _ _ he' hle' hm d⟩
        · have L := (cs.ctx hS hW ν).1 hu
          have hoff := off_cons hu hc'
          have hx' : ∃ X, (S'.ctxAt Γ₀ (cmap τ k g ν)).ref x = some (.VTypeDia X) :=
            hx.imp fun _ hX => L.ref hX
          obtain ⟨e', he', -⟩ := cs.edge_off _ e he hoff
          rw [cmap_cons hc'] at he'
          rw [cs.F_off h0 hS hW hu] at hm
          have e₁ : cs.lf h0 hS hW ⟨i :: ν, WFF.mono hle (WFF.fold hO' x hx θ)⟩ =
              ⟨g ν i :: cmap τ k g ν,
                WFF.mono hle' (WFF.fold hO' x hx' (WFF.mono (L.diaIn x) θ))⟩ := by
            rw [cs.lf_mk, cs.F_off h0 hS hW hoff, WFF.fold_mono hO' L x hx hx']
            exact LF.mono_mono_eq _ (cmap_cons hc') _ _ _ _
          obtain ⟨m, d⟩ := ih hS hW cs Δ' _ hΔ (cons_sub e₁ hΘ)
          exact ⟨m + 1, .foldR hO' _ (g ν i) e' x hx' he' hle' hm d⟩
  | @optL n D Δ Θ hO' ν κ y hy ψ hle h _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      obtain ⟨X, hX⟩ := id hy
      have hS₂ := hS.addOpen hO' hX
      have hW₂ : (D.addOpen ν κ y).WitOK Γ₀ := fun a ρ z he =>
        (hW a ρ z he).imp fun _ h' => (Tree.ctxAt_addOpen ν κ y ρ).ref h'
      have hk := Tree.ctxAt_addOpen (D := D) (Γ₀ := Γ₀) ν κ y
      have hm := hΔ (cs.mem_lf h0 hS hW h)
      have hs := Tree.ctxAt_slots h0 hS ν
      by_cases hu : (k :: τ) <:+ ν
      · have C := (cs.ctx hS hW ν).2 hu
        have cs₂ := cs.addOpen hS hW hX
        have eo : openImg τ k ν (κ, y) = colOpen (cdepth τ ν) (κ, y) := if_pos hu
        rw [eo] at cs₂
        have hk' := Tree.ctxAt_addOpen (D := S') (Γ₀ := Γ₀) (cmap τ k g ν)
          (colOpen (cdepth τ ν) (κ, y)).1 (colOpen (cdepth τ ν) (κ, y)).2
        have hle' : ((S'.ctxAt Γ₀ (cmap τ k g ν)).optInK (colOpen (cdepth τ ν) (κ, y)).1
            (colOpen (cdepth τ ν) (κ, y)).2).Le ((S'.addOpen (cmap τ k g ν)
              (colOpen (cdepth τ ν) (κ, y)).1 (colOpen (cdepth τ ν) (κ, y)).2).ctxAt Γ₀
                (cmap τ k g ν)) := by
          rw [Tree.ctxAt_addOpen_self]
          exact Ctx.Le.refl _
        rw [cs.F_under h0 hS hW hu, WFF.collapse_optx hO' C hs hX hy ψ (hs.optInK κ y)] at hm
        have e₁ : cs₂.lf h0 hS₂ hW₂ ⟨ν, WFF.mono hle ψ⟩ = ⟨cmap τ k g ν,
            WFF.mono hle' (WFF.collapse (C.optInKC hO' hX) (hs.optInK κ y) ψ)⟩ := by
          rw [cs₂.lf_mk, cs₂.F_under h0 hS₂ hW₂ hu]
          exact LF.col_eq rfl rfl _ _ _ _ _ _ ψ
        obtain ⟨m, d⟩ := ih hS₂ hW₂ cs₂ _ _
          (cons_sub e₁ (cs.lf_mono_sub h0 hS hW cs₂ hS₂ hW₂ hk hk' hΔ fun _ _ => rfl))
          (cs.lf_mono_sub h0 hS hW cs₂ hS₂ hW₂ hk hk' hΘ fun _ _ => rfl)
        exact ⟨m + 1, .optL hO' _ _ _ ⟨X, C.witK_col hX⟩ hle' hm d⟩
      · have L := (cs.ctx hS hW ν).1 hu
        have cs₂ := cs.addOpen hS hW hX
        have eo : openImg τ k ν (κ, y) = (κ, y) := if_neg hu
        rw [eo] at cs₂
        have hk' := Tree.ctxAt_addOpen (D := S') (Γ₀ := Γ₀) (cmap τ k g ν) κ y
        have hle' : ((S'.ctxAt Γ₀ (cmap τ k g ν)).optInK κ y).Le
            ((S'.addOpen (cmap τ k g ν) κ y).ctxAt Γ₀ (cmap τ k g ν)) := by
          rw [Tree.ctxAt_addOpen_self]
          exact Ctx.Le.refl _
        rw [cs.F_off h0 hS hW hu] at hm
        have e₁ : cs₂.lf h0 hS₂ hW₂ ⟨ν, WFF.mono hle ψ⟩ = ⟨cmap τ k g ν,
            WFF.mono hle' (WFF.mono (L.optInK κ y) ψ)⟩ := by
          rw [cs₂.lf_mk, cs₂.F_off h0 hS₂ hW₂ hu]
          exact LF.mono_mono_eq ψ rfl _ _ _ _
        obtain ⟨m, d⟩ := ih hS₂ hW₂ cs₂ _ _
          (cons_sub e₁ (cs.lf_mono_sub h0 hS hW cs₂ hS₂ hW₂ hk hk' hΔ fun _ _ => rfl))
          (cs.lf_mono_sub h0 hS hW cs₂ hS₂ hW₂ hk hk' hΘ fun _ _ => rfl)
        exact ⟨m + 1, .optL hO' _ κ y ⟨X, L.witK hX⟩ hle' hm d⟩
  | @reopenR n D Δ Θ hO' ν κ y hy χ h _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have hm := hΘ (cs.mem_lf h0 hS hW h)
      have hs := Tree.ctxAt_slots h0 hS ν
      obtain ⟨X, hX, -⟩ := id hy
      by_cases hu : (k :: τ) <:+ ν
      · have C := (cs.ctx hS hW ν).2 hu
        have hop := C.opened hO' hy
        rw [cs.F_under h0 hS hW hu, WFF.collapse_optx hO' C hs hX _ _ (hs.optInK κ y),
          WFF.collapse_mono C (C.optInKC hO' hX) (Ctx.le_optInK _ κ y) (Ctx.le_optInK _ _ _) hs
            (hs.optInK κ y) χ] at hm
        have e₁ : cs.lf h0 hS hW ⟨ν, χ⟩ = ⟨cmap τ k g ν, WFF.collapse C hs χ⟩ := by
          rw [cs.lf_mk, cs.F_under h0 hS hW hu]
        obtain ⟨m, d⟩ := ih hS hW cs Δ' _ hΔ (cons_sub e₁ hΘ)
        exact ⟨m + 1, .reopenR hO' _ _ _ hop hm d⟩
      · have L := (cs.ctx hS hW ν).1 hu
        have hy' := hy.mono L
        rw [cs.F_off h0 hS hW hu] at hm
        have hm' : (⟨cmap τ k g ν, .optx hO' κ y (hy'.imp fun _ h => h.1)
            (WFF.mono (Ctx.le_optInK _ κ y) (WFF.mono L χ))⟩ : LF σ Γ₀ S') ∈ Θ' := by
          refine (congrArg (· ∈ Θ') (congrArg (Sigma.mk _) ?_)).mp hm
          change WFF.optx hO' κ y _ (WFF.mono (L.optInK κ y) (WFF.mono _ _)) = _
          rw [WFF.mono_mono, WFF.mono_mono]
        have e₁ : cs.lf h0 hS hW ⟨ν, χ⟩ = ⟨cmap τ k g ν, WFF.mono L χ⟩ := by
          rw [cs.lf_mk, cs.F_off h0 hS hW hu]
        obtain ⟨m, d⟩ := ih hS hW cs Δ' _ hΔ (cons_sub e₁ hΘ)
        exact ⟨m + 1, .reopenR hO' _ κ y hy' hm' d⟩
  | @TL n D Δ Θ hT ν hs φ h _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have hs' := Tree.ctxAt_slots h0 cs.ok (cmap τ k g ν)
      have hm := hΔ (cs.mem_lf h0 hS hW h)
      by_cases hu : (k :: τ) <:+ ν
      · have C := (cs.ctx hS hW ν).2 hu
        rw [cs.F_under h0 hS hW hu] at hm
        have e₁ : cs.lf h0 hS hW ⟨ν, WFF.collapse (Ctx.collapses_boxIn_self hT _) hs.boxIn φ⟩ =
            ⟨cmap τ k g ν, WFF.collapse (Ctx.collapses_boxIn_self hT _) hs'.boxIn
              (WFF.collapse C.boxIn hs.boxIn φ)⟩ := by
          rw [cs.lf_mk, cs.F_under h0 hS hW hu]
          exact congrArg (Sigma.mk _) (WFF.collapse_collapse cs.hO (k := cdepth τ ν) (m := 0)
            C.boxIn (Ctx.collapses_boxIn_self hT _) (Ctx.collapses_boxIn_self hT _) C hs.boxIn
            hs'.boxIn hs φ).symm
        obtain ⟨m, d⟩ := ih hS hW cs _ Θ' (cons_sub e₁ hΔ) hΘ
        exact ⟨m + 1, .TL hT _ hs' hm d⟩
      · have L := (cs.ctx hS hW ν).1 hu
        rw [cs.F_off h0 hS hW hu] at hm
        have e₁ : cs.lf h0 hS hW ⟨ν, WFF.collapse (Ctx.collapses_boxIn_self hT _) hs.boxIn φ⟩ =
            ⟨cmap τ k g ν, WFF.collapse (Ctx.collapses_boxIn_self hT _) hs'.boxIn
              (WFF.mono L.boxIn φ)⟩ := by
          rw [cs.lf_mk, cs.F_off h0 hS hW hu]
          exact congrArg (Sigma.mk _) (WFF.collapse_mono _ _ L.boxIn L _ _ φ).symm
        obtain ⟨m, d⟩ := ih hS hW cs _ Θ' (cons_sub e₁ hΔ) hΘ
        exact ⟨m + 1, .TL hT _ hs' hm d⟩
  | @diaT n D Δ Θ hT hO' ν hs x hx φ h _ ih =>
      intro hS hW τ k g S' cs Δ' Θ' hΔ hΘ
      have hs' := Tree.ctxAt_slots h0 cs.ok (cmap τ k g ν)
      have hm := hΘ (cs.mem_lf h0 hS hW h)
      obtain ⟨X, hX⟩ := id hx
      by_cases hu : (k :: τ) <:+ ν
      · have C := (cs.ctx hS hW ν).2 hu
        have hY : (S'.ctxAt Γ₀ (cmap τ k g ν)).ref (x.collapse (cdepth τ ν)) =
            some (.VTypeDia X) := C x _ hX
        rw [cs.F_under h0 hS hW hu] at hm
        have e₁ : cs.lf h0 hS hW ⟨ν, WFF.optx hO' .ident x (hx.imp fun _ h => Ctx.witT_of hT hO' h)
            (WFF.collapse (hx.elim fun _ h => Ctx.collapses_diaIn_optInT hT hO' _ h) (hs.diaIn x)
              φ)⟩ = ⟨cmap τ k g ν, WFF.optx hO' .ident (x.collapse (cdepth τ ν))
                ⟨X, Ctx.witT_of hT hO' hY⟩
                (WFF.collapse (Ctx.collapses_diaIn_optInT hT hO' _ hY) (hs'.diaIn _)
                  (WFF.collapse (C.diaIn x) (hs.diaIn x) φ))⟩ := by
          rw [cs.lf_mk, cs.F_under h0 hS hW hu]
          exact congrArg (Sigma.mk _) (congrArg (WFF.optx hO' .ident _ _)
            (WFF.collapse_collapse hO' (k := cdepth τ ν) (m := 0) (C.diaIn x)
              (Ctx.collapses_diaIn_optInT hT hO' _ hY) (Ctx.collapses_diaIn_optInT hT hO' _ hX)
              (C.optInT (Ctx.witT_of hT hO' hX)) (hs.diaIn x) (hs'.diaIn _) (hs.optInT x)
              φ).symm)
        obtain ⟨m, d⟩ := ih hS hW cs Δ' _ hΔ (cons_sub e₁ hΘ)
        exact ⟨m + 1, .diaT hT hO' _ hs' (x.collapse _) ⟨X, hY⟩ hm d⟩
      · have L := (cs.ctx hS hW ν).1 hu
        have hY : (S'.ctxAt Γ₀ (cmap τ k g ν)).ref x = some (.VTypeDia X) := L.ref hX
        rw [cs.F_off h0 hS hW hu] at hm
        have e₁ : cs.lf h0 hS hW ⟨ν, WFF.optx hO' .ident x (hx.imp fun _ h => Ctx.witT_of hT hO' h)
            (WFF.collapse (hx.elim fun _ h => Ctx.collapses_diaIn_optInT hT hO' _ h) (hs.diaIn x)
              φ)⟩ = ⟨cmap τ k g ν, WFF.optx hO' .ident x ⟨X, Ctx.witT_of hT hO' hY⟩
                (WFF.collapse (Ctx.collapses_diaIn_optInT hT hO' _ hY) (hs'.diaIn _)
                  (WFF.mono (L.diaIn x) φ))⟩ := by
          rw [cs.lf_mk, cs.F_off h0 hS hW hu]
          exact congrArg (Sigma.mk _) (congrArg (WFF.optx hO' .ident x _)
            (WFF.collapse_mono _ _ (L.diaIn x) (L.optInT x) _ _ φ).symm)
        obtain ⟨m, d⟩ := ih hS hW cs Δ' _ hΔ (cons_sub e₁ hΘ)
        exact ⟨m + 1, .diaT hT hO' _ hs' x ⟨X, hY⟩ hm d⟩

/-! ## A fresh child collapsed: T's principal cuts -/

theorem cmap_idIdx_off {τ : Lab} {k : ℕ} : ∀ ρ, ¬ (k :: τ) <:+ ρ → cmap τ k idIdx ρ = ρ
  | [], _ => rfl
  | i :: ρ, h => by
      have hρ : ¬ (k :: τ) <:+ ρ := fun h' => h (h'.trans (List.suffix_cons i ρ))
      have hne : i :: ρ ≠ k :: τ := fun e => h (e ▸ List.suffix_refl _)
      rw [cmap_cons hne, cmap_idIdx_off ρ hρ]
      rfl

theorem cmap_idIdx_c (τ : Lab) (k : ℕ) : cmap τ k idIdx (k :: τ) = τ := by
  rw [cmap_c, cmap_idIdx_off τ (Tree.not_suffix_cons k τ)]

theorem Seq.mono_self {σ : Signature} {Γ₀ : Ctx} {D : Tree}
    (h : ∀ ρ, (D.ctxAt Γ₀ ρ).Le (D.ctxAt Γ₀ ρ)) (L : Seq σ Γ₀ D) : Seq.mono h L = L := by
  unfold Seq.mono
  conv_rhs => rw [← List.map_id L]
  refine List.map_congr_left fun p _ => ?_
  obtain ⟨ρ, φ⟩ := p
  exact congrArg (Sigma.mk ρ) (WFF.mono_refl _ φ)

namespace CSetup

variable {σ : Signature} {Γ₀ : Ctx} {τ : Lab} {k : ℕ}

/-- ⭐**Collapsing a fresh child** (T's principal cuts): a tree with a vacant child `c` added, onto
    a tree with the same edges and births, as large node by node, where `c`'s `◇_x` (if it is
    one) is opened at `τ`. -/
theorem ofEdge {D S' : Tree} (hok : D.OK Γ₀) (hT : ModalSys.T = true) (hO : ModalSys.Opt = true)
    {Δ Θ : Seq σ Γ₀ D} (hv : Vacant D (k :: τ) Δ Θ) (e : EdgeKind) (hS' : S'.OK Γ₀)
    (hk : ∀ ρ, (D.ctxAt Γ₀ ρ).Le (S'.ctxAt Γ₀ ρ)) (hedge : ∀ c, S'.edge c = D.edge c)
    (hbirth : ∀ ρ b, b ∈ D.birthsAt ρ → b ∈ S'.birthsAt ρ)
    (hnames : ∀ b ∈ S'.births, b ∈ D.births)
    (he : ∀ x, e = .dia x → (S'.ctxAt Γ₀ τ).Opened .ident x) :
    CSetup Γ₀ τ k idIdx (D.addEdge (k :: τ) e) S' := by
  have hc := hv.edge _ (List.suffix_refl _)
  refine ⟨hS', hT, hO, fun c e' he' hc' => ?_, fun j ρ e' he' hu => ?_, fun x hx => ?_,
    fun ρ b hb => ?_, fun ρ hρ o ho => ?_, fun ρ hρ o ho => ?_,
    fun b hb => ⟨b, hnames b hb, rfl⟩, ?_⟩
  · have hne : c ≠ k :: τ := fun h => hc' (h ▸ List.suffix_refl _)
    rw [Tree.edge_addEdge, if_neg hne] at he'
    refine ⟨e', ?_, .of_compat (EdgeKind.compat_refl' e')⟩
    rw [cmap_idIdx_off c hc', hedge, he']
  · rw [Tree.edge_addEdge, if_neg (ne_c_of_under hu j),
      hv.edge _ (hu.trans (List.suffix_cons j ρ))] at he'
    cases he'
  · rw [Tree.edge_addEdge, if_pos rfl] at hx
    cases hx
    rw [cmap_idIdx_off τ (Tree.not_suffix_cons k τ)]
    exact he x rfl
  · have hρ : ¬ (k :: τ) <:+ ρ := hv.births _ (Tree.mem_birthsAt.mp hb)
    rw [cmap_idIdx_off ρ hρ]
    exact hbirth ρ b hb
  · rw [cmap_idIdx_off ρ hρ]
    exact (hok.opened ρ o ho).mono (hk ρ)
  · exact absurd hρ (hv.not_opensAt ho)
  · rw [Tree.edge_addEdge, if_pos rfl]
    exact Option.some_ne_none _

/-- Images of a side off `c`, weakened into the source and collapsed into a target whose labels
    are the source's, are the side weakened into the target. -/
theorem map_mono_off {S S' D : Tree} (cs : CSetup Γ₀ τ k idIdx S S') (h0 : Γ₀.SlotsFrom 0)
    (hS : S.OK Γ₀) (hW : S.WitOK Γ₀) (hk : ∀ ρ, (D.ctxAt Γ₀ ρ).Le (S.ctxAt Γ₀ ρ))
    (hk' : ∀ ρ, (D.ctxAt Γ₀ ρ).Le (S'.ctxAt Γ₀ ρ)) {L : Seq σ Γ₀ D}
    (hL : ∀ p ∈ L, ¬ (k :: τ) <:+ p.1) :
    (Seq.mono hk L).map (cs.lf h0 hS hW) ⊆ Seq.mono hk' L := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  have hm := List.mem_map_of_mem (f := fun p : LF σ Γ₀ D =>
    (⟨p.1, WFF.mono (hk' p.1) p.2⟩ : LF σ Γ₀ S')) hp
  obtain ⟨ρ, φ⟩ := p
  change (⟨cmap τ k idIdx ρ, cs.F h0 hS hW ρ (WFF.mono (hk ρ) φ)⟩ : LF σ Γ₀ S') ∈ _
  rw [cs.F_off h0 hS hW (hL _ hp), WFF.mono_mono,
    LF.mono_eq φ (cmap_idIdx_off ρ (hL _ hp)) _ (hk' ρ)]
  exact hm

end CSetup

end GKN

end V12M
