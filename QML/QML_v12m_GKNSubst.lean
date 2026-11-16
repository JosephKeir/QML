import QML.QML_v12m_GKNEmbed

/-!
# QML v12m — `GKN`: substitution across the tree

A **tree substitution** sends a derivation over a source tree to one over a target tree, a
substitution per node (docs §12.49, "tree substitution").  As `GK.subst`, every eigenvariable is
renamed to a name fresh for the target, so the target may have births the source lacks (at nodes
carrying a formula, so that vacant children stay vacant).

* `SubSetup Γ₀ S S' ι E N`: the source `S`, the target `S'`, one index map `ι`, the entry `E ρ r`
  of each root `r` born at `ρ` (a renaming, or a term), and the nodes `N` of the target's extra
  births.  The target's edges are the source's with witnesses renamed by `ι`.
* ⭐`SubSetup.Fam`: the family, by recursion on the node (the edge's view of the parent's, and the
  node's roots by `E`); `okCoh`: a substitution at every node; `fam_box`, `fam_dia`: along an
  edge, the parent's view; `fam_agree`: as the tree grows, the smaller tree's, weakened.
* ⭐`GKN.subst`: **tree substitution**, height-preserving, each rule to itself.
* ⭐Instances: `GKN.weakenBirth` (a new birth at a populated node); `GKN.instance_allR`,
  `GKN.instance_exL` (cut's quantifier instances: the eigenvariable unbound by a term).  They take
  `Tree.WitOK` (every `◇`-edge's witness declared at its parent), kept by every rule.

With `Opt` and T off.
-/

namespace V12M

set_option linter.unusedSectionVars false

variable [ModalSys]

/-- Every root by `er`, everything else by `θ`. -/
def Subst.rootsRen {σ : Signature} {Δ : Ctx} (θ : Subst σ Δ) (er : Root → SubE σ Δ) :
    Subst σ Δ where
  ty v := match v with
    | .root r => er r
    | .step w s => θ.ty (.step w s)
  wit := θ.wit

namespace GKN

variable {σ : Signature}

/-- An edge with its witness renamed. -/
def EdgeKind.ren (ι : VarSymb → VarSymb) : EdgeKind → EdgeKind
  | .box => .box
  | .dia x => .dia (ι x)

theorem EdgeKind.ren_id : ∀ e : EdgeKind, e.ren id = e
  | .box => rfl
  | .dia _ => rfl

/-- A declaration of an inserted context comes from the list or from the context. -/
theorem _root_.V12M.Ctx.inserts_cases {Γ : Ctx} :
    ∀ {L : List (Root × VarType)} {v : VarSymb} {T : VarType}, (Γ.inserts L) v = some T →
      (∃ b ∈ L, v = .root b.1 ∧ T = b.2) ∨ Γ v = some T
  | [], _, _, h => Or.inr h
  | b :: L, v, T, h => by
      change ((Γ.inserts L).insert b.1 b.2) v = some T at h
      simp only [Ctx.insert] at h
      split_ifs at h with h₁ h₂
      · cases h
        exact Or.inl ⟨b, List.mem_cons_self, h₁, rfl⟩
      · rcases Ctx.inserts_cases h with ⟨b', hb', he⟩ | h'
        · exact Or.inl ⟨b', List.mem_cons_of_mem _ hb', he⟩
        · exact Or.inr h'

/-- ⭐**The setup of a substitution across the tree**: the target's edges are the source's with
    witnesses renamed by `ι`; each root `r` born at `ρ` goes to `E ρ r`, coherently with `ι`; `ι`
    fixes what no birth roots; the target's births are at the source's nodes or in `N`. -/
structure SubSetup (Γ₀ : Ctx) (S S' : Tree) (ι : VarSymb → VarSymb)
    (E : (ρ : Lab) → Root → SubE σ (S'.ctxAt Γ₀ ρ)) (N : List Lab) : Prop where
  okS : S.OK Γ₀
  ok : S'.OK Γ₀
  h0 : Γ₀.SlotsFrom 0
  edge : ∀ k ρ, S'.edge (k :: ρ) = (S.edge (k :: ρ)).map (EdgeKind.ren ι)
  wit : ∀ k ρ x, S.edge (k :: ρ) = some (.dia x) →
    ∃ X, (S.ctxAt Γ₀ ρ).ref x = some (.VTypeDia X)
  eok : ∀ ρ b, b ∈ S.birthsAt ρ → (E ρ b.1).OkRef b.2
  eidx : ∀ ρ b p, b ∈ S.birthsAt ρ → (E ρ b.1).idxAlong p = ι ((VarSymb.root b.1).ext p)
  fix : ∀ v : VarSymb, (∀ b ∈ S.births, b.2.1 ≠ v.rt) → ι v = v
  births : ∀ b ∈ S'.births, (∃ b₀ ∈ S.births, b₀.1 = b.1) ∨ b.1 ∈ N

variable {Γ₀ : Ctx} {S S' : Tree} {ι : VarSymb → VarSymb}
  {E : (ρ : Lab) → Root → SubE σ (S'.ctxAt Γ₀ ρ)} {N : List Lab}

theorem SubSetup.edge_dia (hs : SubSetup Γ₀ S S' ι E N) {k : ℕ} {ρ : Lab} {x : VarSymb}
    (he : S.edge (k :: ρ) = some (.dia x)) : S'.edge (k :: ρ) = some (.dia (ι x)) := by
  rw [hs.edge k ρ, he]
  rfl

theorem SubSetup.edge_none (hs : SubSetup Γ₀ S S' ι E N) {k : ℕ} {ρ : Lab}
    (he : S.edge (k :: ρ) = none) : S'.edge (k :: ρ) = none := by
  rw [hs.edge k ρ, he]
  rfl

open Classical in
/-- The entry at a root of a node: `E` at a birth, the root itself otherwise. -/
noncomputable def SubSetup.rootE (_hs : SubSetup Γ₀ S S' ι E N) (ρ : Lab) (r : Root) :
    SubE σ (S'.ctxAt Γ₀ ρ) :=
  if ∃ U, (r, U) ∈ S.birthsAt ρ then E ρ r else .ren (.root r)

theorem SubSetup.rootE_born (hs : SubSetup Γ₀ S S' ι E N) {ρ : Lab} {r : Root}
    (h : ∃ U, (r, U) ∈ S.birthsAt ρ) : hs.rootE ρ r = E ρ r := if_pos h

theorem SubSetup.rootE_not (hs : SubSetup Γ₀ S S' ι E N) {ρ : Lab} {r : Root}
    (h : ¬ ∃ U, (r, U) ∈ S.birthsAt ρ) : hs.rootE ρ r = .ren (.root r) := if_neg h

/-- The edge's view of the parent's substitution, weakened into the child's target context. -/
noncomputable def SubSetup.viewS (hs : SubSetup Γ₀ S S' ι E N) (k : ℕ) (ρ : Lab)
    (θ : Subst σ (S'.ctxAt Γ₀ ρ)) : Subst σ (S'.ctxAt Γ₀ (k :: ρ)) :=
  match S.edge (k :: ρ) with
  | some (.dia x) =>
      match he' : S'.edge (k :: ρ) with
      | some (.dia y) => (θ.dia x y).mono (Tree.diaIn_le_child hs.ok he')
      | _ => θ.box.mono (Tree.boxIn_le_child hs.ok k ρ)
  | _ => θ.box.mono (Tree.boxIn_le_child hs.ok k ρ)

/-- ⭐**The family**: at each node, the edge's view of the parent's, and the node's roots by
    `rootE`. -/
noncomputable def SubSetup.Fam (hs : SubSetup Γ₀ S S' ι E N) :
    (ρ : Lab) → Subst σ (S'.ctxAt Γ₀ ρ)
  | [] => (Subst.idRen _).rootsRen (hs.rootE [])
  | k :: ρ => (hs.viewS k ρ (hs.Fam ρ)).rootsRen (hs.rootE (k :: ρ))

theorem SubSetup.viewS_dia (hs : SubSetup Γ₀ S S' ι E N) {k : ℕ} {ρ : Lab} {x y : VarSymb}
    (he : S.edge (k :: ρ) = some (.dia x)) (he' : S'.edge (k :: ρ) = some (.dia y))
    (θ : Subst σ (S'.ctxAt Γ₀ ρ)) :
    hs.viewS k ρ θ = (θ.dia x y).mono (Tree.diaIn_le_child hs.ok he') := by
  unfold SubSetup.viewS
  split
  · rename_i x' he₁
    rw [he] at he₁
    cases he₁
    split
    · rename_i y' he₁'
      rw [he'] at he₁'
      cases he₁'
      rfl
    · rename_i hnd
      exact absurd he' (hnd y)
  · rename_i hnd
    exact absurd he (hnd x)

theorem SubSetup.viewS_box (hs : SubSetup Γ₀ S S' ι E N) {k : ℕ} {ρ : Lab}
    (h : ∀ x, S.edge (k :: ρ) ≠ some (.dia x)) (θ : Subst σ (S'.ctxAt Γ₀ ρ)) :
    hs.viewS k ρ θ = θ.box.mono (Tree.boxIn_le_child hs.ok k ρ) := by
  unfold SubSetup.viewS
  split
  · rename_i x he₁
    exact absurd he₁ (h x)
  · rfl

theorem SubSetup.fam_root (hs : SubSetup Γ₀ S S' ι E N) (ρ : Lab) (r : Root) :
    hs.Fam ρ (.root r) = hs.rootE ρ r := by
  cases ρ <;> rfl

theorem SubSetup.fam_step (hs : SubSetup Γ₀ S S' ι E N) (k : ℕ) (ρ : Lab) (w : VarSymb)
    (s : Step) : hs.Fam (k :: ρ) (.step w s) = hs.viewS k ρ (hs.Fam ρ) (.step w s) := rfl

end GKN

/-! ## The family is a substitution at every node -/

namespace GKN

variable {σ : Signature} {Γ₀ : Ctx} {S S' : Tree} {ι : VarSymb → VarSymb}
  {E : (ρ : Lab) → Root → SubE σ (S'.ctxAt Γ₀ ρ)} {N : List Lab}

variable [ModalSys.NoOpt]

theorem Tree.view_of_not_dia {D : Tree} {σ' : Lab} {Γ : Ctx}
    (h : ∀ x, D.edge σ' ≠ some (.dia x)) : D.view σ' Γ = Γ.boxIn := by
  cases he : D.edge σ' with
  | none => exact Tree.view_box (Or.inl he)
  | some e =>
      cases e with
      | box => exact Tree.view_box (Or.inr he)
      | dia x => exact absurd he (h x)

/-- `ι` fixes the addresses of the end sequent's context. -/
theorem SubSetup.fix0 (hs : SubSetup Γ₀ S S' ι E N) {v : VarSymb} {U : VarType}
    (hv : Γ₀ v = some U) (p : List Step) : ι (v.ext p) = v.ext p := by
  refine hs.fix _ fun b hb he => ?_
  rw [VarSymb.ext_rt] at he
  rw [(hs.okS.fresh b hb).ty v he.symm] at hv
  cases hv

/-- A root of the end sequent's context is born nowhere. -/
theorem SubSetup.not_born0 (hs : SubSetup Γ₀ S S' ι E N) {r : Root} {U : VarType}
    (hv : Γ₀ (.root r) = some U) : ¬ ∃ U', (r, U') ∈ S.birthsAt [] := by
  rintro ⟨U', hb⟩
  rw [(hs.okS.fresh _ (Tree.mem_birthsAt.mp hb)).root] at hv
  cases hv

/-- ⭐**The family is a substitution at every node**, with the index map `ι`. -/
theorem SubSetup.okCoh (hs : SubSetup Γ₀ S S' ι E N) :
    ∀ ρ, Subst.Ok (S.ctxAt Γ₀ ρ) (hs.Fam ρ) ∧ Subst.Coh ι (S.ctxAt Γ₀ ρ) (hs.Fam ρ)
  | [] => by
      have hle : Γ₀.Le (S'.ctxAt Γ₀ []) := by
        simp only [Tree.ctxAt]
        exact Ctx.le_inserts _ (Tree.birthsAt_pairwise hs.ok _)
          fun b hb => hs.ok.fresh _ (Tree.mem_birthsAt.mp hb)
      have hok : Subst.Ok (S.ctxAt Γ₀ []) (hs.Fam []) := by
        refine ⟨fun v U hlp hv => ?_, fun hO => absurd hO (by rw [ModalSys.NoOpt.noOpt]; decide)⟩
        simp only [Tree.ctxAt] at hv
        rcases Ctx.inserts_cases hv with ⟨b, hb, rfl, rfl⟩ | hv
        · change (hs.rootE [] b.1).OkRef b.2
          rw [hs.rootE_born ⟨b.2, hb⟩]
          exact hs.eok [] b hb
        · cases v with
          | root r =>
              change (hs.rootE [] r).OkRef U
              rw [hs.rootE_not (hs.not_born0 hv)]
              change (S'.ctxAt Γ₀ []).ref (.root r) = some U
              rw [Ctx.ref_nonproj _ rfl]
              exact hle _ _ hv
          | step w s =>
              change (S'.ctxAt Γ₀ []).ref (.step w s) = some U
              rw [Ctx.ref_nonproj _ hlp]
              exact hle _ _ hv
      refine ⟨hok, Subst.coh_of hok (fun v U hlp hv p => ?_)⟩
      simp only [Tree.ctxAt] at hv
      rcases Ctx.inserts_cases hv with ⟨b, hb, rfl, rfl⟩ | hv
      · change (hs.rootE [] b.1).idxAlong p = _
        rw [hs.rootE_born ⟨b.2, hb⟩]
        exact hs.eidx [] b p hb
      · rw [hs.fix0 hv p]
        cases v with
        | root r =>
            change (hs.rootE [] r).idxAlong p = _
            rw [hs.rootE_not (hs.not_born0 hv)]
            rfl
        | step w s => rfl
  | k :: ρ => by
      obtain ⟨ih₁, ih₂⟩ := hs.okCoh ρ
      have hview : ∀ v U, v.lastProj = false → (S.view (k :: ρ) (S.ctxAt Γ₀ ρ)) v = some U →
          (hs.viewS k ρ (hs.Fam ρ) v).OkRef U ∧
            ∀ p, (hs.viewS k ρ (hs.Fam ρ) v).idxAlong p = ι (v.ext p) := by
        intro v U hlp hv
        by_cases hd : ∃ x, S.edge (k :: ρ) = some (.dia x)
        · obtain ⟨x, he⟩ := hd
          rw [hs.viewS_dia he (hs.edge_dia he)]
          rw [Tree.view_dia he] at hv
          have hx := hs.wit k ρ x he
          have hw : ((hs.Fam ρ).at x).idxAlong [] = ι x := by
            obtain ⟨X, hX⟩ := hx
            exact ih₂.ty x _ hX []
          refine ⟨SubE.okRef_mono _ ((Subst.ok_dia ih₁ hx hw).ty v U hlp hv), fun p => ?_⟩
          change SubE.idxAlong (SubE.mono _ (((hs.Fam ρ).dia x (ι x)) v)) p = _
          rw [SubE.idxAlong_mono, ← Subst.at_nonproj _ hlp]
          exact (Subst.coh_dia ih₁ ih₂ hx).ty v U (by rwa [Ctx.ref_nonproj _ hlp]) p
        · push_neg at hd
          rw [hs.viewS_box hd]
          rw [Tree.view_of_not_dia hd] at hv
          refine ⟨SubE.okRef_mono _ ((Subst.ok_box ih₁).ty v U hlp hv), fun p => ?_⟩
          change SubE.idxAlong (SubE.mono _ (((hs.Fam ρ).box) v)) p = _
          rw [SubE.idxAlong_mono, ← Subst.at_nonproj _ hlp]
          exact (Subst.coh_box ih₁ ih₂).ty v U (by rwa [Ctx.ref_nonproj _ hlp]) p
      have hnoroot : ∀ r U, (S.view (k :: ρ) (S.ctxAt Γ₀ ρ)) (.root r) = some U → False := by
        intro r U hv
        unfold Tree.view at hv
        split at hv <;> cases (show (none : Option VarType) = some U from hv)
      have hok : Subst.Ok (S.ctxAt Γ₀ (k :: ρ)) (hs.Fam (k :: ρ)) := by
        refine ⟨fun v U hlp hv => ?_, fun hO => absurd hO (by rw [ModalSys.NoOpt.noOpt]; decide)⟩
        simp only [Tree.ctxAt] at hv
        rcases Ctx.inserts_cases hv with ⟨b, hb, rfl, rfl⟩ | hv
        · change (hs.rootE (k :: ρ) b.1).OkRef b.2
          rw [hs.rootE_born ⟨b.2, hb⟩]
          exact hs.eok _ b hb
        · cases v with
          | root r => exact (hnoroot r U hv).elim
          | step w s => exact (hview _ U hlp hv).1
      refine ⟨hok, Subst.coh_of hok (fun v U hlp hv p => ?_)⟩
      simp only [Tree.ctxAt] at hv
      rcases Ctx.inserts_cases hv with ⟨b, hb, rfl, rfl⟩ | hv
      · change (hs.rootE (k :: ρ) b.1).idxAlong p = _
        rw [hs.rootE_born ⟨b.2, hb⟩]
        exact hs.eidx _ b p hb
      · cases v with
        | root r => exact (hnoroot r U hv).elim
        | step w s => exact (hview _ U hlp hv).2 p


/-! ## Agreement of substitutions -/

/-- Entries that agree up to weakening at a context's addresses agree in its `□` view. -/
theorem _root_.V12M.Subst.box_eq_mono_of {Γ Δ Δ' : Ctx} {θ : Subst σ Δ} {θ' : Subst σ Δ'}
    (h : Δ.Le Δ') (hat : ∀ w U, Γ.ref w = some U → θ'.at w = (θ.at w).mono h) :
    ∀ v U, v.lastProj = false → Γ.boxIn v = some U → θ'.box v = (θ.box v).mono h.boxIn := by
  intro v U _ hv
  match v with
  | .step w .box =>
      change (θ'.at w).unbox = ((θ.at w).unbox).mono h.boxIn
      rw [hat w _ (Ctx.boxIn_step_box hv), SubE.unbox_mono]
  | .step w .keep =>
      change (θ'.at w).keepE = ((θ.at w).keepE).mono h.boxIn
      rw [hat w _ (Ctx.boxIn_keep hv).2.1, SubE.keepE_mono]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

/-- Entries that agree up to weakening at a context's addresses agree in its `◇_x` view. -/
theorem _root_.V12M.Subst.dia_eq_mono_of {Γ Δ Δ' : Ctx} {θ : Subst σ Δ} {θ' : Subst σ Δ'}
    (h : Δ.Le Δ') (hat : ∀ w U, Γ.ref w = some U → θ'.at w = (θ.at w).mono h)
    (x ιx : VarSymb) :
    ∀ v U, v.lastProj = false → (Γ.diaIn x) v = some U →
      θ'.dia x ιx v = (θ.dia x ιx v).mono (h.diaIn ιx) := by
  intro v U _ hv
  match v with
  | .step w .dia =>
      change (if w = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some U at hv
      change (if w = x then (θ'.at x).diaBody ιx else SubE.hide) =
        SubE.mono _ (if w = x then (θ.at x).diaBody ιx else SubE.hide)
      split_ifs at hv ⊢ with hwx
      · cases hx : Γ.ref x with
        | none => rw [hx] at hv; cases hv
        | some X => rw [hat x X hx, SubE.diaBody_mono]
  | .step w .box =>
      change ((θ'.at w).unbox).mono _ = (((θ.at w).unbox).mono _).mono _
      rw [hat w _ (Ctx.boxIn_step_box (Γ := Γ) hv), SubE.unbox_mono, SubE.mono_mono,
        SubE.mono_mono]
  | .step w .keep =>
      change ((θ'.at w).keepE).mono _ = (((θ.at w).keepE).mono _).mono _
      rw [hat w _ (Ctx.boxIn_keep (Γ := Γ) hv).2.1, SubE.keepE_mono, SubE.mono_mono,
        SubE.mono_mono]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

/-- Without `Opt`, agreement at the visible addresses is similarity. -/
theorem _root_.V12M.Subst.sim_mono_of {Γ Δ Δ' : Ctx} {θ : Subst σ Δ} {θ' : Subst σ Δ'}
    (h : Δ.Le Δ') (hvis : ∀ v U, v.lastProj = false → Γ v = some U → θ' v = (θ v).mono h) :
    Subst.Sim Γ θ' (θ.mono h) :=
  Subst.sim_of (fun v U hl hv => by rw [hvis v U hl hv]; exact .refl _)
    (fun hO => absurd hO (by rw [ModalSys.NoOpt.noOpt]; decide))

/-! ## The family along edges -/

/-- ⭐**Along any edge, the child's family is the parent's `□` view** at the `□` view's
    addresses. -/
theorem SubSetup.fam_box (hs : SubSetup Γ₀ S S' ι E N) (k : ℕ) (ρ : Lab) :
    ∀ v U, v.lastProj = false → (S.ctxAt Γ₀ ρ).boxIn v = some U →
      hs.Fam (k :: ρ) v = ((hs.Fam ρ).box v).mono (Tree.boxIn_le_child hs.ok k ρ) := by
  intro v U hl hv
  cases v with
  | root r => cases (show (none : Option VarType) = some U from hv)
  | step w s =>
      rw [hs.fam_step]
      by_cases hd : ∃ x, S.edge (k :: ρ) = some (.dia x)
      · obtain ⟨x, he⟩ := hd
        rw [hs.viewS_dia he (hs.edge_dia he)]
        change (((hs.Fam ρ).dia x (ι x)) (.step w s)).mono _ = _
        have e := Subst.dia_eq_box_mono (hs.Fam ρ) x (ι x) (.step w s) U
          (by rwa [Ctx.ref_nonproj _ hl])
        rw [Subst.at_nonproj _ hl, Subst.at_nonproj _ hl] at e
        rw [e, SubE.mono_mono]
      · push_neg at hd
        rw [hs.viewS_box hd]
        rfl

/-- ⭐**Along a `◇_x`-edge, the child's family is the parent's `◇_x` view.** -/
theorem SubSetup.fam_dia (hs : SubSetup Γ₀ S S' ι E N) {k : ℕ} {ρ : Lab} {x : VarSymb}
    (he : S.edge (k :: ρ) = some (.dia x)) :
    ∀ v U, v.lastProj = false → ((S.ctxAt Γ₀ ρ).diaIn x) v = some U →
      hs.Fam (k :: ρ) v =
        (((hs.Fam ρ).dia x (ι x)) v).mono (Tree.diaIn_le_child hs.ok (hs.edge_dia he)) := by
  intro v U _ hv
  cases v with
  | root r => cases (show (none : Option VarType) = some U from hv)
  | step w s =>
      rw [hs.fam_step, hs.viewS_dia he (hs.edge_dia he)]
      rfl

/-! ## The family as the tree grows -/

/-- ⭐**The family agrees with the smaller tree's, weakened**, at every node of a parent-closed
    set on which the edges (source and target) agree and the roots' entries agree. -/
theorem SubSetup.fam_agree {S₁ S₁' S₂ S₂' : Tree} {ι₁ ι₂ : VarSymb → VarSymb}
    {E₁ : (ρ : Lab) → Root → SubE σ (S₁'.ctxAt Γ₀ ρ)}
    {E₂ : (ρ : Lab) → Root → SubE σ (S₂'.ctxAt Γ₀ ρ)} {N₁ N₂ : List Lab}
    (hs₁ : SubSetup Γ₀ S₁ S₁' ι₁ E₁ N₁) (hs₂ : SubSetup Γ₀ S₂ S₂' ι₂ E₂ N₂)
    (P : Lab → Prop) (hP : ∀ k ρ, P (k :: ρ) → P ρ)
    (hle : ∀ ρ, (S₁'.ctxAt Γ₀ ρ).Le (S₂'.ctxAt Γ₀ ρ))
    (hedge : ∀ k ρ, P (k :: ρ) → S₂.edge (k :: ρ) = S₁.edge (k :: ρ))
    (hedge' : ∀ k ρ, P (k :: ρ) → S₂'.edge (k :: ρ) = S₁'.edge (k :: ρ))
    (hroot : ∀ ρ, P ρ → ∀ r U, (S₁.ctxAt Γ₀ ρ) (.root r) = some U →
      hs₂.rootE ρ r = (hs₁.rootE ρ r).mono (hle ρ)) :
    ∀ ρ, P ρ → ∀ v U, v.lastProj = false → (S₁.ctxAt Γ₀ ρ) v = some U →
      hs₂.Fam ρ v = (hs₁.Fam ρ v).mono (hle ρ)
  | [], hρ, v, U, _, hv => by
      cases v with
      | root r =>
          rw [hs₁.fam_root, hs₂.fam_root]
          exact hroot [] hρ r U hv
      | step w s => rfl
  | k :: ρ, hρ, v, U, hl, hv => by
      cases v with
      | root r =>
          rw [hs₁.fam_root, hs₂.fam_root]
          exact hroot _ hρ r U hv
      | step w s =>
          have ih := SubSetup.fam_agree hs₁ hs₂ P hP hle hedge hedge' hroot ρ (hP k ρ hρ)
          have hat := Subst.at_eq_mono_of (hle ρ) ih
          simp only [Tree.ctxAt] at hv
          rcases Ctx.inserts_cases hv with ⟨b, _, he, _⟩ | hv
          · cases he
          rw [hs₁.fam_step, hs₂.fam_step]
          by_cases hd : ∃ x, S₁.edge (k :: ρ) = some (.dia x)
          · obtain ⟨x, he₁⟩ := hd
            have he₂ := (hedge k ρ hρ).trans he₁
            have he₁' := hs₁.edge_dia he₁
            have he₂' := (hedge' k ρ hρ).trans he₁'
            rw [hs₂.viewS_dia he₂ he₂', hs₁.viewS_dia he₁ he₁']
            rw [Tree.view_dia he₁] at hv
            change (((hs₂.Fam ρ).dia x (ι₁ x)) _).mono _ =
              ((((hs₁.Fam ρ).dia x (ι₁ x)) _).mono _).mono _
            rw [Subst.dia_eq_mono_of (hle ρ) hat x _ _ U hl hv, SubE.mono_mono, SubE.mono_mono]
          · push_neg at hd
            have hd₂ : ∀ x, S₂.edge (k :: ρ) ≠ some (.dia x) := fun x h =>
              hd x ((hedge k ρ hρ).symm.trans h)
            rw [hs₂.viewS_box hd₂, hs₁.viewS_box hd]
            rw [Tree.view_of_not_dia hd] at hv
            change (((hs₂.Fam ρ).box) _).mono _ = ((((hs₁.Fam ρ).box) _).mono _).mono _
            rw [Subst.box_eq_mono_of (hle ρ) hat _ U hl hv, SubE.mono_mono, SubE.mono_mono]

/-! ## Substituting a tree sequent -/

/-- A formula at a node, substituted by the node's family. -/
noncomputable def SubSetup.lf (hs : SubSetup Γ₀ S S' ι E N) (p : LF σ Γ₀ S) : LF σ Γ₀ S' :=
  ⟨p.1, WFF.subst ι (hs.Fam p.1) (hs.okCoh p.1).1 (hs.okCoh p.1).2
    (Tree.ctxAt_slots hs.h0 hs.okS p.1) (Tree.ctxAt_slots hs.h0 hs.ok p.1) p.2⟩

theorem SubSetup.lf_mk (hs : SubSetup Γ₀ S S' ι E N) (ρ : Lab) (φ : WFF σ (S.ctxAt Γ₀ ρ) 0) :
    hs.lf ⟨ρ, φ⟩ = ⟨ρ, WFF.subst ι (hs.Fam ρ) (hs.okCoh ρ).1 (hs.okCoh ρ).2
      (Tree.ctxAt_slots hs.h0 hs.okS ρ) (Tree.ctxAt_slots hs.h0 hs.ok ρ) φ⟩ := rfl

/-- ⭐**Substitution commutes with weakening as the tree grows**, for a side on the agreeing
    nodes. -/
theorem SubSetup.lf_mono {S₁ S₁' S₂ S₂' : Tree} {ι₁ ι₂ : VarSymb → VarSymb}
    {E₁ : (ρ : Lab) → Root → SubE σ (S₁'.ctxAt Γ₀ ρ)}
    {E₂ : (ρ : Lab) → Root → SubE σ (S₂'.ctxAt Γ₀ ρ)} {N₁ N₂ : List Lab}
    (hs₁ : SubSetup Γ₀ S₁ S₁' ι₁ E₁ N₁) (hs₂ : SubSetup Γ₀ S₂ S₂' ι₂ E₂ N₂)
    (P : Lab → Prop) (hP : ∀ k ρ, P (k :: ρ) → P ρ)
    (hle : ∀ ρ, (S₁'.ctxAt Γ₀ ρ).Le (S₂'.ctxAt Γ₀ ρ))
    (hedge : ∀ k ρ, P (k :: ρ) → S₂.edge (k :: ρ) = S₁.edge (k :: ρ))
    (hedge' : ∀ k ρ, P (k :: ρ) → S₂'.edge (k :: ρ) = S₁'.edge (k :: ρ))
    (hroot : ∀ ρ, P ρ → ∀ r U, (S₁.ctxAt Γ₀ ρ) (.root r) = some U →
      hs₂.rootE ρ r = (hs₁.rootE ρ r).mono (hle ρ))
    (hk : ∀ ρ, (S₁.ctxAt Γ₀ ρ).Le (S₂.ctxAt Γ₀ ρ)) (L : Seq σ Γ₀ S₁) (hL : ∀ p ∈ L, P p.1) :
    (Seq.mono hk L).map hs₂.lf = Seq.mono hle (L.map hs₁.lf) := by
  unfold Seq.mono
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun p hp => ?_
  obtain ⟨ρ, φ⟩ := p
  exact congrArg (Sigma.mk ρ) (WFF.subst_mono_eq (hk ρ) (hle ρ) (hs₁.Fam ρ) _ _ (hs₂.Fam ρ) _ _
    (Tree.ctxAt_slots hs₁.h0 hs₁.okS ρ) (Tree.ctxAt_slots hs₁.h0 hs₂.okS ρ)
    (Tree.ctxAt_slots hs₁.h0 hs₁.ok ρ) (Tree.ctxAt_slots hs₁.h0 hs₂.ok ρ)
    (Subst.sim_mono_of (hle ρ)
      (hs₁.fam_agree hs₂ P hP hle hedge hedge' hroot ρ (hL _ hp))) φ)

/-! ## The setup as the tree grows -/

open Classical in
/-- The entries after a birth: the new root to its new name, the rest weakened. -/
noncomputable def SubSetup.EBirth (E : (ρ : Lab) → Root → SubE σ (S'.ctxAt Γ₀ ρ)) {v' : ℕ}
    (hv' : S'.Fresh Γ₀ (.free v')) (τ : Lab) (T : VarType) (v : ℕ) :
    (ρ : Lab) → Root → SubE σ ((S'.addBirth τ (.free v') T).ctxAt Γ₀ ρ) := fun ρ r =>
  if ρ = τ ∧ r = .free v then .ren (.root (.free v'))
  else (E ρ r).mono (Tree.ctxAt_addBirth hv' τ T ρ)

theorem SubSetup.eBirth_new (E : (ρ : Lab) → Root → SubE σ (S'.ctxAt Γ₀ ρ)) {v' : ℕ}
    (hv' : S'.Fresh Γ₀ (.free v')) (τ : Lab) (T : VarType) (v : ℕ) :
    SubSetup.EBirth E hv' τ T v τ (.free v) = .ren (.root (.free v')) := if_pos ⟨rfl, rfl⟩

theorem SubSetup.eBirth_old (E : (ρ : Lab) → Root → SubE σ (S'.ctxAt Γ₀ ρ)) {v' : ℕ}
    (hv' : S'.Fresh Γ₀ (.free v')) (τ : Lab) (T : VarType) {v : ℕ} {ρ : Lab} {r : Root}
    (h : r ≠ .free v) :
    SubSetup.EBirth E hv' τ T v ρ r = (E ρ r).mono (Tree.ctxAt_addBirth hv' τ T ρ) :=
  if_neg fun h' => h h'.2

/-- ⭐**The setup survives a birth**: a tree-fresh name of the source to a tree-fresh name of the
    target. -/
theorem SubSetup.addBirth (hs : SubSetup Γ₀ S S' ι E N) {v v' : ℕ}
    (hv : S.Fresh Γ₀ (.free v)) (hv' : S'.Fresh Γ₀ (.free v')) (τ : Lab) (T : VarType) :
    SubSetup Γ₀ (S.addBirth τ (.free v) T) (S'.addBirth τ (.free v') T)
      (VarSymb.renameIdx ι v v') (SubSetup.EBirth E hv' τ T v) N where
  okS := hs.okS.addBirth hv τ T
  ok := hs.ok.addBirth hv' τ T
  h0 := hs.h0
  edge k ρ := by
    change S'.edge (k :: ρ) = (S.edge (k :: ρ)).map _
    rw [hs.edge k ρ]
    cases he : S.edge (k :: ρ) with
    | none => rfl
    | some e =>
        cases e with
        | box => rfl
        | dia x =>
            obtain ⟨X, hX⟩ := hs.wit k ρ x he
            have hrt := (hv.at ρ).rt_ne hX
            change some (EdgeKind.dia (ι x)) = some (EdgeKind.dia (VarSymb.renameIdx ι v v' x))
            unfold VarSymb.renameIdx
            rw [if_neg hrt]
  wit k ρ x he := (hs.wit k ρ x he).imp fun _ hX => (Tree.ctxAt_addBirth hv τ T ρ).ref hX
  eok ρ b hb := by
    rw [Tree.birthsAt_addBirth] at hb
    split_ifs at hb with hρ
    · rcases List.mem_cons.mp hb with rfl | hb
      · subst hρ
        rw [SubSetup.eBirth_new]
        change ((S'.addBirth ρ (.free v') T).ctxAt Γ₀ ρ).ref (.root (.free v')) = some T
        rw [Ctx.ref_nonproj _ rfl]
        refine Tree.ctxAt_root (hs.ok.addBirth hv' ρ T) (b := (.free v', T)) ?_
        rw [Tree.birthsAt_addBirth, if_pos rfl]
        exact List.mem_cons_self
      · rw [SubSetup.eBirth_old _ _ _ _ (hv.births _ (Tree.mem_birthsAt.mp hb))]
        exact SubE.okRef_mono _ (hs.eok ρ b hb)
    · rw [SubSetup.eBirth_old _ _ _ _ (hv.births _ (Tree.mem_birthsAt.mp hb))]
      exact SubE.okRef_mono _ (hs.eok ρ b hb)
  eidx ρ b p hb := by
    have hold : b ∈ S.birthsAt ρ → (SubSetup.EBirth E hv' τ T v ρ b.1).idxAlong p =
        VarSymb.renameIdx ι v v' ((VarSymb.root b.1).ext p) := fun hb => by
      have hne := hv.births _ (Tree.mem_birthsAt.mp hb)
      rw [SubSetup.eBirth_old _ _ _ _ hne, SubE.idxAlong_mono, hs.eidx ρ b p hb]
      unfold VarSymb.renameIdx
      rw [if_neg (by rw [VarSymb.ext_rt]; exact hne)]
    rw [Tree.birthsAt_addBirth] at hb
    split_ifs at hb with hρ
    · rcases List.mem_cons.mp hb with rfl | hb
      · subst hρ
        rw [SubSetup.eBirth_new]
        unfold VarSymb.renameIdx
        rw [if_pos (by rw [VarSymb.ext_rt]; rfl), VarSymb.ext_path]
        rfl
      · exact hold hb
    · exact hold hb
  fix w hw := by
    unfold VarSymb.renameIdx
    rw [if_neg (fun h => hw (τ, .free v, T) List.mem_cons_self h.symm)]
    exact hs.fix w fun b hb => hw b (List.mem_cons_of_mem _ hb)
  births b hb := by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Or.inl ⟨(τ, .free v, T), List.mem_cons_self, rfl⟩
    · exact (hs.births b hb).imp_left fun ⟨b₀, h, e⟩ => ⟨b₀, List.mem_cons_of_mem _ h, e⟩

/-- The entries after a new edge: weakened. -/
noncomputable def SubSetup.EEdge (E : (ρ : Lab) → Root → SubE σ (S'.ctxAt Γ₀ ρ)) {c : Lab}
    (hc : S'.edge c = none) (e : EdgeKind) :
    (ρ : Lab) → Root → SubE σ ((S'.addEdge c e).ctxAt Γ₀ ρ) := fun ρ r =>
  (E ρ r).mono (Tree.ctxAt_addEdge hc e ρ)

/-- ⭐**The setup survives a new edge**, its witness renamed. -/
theorem SubSetup.addEdge (hs : SubSetup Γ₀ S S' ι E N) {j : ℕ} {ν : Lab}
    (hc : S.edge (j :: ν) = none) (e : EdgeKind)
    (hw : ∀ k ρ x, j :: ν = k :: ρ → e = .dia x →
      ∃ X, (S.ctxAt Γ₀ ρ).ref x = some (.VTypeDia X)) :
    SubSetup Γ₀ (S.addEdge (j :: ν) e) (S'.addEdge (j :: ν) (e.ren ι)) ι
      (SubSetup.EEdge E (hs.edge_none hc) (e.ren ι)) N where
  okS := hs.okS.addEdge _ e
  ok := hs.ok.addEdge _ _
  h0 := hs.h0
  edge k' ρ' := by
    rw [Tree.edge_addEdge, Tree.edge_addEdge]
    split
    · rfl
    · exact hs.edge k' ρ'
  wit k ρ x he := by
    rw [Tree.edge_addEdge] at he
    split at he
    · rename_i hk
      cases he
      exact (hw k ρ x hk.symm rfl).imp fun _ hX => (Tree.ctxAt_addEdge hc _ ρ).ref hX
    · exact (hs.wit k ρ x he).imp fun _ hX => (Tree.ctxAt_addEdge hc e ρ).ref hX
  eok ρ b hb := SubE.okRef_mono _ (hs.eok ρ b hb)
  eidx ρ b p hb := by
    unfold SubSetup.EEdge
    rw [SubE.idxAlong_mono]
    exact hs.eidx ρ b p hb
  fix := hs.fix
  births := hs.births

/-! ## Vacancy and populated nodes -/

/-- Every node of `N` carries a formula of the sequent. -/
def Pop {D : Tree} (N : List Lab) (Δ Θ : Seq σ Γ₀ D) : Prop :=
  ∀ ρ ∈ N, (∃ q ∈ Δ, q.1 = ρ) ∨ (∃ q ∈ Θ, q.1 = ρ)

theorem Pop.cons_l {D : Tree} {Δ Θ : Seq σ Γ₀ D} (h : Pop N Δ Θ) (x : LF σ Γ₀ D) :
    Pop N (x :: Δ) Θ := fun ρ hρ =>
  (h ρ hρ).imp_left fun ⟨q, hq, e⟩ => ⟨q, List.mem_cons_of_mem _ hq, e⟩

theorem Pop.cons_r {D : Tree} {Δ Θ : Seq σ Γ₀ D} (h : Pop N Δ Θ) (x : LF σ Γ₀ D) :
    Pop N Δ (x :: Θ) := fun ρ hρ =>
  (h ρ hρ).imp_right fun ⟨q, hq, e⟩ => ⟨q, List.mem_cons_of_mem _ hq, e⟩

theorem Pop.mono {D D' : Tree} {Δ Θ : Seq σ Γ₀ D} (h : Pop N Δ Θ)
    (hk : ∀ τ, (D.ctxAt Γ₀ τ).Le (D'.ctxAt Γ₀ τ)) : Pop N (Seq.mono hk Δ) (Seq.mono hk Θ) :=
  fun ρ hρ => (h ρ hρ).imp (fun ⟨_, hq, e⟩ => ⟨_, List.mem_map_of_mem hq, e⟩)
    (fun ⟨_, hq, e⟩ => ⟨_, List.mem_map_of_mem hq, e⟩)

/-- A vacant node stays vacant. -/
theorem SubSetup.vacant (hs : SubSetup Γ₀ S S' ι E N) {j : ℕ} {ν : Lab}
    {Δ Θ : Seq σ Γ₀ S} (hv : Vacant S (j :: ν) Δ Θ) (hN : Pop N Δ Θ) :
    Vacant S' (j :: ν) (Δ.map hs.lf) (Θ.map hs.lf) where
  edge τ h := by
    cases τ with
    | nil => exact absurd (List.suffix_nil.mp h) (List.cons_ne_nil _ _)
    | cons k ρ => rw [hs.edge k ρ, hv.edge _ h]; rfl
  births b hb := by
    rcases hs.births b hb with ⟨b₀, hb₀, e⟩ | hn
    · rw [← e]
      exact hv.births b₀ hb₀
    · rcases hN _ hn with ⟨q, hq, e⟩ | ⟨q, hq, e⟩
      · rw [← e]
        exact hv.left q hq
      · rw [← e]
        exact hv.right q hq
  left p hp := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hv.left q hq
  right p hp := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hv.right q hq

theorem Tree.not_suffix_cons (k : ℕ) (τ : Lab) : ¬ (k :: τ) <:+ τ := fun h' => by
  have := h'.length_le
  simp at this

/-! ## ⭐Substitution across the tree -/

/-- The roots' entries after a birth agree with the old ones at the old roots. -/
theorem SubSetup.rootE_addBirth {D : Tree} (hs : SubSetup Γ₀ D S' ι E N) {v v' : ℕ}
    (hv : D.Fresh Γ₀ (.free v)) (hv' : S'.Fresh Γ₀ (.free v')) (τ : Lab) (T : VarType) :
    ∀ ρ, True → ∀ r U, (D.ctxAt Γ₀ ρ) (.root r) = some U →
      (hs.addBirth hv hv' τ T).rootE ρ r =
        (hs.rootE ρ r).mono (Tree.ctxAt_addBirth hv' τ T ρ) := by
  intro ρ _ r U hr
  have hne : r ≠ .free v := fun he => by
    rw [he, (hv.at ρ).root] at hr
    cases hr
  by_cases hb : ∃ U, (r, U) ∈ D.birthsAt ρ
  · have hb₂ : ∃ U, (r, U) ∈ (D.addBirth τ (.free v) T).birthsAt ρ := by
      obtain ⟨U', h⟩ := hb
      refine ⟨U', ?_⟩
      rw [Tree.birthsAt_addBirth]
      split_ifs
      · exact List.mem_cons_of_mem _ h
      · exact h
    rw [hs.rootE_born hb, SubSetup.rootE_born _ hb₂, SubSetup.eBirth_old _ _ _ _ hne]
  · have hb₂ : ¬ ∃ U, (r, U) ∈ (D.addBirth τ (.free v) T).birthsAt ρ := by
      rintro ⟨U', h⟩
      rw [Tree.birthsAt_addBirth] at h
      split_ifs at h
      · rcases List.mem_cons.mp h with h | h
        · exact hne (congrArg Prod.fst h)
        · exact hb ⟨U', h⟩
      · exact hb ⟨U', h⟩
    rw [hs.rootE_not hb, SubSetup.rootE_not _ hb₂]
    rfl

/-- The roots' entries after a new edge are the old ones, weakened. -/
theorem SubSetup.rootE_addEdge {D : Tree} (hs : SubSetup Γ₀ D S' ι E N) {j : ℕ} {ν : Lab}
    (hc : D.edge (j :: ν) = none) (e : EdgeKind)
    (hw : ∀ k ρ x, j :: ν = k :: ρ → e = .dia x →
      ∃ X, (D.ctxAt Γ₀ ρ).ref x = some (.VTypeDia X)) (P : Lab → Prop) :
    ∀ ρ, P ρ → ∀ r U, (D.ctxAt Γ₀ ρ) (.root r) = some U →
      (hs.addEdge hc e hw).rootE ρ r =
        (hs.rootE ρ r).mono (Tree.ctxAt_addEdge (hs.edge_none hc) (e.ren ι) ρ) := by
  intro ρ _ r _ _
  by_cases hb : ∃ U, (r, U) ∈ D.birthsAt ρ
  · rw [hs.rootE_born hb, (hs.addEdge hc e hw).rootE_born hb]
    rfl
  · rw [hs.rootE_not hb, (hs.addEdge hc e hw).rootE_not hb]
    rfl

/-- ⭐**Tree substitution**, height-preserving: a derivation over the source tree goes to one of
    the substituted tree sequent over the target tree, each rule to itself, every eigenvariable
    renamed to a name fresh for the target. -/
theorem subst [Γ₀.Presented] {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (p : GKN σ Γ₀ n D Δ Θ) :
    ∀ {S' : Tree} {ι : VarSymb → VarSymb} {E : (ρ : Lab) → Root → SubE σ (S'.ctxAt Γ₀ ρ)}
      {N : List Lab} (hs : SubSetup Γ₀ D S' ι E N), Pop N Δ Θ →
      GKN σ Γ₀ n S' (Δ.map hs.lf) (Θ.map hs.lf) := by
  induction p with
  | ax τ P hP h₁ h₂ =>
      intro S' ι E N hs _
      exact .ax τ _ hP.subst (List.mem_map_of_mem (f := hs.lf) h₁)
        (List.mem_map_of_mem (f := hs.lf) h₂)
  | botL τ h => intro S' ι E N hs _; exact .botL τ (List.mem_map_of_mem (f := hs.lf) h)
  | topR τ h => intro S' ι E N hs _; exact .topR τ (List.mem_map_of_mem (f := hs.lf) h)
  | andL τ h _ ih =>
      intro S' ι E N hs hN
      exact .andL τ (List.mem_map_of_mem (f := hs.lf) h) (ih hs ((hN.cons_l _).cons_l _))
  | andR τ h _ _ ih₁ ih₂ =>
      intro S' ι E N hs hN
      exact .andR τ (List.mem_map_of_mem (f := hs.lf) h) (ih₁ hs (hN.cons_r _))
        (ih₂ hs (hN.cons_r _))
  | orL τ h _ _ ih₁ ih₂ =>
      intro S' ι E N hs hN
      exact .orL τ (List.mem_map_of_mem (f := hs.lf) h) (ih₁ hs (hN.cons_l _))
        (ih₂ hs (hN.cons_l _))
  | orR τ h _ ih =>
      intro S' ι E N hs hN
      exact .orR τ (List.mem_map_of_mem (f := hs.lf) h) (ih hs ((hN.cons_r _).cons_r _))
  | impL τ h _ _ ih₁ ih₂ =>
      intro S' ι E N hs hN
      exact .impL τ (List.mem_map_of_mem (f := hs.lf) h) (ih₁ hs (hN.cons_r _))
        (ih₂ hs (hN.cons_l _))
  | impR τ h _ ih =>
      intro S' ι E N hs hN
      exact .impR τ (List.mem_map_of_mem (f := hs.lf) h) (ih hs ((hN.cons_l _).cons_r _))
  | allL τ hsτ T' t' h _ ih =>
      intro S' ι E N hs hN
      have ih' := ih hs (hN.cons_l _)
      rw [List.map_cons, hs.lf_mk, WFF.subst_instantiate] at ih'
      exact .allL τ (Tree.ctxAt_slots hs.h0 hs.ok τ) T'
        (Term.subst ι (hs.Fam τ) (hs.okCoh τ).1 (hs.okCoh τ).2 t')
        (List.mem_map_of_mem (f := hs.lf) h) ih'
  | exR τ hsτ T' t' h _ ih =>
      intro S' ι E N hs hN
      have ih' := ih hs (hN.cons_r _)
      rw [List.map_cons, hs.lf_mk, WFF.subst_instantiate] at ih'
      exact .exR τ (Tree.ctxAt_slots hs.h0 hs.ok τ) T'
        (Term.subst ι (hs.Fam τ) (hs.okCoh τ).1 (hs.okCoh τ).2 t')
        (List.mem_map_of_mem (f := hs.lf) h) ih'
  | ref τ t' _ ih =>
      intro S' ι E N hs hN
      exact .ref τ (Term.subst ι (hs.Fam τ) (hs.okCoh τ).1 (hs.okCoh τ).2 t')
        (ih hs (hN.cons_l _))
  | repl τ hsτ hP t₁ t₂ h₁ h₂ _ ih =>
      intro S' ι E N hs hN
      have ih' := ih hs (hN.cons_l _)
      rw [List.map_cons, hs.lf_mk, WFF.subst_instantiate] at ih'
      refine .repl τ (Tree.ctxAt_slots hs.h0 hs.ok τ) hP.subst
        (Term.subst ι (hs.Fam τ) (hs.okCoh τ).1 (hs.okCoh τ).2 t₁)
        (Term.subst ι (hs.Fam τ) (hs.okCoh τ).1 (hs.okCoh τ).2 t₂)
        (List.mem_map_of_mem (f := hs.lf) h₁) ?_ ih'
      have hm := List.mem_map_of_mem (f := hs.lf) h₂
      rw [hs.lf_mk, WFF.subst_instantiate] at hm
      exact hm
  | @allR n D Δ Θ τ hsτ v T' hv φ hle h _ ih =>
      intro S' ι E N hs hN
      obtain ⟨v', hv'⟩ := exists_treeFresh (Γ₀ := Γ₀) S'
      have hs₂ := hs.addBirth hv hv' τ T'
      have hk := Tree.ctxAt_addBirth hv τ T'
      have hk' := Tree.ctxAt_addBirth hv' τ T'
      have ih' := ih hs₂ ((hN.mono hk).cons_r _)
      have hm : ∀ L : Seq σ Γ₀ D, (Seq.mono hk L).map hs₂.lf = Seq.mono hk' (L.map hs.lf) :=
        fun L => hs.lf_mono hs₂ (fun _ => True) (fun _ _ _ => trivial) hk' (fun _ _ _ => rfl)
          (fun _ _ _ => rfl) (hs.rootE_addBirth hv hv' τ T') hk L (fun _ _ => trivial)
      have hfτ := hv.at τ
      have hfτ' := hv'.at τ
      have hsτ' := Tree.ctxAt_slots hs.h0 hs.ok τ
      have hθ := (hs.okCoh τ).1
      have hc := (hs.okCoh τ).2
      have hle' := Tree.insert_le_addBirth (D := S') (Γ₀ := Γ₀) τ (.free v') T'
      have hsim : Subst.Sim ((D.ctxAt Γ₀ τ).insert (.free v) T') (hs₂.Fam τ)
          (((hs.Fam τ).rename v v' T' hfτ'.root).mono hle') := by
        refine Subst.sim_mono_of hle' fun w U hl hw => ?_
        by_cases hw0 : w = .root (.free v)
        · subst hw0
          have hb : ∃ U, (Root.free v, U) ∈ (D.addBirth τ (.free v) T').birthsAt τ :=
            ⟨T', by rw [Tree.birthsAt_addBirth, if_pos rfl]; exact List.mem_cons_self⟩
          rw [hs₂.fam_root, Subst.rename_root, SubSetup.rootE_born _ hb, SubSetup.eBirth_new]
          rfl
        · rw [Subst.rename_ne _ _ _ _ hw0, SubE.mono_mono]
          rcases Ctx.inserts_cases (L := [(.free v, T')]) hw with ⟨b, hb, he, _⟩ | hw'
          · rw [List.mem_singleton] at hb
            subst hb
            exact absurd he hw0
          · rw [hs.fam_agree hs₂ (fun _ => True) (fun _ _ _ => trivial) hk' (fun _ _ _ => rfl)
              (fun _ _ _ => rfl) (hs.rootE_addBirth hv hv' τ T') τ trivial w U hl hw']
      have e₁ : hs₂.lf ⟨τ, WFF.mono hle φ⟩ = ⟨τ, WFF.mono hle' (WFF.subst
          (VarSymb.renameIdx ι v v') ((hs.Fam τ).rename v v' T' hfτ'.root)
          (Subst.ok_rename hθ T' hfτ'.root) (Subst.coh_rename hθ hc hfτ T' hfτ'.root)
          (hsτ.insertFree v T') (hsτ'.insertFree v' T') φ)⟩ :=
        congrArg (Sigma.mk τ) (WFF.subst_mono_eq hle hle' _ _ _ (hs₂.Fam τ) _ _
          (hsτ.insertFree v T') (Tree.ctxAt_slots hs.h0 hs₂.okS τ) (hsτ'.insertFree v' T')
          (Tree.ctxAt_slots hs.h0 hs₂.ok τ) hsim φ)
      rw [List.map_cons, hm, hm, e₁] at ih'
      refine .allR τ hsτ' v' T' hv' hle' ?_ ih'
      rw [← congrArg (WFF.all T') (WFF.subst_bindFree (hs.Fam τ) hθ hc hsτ hsτ' hfτ hfτ' T' φ)]
      exact List.mem_map_of_mem (f := hs.lf) h
  | @exL n D Δ Θ τ hsτ v T' hv φ hle h _ ih =>
      intro S' ι E N hs hN
      obtain ⟨v', hv'⟩ := exists_treeFresh (Γ₀ := Γ₀) S'
      have hs₂ := hs.addBirth hv hv' τ T'
      have hk := Tree.ctxAt_addBirth hv τ T'
      have hk' := Tree.ctxAt_addBirth hv' τ T'
      have ih' := ih hs₂ ((hN.mono hk).cons_l _)
      have hm : ∀ L : Seq σ Γ₀ D, (Seq.mono hk L).map hs₂.lf = Seq.mono hk' (L.map hs.lf) :=
        fun L => hs.lf_mono hs₂ (fun _ => True) (fun _ _ _ => trivial) hk' (fun _ _ _ => rfl)
          (fun _ _ _ => rfl) (hs.rootE_addBirth hv hv' τ T') hk L (fun _ _ => trivial)
      have hfτ := hv.at τ
      have hfτ' := hv'.at τ
      have hsτ' := Tree.ctxAt_slots hs.h0 hs.ok τ
      have hθ := (hs.okCoh τ).1
      have hc := (hs.okCoh τ).2
      have hle' := Tree.insert_le_addBirth (D := S') (Γ₀ := Γ₀) τ (.free v') T'
      have hsim : Subst.Sim ((D.ctxAt Γ₀ τ).insert (.free v) T') (hs₂.Fam τ)
          (((hs.Fam τ).rename v v' T' hfτ'.root).mono hle') := by
        refine Subst.sim_mono_of hle' fun w U hl hw => ?_
        by_cases hw0 : w = .root (.free v)
        · subst hw0
          have hb : ∃ U, (Root.free v, U) ∈ (D.addBirth τ (.free v) T').birthsAt τ :=
            ⟨T', by rw [Tree.birthsAt_addBirth, if_pos rfl]; exact List.mem_cons_self⟩
          rw [hs₂.fam_root, Subst.rename_root, SubSetup.rootE_born _ hb, SubSetup.eBirth_new]
          rfl
        · rw [Subst.rename_ne _ _ _ _ hw0, SubE.mono_mono]
          rcases Ctx.inserts_cases (L := [(.free v, T')]) hw with ⟨b, hb, he, _⟩ | hw'
          · rw [List.mem_singleton] at hb
            subst hb
            exact absurd he hw0
          · rw [hs.fam_agree hs₂ (fun _ => True) (fun _ _ _ => trivial) hk' (fun _ _ _ => rfl)
              (fun _ _ _ => rfl) (hs.rootE_addBirth hv hv' τ T') τ trivial w U hl hw']
      have e₁ : hs₂.lf ⟨τ, WFF.mono hle φ⟩ = ⟨τ, WFF.mono hle' (WFF.subst
          (VarSymb.renameIdx ι v v') ((hs.Fam τ).rename v v' T' hfτ'.root)
          (Subst.ok_rename hθ T' hfτ'.root) (Subst.coh_rename hθ hc hfτ T' hfτ'.root)
          (hsτ.insertFree v T') (hsτ'.insertFree v' T') φ)⟩ :=
        congrArg (Sigma.mk τ) (WFF.subst_mono_eq hle hle' _ _ _ (hs₂.Fam τ) _ _
          (hsτ.insertFree v T') (Tree.ctxAt_slots hs.h0 hs₂.okS τ) (hsτ'.insertFree v' T')
          (Tree.ctxAt_slots hs.h0 hs₂.ok τ) hsim φ)
      rw [List.map_cons, hm, hm, e₁] at ih'
      refine .exL τ hsτ' v' T' hv' hle' ?_ ih'
      rw [← congrArg (WFF.ex T') (WFF.subst_bindFree (hs.Fam τ) hθ hc hsτ hsτ' hfτ hfτ' T' φ)]
      exact List.mem_map_of_mem (f := hs.lf) h
  | @boxL n D Δ Θ τ k e χ he hle h _ ih =>
      intro S' ι E N hs hN
      have ih' := ih hs (hN.cons_l _)
      have he' : S'.edge (k :: τ) = some (e.ren ι) := by rw [hs.edge k τ, he]; rfl
      have hle' := Tree.boxIn_le_child hs.ok k τ
      have hθ := (hs.okCoh τ).1
      have hc := (hs.okCoh τ).2
      have hsτ := Tree.ctxAt_slots hs.h0 hs.okS τ
      have hsτ' := Tree.ctxAt_slots hs.h0 hs.ok τ
      have e₁ : hs.lf ⟨k :: τ, WFF.mono hle χ⟩ = ⟨k :: τ, WFF.mono hle' (WFF.subst ι
          (hs.Fam τ).box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hsτ.boxIn hsτ'.boxIn χ)⟩ :=
        congrArg (Sigma.mk _) (WFF.subst_mono_eq hle hle' _ _ _ (hs.Fam (k :: τ)) _ _
          hsτ.boxIn (Tree.ctxAt_slots hs.h0 hs.okS _) hsτ'.boxIn (Tree.ctxAt_slots hs.h0 hs.ok _)
          (Subst.sim_mono_of hle' fun w U hl hw => hs.fam_box k τ w U hl hw) χ)
      rw [List.map_cons, e₁] at ih'
      exact .boxL τ k _ he' hle' (List.mem_map_of_mem (f := hs.lf) h) ih'
  | @diaR n D Δ Θ τ k x hx ψ he hle h _ ih =>
      intro S' ι E N hs hN
      have ih' := ih hs (hN.cons_r _)
      have he' := hs.edge_dia he
      have hle' := Tree.diaIn_le_child hs.ok he'
      have hθ := (hs.okCoh τ).1
      have hc := (hs.okCoh τ).2
      have hsτ := Tree.ctxAt_slots hs.h0 hs.okS τ
      have hsτ' := Tree.ctxAt_slots hs.h0 hs.ok τ
      have hw : ((hs.Fam τ).at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hx' : ∃ X, (S'.ctxAt Γ₀ τ).ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      have e₁ : hs.lf ⟨k :: τ, WFF.mono hle ψ⟩ = ⟨k :: τ, WFF.mono hle' (WFF.subst ι
          ((hs.Fam τ).dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
          (hsτ.diaIn x) (hsτ'.diaIn _) ψ)⟩ :=
        congrArg (Sigma.mk _) (WFF.subst_mono_eq hle hle' _ _ _ (hs.Fam (k :: τ)) _ _
          (hsτ.diaIn x) (Tree.ctxAt_slots hs.h0 hs.okS _) (hsτ'.diaIn _)
          (Tree.ctxAt_slots hs.h0 hs.ok _)
          (Subst.sim_mono_of hle' fun w U hl hw => hs.fam_dia he w U hl hw) ψ)
      rw [List.map_cons, e₁] at ih'
      exact .diaR τ k (ι x) hx' he' hle' (List.mem_map_of_mem (f := hs.lf) h) ih'
  | @boxR n D Δ Θ τ k φ hv hle h _ ih =>
      intro S' ι E N hs hN
      have hnone := hv.edge _ (List.suffix_refl _)
      have hw : ∀ j ρ y, k :: τ = j :: ρ → EdgeKind.box = .dia y →
          ∃ X, (D.ctxAt Γ₀ ρ).ref y = some (.VTypeDia X) := fun _ _ _ _ he => by cases he
      have hs₂ := hs.addEdge hnone .box hw
      have hv' := hs.vacant hv hN
      have hnone' := hv'.edge _ (List.suffix_refl _)
      have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hnone EdgeKind.box
      have hk' := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hnone' EdgeKind.box
      have ih' := ih hs₂ ((hN.mono hk).cons_r _)
      have hP : ∀ j ρ, ¬ (k :: τ) <:+ (j :: ρ) → ¬ (k :: τ) <:+ ρ :=
        fun j ρ h h' => h (h'.trans (List.suffix_cons j ρ))
      have hedge : ∀ j ρ, ¬ (k :: τ) <:+ (j :: ρ) →
          (D.addEdge (k :: τ) .box).edge (j :: ρ) = D.edge (j :: ρ) := fun j ρ h => by
        rw [Tree.edge_addEdge, if_neg (fun he : j :: ρ = k :: τ => h (he ▸ List.suffix_refl _))]
      have hedge' : ∀ j ρ, ¬ (k :: τ) <:+ (j :: ρ) →
          (S'.addEdge (k :: τ) .box).edge (j :: ρ) = S'.edge (j :: ρ) := fun j ρ h => by
        rw [Tree.edge_addEdge, if_neg (fun he : j :: ρ = k :: τ => h (he ▸ List.suffix_refl _))]
      have hroot := hs.rootE_addEdge hnone .box hw (fun ρ => ¬ (k :: τ) <:+ ρ)
      have hm : ∀ L : Seq σ Γ₀ D, (∀ p ∈ L, ¬ (k :: τ) <:+ p.1) →
          (Seq.mono hk L).map hs₂.lf = Seq.mono hk' (L.map hs.lf) :=
        fun L hL => hs.lf_mono hs₂ (fun ρ => ¬ (k :: τ) <:+ ρ) hP hk' hedge hedge' hroot hk L hL
      have hsτ := Tree.ctxAt_slots hs.h0 hs.okS τ
      have hsτ' := Tree.ctxAt_slots hs.h0 hs.ok τ
      have hθ := (hs.okCoh τ).1
      have hc := (hs.okCoh τ).2
      have hle' := Tree.boxIn_le_addEdge (Γ₀ := Γ₀) hnone' hv'.birthsAt
      have hat := Subst.at_eq_mono_of (hk' τ)
        (hs.fam_agree hs₂ (fun ρ => ¬ (k :: τ) <:+ ρ) hP hk' hedge hedge' hroot τ
          (Tree.not_suffix_cons k τ))
      have e₁ : hs₂.lf ⟨k :: τ, WFF.mono hle φ⟩ = ⟨k :: τ, WFF.mono hle' (WFF.subst ι
          (hs.Fam τ).box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hsτ.boxIn hsτ'.boxIn φ)⟩ :=
        congrArg (Sigma.mk _) (WFF.subst_mono_eq hle hle' _ _ _ (hs₂.Fam (k :: τ)) _ _
          hsτ.boxIn (Tree.ctxAt_slots hs.h0 hs₂.okS _) hsτ'.boxIn
          (Tree.ctxAt_slots hs.h0 hs₂.ok _)
          (Subst.sim_mono_of hle' fun w U hl hw => by
            rw [hs₂.fam_box k τ w U hl ((hk τ).boxIn w U hw),
              Subst.box_eq_mono_of (hk' τ) hat w U hl hw, SubE.mono_mono]) φ)
      rw [List.map_cons, hm Δ hv.left, hm Θ hv.right, e₁] at ih'
      exact .boxR τ k hv' hle' (List.mem_map_of_mem (f := hs.lf) h) ih'
  | @serial n D Δ Θ hD τ k hv _ ih =>
      intro S' ι E N hs hN
      have hnone := hv.edge _ (List.suffix_refl _)
      have hw : ∀ j ρ y, k :: τ = j :: ρ → EdgeKind.box = .dia y →
          ∃ X, (D.ctxAt Γ₀ ρ).ref y = some (.VTypeDia X) := fun _ _ _ _ he => by cases he
      have hs₂ := hs.addEdge hnone .box hw
      have hv' := hs.vacant hv hN
      have hnone' := hv'.edge _ (List.suffix_refl _)
      have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hnone EdgeKind.box
      have hk' := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hnone' EdgeKind.box
      have ih' := ih hs₂ (hN.mono hk)
      have hP : ∀ j ρ, ¬ (k :: τ) <:+ (j :: ρ) → ¬ (k :: τ) <:+ ρ :=
        fun j ρ h h' => h (h'.trans (List.suffix_cons j ρ))
      have hedge : ∀ j ρ, ¬ (k :: τ) <:+ (j :: ρ) →
          (D.addEdge (k :: τ) .box).edge (j :: ρ) = D.edge (j :: ρ) := fun j ρ h => by
        rw [Tree.edge_addEdge, if_neg (fun he : j :: ρ = k :: τ => h (he ▸ List.suffix_refl _))]
      have hedge' : ∀ j ρ, ¬ (k :: τ) <:+ (j :: ρ) →
          (S'.addEdge (k :: τ) .box).edge (j :: ρ) = S'.edge (j :: ρ) := fun j ρ h => by
        rw [Tree.edge_addEdge, if_neg (fun he : j :: ρ = k :: τ => h (he ▸ List.suffix_refl _))]
      have hroot := hs.rootE_addEdge hnone .box hw (fun ρ => ¬ (k :: τ) <:+ ρ)
      have hm : ∀ L : Seq σ Γ₀ D, (∀ p ∈ L, ¬ (k :: τ) <:+ p.1) →
          (Seq.mono hk L).map hs₂.lf = Seq.mono hk' (L.map hs.lf) :=
        fun L hL => hs.lf_mono hs₂ (fun ρ => ¬ (k :: τ) <:+ ρ) hP hk' hedge hedge' hroot hk L hL
      rw [hm Δ hv.left, hm Θ hv.right] at ih'
      exact .serial hD τ k hv' ih'
  | @diaL n D Δ Θ τ k x hx ψ hv hle h _ ih =>
      intro S' ι E N hs hN
      have hθ := (hs.okCoh τ).1
      have hc := (hs.okCoh τ).2
      have hsτ := Tree.ctxAt_slots hs.h0 hs.okS τ
      have hsτ' := Tree.ctxAt_slots hs.h0 hs.ok τ
      have hw : ((hs.Fam τ).at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hx' : ∃ X, (S'.ctxAt Γ₀ τ).ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      have hnone := hv.edge _ (List.suffix_refl _)
      have hwx : ∀ j ρ y, k :: τ = j :: ρ → EdgeKind.dia x = .dia y →
          ∃ X, (D.ctxAt Γ₀ ρ).ref y = some (.VTypeDia X) := fun j ρ y hj he => by
        cases hj
        cases he
        exact hx
      have hs₂ := hs.addEdge hnone (.dia x) hwx
      have hv' := hs.vacant hv hN
      have hnone' := hv'.edge _ (List.suffix_refl _)
      have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hnone (EdgeKind.dia x)
      have hk' := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hnone' (EdgeKind.dia (ι x))
      have ih' := ih hs₂ ((hN.mono hk).cons_l _)
      have hP : ∀ j ρ, ¬ (k :: τ) <:+ (j :: ρ) → ¬ (k :: τ) <:+ ρ :=
        fun j ρ h h' => h (h'.trans (List.suffix_cons j ρ))
      have hedge : ∀ j ρ, ¬ (k :: τ) <:+ (j :: ρ) →
          (D.addEdge (k :: τ) (.dia x)).edge (j :: ρ) = D.edge (j :: ρ) := fun j ρ h => by
        rw [Tree.edge_addEdge, if_neg (fun he : j :: ρ = k :: τ => h (he ▸ List.suffix_refl _))]
      have hedge' : ∀ j ρ, ¬ (k :: τ) <:+ (j :: ρ) →
          (S'.addEdge (k :: τ) (.dia (ι x))).edge (j :: ρ) = S'.edge (j :: ρ) := fun j ρ h => by
        rw [Tree.edge_addEdge, if_neg (fun he : j :: ρ = k :: τ => h (he ▸ List.suffix_refl _))]
      have hroot := hs.rootE_addEdge hnone (.dia x) hwx (fun ρ => ¬ (k :: τ) <:+ ρ)
      have hm : ∀ L : Seq σ Γ₀ D, (∀ p ∈ L, ¬ (k :: τ) <:+ p.1) →
          (Seq.mono hk L).map hs₂.lf = Seq.mono hk' (L.map hs.lf) :=
        fun L hL => hs.lf_mono hs₂ (fun ρ => ¬ (k :: τ) <:+ ρ) hP hk' hedge hedge' hroot hk L hL
      have hle' := Tree.diaIn_le_addEdge (Γ₀ := Γ₀) hnone' hv'.birthsAt (ι x)
      have hat := Subst.at_eq_mono_of (hk' τ)
        (hs.fam_agree hs₂ (fun ρ => ¬ (k :: τ) <:+ ρ) hP hk' hedge hedge' hroot τ
          (Tree.not_suffix_cons k τ))
      have he₂ : (D.addEdge (k :: τ) (.dia x)).edge (k :: τ) = some (.dia x) := by
        rw [Tree.edge_addEdge, if_pos rfl]
      have e₁ : hs₂.lf ⟨k :: τ, WFF.mono hle ψ⟩ = ⟨k :: τ, WFF.mono hle' (WFF.subst ι
          ((hs.Fam τ).dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
          (hsτ.diaIn x) (hsτ'.diaIn _) ψ)⟩ :=
        congrArg (Sigma.mk _) (WFF.subst_mono_eq hle hle' _ _ _ (hs₂.Fam (k :: τ)) _ _
          (hsτ.diaIn x) (Tree.ctxAt_slots hs.h0 hs₂.okS _) (hsτ'.diaIn _)
          (Tree.ctxAt_slots hs.h0 hs₂.ok _)
          (Subst.sim_mono_of hle' fun w U hl hw => by
            rw [hs₂.fam_dia he₂ w U hl ((hk τ).diaIn x w U hw),
              Subst.dia_eq_mono_of (hk' τ) hat x (ι x) w U hl hw, SubE.mono_mono]) ψ)
      rw [List.map_cons, hm Δ hv.left, hm Θ hv.right, e₁] at ih'
      exact .diaL τ k (ι x) hx' hv' hle' (List.mem_map_of_mem (f := hs.lf) h) ih'

end GKN

/-! ## Where the family is the identity -/

namespace GKN

variable {σ : Signature} {Γ₀ : Ctx} [ModalSys.NoOpt]

/-- The tree's `◇`-edges have witnesses of their parents' contexts (every rule keeps this; the
    empty tree has it). -/
def Tree.WitOK (Γ₀ : Ctx) (D : Tree) : Prop :=
  ∀ k ρ x, D.edge (k :: ρ) = some (.dia x) → ∃ X, (D.ctxAt Γ₀ ρ).ref x = some (.VTypeDia X)

theorem Tree.witOK_empty : (({} : Tree)).WitOK Γ₀ := fun _ _ _ he => by cases he

theorem Tree.WitOK.addBirth {D : Tree} (h : D.WitOK Γ₀) {r : Root} (hu : D.Fresh Γ₀ r)
    (τ : Lab) (T : VarType) : (D.addBirth τ r T).WitOK Γ₀ := fun k ρ x he =>
  (h k ρ x he).imp fun _ hX => (Tree.ctxAt_addBirth hu τ T ρ).ref hX

theorem Tree.WitOK.addEdge {D : Tree} (h : D.WitOK Γ₀) {c : Lab} (hc : D.edge c = none)
    (e : EdgeKind)
    (hw : ∀ k ρ x, c = k :: ρ → e = .dia x → ∃ X, (D.ctxAt Γ₀ ρ).ref x = some (.VTypeDia X)) :
    (D.addEdge c e).WitOK Γ₀ := fun k ρ x he => by
  rw [Tree.edge_addEdge] at he
  split at he
  · rename_i hk
    cases he
    exact (hw k ρ x hk.symm rfl).imp fun _ hX => (Tree.ctxAt_addEdge hc _ ρ).ref hX
  · exact (h k ρ x he).imp fun _ hX => (Tree.ctxAt_addEdge hc e ρ).ref hX

theorem Tree.mem_birthsAt_addBirth {D : Tree} {ρ τ : Lab} {r : Root} {T : VarType}
    {b : Root × VarType} (hb : b ∈ D.birthsAt ρ) : b ∈ (D.addBirth τ r T).birthsAt ρ := by
  rw [Tree.birthsAt_addBirth]
  split_ifs
  · exact List.mem_cons_of_mem _ hb
  · exact hb

variable {S S' : Tree} {ι : VarSymb → VarSymb} {E : (ρ : Lab) → Root → SubE σ (S'.ctxAt Γ₀ ρ)}
  {N : List Lab}

/-- ⭐**Where the roots go to themselves and the witnesses are fixed, the family is the identity**,
    on any tree `D₀` with the source's edges. -/
theorem SubSetup.fam_ren (hs : SubSetup Γ₀ S S' ι E N) (D₀ : Tree)
    (hedge : ∀ k ρ, D₀.edge (k :: ρ) = S.edge (k :: ρ))
    (hr : ∀ ρ r U, (D₀.ctxAt Γ₀ ρ) (.root r) = some U → hs.rootE ρ r = .ren (.root r))
    (hι : ∀ k ρ x, S.edge (k :: ρ) = some (.dia x) → ι x = x) :
    ∀ ρ v U, v.lastProj = false → (D₀.ctxAt Γ₀ ρ) v = some U → hs.Fam ρ v = .ren v := by
  intro ρ
  induction ρ with
  | nil =>
      intro v U _ hv
      cases v with
      | root r => rw [hs.fam_root]; exact hr [] r U hv
      | step w s => rfl
  | cons k ρ ih =>
      intro v U hl hv
      cases v with
      | root r => rw [hs.fam_root]; exact hr _ r U hv
      | step w s =>
          have hat : ∀ w U, (D₀.ctxAt Γ₀ ρ).ref w = some U → (hs.Fam ρ).at w = .ren w :=
            fun w U h => by
              rw [Subst.at_eq_mono_of (Ctx.Le.refl _) (θ' := Subst.idRen (S'.ctxAt Γ₀ ρ)) ih w U h,
                Subst.at_idRen]
              rfl
          simp only [Tree.ctxAt] at hv
          rcases Ctx.inserts_cases hv with ⟨b, _, he, _⟩ | hv
          · cases he
          rw [hs.fam_step]
          by_cases hd : ∃ x, S.edge (k :: ρ) = some (.dia x)
          · obtain ⟨x, he⟩ := hd
            have hιx := hι k ρ x he
            rw [hs.viewS_dia he (hs.edge_dia he)]
            rw [Tree.view_dia ((hedge k ρ).trans he)] at hv
            cases s with
            | dia =>
                change (if w = x then (match (D₀.ctxAt Γ₀ ρ).ref x with
                  | some (.VTypeDia X) => some X | _ => none) else none) = some U at hv
                split_ifs at hv with hwx
                cases hX : (D₀.ctxAt Γ₀ ρ).ref x with
                | none => rw [hX] at hv; cases hv
                | some X =>
                    change SubE.mono _ (if w = x then ((hs.Fam ρ).at x).diaBody (ι x)
                      else SubE.hide) = _
                    rw [if_pos hwx, hat x X hX]
                    change SubE.ren (.step (ι x) .dia) = _
                    rw [hιx, hwx]
            | box =>
                obtain ⟨hk, hw⟩ := Ctx.boxIn_box (Γ := D₀.ctxAt Γ₀ ρ) hv
                change SubE.mono _ ((((hs.Fam ρ).at w).unbox).mono _) = _
                rw [hat w _ hw]
                change SubE.ren w.inner = _
                rw [VarSymb.inner_box hk]
            | keep =>
                change SubE.mono _ ((((hs.Fam ρ).at w).keepE).mono _) = _
                rw [hat w _ (Ctx.boxIn_keep (Γ := D₀.ctxAt Γ₀ ρ) hv).2.1]
                rfl
            | fst => cases hv
            | snd => cases hv
            | here => cases hv
            | «at» => cases hv
          · push_neg at hd
            rw [hs.viewS_box hd]
            rw [Tree.view_of_not_dia (D := D₀) fun x h => hd x ((hedge k ρ).symm.trans h)] at hv
            cases s with
            | box =>
                obtain ⟨hk, hw⟩ := Ctx.boxIn_box (Γ := D₀.ctxAt Γ₀ ρ) hv
                change SubE.mono _ ((hs.Fam ρ).at w).unbox = _
                rw [hat w _ hw]
                change SubE.ren w.inner = _
                rw [VarSymb.inner_box hk]
            | keep =>
                change SubE.mono _ ((hs.Fam ρ).at w).keepE = _
                rw [hat w _ (Ctx.boxIn_keep (Γ := D₀.ctxAt Γ₀ ρ) hv).2.1]
                rfl
            | dia => cases hv
            | fst => cases hv
            | snd => cases hv
            | here => cases hv
            | «at» => cases hv

theorem SubSetup.at_ren (hs : SubSetup Γ₀ S S' ι E N) (D₀ : Tree)
    (hedge : ∀ k ρ, D₀.edge (k :: ρ) = S.edge (k :: ρ))
    (hr : ∀ ρ r U, (D₀.ctxAt Γ₀ ρ) (.root r) = some U → hs.rootE ρ r = .ren (.root r))
    (hι : ∀ k ρ x, S.edge (k :: ρ) = some (.dia x) → ι x = x) (ρ : Lab) :
    ∀ v U, (D₀.ctxAt Γ₀ ρ).ref v = some U → (hs.Fam ρ).at v = .ren v := fun v U h => by
  rw [Subst.at_eq_mono_of (Ctx.Le.refl _) (θ' := Subst.idRen (S'.ctxAt Γ₀ ρ))
    (hs.fam_ren D₀ hedge hr hι ρ) v U h, Subst.at_idRen]
  rfl

/-! ## Weakening by a birth -/

/-- The setup weakening by a birth: everything to itself. -/
theorem SubSetup.weaken {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀) (h0 : Γ₀.SlotsFrom 0)
    {v : ℕ} (hv : D.Fresh Γ₀ (.free v)) (τ : Lab) (T : VarType) :
    SubSetup Γ₀ D (D.addBirth τ (.free v) T) id (fun _ r => SubE.ren (σ := σ) (.root r))
      [τ] where
  okS := hok
  ok := hok.addBirth hv τ T
  h0 := h0
  edge k ρ := by
    change D.edge (k :: ρ) = (D.edge (k :: ρ)).map _
    cases D.edge (k :: ρ) with
    | none => rfl
    | some e => exact congrArg some (EdgeKind.ren_id e).symm
  wit := hW
  eok ρ b hb := by
    change ((D.addBirth τ (.free v) T).ctxAt Γ₀ ρ).ref (.root b.1) = some b.2
    rw [Ctx.ref_nonproj _ rfl]
    exact Tree.ctxAt_root (hok.addBirth hv τ T) (Tree.mem_birthsAt_addBirth hb)
  eidx _ _ _ _ := rfl
  fix _ _ := rfl
  births b hb := by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Or.inr (List.mem_singleton_self _)
    · exact Or.inl ⟨b, hb, rfl⟩

theorem SubSetup.lf_weaken {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀) (h0 : Γ₀.SlotsFrom 0)
    {v : ℕ} (hv : D.Fresh Γ₀ (.free v)) (τ : Lab) (T : VarType) (L : Seq σ Γ₀ D) :
    L.map (SubSetup.weaken hok hW h0 hv τ T).lf = Seq.mono (Tree.ctxAt_addBirth hv τ T) L := by
  refine List.map_congr_left fun p _ => ?_
  obtain ⟨ρ, ψ⟩ := p
  refine congrArg (Sigma.mk ρ) ?_
  dsimp only
  exact WFF.subst_ren (Tree.ctxAt_addBirth hv τ T ρ) _ _ _ _ _
    ((SubSetup.weaken hok hW h0 hv τ T).at_ren D (fun _ _ => rfl)
      (fun _ _ _ _ => by unfold SubSetup.rootE; split <;> rfl) (fun _ _ _ _ => rfl) ρ) ψ

/-- ⭐**Weakening by a birth** of a tree-fresh name at a node carrying a formula, height kept
    (eigenvariables renamed as needed). -/
theorem weakenBirth [Γ₀.Presented] {n : ℕ} {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀)
    {Δ Θ : Seq σ Γ₀ D} (p : GKN σ Γ₀ n D Δ Θ) {v : ℕ} (hv : D.Fresh Γ₀ (.free v)) (τ : Lab)
    (T : VarType) (hτ : (∃ q ∈ Δ, q.1 = τ) ∨ (∃ q ∈ Θ, q.1 = τ)) :
    GKN σ Γ₀ n (D.addBirth τ (.free v) T) (Seq.mono (Tree.ctxAt_addBirth hv τ T) Δ)
      (Seq.mono (Tree.ctxAt_addBirth hv τ T) Θ) := by
  have q := GKN.subst p (SubSetup.weaken hok hW Ctx.NoSlots.slots hv τ T) (fun ρ hρ => by
    rw [List.mem_singleton] at hρ
    subst hρ
    exact hτ)
  rwa [SubSetup.lf_weaken hok hW Ctx.NoSlots.slots hv τ T,
    SubSetup.lf_weaken hok hW Ctx.NoSlots.slots hv τ T] at q

/-! ## ⭐Unbinding an eigenvariable: cut's quantifier instance -/

open Classical in
/-- The entries unbinding `u`, born at `τ₀`, by `t`. -/
noncomputable def unbindE (D : Tree) (τ₀ : Lab) (u : ℕ) {T : VarType} {a : Ann T}
    (t : Term σ (D.ctxAt Γ₀ τ₀) T a) (ρ : Lab) (r : Root) : SubE σ (D.ctxAt Γ₀ ρ) :=
  if h : ρ = τ₀ ∧ r = .free u then .tm (Term.mono (by rw [h.1]; exact Ctx.Le.refl _) t)
  else .ren (.root r)

/-- ⭐**The setup that unbinds** a tree-fresh `u`, born at `τ₀`, by a term at `τ₀`. -/
theorem SubSetup.unbind {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀) (h0 : Γ₀.SlotsFrom 0)
    {u : ℕ} (hu : D.Fresh Γ₀ (.free u)) (τ₀ : Lab) (T : VarType) {a : Ann T}
    (t : Term σ (D.ctxAt Γ₀ τ₀) T a) :
    SubSetup Γ₀ (D.addBirth τ₀ (.free u) T) D (Subst.singleIdx (.free u) (.tm t))
      (unbindE D τ₀ u t) [] where
  okS := hok.addBirth hu τ₀ T
  ok := hok
  h0 := h0
  edge k ρ := by
    change D.edge (k :: ρ) = Option.map _ (D.edge (k :: ρ))
    cases he : D.edge (k :: ρ) with
    | none => rfl
    | some e =>
        cases e with
        | box => rfl
        | dia x =>
            obtain ⟨X, hX⟩ := hW k ρ x he
            have hrt := (hu.at ρ).rt_ne hX
            change some (EdgeKind.dia x) =
              some (EdgeKind.dia (Subst.singleIdx (.free u) (.tm t) x))
            unfold Subst.singleIdx
            rw [if_neg hrt]
  wit k ρ x he := (hW k ρ x he).imp fun _ hX => (Tree.ctxAt_addBirth hu τ₀ T ρ).ref hX
  eok ρ b hb := by
    rw [Tree.birthsAt_addBirth] at hb
    split_ifs at hb with hρ
    · rcases List.mem_cons.mp hb with rfl | hb
      · unfold unbindE
        rw [dif_pos ⟨hρ, rfl⟩]
        rfl
      · unfold unbindE
        rw [dif_neg fun h => hu.births _ (Tree.mem_birthsAt.mp hb) h.2]
        change (D.ctxAt Γ₀ ρ).ref (.root b.1) = some b.2
        rw [Ctx.ref_nonproj _ rfl]
        exact Tree.ctxAt_root hok hb
    · unfold unbindE
      rw [dif_neg fun h => hu.births _ (Tree.mem_birthsAt.mp hb) h.2]
      change (D.ctxAt Γ₀ ρ).ref (.root b.1) = some b.2
      rw [Ctx.ref_nonproj _ rfl]
      exact Tree.ctxAt_root hok hb
  eidx ρ b p hb := by
    have hold : b ∈ D.birthsAt ρ → (unbindE D τ₀ u t ρ b.1).idxAlong p =
        Subst.singleIdx (.free u) (.tm t) ((VarSymb.root b.1).ext p) := fun hb => by
      have hne := hu.births _ (Tree.mem_birthsAt.mp hb)
      unfold unbindE
      rw [dif_neg fun h => hne h.2]
      change (VarSymb.root b.1).ext p = _
      unfold Subst.singleIdx
      rw [VarSymb.ext_rt, if_neg (show (VarSymb.root b.1).rt ≠ .free u from hne)]
    rw [Tree.birthsAt_addBirth] at hb
    split_ifs at hb with hρ
    · rcases List.mem_cons.mp hb with rfl | hb
      · unfold unbindE
        rw [dif_pos ⟨hρ, rfl⟩]
        change a.idxAt p = Subst.singleIdx (.free u) (.tm t) _
        unfold Subst.singleIdx
        split
        · rw [VarSymb.ext_path]
          rfl
        · rename_i hc
          exact absurd (by rw [VarSymb.ext_rt]; rfl) hc
      · exact hold hb
    · exact hold hb
  fix w hw := by
    unfold Subst.singleIdx
    rw [if_neg (fun h => hw (τ₀, .free u, T) List.mem_cons_self h.symm)]
  births b hb := Or.inl ⟨b, List.mem_cons_of_mem _ hb, rfl⟩

variable {τ₀ : Lab} {u : ℕ} {T : VarType} {a : Ann T}

/-- Unbinding fixes the roots and witnesses of the tree without the birth. -/
theorem unbind_ren {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀) (h0 : Γ₀.SlotsFrom 0)
    (hu : D.Fresh Γ₀ (.free u)) (t : Term σ (D.ctxAt Γ₀ τ₀) T a) :
    (∀ ρ r U, (D.ctxAt Γ₀ ρ) (.root r) = some U →
      (SubSetup.unbind hok hW h0 hu τ₀ T t).rootE ρ r = .ren (.root r)) ∧
    (∀ k ρ x, (D.addBirth τ₀ (.free u) T).edge (k :: ρ) = some (.dia x) →
      Subst.singleIdx (.free u) (.tm t) x = x) := by
  refine ⟨fun ρ r U hr => ?_, fun k ρ x he => ?_⟩
  · have hne : r ≠ .free u := fun he => by
      rw [he, (hu.at ρ).root] at hr
      cases hr
    unfold SubSetup.rootE unbindE
    split
    · rw [dif_neg fun h => hne h.2]
    · rfl
  · obtain ⟨X, hX⟩ := hW k ρ x he
    unfold Subst.singleIdx
    rw [if_neg ((hu.at ρ).rt_ne hX)]

/-- Unbinding leaves a side over the tree without the birth alone. -/
theorem lf_unbind {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀) (h0 : Γ₀.SlotsFrom 0)
    (hu : D.Fresh Γ₀ (.free u)) (t : Term σ (D.ctxAt Γ₀ τ₀) T a) (L : Seq σ Γ₀ D) :
    (Seq.mono (Tree.ctxAt_addBirth hu τ₀ T) L).map (SubSetup.unbind hok hW h0 hu τ₀ T t).lf =
      L := by
  unfold Seq.mono
  rw [List.map_map]
  conv_rhs => rw [← List.map_id L]
  refine List.map_congr_left fun p _ => ?_
  obtain ⟨ρ, ψ⟩ := p
  change (SubSetup.unbind hok hW h0 hu τ₀ T t).lf ⟨ρ, WFF.mono _ ψ⟩ = ⟨ρ, ψ⟩
  refine congrArg (Sigma.mk ρ) ?_
  dsimp only
  have hren := unbind_ren hok hW h0 hu t
  rw [WFF.subst_mono _ _ _ _ (Tree.ctxAt_slots h0 hok ρ),
    WFF.subst_ren (Ctx.Le.refl _) _ _ _ _ _
      ((SubSetup.unbind hok hW h0 hu τ₀ T t).at_ren D (fun _ _ => rfl) hren.1 hren.2 ρ),
    WFF.mono_refl]

/-- Unbinding the eigenvariable's formula is instantiating its binding. -/
theorem lf_unbind_new {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀) (h0 : Γ₀.SlotsFrom 0)
    (hsτ : (D.ctxAt Γ₀ τ₀).SlotsFrom 0) (hu : D.Fresh Γ₀ (.free u))
    {φ : WFF σ ((D.ctxAt Γ₀ τ₀).insert (.free u) T) 0}
    (hle : ((D.ctxAt Γ₀ τ₀).insert (.free u) T).Le ((D.addBirth τ₀ (.free u) T).ctxAt Γ₀ τ₀))
    (t : Term σ (D.ctxAt Γ₀ τ₀) T a) :
    (SubSetup.unbind hok hW h0 hu τ₀ T t).lf ⟨τ₀, WFF.mono hle φ⟩ =
      ⟨τ₀, WFF.instantiate hsτ t (WFF.bindFree u (hu.at τ₀) hsτ T φ)⟩ := by
  haveI : (D.ctxAt Γ₀ τ₀).NoSlots := ⟨hsτ⟩
  have hs := SubSetup.unbind hok hW h0 hu τ₀ T t
  have hren := unbind_ren hok hW h0 hu t
  have hfr := hu.at τ₀
  have hsim : Subst.Sim ((D.ctxAt Γ₀ τ₀).insert (.free u) T)
      ((SubSetup.unbind hok hW h0 hu τ₀ T t).Fam τ₀)
      ((Subst.single (.free u) (.tm t)).mono (Ctx.Le.refl _)) := by
    refine Subst.sim_mono_of _ fun v U hl hv => ?_
    by_cases hvr : v = .root (.free u)
    · subst hvr
      have hb : ∃ U, (Root.free u, U) ∈ (D.addBirth τ₀ (.free u) T).birthsAt τ₀ :=
        ⟨T, by rw [Tree.birthsAt_addBirth, if_pos rfl]; exact List.mem_cons_self⟩
      rw [SubSetup.fam_root, Subst.single_root,
        (SubSetup.unbind hok hW h0 hu τ₀ T t).rootE_born hb]
      unfold unbindE
      rw [dif_pos ⟨rfl, rfl⟩]
      rfl
    · rw [Subst.single_ne _ hvr, (SubSetup.unbind hok hW h0 hu τ₀ T t).fam_ren D
        (fun _ _ => rfl) hren.1 hren.2 τ₀ v U hl (Ctx.insert_ne_some hv hvr)]
      rfl
  have e₁ := WFF.subst_mono_eq hle (Ctx.Le.refl _) (Subst.single (.free u) (.tm t))
    (Subst.ok_single (Ctx.Le.refl _) rfl) (Subst.coh_single hfr (Ctx.Le.refl _) rfl)
    ((SubSetup.unbind hok hW h0 hu τ₀ T t).Fam τ₀) (hs.okCoh τ₀).1 (hs.okCoh τ₀).2
    (hsτ.insertFree u T) (Tree.ctxAt_slots h0 hs.okS τ₀) hsτ (Tree.ctxAt_slots h0 hs.ok τ₀) hsim φ
  rw [WFF.mono_refl] at e₁
  have e₂ := WFF.instantiate_bindFree (Ctx.Le.refl (D.ctxAt Γ₀ τ₀)) u hfr t φ
  rw [WFF.mono_refl] at e₂
  rw [SubSetup.lf_mk, e₁, ← e₂]

/-- ⭐**Cut's quantifier instance, `∀`**: from an `allR` premise over the tree with the
    eigenvariable `u` born at `τ₀`, the instance at any term of `τ₀`, over the tree without the
    birth, of the same height. -/
theorem instance_allR [Γ₀.Presented] {n : ℕ} {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀)
    {Δ Θ : Seq σ Γ₀ D} (τ₀ : Lab) (hsτ : (D.ctxAt Γ₀ τ₀).SlotsFrom 0)
    {u : ℕ} (T : VarType) (hu : D.Fresh Γ₀ (.free u))
    {φ : WFF σ ((D.ctxAt Γ₀ τ₀).insert (.free u) T) 0}
    (hle : ((D.ctxAt Γ₀ τ₀).insert (.free u) T).Le ((D.addBirth τ₀ (.free u) T).ctxAt Γ₀ τ₀))
    (p : GKN σ Γ₀ n (D.addBirth τ₀ (.free u) T) (Seq.mono (Tree.ctxAt_addBirth hu τ₀ T) Δ)
      (⟨τ₀, WFF.mono hle φ⟩ :: Seq.mono (Tree.ctxAt_addBirth hu τ₀ T) Θ))
    {a : Ann T} (t : Term σ (D.ctxAt Γ₀ τ₀) T a) :
    GKN σ Γ₀ n D Δ
      (⟨τ₀, WFF.instantiate hsτ t (WFF.bindFree u (hu.at τ₀) hsτ T φ)⟩ :: Θ) := by
  have q := GKN.subst p (SubSetup.unbind hok hW Ctx.NoSlots.slots hu τ₀ T t)
    (fun _ h => absurd h List.not_mem_nil)
  rw [List.map_cons, lf_unbind hok hW Ctx.NoSlots.slots hu t,
    lf_unbind hok hW Ctx.NoSlots.slots hu t,
    lf_unbind_new hok hW Ctx.NoSlots.slots hsτ hu hle t] at q
  exact q

/-- ⭐**Cut's quantifier instance, `∃`**: as `instance_allR`, from an `exL` premise. -/
theorem instance_exL [Γ₀.Presented] {n : ℕ} {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀)
    {Δ Θ : Seq σ Γ₀ D} (τ₀ : Lab) (hsτ : (D.ctxAt Γ₀ τ₀).SlotsFrom 0)
    {u : ℕ} (T : VarType) (hu : D.Fresh Γ₀ (.free u))
    {φ : WFF σ ((D.ctxAt Γ₀ τ₀).insert (.free u) T) 0}
    (hle : ((D.ctxAt Γ₀ τ₀).insert (.free u) T).Le ((D.addBirth τ₀ (.free u) T).ctxAt Γ₀ τ₀))
    (p : GKN σ Γ₀ n (D.addBirth τ₀ (.free u) T)
      (⟨τ₀, WFF.mono hle φ⟩ :: Seq.mono (Tree.ctxAt_addBirth hu τ₀ T) Δ)
      (Seq.mono (Tree.ctxAt_addBirth hu τ₀ T) Θ))
    {a : Ann T} (t : Term σ (D.ctxAt Γ₀ τ₀) T a) :
    GKN σ Γ₀ n D
      (⟨τ₀, WFF.instantiate hsτ t (WFF.bindFree u (hu.at τ₀) hsτ T φ)⟩ :: Δ) Θ := by
  have q := GKN.subst p (SubSetup.unbind hok hW Ctx.NoSlots.slots hu τ₀ T t)
    (fun _ h => absurd h List.not_mem_nil)
  rw [List.map_cons, lf_unbind hok hW Ctx.NoSlots.slots hu t,
    lf_unbind hok hW Ctx.NoSlots.slots hu t,
    lf_unbind_new hok hW Ctx.NoSlots.slots hsτ hu hle t] at q
  exact q

end GKN

end V12M
