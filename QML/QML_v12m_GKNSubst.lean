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

With T off (`[ModalSys.NoT]`); `Opt` either way: a node's family opens what the node opens
(`openS`), and re-opening an opened witness changes nothing (`openS_agree`).
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
  /-- The target opens each source opening's image. -/
  opens : ∀ ρ, ∀ o ∈ S.opensAt ρ, (S'.ctxAt Γ₀ ρ).Opened o.1 (ι o.2)
  /-- The target's openings are at the source's opened nodes or in `N`. -/
  opensT : ∀ o ∈ S'.opens, (∃ o₀ ∈ S.opens, o₀.1 = o.1) ∨ o.1 ∈ N

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

/-- A substitution into the view of a witness of a kind. -/
def _root_.V12M.Subst.optInK {Δ : Ctx} (θ : Subst σ Δ) :
    (κ : WitKind) → (y z : VarSymb) → Subst σ (Δ.optInK κ z)
  | .arrow, y, z => θ.optIn y z
  | .ident, y, z => θ.optInT y z

theorem _root_.V12M.Subst.mono_wit {Δ Δ' : Ctx} (θ : Subst σ Δ) (h : Δ.Le Δ') (y : VarSymb) :
    (θ.mono h).wit y = (θ.wit y).mono h := rfl

theorem _root_.V12M.Subst.rename_wit {Δ : Ctx} (θ : Subst σ Δ) (u u' : ℕ) (T : VarType)
    (h : Δ (.root (.free u')) = none) (y : VarSymb) :
    (θ.rename u u' T h).wit y = (θ.wit y).mono (Ctx.le_insert h T) := rfl

theorem _root_.V12M.Subst.optIn_wit {Δ : Ctx} (θ : Subst σ Δ) (x z y : VarSymb) :
    (θ.optIn x z).wit y = (θ.wit y).mono (Ctx.le_optIn Δ z) := rfl

theorem _root_.V12M.Subst.dia_wit {Δ : Ctx} (θ : Subst σ Δ) (x z y : VarSymb) :
    (θ.dia x z).wit y = (θ.box.wit y).mono (Ctx.le_boxIn_diaIn Δ z) := rfl

theorem _root_.V12M.Subst.optInK_wit {Δ : Ctx} (θ : Subst σ Δ) :
    ∀ (κ : WitKind) (x z y : VarSymb),
      (θ.optInK κ x z).wit y = (θ.wit y).mono (Ctx.le_optInK Δ κ z)
  | .arrow, _, _, _ => rfl
  | .ident, _, _, _ => rfl

theorem _root_.V12M.Subst.optInK_ne {Δ : Ctx} (θ : Subst σ Δ) :
    ∀ (κ : WitKind) (x z : VarSymb) {v : VarSymb}, v ≠ .step x κ.step →
      θ.optInK κ x z v = (θ v).mono (Ctx.le_optInK Δ κ z)
  | .arrow, _, z, _, h => Subst.optIn_ne _ z h
  | .ident, _, z, _, h => Subst.optInT_ne _ z h

/-- ⭐**The family's openings**: each source opening `(κ, y)` opened in the substitution at its
    image `ι y`, which the target opens already, so the result weakens back into the target. -/
noncomputable def openS {Δ : Ctx} (ι : VarSymb → VarSymb) :
    (L : List (WitKind × VarSymb)) → (∀ o ∈ L, Δ.Opened o.1 (ι o.2)) → Subst σ Δ → Subst σ Δ
  | [], _, θ => θ
  | o :: L, h, θ =>
      ((openS ι L (fun o' h' => h o' (List.mem_cons_of_mem _ h')) θ).optInK o.1 o.2
        (ι o.2)).mono (Ctx.optInK_le_of (Ctx.Le.refl Δ) (h o List.mem_cons_self))

/-- ⭐**The family**: at each node, the edge's view of the parent's and the node's roots by
    `rootE` (the base), then the node's openings (`openS`). -/
noncomputable def SubSetup.Fam (hs : SubSetup Γ₀ S S' ι E N) :
    (ρ : Lab) → Subst σ (S'.ctxAt Γ₀ ρ)
  | [] => openS ι (S.opensAt []) (hs.opens [])
      ((Subst.idRen _).rootsRen (hs.rootE []))
  | k :: ρ => openS ι (S.opensAt (k :: ρ)) (hs.opens (k :: ρ))
      ((hs.viewS k ρ (hs.Fam ρ)).rootsRen (hs.rootE (k :: ρ)))

/-- The family before the node's openings. -/
noncomputable def SubSetup.base (hs : SubSetup Γ₀ S S' ι E N) :
    (ρ : Lab) → Subst σ (S'.ctxAt Γ₀ ρ)
  | [] => (Subst.idRen _).rootsRen (hs.rootE [])
  | k :: ρ => (hs.viewS k ρ (hs.Fam ρ)).rootsRen (hs.rootE (k :: ρ))

theorem SubSetup.fam_eq (hs : SubSetup Γ₀ S S' ι E N) (ρ : Lab) :
    hs.Fam ρ = openS ι (S.opensAt ρ) (hs.opens ρ) (hs.base ρ) := by
  cases ρ <;> rfl

theorem _root_.V12M.SubE.mono_self {Δ : Ctx} (h : Δ.Le Δ) : ∀ e : SubE σ Δ, e.mono h = e
  | .hide => rfl
  | .ren _ => rfl
  | .tm t => congrArg SubE.tm (Term.mono_refl h t)

theorem _root_.V12M.WitE.mono_self {Δ : Ctx} (h : Δ.Le Δ) : ∀ e : WitE σ Δ, e.mono h = e
  | .hide => rfl
  | .ren _ => rfl
  | .tm z b => congrArg (WitE.tm z) (Term.mono_refl _ b)

theorem openS_wit {Δ : Ctx} (ι : VarSymb → VarSymb) :
    ∀ (L : List (WitKind × VarSymb)) (h : ∀ o ∈ L, Δ.Opened o.1 (ι o.2)) (θ : Subst σ Δ)
      (y : VarSymb), (openS ι L h θ).wit y = θ.wit y
  | [], _, _, _ => rfl
  | ⟨κ, x⟩ :: L, h, θ, y => by
      have ih := openS_wit ι L (fun o' h' => h o' (List.mem_cons_of_mem _ h')) θ y
      rw [openS, Subst.mono_wit, Subst.optInK_wit, WitE.mono_mono, WitE.mono_self, ih]

/-- Away from the openings' contents the openings change nothing. -/
theorem openS_ne {Δ : Ctx} (ι : VarSymb → VarSymb) :
    ∀ (L : List (WitKind × VarSymb)) (h : ∀ o ∈ L, Δ.Opened o.1 (ι o.2)) (θ : Subst σ Δ)
      (v : VarSymb), (∀ o ∈ L, v ≠ .step o.2 o.1.step) → openS ι L h θ v = θ v
  | [], _, _, _, _ => rfl
  | ⟨κ, x⟩ :: L, h, θ, v, hv => by
      have ih := openS_ne ι L (fun o' h' => h o' (List.mem_cons_of_mem _ h')) θ v
        (fun o' h' => hv o' (List.mem_cons_of_mem _ h'))
      have hne := hv ⟨κ, x⟩ List.mem_cons_self
      rw [openS, Subst.mono_apply, Subst.optInK_ne _ _ _ _ hne, SubE.mono_mono, SubE.mono_self,
        ih]

/-- An arrow opening's content: the body of the witness's entry. -/
theorem openS_content {Δ : Ctx} (ι : VarSymb → VarSymb) :
    ∀ (L : List (WitKind × VarSymb)) (h : ∀ o ∈ L, Δ.Opened o.1 (ι o.2)) (θ : Subst σ Δ)
      (y : VarSymb) (hy : (WitKind.arrow, y) ∈ L),
      openS ι L h θ (.step y .dia) =
        ((θ.wit y).optBody (ι y)).mono (Ctx.optInK_le_of (Γ := Δ) (Ξ := Δ) (κ := .arrow)
          (y := ι y) (Ctx.Le.refl Δ) (h (.arrow, y) hy))
  | [], _, _, _, hy => by simp at hy
  | ⟨κ, x⟩ :: L, h, θ, y, hy => by
      by_cases he : κ = .arrow ∧ x = y
      · obtain ⟨rfl, rfl⟩ := he
        rw [openS, Subst.mono_apply]
        change SubE.mono _ ((Subst.optIn (openS ι L _ θ) x (ι x)) (.step x .dia)) = _
        rw [Subst.optIn_content, openS_wit]
      · have hy' : (WitKind.arrow, y) ∈ L := by
          rcases List.mem_cons.mp hy with h' | h'
          · exact absurd ⟨(Prod.mk.inj h').1.symm, (Prod.mk.inj h').2.symm⟩ he
          · exact h'
        have ih := openS_content ι L (fun o' h' => h o' (List.mem_cons_of_mem _ h')) θ y hy'
        have hne : VarSymb.step y .dia ≠ .step x κ.step := by
          cases κ with
          | arrow => exact fun e => he ⟨rfl, (VarSymb.step.inj e).1.symm⟩
          | ident => exact fun e => by cases e
        rw [openS, Subst.mono_apply, Subst.optInK_ne _ _ _ _ hne, SubE.mono_mono, SubE.mono_self,
          ih]

/-- ⭐**Openings that take effect keep a substitution one**, for the opened context. -/
theorem openS_okCoh {Δ Γ : Ctx} {ι : VarSymb → VarSymb} :
    ∀ (L : List (WitKind × VarSymb)) (h : ∀ o ∈ L, Δ.Opened o.1 (ι o.2)) (θ : Subst σ Δ),
      Subst.Ok Γ θ → Subst.Coh ι Γ θ → Γ.OptsEff L →
      Subst.Ok (Γ.optInsK L) (openS ι L h θ) ∧ Subst.Coh ι (Γ.optInsK L) (openS ι L h θ)
  | [], _, _, h₁, h₂, _ => ⟨h₁, h₂⟩
  | ⟨κ, y⟩ :: L, h, θ, h₁, h₂, ⟨he, hO, X, hX⟩ => by
      obtain ⟨ih₁, ih₂⟩ := openS_okCoh L (fun o' h' => h o' (List.mem_cons_of_mem _ h')) θ h₁ h₂ he
      cases κ with
      | arrow =>
          exact ⟨Subst.ok_mono (Subst.ok_optIn ih₁ hO hX (ih₂.wit hO y X hX [])) _,
            Subst.coh_mono (Subst.coh_optIn ih₁ ih₂ hO hX) _⟩
      | ident =>
          exact ⟨Subst.ok_mono (Subst.ok_optInT ih₁ hX (ih₂ y _ (Ctx.witT_spec hX).2.2 [])) _,
            Subst.coh_mono (Subst.coh_optInT ih₁ ih₂ hX) _⟩

/-- ⭐**At the addresses the context declared before its openings, the openings change
    nothing**: re-opening an opened witness is the identity (`Subst.Coh.opened`). -/
theorem openS_agree {Δ Γ : Ctx} {ι : VarSymb → VarSymb} :
    ∀ (L : List (WitKind × VarSymb)) (h : ∀ o ∈ L, Δ.Opened o.1 (ι o.2)) (θ : Subst σ Δ),
      Subst.Ok Γ θ → Subst.Coh ι Γ θ → Γ.OptsEff L →
      ∀ v U, Γ v = some U → openS ι L h θ v = θ v
  | [], _, _, _, _, _, _, _, _ => rfl
  | ⟨κ, y⟩ :: L, h, θ, h₁, h₂, ⟨he, hO, X, hX⟩, v, U, hv => by
      have hL : ∀ o ∈ L, Δ.Opened o.1 (ι o.2) := fun o' h' => h o' (List.mem_cons_of_mem _ h')
      obtain ⟨ih₁, ih₂⟩ := openS_okCoh L hL θ h₁ h₂ he
      have ih := openS_agree L hL θ h₁ h₂ he v U hv
      have hv' : (Γ.optInsK L) v = some U := Ctx.le_optInsK Γ L v U hv
      cases κ with
      | arrow =>
          change SubE.mono _ ((Subst.optIn (openS ι L hL θ) y (ι y)) v) = θ v
          by_cases hc : v = .step y .dia
          · subst hc
            have hUX : U = X := by
              rcases (Γ.optInsK L).wit_dia y X hX with h' | h'
              · rw [show (Γ.optInsK L) (.step y .dia) = (Γ.optInsK L).ty (.step y .dia) from rfl,
                  h'] at hv'
                cases hv'
              · rw [show (Γ.optInsK L) (.step y .dia) = (Γ.optInsK L).ty (.step y .dia) from rfl,
                  h'] at hv'
                exact (Option.some.inj hv').symm
            subst hUX
            rw [Subst.optIn_content,
              ← ih₂.opened hO y U (ι y) hX hv' (ih₂.wit hO y U hX []), SubE.mono_mono,
              SubE.mono_self, ih]
          · rw [Subst.optIn_ne _ _ hc, SubE.mono_mono, SubE.mono_self, ih]
      | ident =>
          change SubE.mono _ ((Subst.optInT (openS ι L hL θ) y (ι y)) v) = θ v
          by_cases hc : v = .step y .at
          · subst hc
            obtain ⟨-, -, hr⟩ := Ctx.witT_spec hX
            have h₃ := (Γ.optInsK L).at_coh y U hv'
            rw [Ctx.refAll_of_ref _ y hr] at h₃
            cases h₃
            rw [Subst.optInT_content,
              ← ih₂.openedT y X (ι y) hX hv' (ih₂ y _ hr []), SubE.mono_mono, SubE.mono_self, ih]
          · rw [Subst.optInT_ne _ _ hc, SubE.mono_mono, SubE.mono_self, ih]

theorem SubSetup.fam_root (hs : SubSetup Γ₀ S S' ι E N) (ρ : Lab) (r : Root) :
    hs.Fam ρ (.root r) = hs.rootE ρ r := by
  rw [hs.fam_eq, openS_ne _ _ _ _ _ fun _ _ h => by cases h]
  cases ρ <;> rfl

theorem SubSetup.base_step (hs : SubSetup Γ₀ S S' ι E N) (k : ℕ) (ρ : Lab) (w : VarSymb)
    (s : Step) : hs.base (k :: ρ) (.step w s) = hs.viewS k ρ (hs.Fam ρ) (.step w s) := rfl

theorem SubSetup.base_wit_cons (hs : SubSetup Γ₀ S S' ι E N) (k : ℕ) (ρ : Lab) (y : VarSymb) :
    (hs.base (k :: ρ)).wit y = (hs.viewS k ρ (hs.Fam ρ)).wit y := rfl

theorem _root_.V12M.Subst.box_wit {Δ : Ctx} (θ : Subst σ Δ) (y : VarSymb) :
    θ.box.wit y = (θ.at y).toWit := rfl

theorem _root_.V12M.Subst.dia_content {Δ : Ctx} (θ : Subst σ Δ) (x z : VarSymb) :
    θ.dia x z (.step x .dia) = (θ.at x).diaBody z := if_pos rfl

theorem SubSetup.wit_fam (hs : SubSetup Γ₀ S S' ι E N) (ρ : Lab) (y : VarSymb) :
    (hs.Fam ρ).wit y = (hs.base ρ).wit y := by
  rw [hs.fam_eq, openS_wit]

end GKN

/-! ## The family is a substitution at every node -/

namespace GKN

variable {σ : Signature} {Γ₀ : Ctx} {S S' : Tree} {ι : VarSymb → VarSymb}
  {E : (ρ : Lab) → Root → SubE σ (S'.ctxAt Γ₀ ρ)} {N : List Lab}

variable [ModalSys.NoT]

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

/-- ⭐**A node's roots by `er`**: a substitution for a context is one for it with declarations
    inserted, given the declarations' entries (and `er` agreeing at the context's own roots). -/
theorem rootsRen_okCoh {Δ Γ : Ctx} {θ : Subst σ Δ} {er : Root → SubE σ Δ}
    {L : List (Root × VarType)} (h₁ : Subst.Ok Γ θ) (h₂ : Subst.Coh ι Γ θ)
    (hroot : ∀ r U, Γ (.root r) = some U → er r = θ (.root r))
    (hL : ∀ b ∈ L, (er b.1).OkRef b.2 ∧ ∀ p, (er b.1).idxAlong p = ι ((VarSymb.root b.1).ext p)) :
    Subst.Ok (Γ.inserts L) (θ.rootsRen er) ∧ Subst.Coh ι (Γ.inserts L) (θ.rootsRen er) := by
  have hwit : (Γ.inserts L).wit = Γ.wit := Ctx.inserts_wit Γ L
  have hstep : ∀ w s U, (Γ.inserts L) (.step w s) = some U → Γ (.step w s) = some U := by
    intro w s U hv
    rcases Ctx.inserts_cases hv with ⟨b, _, he, _⟩ | hv
    · cases he
    · exact hv
  have hok : Subst.Ok (Γ.inserts L) (θ.rootsRen er) := by
    refine ⟨fun v U hlp hv => ?_, fun hO y X hy => h₁.wit hO y X (by rwa [hwit] at hy)⟩
    rcases Ctx.inserts_cases hv with ⟨b, hb, rfl, rfl⟩ | hv
    · exact (hL b hb).1
    · cases v with
      | root r =>
          change (er r).OkRef U
          rw [hroot r U hv]
          exact h₁ _ _ hlp hv
      | step w s => exact h₁ _ _ hlp hv
  refine ⟨hok, Subst.coh_of hok (fun v U hlp hv p => ?_)
    (fun hO y X hy p => h₂.wit hO y X (by rwa [hwit] at hy) p)
    (fun hO y X z hy hyd hz => h₂.opened hO y X z (by rwa [hwit] at hy) (hstep _ _ _ hyd) hz)
    (fun hO y X z hy hyd hz => h₂.openedTo hO y X z (by rwa [hwit] at hy) (hstep _ _ _ hyd) hz)
    (fun _ _ _ hy _ _ => (ModalSys.NoT.absurd (Ctx.witT_spec hy).1).elim)
    (fun _ _ _ hy _ _ => (ModalSys.NoT.absurd (Ctx.witT_spec hy).1).elim)⟩
  rcases Ctx.inserts_cases hv with ⟨b, hb, rfl, rfl⟩ | hv
  · exact (hL b hb).2 p
  · have e := h₂ v U (by rwa [Ctx.ref_nonproj _ hlp]) p
    rw [Subst.at_nonproj _ hlp] at e
    cases v with
    | root r =>
        change (er r).idxAlong p = _
        rw [hroot r U hv]
        exact e
    | step w s => exact e

/-- At the root, the identity renaming with the index map `ι`, which fixes `Γ₀`'s addresses. -/
theorem SubSetup.okCoh_id (hs : SubSetup Γ₀ S S' ι E N) (hle : Γ₀.Le (S'.ctxAt Γ₀ [])) :
    Subst.Ok Γ₀ (Subst.idRen (σ := σ) (S'.ctxAt Γ₀ [])) ∧
      Subst.Coh ι Γ₀ (Subst.idRen (σ := σ) (S'.ctxAt Γ₀ [])) := by
  have h₁ := Subst.ok_idRen.restrict (σ := σ) hle
  have h₂ := Subst.coh_idRen.restrict (σ := σ) hle
  refine ⟨h₁, Subst.coh_of h₁ (fun v U hlp hv p => ?_) (fun hO y X hy p => ?_)
    (fun hO y X z hy hyd hz => h₂.opened hO y X z hy hyd hz)
    (fun hO y X z hy hyd hz => h₂.openedTo hO y X z hy hyd hz)
    (fun _ _ _ hy _ _ => (ModalSys.NoT.absurd (Ctx.witT_spec hy).1).elim)
    (fun _ _ _ hy _ _ => (ModalSys.NoT.absurd (Ctx.witT_spec hy).1).elim)⟩
  · change (VarSymb.ext v p) = ι (v.ext p)
    exact (hs.fix0 hv p).symm
  · change (VarSymb.ext y p) = ι (y.ext p)
    refine (hs.fix _ fun b hb he => ?_).symm
    rw [VarSymb.ext_rt] at he
    rw [(hs.okS.fresh b hb).wit y he.symm] at hy
    cases hy

/-- The view's substitution is one for the child's view. -/
theorem SubSetup.viewS_okCoh (hs : SubSetup Γ₀ S S' ι E N) (k : ℕ) (ρ : Lab)
    (ih₁ : Subst.Ok (S.ctxAt Γ₀ ρ) (hs.Fam ρ)) (ih₂ : Subst.Coh ι (S.ctxAt Γ₀ ρ) (hs.Fam ρ)) :
    Subst.Ok (S.view (k :: ρ) (S.ctxAt Γ₀ ρ)) (hs.viewS k ρ (hs.Fam ρ)) ∧
      Subst.Coh ι (S.view (k :: ρ) (S.ctxAt Γ₀ ρ)) (hs.viewS k ρ (hs.Fam ρ)) := by
  by_cases hd : ∃ x, S.edge (k :: ρ) = some (.dia x)
  · obtain ⟨x, he⟩ := hd
    rw [hs.viewS_dia he (hs.edge_dia he), Tree.view_dia he]
    have hx := hs.wit k ρ x he
    have hw : ((hs.Fam ρ).at x).idxAlong [] = ι x := by
      obtain ⟨X, hX⟩ := hx
      exact ih₂.ty x _ hX []
    exact ⟨Subst.ok_mono (Subst.ok_dia ih₁ hx hw) _, Subst.coh_mono (Subst.coh_dia ih₁ ih₂ hx) _⟩
  · push_neg at hd
    rw [hs.viewS_box hd, Tree.view_of_not_dia hd]
    exact ⟨Subst.ok_mono (Subst.ok_box ih₁) _, Subst.coh_mono (Subst.coh_box ih₁ ih₂) _⟩

/-- The base is a substitution for the node's context before its openings, given the parent's
    family. -/
theorem SubSetup.baseOkCoh_of (hs : SubSetup Γ₀ S S' ι E N) :
    ∀ ρ, (∀ k ρ', ρ = k :: ρ' →
      Subst.Ok (S.ctxAt Γ₀ ρ') (hs.Fam ρ') ∧ Subst.Coh ι (S.ctxAt Γ₀ ρ') (hs.Fam ρ')) →
      Subst.Ok (S.preAt Γ₀ ρ) (hs.base ρ) ∧ Subst.Coh ι (S.preAt Γ₀ ρ) (hs.base ρ)
  | [], _ => by
      have hle : Γ₀.Le (S'.ctxAt Γ₀ []) := by
        simp only [Tree.ctxAt]
        exact (Ctx.le_inserts _ (Tree.birthsAt_pairwise hs.ok _)
          fun b hb => hs.ok.fresh _ (Tree.mem_birthsAt.mp hb)).trans (Ctx.le_optInsK _ _)
      obtain ⟨h₁, h₂⟩ := hs.okCoh_id hle
      refine rootsRen_okCoh h₁ h₂ (fun r U hv => ?_) fun b hb => ?_
      · rw [hs.rootE_not (hs.not_born0 hv)]
        rfl
      · rw [hs.rootE_born ⟨b.2, hb⟩]
        exact ⟨hs.eok [] b hb, fun p => hs.eidx [] b p hb⟩
  | k :: ρ, ih => by
      obtain ⟨h₁, h₂⟩ := hs.viewS_okCoh k ρ (ih k ρ rfl).1 (ih k ρ rfl).2
      refine rootsRen_okCoh h₁ h₂ (fun r U hv => ?_) fun b hb => ?_
      · exfalso
        unfold Tree.view at hv
        split at hv <;> cases (show (none : Option VarType) = some U from hv)
      · rw [hs.rootE_born ⟨b.2, hb⟩]
        exact ⟨hs.eok _ b hb, fun p => hs.eidx _ b p hb⟩

/-- ⭐**The family is a substitution at every node**, with the index map `ι`. -/
theorem SubSetup.okCoh (hs : SubSetup Γ₀ S S' ι E N) :
    ∀ ρ, Subst.Ok (S.ctxAt Γ₀ ρ) (hs.Fam ρ) ∧ Subst.Coh ι (S.ctxAt Γ₀ ρ) (hs.Fam ρ)
  | [] => by
      obtain ⟨h₁, h₂⟩ := hs.baseOkCoh_of [] fun _ _ h => by cases h
      rw [hs.fam_eq]
      exact openS_okCoh _ _ _ h₁ h₂ (hs.okS.eff [])
  | k :: ρ => by
      obtain ⟨h₁, h₂⟩ := hs.baseOkCoh_of (k :: ρ) fun _ _ h => by
        cases h
        exact hs.okCoh ρ
      rw [hs.fam_eq]
      exact openS_okCoh _ _ _ h₁ h₂ (hs.okS.eff (k :: ρ))

theorem SubSetup.baseOkCoh (hs : SubSetup Γ₀ S S' ι E N) (ρ : Lab) :
    Subst.Ok (S.preAt Γ₀ ρ) (hs.base ρ) ∧ Subst.Coh ι (S.preAt Γ₀ ρ) (hs.base ρ) :=
  hs.baseOkCoh_of ρ fun _ ρ' h => by subst h; exact hs.okCoh ρ'

/-- ⭐**At the addresses a node declared before its openings, the family is the base.** -/
theorem SubSetup.fam_base (hs : SubSetup Γ₀ S S' ι E N) (ρ : Lab) {v : VarSymb} {U : VarType}
    (hv : (S.preAt Γ₀ ρ) v = some U) : hs.Fam ρ v = hs.base ρ v := by
  rw [hs.fam_eq]
  exact openS_agree _ _ _ (hs.baseOkCoh ρ).1 (hs.baseOkCoh ρ).2 (hs.okS.eff ρ) v U hv

/-- At a child, at the view's addresses, the family is the view of the parent's. -/
theorem SubSetup.fam_step (hs : SubSetup Γ₀ S S' ι E N) (k : ℕ) (ρ : Lab) {w : VarSymb}
    {s : Step} {U : VarType} (hv : (S.view (k :: ρ) (S.ctxAt Γ₀ ρ)) (.step w s) = some U) :
    hs.Fam (k :: ρ) (.step w s) = hs.viewS k ρ (hs.Fam ρ) (.step w s) :=
  hs.fam_base (k :: ρ) (Tree.view_le_preAt hs.okS k ρ _ _ hv)


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

theorem _root_.V12M.Ctx.OptsEff.opt {Γ : Ctx} :
    ∀ {L : List (WitKind × VarSymb)}, Γ.OptsEff L → ∀ {o}, o ∈ L → ModalSys.Opt = true
  | [], _, _, h => by simp at h
  | _ :: L, ⟨he, hO, _⟩, o, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact hO
      · exact Ctx.OptsEff.opt he h

/-- Agreement at the visible addresses and at the witnesses is similarity. -/
theorem _root_.V12M.Subst.sim_mono_of {Γ Δ Δ' : Ctx} {θ : Subst σ Δ} {θ' : Subst σ Δ'}
    (h : Δ.Le Δ') (hvis : ∀ v U, v.lastProj = false → Γ v = some U → θ' v = (θ v).mono h)
    (hwit : ∀ y X, Γ.wit y = some X → θ'.wit y = (θ.wit y).mono h) :
    Subst.Sim Γ θ' (θ.mono h) :=
  Subst.sim_of (fun v U hl hv => by rw [hvis v U hl hv]; exact .refl _)
    (fun _ y X hy => by rw [hwit y X hy]; exact .refl _)

/-! ## The family along edges -/

theorem SubSetup.viewS_wit (hs : SubSetup Γ₀ S S' ι E N) (k : ℕ) (ρ : Lab)
    (θ : Subst σ (S'.ctxAt Γ₀ ρ)) (y : VarSymb) :
    (hs.viewS k ρ θ).wit y = ((θ.box).wit y).mono (Tree.boxIn_le_child hs.ok k ρ) := by
  unfold SubSetup.viewS
  split
  · split
    · rw [Subst.mono_wit, Subst.dia_wit, WitE.mono_mono]
    · rfl
  · rfl

/-- The child's witnesses' entries are the parent's `□` view's. -/
theorem SubSetup.fam_wit (hs : SubSetup Γ₀ S S' ι E N) (k : ℕ) (ρ : Lab) (y : VarSymb) :
    (hs.Fam (k :: ρ)).wit y = ((hs.Fam ρ).box.wit y).mono (Tree.boxIn_le_child hs.ok k ρ) := by
  rw [hs.wit_fam, ← hs.viewS_wit]
  rfl

/-- ⭐**Along any edge, the child's family is the parent's `□` view** at the `□` view's
    addresses. -/
theorem SubSetup.fam_box (hs : SubSetup Γ₀ S S' ι E N) (k : ℕ) (ρ : Lab) :
    ∀ v U, v.lastProj = false → (S.ctxAt Γ₀ ρ).boxIn v = some U →
      hs.Fam (k :: ρ) v = ((hs.Fam ρ).box v).mono (Tree.boxIn_le_child hs.ok k ρ) := by
  intro v U hl hv
  cases v with
  | root r => cases (show (none : Option VarType) = some U from hv)
  | step w s =>
      rw [hs.fam_step k ρ (Tree.boxIn_le_view _ _ _ _ hv)]
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
      rw [hs.fam_step k ρ (by rwa [Tree.view_dia he]), hs.viewS_dia he (hs.edge_dia he)]
      rfl

theorem SubSetup.fam_dia_wit (hs : SubSetup Γ₀ S S' ι E N) {k : ℕ} {ρ : Lab} {x : VarSymb}
    (he : S.edge (k :: ρ) = some (.dia x)) (y : VarSymb) :
    (hs.Fam (k :: ρ)).wit y =
      (((hs.Fam ρ).dia x (ι x)).wit y).mono (Tree.diaIn_le_child hs.ok (hs.edge_dia he)) := by
  rw [hs.fam_wit, Subst.dia_wit, WitE.mono_mono]

/-- A child's witnesses are the parent's `□` view's: `Opt` is on. -/
theorem _root_.V12M.GKN.Tree.wit_child_opt {Γ₀ : Ctx} {D : Tree} {k : ℕ} {ρ : Lab} {y : VarSymb}
    {X : VarType} (hy : (D.ctxAt Γ₀ (k :: ρ)).wit y = some X) :
    ModalSys.Opt = true ∧ (D.ctxAt Γ₀ ρ).ref y = some (.VTypeDia X) := by
  rw [Tree.ctxAt_wit] at hy
  unfold Tree.view at hy
  split at hy <;> exact Ctx.boxIn_wit.mp hy

/-- ⭐**At a child the `◇_x` view fits, the child's family is the parent's `◇_x` view**: along a
    `◇_x`-edge (`fam_dia`), or where `x` is opened (its content by `Subst.toWit_optBody`). -/
theorem SubSetup.fam_fit (hs : SubSetup Γ₀ S S' ι E N) {k : ℕ} {ρ : Lab} {x : VarSymb}
    {e : EdgeKind} (he : S.edge (k :: ρ) = some e)
    (hf : (EdgeKind.dia x).Fits (S.ctxAt Γ₀ (k :: ρ)) e)
    (hx : ∃ X, (S.ctxAt Γ₀ ρ).ref x = some (.VTypeDia X))
    (hle : ((S'.ctxAt Γ₀ ρ).diaIn (ι x)).Le (S'.ctxAt Γ₀ (k :: ρ))) :
    ∀ v U, v.lastProj = false → ((S.ctxAt Γ₀ ρ).diaIn x) v = some U →
      hs.Fam (k :: ρ) v = (((hs.Fam ρ).dia x (ι x)) v).mono hle := by
  intro v U hl hv
  by_cases hd : S.edge (k :: ρ) = some (.dia x)
  · exact hs.fam_dia hd v U hl hv
  have hθ := (hs.okCoh ρ).1
  have hc := (hs.okCoh ρ).2
  match v with
  | .step w .dia =>
      change (if w = x then
        (match (S.ctxAt Γ₀ ρ).ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some U at hv
      split_ifs at hv with hwx
      subst hwx
      obtain ⟨X, hX⟩ := hx
      rw [hX] at hv
      obtain rfl : X = U := Option.some.inj hv
      rcases hf with hf | ⟨x', hx', ho⟩
      · cases e with
        | box => exact hf.elim
        | dia z =>
            change w = z at hf
            subst hf
            exact absurd he hd
      · cases hx'
        obtain ⟨X', hX', hd'⟩ := ho
        obtain ⟨hO, hr⟩ := Tree.wit_child_opt hX'
        rw [hX] at hr
        cases hr
        have hmem : (WitKind.arrow, w) ∈ S.opensAt (k :: ρ) := by
          rw [Tree.ctxAt_eq_pre] at hd'
          rcases Ctx.optInsK_cases hd' with hd' | ⟨⟨κ, y⟩, ho, he'⟩
          · exfalso
            simp only [Tree.preAt] at hd'
            rcases Ctx.inserts_cases hd' with ⟨b, _, hb, _⟩ | hd'
            · cases hb
            · have hv' : S.edge (k :: ρ) ≠ some (.dia w) := hd
              unfold Tree.view at hd'
              split at hd'
              · rename_i z hz
                have hzw : z ≠ w := fun e' => hv' (e' ▸ hz)
                change (if w = z then _ else none) = some X at hd'
                rw [if_neg (Ne.symm hzw)] at hd'
                cases hd'
              · cases hd'
          · cases κ with
            | ident => cases he'
            | arrow =>
                cases he'
                exact ho
        have hw' : ((hs.Fam ρ).at w).idxAlong [] = ι w := hc.ty w _ hX []
        obtain ⟨Y, hY⟩ := SubE.ref_witness (Subst.okRef_at hθ hX) hw'
        rw [hs.fam_eq, openS_content _ _ _ _ _ hmem, hs.base_wit_cons, hs.viewS_wit,
          ← WitE.optBody_mono, SubE.mono_mono, Subst.box_wit, Subst.dia_content,
          SubE.toWit_optBody hO (ι w) (Subst.okRef_at hθ hX)
            (Ctx.le_diaIn_boxIn_optIn hO hY), SubE.mono_mono]
  | .step w .box =>
      have hb : (S.ctxAt Γ₀ ρ).boxIn (.step w .box) = some U := hv
      rw [hs.fam_box k ρ _ U hl hb]
      have e := Subst.dia_eq_box_mono (hs.Fam ρ) x (ι x) (.step w .box) U
        (by rwa [Ctx.ref_nonproj _ hl])
      rw [Subst.at_nonproj _ hl, Subst.at_nonproj _ hl] at e
      rw [e, SubE.mono_mono]
  | .step w .keep =>
      have hb : (S.ctxAt Γ₀ ρ).boxIn (.step w .keep) = some U := hv
      rw [hs.fam_box k ρ _ U hl hb]
      have e := Subst.dia_eq_box_mono (hs.Fam ρ) x (ι x) (.step w .keep) U
        (by rwa [Ctx.ref_nonproj _ hl])
      rw [Subst.at_nonproj _ hl, Subst.at_nonproj _ hl] at e
      rw [e, SubE.mono_mono]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv
  | .step _ .at => cases hv

/-- The target fits the image of a fitting child. -/
theorem SubSetup.fits (hs : SubSetup Γ₀ S S' ι E N) {k : ℕ} {ρ : Lab} {x : VarSymb}
    {e : EdgeKind} (hf : (EdgeKind.dia x).Fits (S.ctxAt Γ₀ (k :: ρ)) e) :
    (EdgeKind.dia (ι x)).Fits (S'.ctxAt Γ₀ (k :: ρ)) (e.ren ι) := by
  rcases hf with hf | ⟨x', hx', ho⟩
  · cases e with
    | box => exact hf.elim
    | dia z =>
        change x = z at hf
        subst hf
        exact .inl rfl
  · cases hx'
    obtain ⟨X, hX, hd⟩ := ho
    have hO := (Tree.wit_child_opt hX).1
    have hc := (hs.okCoh (k :: ρ)).2
    obtain ⟨Z, hZ, hZd⟩ := hc.openedTo hO x X _ hX hd (hc.wit hO x X hX [])
    exact .inr ⟨ι x, rfl, Z, hZ, hZd⟩

/-! ## The family as the tree grows -/

theorem _root_.V12M.WitE.optBody_mono_congr {Δ Δ' : Ctx} (e : WitE σ Δ) {z₁ z₂ : VarSymb}
    (hz : z₁ = z₂) (b₁ : (Δ.optIn z₁).Le Δ') (b₂ : (Δ.optIn z₂).Le Δ') :
    (e.optBody z₁).mono b₁ = (e.optBody z₂).mono b₂ := by
  subst hz
  rfl

/-- ⭐**The family agrees with the smaller tree's, weakened**, at every node of a parent-closed
    set on which the edges (source and target) agree, the roots' entries agree, the nodes before
    their openings grow and the openings are kept: at the addresses and at the witnesses. -/
theorem SubSetup.fam_agree {S₁ S₁' S₂ S₂' : Tree} {ι₁ ι₂ : VarSymb → VarSymb}
    {E₁ : (ρ : Lab) → Root → SubE σ (S₁'.ctxAt Γ₀ ρ)}
    {E₂ : (ρ : Lab) → Root → SubE σ (S₂'.ctxAt Γ₀ ρ)} {N₁ N₂ : List Lab}
    (hs₁ : SubSetup Γ₀ S₁ S₁' ι₁ E₁ N₁) (hs₂ : SubSetup Γ₀ S₂ S₂' ι₂ E₂ N₂)
    (P : Lab → Prop) (hP : ∀ k ρ, P (k :: ρ) → P ρ)
    (hle : ∀ ρ, (S₁'.ctxAt Γ₀ ρ).Le (S₂'.ctxAt Γ₀ ρ))
    (hedge : ∀ k ρ, P (k :: ρ) → S₂.edge (k :: ρ) = S₁.edge (k :: ρ))
    (hedge' : ∀ k ρ, P (k :: ρ) → S₂'.edge (k :: ρ) = S₁'.edge (k :: ρ))
    (hroot : ∀ ρ, P ρ → ∀ r U, (S₁.ctxAt Γ₀ ρ) (.root r) = some U →
      hs₂.rootE ρ r = (hs₁.rootE ρ r).mono (hle ρ))
    (hpre : ∀ ρ, P ρ → (S₁.preAt Γ₀ ρ).Le (S₂.preAt Γ₀ ρ))
    (hopen : ∀ ρ, P ρ → ∀ o ∈ S₁.opensAt ρ, o ∈ S₂.opensAt ρ) :
    ∀ ρ, P ρ → (∀ v U, v.lastProj = false → (S₁.ctxAt Γ₀ ρ) v = some U →
      hs₂.Fam ρ v = (hs₁.Fam ρ v).mono (hle ρ)) ∧
      (∀ y X, (S₁.ctxAt Γ₀ ρ).wit y = some X →
        (hs₂.Fam ρ).wit y = ((hs₁.Fam ρ).wit y).mono (hle ρ)) := by
  intro ρ hρ
  -- the bases agree, at the addresses and witnesses before the openings
  have hbase : (∀ v U, v.lastProj = false → (S₁.preAt Γ₀ ρ) v = some U →
      hs₂.base ρ v = (hs₁.base ρ v).mono (hle ρ)) ∧
      (∀ y X, (S₁.preAt Γ₀ ρ).wit y = some X →
        (hs₂.base ρ).wit y = ((hs₁.base ρ).wit y).mono (hle ρ)) := by
    cases ρ with
    | nil =>
        refine ⟨fun v U _ hv => ?_, fun y X _ => rfl⟩
        cases v with
        | root r =>
            have e₁ := hs₁.fam_root [] r
            have e₂ := hs₂.fam_root [] r
            rw [hs₁.fam_eq, openS_ne _ _ _ _ _ fun _ _ h => by cases h] at e₁
            rw [hs₂.fam_eq, openS_ne _ _ _ _ _ fun _ _ h => by cases h] at e₂
            rw [e₁, e₂]
            exact hroot [] hρ r U (Ctx.le_optInsK _ _ _ _ hv)
        | step w s => rfl
    | cons k ρ =>
        obtain ⟨ih, ihw⟩ := SubSetup.fam_agree hs₁ hs₂ P hP hle hedge hedge' hroot hpre hopen ρ
          (hP k ρ hρ)
        have hat := Subst.at_eq_mono_of (hle ρ) ih
        refine ⟨fun v U hl hv => ?_, fun y X hy => ?_⟩
        · cases v with
          | root r =>
              have e₁ := hs₁.fam_root (k :: ρ) r
              have e₂ := hs₂.fam_root (k :: ρ) r
              rw [hs₁.fam_eq, openS_ne _ _ _ _ _ fun _ _ h => by cases h] at e₁
              rw [hs₂.fam_eq, openS_ne _ _ _ _ _ fun _ _ h => by cases h] at e₂
              rw [e₁, e₂]
              exact hroot _ hρ r U (Ctx.le_optInsK _ _ _ _ hv)
          | step w s =>
              simp only [Tree.preAt] at hv
              rcases Ctx.inserts_cases hv with ⟨b, _, he, _⟩ | hv
              · cases he
              rw [hs₁.base_step, hs₂.base_step]
              by_cases hd : ∃ x, S₁.edge (k :: ρ) = some (.dia x)
              · obtain ⟨x, he₁⟩ := hd
                have he₂ := (hedge k ρ hρ).trans he₁
                have he₁' := hs₁.edge_dia he₁
                have he₂' := (hedge' k ρ hρ).trans he₁'
                rw [hs₂.viewS_dia he₂ he₂', hs₁.viewS_dia he₁ he₁']
                rw [Tree.view_dia he₁] at hv
                change (((hs₂.Fam ρ).dia x (ι₁ x)) _).mono _ =
                  ((((hs₁.Fam ρ).dia x (ι₁ x)) _).mono _).mono _
                rw [Subst.dia_eq_mono_of (hle ρ) hat x _ _ U hl hv, SubE.mono_mono,
                  SubE.mono_mono]
              · push_neg at hd
                have hd₂ : ∀ x, S₂.edge (k :: ρ) ≠ some (.dia x) := fun x h =>
                  hd x ((hedge k ρ hρ).symm.trans h)
                rw [hs₂.viewS_box hd₂, hs₁.viewS_box hd]
                rw [Tree.view_of_not_dia hd] at hv
                change (((hs₂.Fam ρ).box) _).mono _ = ((((hs₁.Fam ρ).box) _).mono _).mono _
                rw [Subst.box_eq_mono_of (hle ρ) hat _ U hl hv, SubE.mono_mono, SubE.mono_mono]
        · have hy' : (S₁.ctxAt Γ₀ ρ).boxIn.wit y = some X := by
            simp only [Tree.preAt] at hy
            rw [Ctx.inserts_wit] at hy
            unfold Tree.view at hy
            split at hy <;> exact hy
          obtain ⟨_, hr⟩ := Ctx.boxIn_wit.mp hy'
          have e₁ := hs₁.fam_wit k ρ y
          have e₂ := hs₂.fam_wit k ρ y
          rw [hs₁.wit_fam] at e₁
          rw [hs₂.wit_fam] at e₂
          rw [e₁, e₂]
          change ((hs₂.Fam ρ).at y).toWit.mono _ = (((hs₁.Fam ρ).at y).toWit.mono _).mono _
          rw [hat y _ hr, SubE.toWit_mono]
          simp only [WitE.mono_mono]
  obtain ⟨hb, hbw⟩ := hbase
  have hwit : ∀ y X, (S₁.ctxAt Γ₀ ρ).wit y = some X → (S₁.preAt Γ₀ ρ).wit y = some X :=
    fun y X hy => by rwa [Tree.ctxAt_eq_pre, Ctx.optInsK_wit] at hy
  refine ⟨fun v U hl hv => ?_, fun y X hy => ?_⟩
  · rw [Tree.ctxAt_eq_pre] at hv
    rcases Ctx.optInsK_cases hv with hv | ⟨⟨κ, y⟩, ho, rfl⟩
    · rw [hs₁.fam_base ρ hv, hs₂.fam_base ρ (hpre ρ hρ _ _ hv)]
      exact hb _ U hl hv
    · obtain ⟨X, hX, -⟩ := hs₁.okS.opened ρ _ ho
      cases κ with
      | ident => exact (ModalSys.NoT.absurd (Ctx.witT_spec hX).1).elim
      | arrow =>
          have hy := hwit y X hX
          have ew := hbw y X hy
          have hO := Ctx.OptsEff.opt (hs₁.okS.eff ρ) ho
          have hι : ι₂ y = ι₁ y := by
            have c₁ := (hs₁.baseOkCoh ρ).2.wit hO y X hy []
            have c₂ := (hs₂.baseOkCoh ρ).2.wit hO y X ((hpre ρ hρ).wit y X hy) []
            rw [ew, WitE.idxAlong_mono, c₁] at c₂
            exact c₂.symm
          change hs₂.Fam ρ (.step y .dia) = (hs₁.Fam ρ (.step y .dia)).mono (hle ρ)
          rw [hs₁.fam_eq, hs₂.fam_eq, openS_content _ _ _ _ _ ho,
            openS_content _ _ _ _ _ (hopen ρ hρ _ ho), ew, ← WitE.optBody_mono,
            SubE.mono_mono, SubE.mono_mono]
          exact WitE.optBody_mono_congr _ hι _ _
  · rw [hs₁.wit_fam, hs₂.wit_fam]
    exact hbw y X (hwit y X hy)

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
    (hpre : ∀ ρ, P ρ → (S₁.preAt Γ₀ ρ).Le (S₂.preAt Γ₀ ρ))
    (hopen : ∀ ρ, P ρ → ∀ o ∈ S₁.opensAt ρ, o ∈ S₂.opensAt ρ)
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
      (hs₁.fam_agree hs₂ P hP hle hedge hedge' hroot hpre hopen ρ (hL _ hp)).1
      (hs₁.fam_agree hs₂ P hP hle hedge hedge' hroot hpre hopen ρ (hL _ hp)).2) φ)

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
  opens ρ o ho := by
    obtain ⟨X, hX, -⟩ := hs.okS.opened ρ o ho
    have hrt : o.2.rt ≠ .free v := by
      obtain ⟨κ, y⟩ := o
      cases κ with
      | arrow =>
          intro he
          have := (hv.at ρ).wit y he
          change (S.ctxAt Γ₀ ρ).wit y = some X at hX
          rw [this] at hX
          cases hX
      | ident => exact (hv.at ρ).rt_ne (Ctx.witT_spec hX).2.2
    have e : VarSymb.renameIdx ι v v' o.2 = ι o.2 := by
      unfold VarSymb.renameIdx
      rw [if_neg hrt]
    rw [e]
    exact (hs.opens ρ o ho).mono (Tree.ctxAt_addBirth hv' τ T ρ)
  opensT := hs.opensT

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
  okS := hs.okS.addEdge hc e
  ok := hs.ok.addEdge (hs.edge_none hc) _
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
  opens ρ o ho := (hs.opens ρ o ho).mono (Tree.ctxAt_addEdge (hs.edge_none hc) (e.ren ι) ρ)
  opensT := hs.opensT

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
  opens o ho := by
    rcases hs.opensT o ho with ⟨o₀, ho₀, e⟩ | hn
    · rw [← e]
      exact hv.opens o₀ ho₀
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

/-- A source witness's image is a target witness. -/
theorem SubSetup.wit_img (hs : SubSetup Γ₀ S S' ι E N) (hO : ModalSys.Opt = true) {τ : Lab}
    {y : VarSymb} {X : VarType} (hX : (S.ctxAt Γ₀ τ).wit y = some X) :
    ∃ X', (S'.ctxAt Γ₀ τ).wit (ι y) = some X' :=
  WitE.wit_of ((hs.okCoh τ).1.wit hO y X hX) ((hs.okCoh τ).2.wit hO y X hX [])

/-- The entries after a new opening: weakened. -/
noncomputable def SubSetup.EOpen (E : (ρ : Lab) → Root → SubE σ (S'.ctxAt Γ₀ ρ)) (τ : Lab)
    (κ : WitKind) (z : VarSymb) :
    (ρ : Lab) → Root → SubE σ ((S'.addOpen τ κ z).ctxAt Γ₀ ρ) := fun ρ r =>
  (E ρ r).mono (Tree.ctxAt_addOpen τ κ z ρ)

/-- ⭐**The setup survives a new arrow opening**, its witness renamed. -/
theorem SubSetup.addOpen (hs : SubSetup Γ₀ S S' ι E N) (hO : ModalSys.Opt = true) {τ : Lab}
    {y : VarSymb} {X : VarType} (hX : (S.ctxAt Γ₀ τ).wit y = some X) :
    SubSetup Γ₀ (S.addOpen τ .arrow y) (S'.addOpen τ .arrow (ι y)) ι
      (SubSetup.EOpen E τ .arrow (ι y)) N where
  okS := hs.okS.addOpen (κ := .arrow) hO hX
  ok := hs.ok.addOpen (κ := .arrow) hO (hs.wit_img hO hX).choose_spec
  h0 := hs.h0
  edge := hs.edge
  wit k ρ x he := (hs.wit k ρ x he).imp fun _ hX => (Tree.ctxAt_addOpen τ .arrow y ρ).ref hX
  eok ρ b hb := SubE.okRef_mono _ (hs.eok ρ b hb)
  eidx ρ b p hb := by
    unfold SubSetup.EOpen
    rw [SubE.idxAlong_mono]
    exact hs.eidx ρ b p hb
  fix := hs.fix
  births := hs.births
  opens ρ o ho := by
    rw [Tree.opensAt_addOpen] at ho
    split_ifs at ho with hρ
    · subst hρ
      rcases List.mem_cons.mp ho with rfl | ho
      · rw [Tree.ctxAt_addOpen_self]
        exact Ctx.opened_self (κ := .arrow) (hs.wit_img hO hX).choose_spec
      · exact (hs.opens _ o ho).mono (Tree.ctxAt_addOpen _ _ _ _)
    · exact (hs.opens ρ o ho).mono (Tree.ctxAt_addOpen _ _ _ _)
  opensT o ho := by
    rcases List.mem_cons.mp ho with rfl | ho
    · exact Or.inl ⟨(τ, .arrow, y), List.mem_cons_self, rfl⟩
    · exact (hs.opensT o ho).imp_left fun ⟨o₀, h, e⟩ => ⟨o₀, List.mem_cons_of_mem _ h, e⟩

theorem SubSetup.rootE_addOpen {D : Tree} (hs : SubSetup Γ₀ D S' ι E N) (hO : ModalSys.Opt = true)
    {τ : Lab} {y : VarSymb} {X : VarType} (hX : (D.ctxAt Γ₀ τ).wit y = some X) :
    ∀ ρ, True → ∀ r U, (D.ctxAt Γ₀ ρ) (.root r) = some U →
      (hs.addOpen hO hX).rootE ρ r =
        (hs.rootE ρ r).mono (Tree.ctxAt_addOpen τ .arrow (ι y) ρ) := by
  intro ρ _ r _ _
  by_cases hb : ∃ U, (r, U) ∈ D.birthsAt ρ
  · rw [hs.rootE_born hb, (hs.addOpen hO hX).rootE_born hb]
    rfl
  · rw [hs.rootE_not hb, (hs.addOpen hO hX).rootE_not hb]
    rfl

/-- At the new opening's node, the family is the old one opened. -/
theorem SubSetup.sim_addOpen {D : Tree} (hs : SubSetup Γ₀ D S' ι E N) (hO : ModalSys.Opt = true)
    {τ : Lab} {y : VarSymb} {X : VarType} (hX : (D.ctxAt Γ₀ τ).wit y = some X)
    (hle' : ((S'.ctxAt Γ₀ τ).optIn (ι y)).Le ((S'.addOpen τ .arrow (ι y)).ctxAt Γ₀ τ)) :
    Subst.Sim ((D.ctxAt Γ₀ τ).optIn y) ((hs.addOpen hO hX).Fam τ)
      (((hs.Fam τ).optIn y (ι y)).mono hle') := by
  have hag := hs.fam_agree (hs.addOpen hO hX) (fun _ => True) (fun _ _ _ => trivial)
    (Tree.ctxAt_addOpen τ .arrow (ι y)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (hs.rootE_addOpen hO hX) (fun ρ _ => Tree.preAt_addOpen τ .arrow y ρ)
    (fun ρ _ o ho => by
      rw [Tree.opensAt_addOpen]
      split_ifs
      · exact List.mem_cons_of_mem _ ho
      · exact ho) τ trivial
  refine Subst.sim_mono_of hle' (fun v U hl hv => ?_) (fun y' X' hy' => ?_)
  · by_cases hc : v = .step y .dia
    · subst hc
      have hmem : (WitKind.arrow, y) ∈ (D.addOpen τ .arrow y).opensAt τ := by
        rw [Tree.opensAt_addOpen, if_pos rfl]
        exact List.mem_cons_self
      rw [SubSetup.fam_eq, openS_content _ _ _ _ _ hmem, ← SubSetup.wit_fam, hag.2 y X hX,
        Subst.optIn_content, ← WitE.optBody_mono, SubE.mono_mono]
    · rw [Ctx.optIn_ne hc] at hv
      rw [hag.1 v U hl hv, Subst.optIn_ne _ _ hc, SubE.mono_mono]
  · rw [hag.2 y' X' hy', Subst.optIn_wit, WitE.mono_mono]

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
          (fun _ _ _ => rfl) (hs.rootE_addBirth hv hv' τ T')
          (fun ρ _ => Tree.preAt_addBirth hv τ T' ρ) (fun _ _ _ h => h) hk L
          (fun _ _ => trivial)
      have hfτ := hv.at τ
      have hfτ' := hv'.at τ
      have hsτ' := Tree.ctxAt_slots hs.h0 hs.ok τ
      have hθ := (hs.okCoh τ).1
      have hc := (hs.okCoh τ).2
      have hle' := Tree.insert_le_addBirth (D := S') (Γ₀ := Γ₀) hv' τ T'
      have hsim : Subst.Sim ((D.ctxAt Γ₀ τ).insert (.free v) T') (hs₂.Fam τ)
          (((hs.Fam τ).rename v v' T' hfτ'.root).mono hle') := by
        refine Subst.sim_mono_of hle' (fun w U hl hw => ?_) (fun y X hy => by
          rw [(hs.fam_agree hs₂ (fun _ => True) (fun _ _ _ => trivial) hk' (fun _ _ _ => rfl)
            (fun _ _ _ => rfl) (hs.rootE_addBirth hv hv' τ T')
            (fun ρ _ => Tree.preAt_addBirth hv τ T' ρ) (fun _ _ _ h => h) τ
            trivial).2 y X hy, Subst.rename_wit]
          simp only [WitE.mono_mono])
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
          · rw [(hs.fam_agree hs₂ (fun _ => True) (fun _ _ _ => trivial) hk' (fun _ _ _ => rfl)
              (fun _ _ _ => rfl) (hs.rootE_addBirth hv hv' τ T')
              (fun ρ _ => Tree.preAt_addBirth hv τ T' ρ) (fun _ _ _ h => h) τ trivial).1 w U hl hw']
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
          (fun _ _ _ => rfl) (hs.rootE_addBirth hv hv' τ T')
          (fun ρ _ => Tree.preAt_addBirth hv τ T' ρ) (fun _ _ _ h => h) hk L
          (fun _ _ => trivial)
      have hfτ := hv.at τ
      have hfτ' := hv'.at τ
      have hsτ' := Tree.ctxAt_slots hs.h0 hs.ok τ
      have hθ := (hs.okCoh τ).1
      have hc := (hs.okCoh τ).2
      have hle' := Tree.insert_le_addBirth (D := S') (Γ₀ := Γ₀) hv' τ T'
      have hsim : Subst.Sim ((D.ctxAt Γ₀ τ).insert (.free v) T') (hs₂.Fam τ)
          (((hs.Fam τ).rename v v' T' hfτ'.root).mono hle') := by
        refine Subst.sim_mono_of hle' (fun w U hl hw => ?_) (fun y X hy => by
          rw [(hs.fam_agree hs₂ (fun _ => True) (fun _ _ _ => trivial) hk' (fun _ _ _ => rfl)
            (fun _ _ _ => rfl) (hs.rootE_addBirth hv hv' τ T')
            (fun ρ _ => Tree.preAt_addBirth hv τ T' ρ) (fun _ _ _ h => h) τ
            trivial).2 y X hy, Subst.rename_wit]
          simp only [WitE.mono_mono])
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
          · rw [(hs.fam_agree hs₂ (fun _ => True) (fun _ _ _ => trivial) hk' (fun _ _ _ => rfl)
              (fun _ _ _ => rfl) (hs.rootE_addBirth hv hv' τ T')
              (fun ρ _ => Tree.preAt_addBirth hv τ T' ρ) (fun _ _ _ h => h) τ trivial).1 w U hl hw']
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
          (Subst.sim_mono_of hle' (fun w U hl hw => hs.fam_box k τ w U hl hw)
            fun y _ _ => hs.fam_wit k τ y) χ)
      rw [List.map_cons, e₁] at ih'
      exact .boxL τ k _ he' hle' (List.mem_map_of_mem (f := hs.lf) h) ih'
  | @diaR n D Δ Θ τ k e x hx ψ he hf hle h _ ih =>
      intro S' ι E N hs hN
      have ih' := ih hs (hN.cons_r _)
      have he' : S'.edge (k :: τ) = some (e.ren ι) := by rw [hs.edge k τ, he]; rfl
      have hf' := hs.fits hf
      have hle' := Tree.diaIn_le_fit hs.ok he' hf'
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
          (Subst.sim_mono_of hle' (fun w U hl hw => hs.fam_fit he hf hx hle' w U hl hw)
            fun y _ _ => by
              rw [hs.fam_wit, Subst.dia_wit, WitE.mono_mono]) ψ)
      rw [List.map_cons, e₁] at ih'
      exact .diaR τ k (e.ren ι) (ι x) hx' he' hf' hle' (List.mem_map_of_mem (f := hs.lf) h) ih'
  | @optL n D Δ Θ hO τ κ y hy ψ hle h _ ih =>
      intro S' ι E N hs hN
      cases κ with
      | ident => exact (ModalSys.NoT.absurd (Ctx.witT_spec hy.choose_spec).1).elim
      | arrow =>
      obtain ⟨X, hX⟩ := id hy
      have hθ := (hs.okCoh τ).1
      have hc := (hs.okCoh τ).2
      have hsτ := Tree.ctxAt_slots hs.h0 hs.okS τ
      have hsτ' := Tree.ctxAt_slots hs.h0 hs.ok τ
      have hs₂ := hs.addOpen hO hX
      have hk := Tree.ctxAt_addOpen (D := D) (Γ₀ := Γ₀) τ .arrow y
      have hk' := Tree.ctxAt_addOpen (D := S') (Γ₀ := Γ₀) τ .arrow (ι y)
      have ih' := ih hs₂ ((hN.mono hk).cons_l _)
      have hm : ∀ L : Seq σ Γ₀ D, (Seq.mono hk L).map hs₂.lf = Seq.mono hk' (L.map hs.lf) :=
        fun L => hs.lf_mono hs₂ (fun _ => True) (fun _ _ _ => trivial) hk' (fun _ _ _ => rfl)
          (fun _ _ _ => rfl) (hs.rootE_addOpen hO hX)
          (fun ρ _ => Tree.preAt_addOpen τ .arrow y ρ)
          (fun ρ _ o ho => by
            rw [Tree.opensAt_addOpen]
            split_ifs
            · exact List.mem_cons_of_mem _ ho
            · exact ho) hk L (fun _ _ => trivial)
      have hle' : ((S'.ctxAt Γ₀ τ).optIn (ι y)).Le ((S'.addOpen τ .arrow (ι y)).ctxAt Γ₀ τ) := by
        rw [Tree.ctxAt_addOpen_self]
        exact Ctx.Le.refl _
      have hθy := Subst.ok_optIn hθ hO hX (hc.wit hO y X hX [])
      have hcy := Subst.coh_optIn hθ hc hO hX
      have e₁ : hs₂.lf ⟨τ, WFF.mono hle ψ⟩ = ⟨τ, WFF.mono hle' (WFF.subst ι
          ((hs.Fam τ).optIn y (ι y)) hθy hcy (hsτ.optIn y) (hsτ'.optIn _) ψ)⟩ :=
        congrArg (Sigma.mk _) (WFF.subst_mono_eq hle hle' _ _ _ (hs₂.Fam τ) _ _ (hsτ.optIn y)
          (Tree.ctxAt_slots hs.h0 hs₂.okS _) (hsτ'.optIn _) (Tree.ctxAt_slots hs.h0 hs₂.ok _)
          (hs.sim_addOpen hO hX hle') ψ)
      rw [List.map_cons, hm Δ, hm Θ, e₁] at ih'
      exact .optL hO τ .arrow (ι y) (hs.wit_img hO hX) hle' (List.mem_map_of_mem (f := hs.lf) h)
        ih'
  | @reopenR n D Δ Θ hO τ κ y hy χ h _ ih =>
      intro S' ι E N hs hN
      have ih' := ih hs (hN.cons_r _)
      rw [List.map_cons] at ih'
      cases κ with
      | ident => exact (ModalSys.NoT.absurd (Ctx.witT_spec hy.choose_spec.1).1).elim
      | arrow =>
          have hθ := (hs.okCoh τ).1
          have hc := (hs.okCoh τ).2
          have hsτ := Tree.ctxAt_slots hs.h0 hs.okS τ
          have hsτ' := Tree.ctxAt_slots hs.h0 hs.ok τ
          obtain ⟨X, hX, hXd⟩ := id hy
          refine .reopenR hO τ .arrow (ι y)
            (hc.openedTo hO y X (ι y) hX hXd (hc.wit hO y X hX [])) ?_ ih'
          have e := congrArg (fun φ => (⟨τ, WFF.optx hO .arrow (ι y)
              (WitE.wit_of (hθ.wit hO y X hX) (hc.wit hO y X hX [])) φ⟩ : LF σ Γ₀ S'))
            (WFF.subst_optIn_mono (hs.Fam τ) hθ hc hO hX hsτ hsτ' (hsτ'.optIn _) χ)
          exact (congrArg (· ∈ List.map hs.lf Θ) e).mp (List.mem_map_of_mem (f := hs.lf) h)
  | @foldR n D Δ Θ hO τ k e x hx θ he hle h _ ih =>
      intro S' ι E N hs hN
      have ih' := ih hs (hN.cons_r _)
      have he' : S'.edge (k :: τ) = some (e.ren ι) := by rw [hs.edge k τ, he]; rfl
      have hle' := Tree.boxIn_le_child hs.ok k τ
      have hθ := (hs.okCoh τ).1
      have hc := (hs.okCoh τ).2
      have hsτ := Tree.ctxAt_slots hs.h0 hs.okS τ
      have hsτ' := Tree.ctxAt_slots hs.h0 hs.ok τ
      haveI : (D.ctxAt Γ₀ τ).NoSlots := ⟨hsτ⟩
      haveI : (S'.ctxAt Γ₀ τ).NoSlots := ⟨hsτ'⟩
      have hw : ((hs.Fam τ).at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hx' : ∃ X, (S'.ctxAt Γ₀ τ).ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      have hfold : WFF.subst ι (hs.Fam τ).box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hsτ.boxIn
          hsτ'.boxIn (WFF.fold hO x hx θ) = WFF.fold hO (ι x) hx' (WFF.subst ι
            ((hs.Fam τ).dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
            (hsτ.diaIn x) (hsτ'.diaIn _) θ) :=
        (List.cons.inj (subst_optDia (hs.Fam τ) hθ hc hsτ hO (WFF.dia x hx θ))).1
      have e₁ : hs.lf ⟨k :: τ, WFF.mono hle (WFF.fold hO x hx θ)⟩ = ⟨k :: τ, WFF.mono hle'
          (WFF.fold hO (ι x) hx' (WFF.subst ι ((hs.Fam τ).dia x (ι x)) (Subst.ok_dia hθ hx hw)
            (Subst.coh_dia hθ hc hx) (hsτ.diaIn x) (hsτ'.diaIn _) θ))⟩ := by
        rw [← hfold]
        exact congrArg (Sigma.mk _) (WFF.subst_mono_eq hle hle' _ _ _ (hs.Fam (k :: τ)) _ _
          hsτ.boxIn (Tree.ctxAt_slots hs.h0 hs.okS _) hsτ'.boxIn (Tree.ctxAt_slots hs.h0 hs.ok _)
          (Subst.sim_mono_of hle' (fun w U hl hw => hs.fam_box k τ w U hl hw)
            fun y _ _ => hs.fam_wit k τ y) _)
      rw [List.map_cons, e₁] at ih'
      exact .foldR hO τ k (e.ren ι) (ι x) hx' he' hle' (List.mem_map_of_mem (f := hs.lf) h) ih'
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
        fun L hL => hs.lf_mono hs₂ (fun ρ => ¬ (k :: τ) <:+ ρ) hP hk' hedge hedge' hroot
          (fun ρ _ => Tree.preAt_addEdge hnone _ ρ) (fun _ _ _ h => h) hk L hL
      have hsτ := Tree.ctxAt_slots hs.h0 hs.okS τ
      have hsτ' := Tree.ctxAt_slots hs.h0 hs.ok τ
      have hθ := (hs.okCoh τ).1
      have hc := (hs.okCoh τ).2
      have hle' := Tree.boxIn_le_addEdge (Γ₀ := Γ₀) hnone' hv'.birthsAt hv'.opensAt
      have hat := Subst.at_eq_mono_of (hk' τ)
        (hs.fam_agree hs₂ (fun ρ => ¬ (k :: τ) <:+ ρ) hP hk' hedge hedge' hroot
          (fun ρ _ => Tree.preAt_addEdge hnone _ ρ) (fun _ _ _ h => h) τ
          (Tree.not_suffix_cons k τ)).1
      have e₁ : hs₂.lf ⟨k :: τ, WFF.mono hle φ⟩ = ⟨k :: τ, WFF.mono hle' (WFF.subst ι
          (hs.Fam τ).box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hsτ.boxIn hsτ'.boxIn φ)⟩ :=
        congrArg (Sigma.mk _) (WFF.subst_mono_eq hle hle' _ _ _ (hs₂.Fam (k :: τ)) _ _
          hsτ.boxIn (Tree.ctxAt_slots hs.h0 hs₂.okS _) hsτ'.boxIn
          (Tree.ctxAt_slots hs.h0 hs₂.ok _)
          (Subst.sim_mono_of hle' (fun w U hl hw => by
            rw [hs₂.fam_box k τ w U hl ((hk τ).boxIn w U hw),
              Subst.box_eq_mono_of (hk' τ) hat w U hl hw, SubE.mono_mono])
            fun y X hy => by
              rw [hs₂.fam_wit, Subst.box_wit, Subst.box_wit, hat y _ (Ctx.boxIn_wit.mp hy).2,
                SubE.toWit_mono]
              simp only [WitE.mono_mono]) φ)
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
        fun L hL => hs.lf_mono hs₂ (fun ρ => ¬ (k :: τ) <:+ ρ) hP hk' hedge hedge' hroot
          (fun ρ _ => Tree.preAt_addEdge hnone _ ρ) (fun _ _ _ h => h) hk L hL
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
        fun L hL => hs.lf_mono hs₂ (fun ρ => ¬ (k :: τ) <:+ ρ) hP hk' hedge hedge' hroot
          (fun ρ _ => Tree.preAt_addEdge hnone _ ρ) (fun _ _ _ h => h) hk L hL
      have hle' := Tree.diaIn_le_addEdge (Γ₀ := Γ₀) hnone' hv'.birthsAt hv'.opensAt (ι x)
      have hat := Subst.at_eq_mono_of (hk' τ)
        (hs.fam_agree hs₂ (fun ρ => ¬ (k :: τ) <:+ ρ) hP hk' hedge hedge' hroot
          (fun ρ _ => Tree.preAt_addEdge hnone _ ρ) (fun _ _ _ h => h) τ
          (Tree.not_suffix_cons k τ)).1
      have he₂ : (D.addEdge (k :: τ) (.dia x)).edge (k :: τ) = some (.dia x) := by
        rw [Tree.edge_addEdge, if_pos rfl]
      have e₁ : hs₂.lf ⟨k :: τ, WFF.mono hle ψ⟩ = ⟨k :: τ, WFF.mono hle' (WFF.subst ι
          ((hs.Fam τ).dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
          (hsτ.diaIn x) (hsτ'.diaIn _) ψ)⟩ :=
        congrArg (Sigma.mk _) (WFF.subst_mono_eq hle hle' _ _ _ (hs₂.Fam (k :: τ)) _ _
          (hsτ.diaIn x) (Tree.ctxAt_slots hs.h0 hs₂.okS _) (hsτ'.diaIn _)
          (Tree.ctxAt_slots hs.h0 hs₂.ok _)
          (Subst.sim_mono_of hle' (fun w U hl hw => by
            rw [hs₂.fam_dia he₂ w U hl ((hk τ).diaIn x w U hw),
              Subst.dia_eq_mono_of (hk' τ) hat x (ι x) w U hl hw, SubE.mono_mono])
            fun y X hy => by
              rw [hs₂.fam_wit, Subst.dia_wit, Subst.box_wit, Subst.box_wit,
                hat y _ (Ctx.boxIn_wit.mp hy).2, SubE.toWit_mono]
              simp only [WitE.mono_mono]) ψ)
      rw [List.map_cons, hm Δ hv.left, hm Θ hv.right, e₁] at ih'
      exact .diaL τ k (ι x) hx' hv' hle' (List.mem_map_of_mem (f := hs.lf) h) ih'

end GKN

/-! ## Where the family is the identity -/

namespace GKN

variable {σ : Signature} {Γ₀ : Ctx} [ModalSys.NoT]

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

/-- An opening's name is no tree-fresh root. -/
theorem Tree.opened_rt_ne {D : Tree} (hok : D.OK Γ₀) {r : Root} (hf : D.Fresh Γ₀ r) {ρ : Lab}
    {o : WitKind × VarSymb} (ho : o ∈ D.opensAt ρ) : o.2.rt ≠ r := by
  obtain ⟨X, hX, -⟩ := hok.opened ρ o ho
  obtain ⟨κ, y⟩ := o
  cases κ with
  | arrow =>
      intro he
      have := (hf.at ρ).wit y he
      change (D.ctxAt Γ₀ ρ).wit y = some X at hX
      rw [this] at hX
      cases hX
  | ident => exact (hf.at ρ).rt_ne (Ctx.witT_spec hX).2.2

/-- At an opening's content, where the witness is fixed and its entry the identity, the family
    is the identity. -/
theorem SubSetup.fam_ren_content (hs : SubSetup Γ₀ S S' ι E N) (D₀ : Tree) (hok₀ : D₀.OK Γ₀)
    (hopen : ∀ ρ, D₀.opensAt ρ = S.opensAt ρ) (hιo : ∀ ρ, ∀ o ∈ S.opensAt ρ, ι o.2 = o.2)
    (ρ : Lab) (hat : ∀ k ρ', ρ = k :: ρ' → ∀ w U, (D₀.ctxAt Γ₀ ρ').ref w = some U →
      (hs.Fam ρ').at w = .ren w)
    {o : WitKind × VarSymb} (ho : o ∈ S.opensAt ρ) : hs.Fam ρ (.step o.2 o.1.step) =
      .ren (.step o.2 o.1.step) := by
  obtain ⟨κ, y⟩ := o
  have ho₀ : (κ, y) ∈ D₀.opensAt ρ := by rw [hopen]; exact ho
  obtain ⟨X, hX, -⟩ := hok₀.opened ρ _ ho₀
  cases κ with
  | ident => exact (ModalSys.NoT.absurd (Ctx.witT_spec hX).1).elim
  | arrow =>
      have hb : (hs.base ρ).wit y = .ren y := by
        cases ρ with
        | nil => rfl
        | cons k ρ' =>
            rw [hs.base_wit_cons, hs.viewS_wit, Subst.box_wit,
              hat k ρ' rfl y _ (Tree.wit_child_opt hX).2]
            rfl
      change hs.Fam ρ (.step y .dia) = _
      rw [hs.fam_eq, openS_content _ _ _ _ _ ho, hb]
      change SubE.ren (.step (ι y) .dia) = _
      exact congrArg (fun z => SubE.ren (VarSymb.step z .dia)) (hιo ρ _ ho)

/-- ⭐**Where the roots go to themselves and the witnesses are fixed, the family is the identity**,
    on any tree `D₀` with the source's edges. -/
theorem SubSetup.fam_ren (hs : SubSetup Γ₀ S S' ι E N) (D₀ : Tree)
    (hedge : ∀ k ρ, D₀.edge (k :: ρ) = S.edge (k :: ρ))
    (hr : ∀ ρ r U, (D₀.ctxAt Γ₀ ρ) (.root r) = some U → hs.rootE ρ r = .ren (.root r))
    (hι : ∀ k ρ x, S.edge (k :: ρ) = some (.dia x) → ι x = x) (hok₀ : D₀.OK Γ₀)
    (hopen : ∀ ρ, D₀.opensAt ρ = S.opensAt ρ) (hιo : ∀ ρ, ∀ o ∈ S.opensAt ρ, ι o.2 = o.2) :
    ∀ ρ v U, v.lastProj = false → (D₀.ctxAt Γ₀ ρ) v = some U → hs.Fam ρ v = .ren v := by
  intro ρ
  induction ρ with
  | nil =>
      intro v U _ hv
      cases v with
      | root r => rw [hs.fam_root]; exact hr [] r U hv
      | step w s =>
          by_cases hc : ∃ o ∈ S.opensAt [], VarSymb.step w s = .step o.2 o.1.step
          · obtain ⟨o, ho, he⟩ := hc
            rw [he]
            exact hs.fam_ren_content D₀ hok₀ hopen hιo [] (fun _ _ h => by cases h) ho
          · push_neg at hc
            rw [hs.fam_eq, openS_ne _ _ _ _ _ hc]
            rfl
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
          by_cases hc : ∃ o ∈ S.opensAt (k :: ρ), VarSymb.step w s = .step o.2 o.1.step
          · obtain ⟨o, ho, he⟩ := hc
            rw [he]
            exact hs.fam_ren_content D₀ hok₀ hopen hιo (k :: ρ)
              (fun _ _ h w U hw => by cases h; exact hat w U hw) ho
          push_neg at hc
          rw [Tree.ctxAt_eq_pre] at hv
          rcases Ctx.optInsK_cases hv with hv | ⟨o, ho, he⟩
          swap
          · exact absurd he (hc o (by rw [← hopen]; exact ho))
          simp only [Tree.preAt] at hv
          rcases Ctx.inserts_cases hv with ⟨b, _, he, _⟩ | hv
          · cases he
          rw [hs.fam_eq, openS_ne _ _ _ _ _ hc, hs.base_step]
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
    (hι : ∀ k ρ x, S.edge (k :: ρ) = some (.dia x) → ι x = x) (hok₀ : D₀.OK Γ₀)
    (hopen : ∀ ρ, D₀.opensAt ρ = S.opensAt ρ) (hιo : ∀ ρ, ∀ o ∈ S.opensAt ρ, ι o.2 = o.2)
    (ρ : Lab) :
    ∀ v U, (D₀.ctxAt Γ₀ ρ).ref v = some U → (hs.Fam ρ).at v = .ren v := fun v U h => by
  rw [Subst.at_eq_mono_of (Ctx.Le.refl _) (θ' := Subst.idRen (S'.ctxAt Γ₀ ρ))
    (hs.fam_ren D₀ hedge hr hι hok₀ hopen hιo ρ) v U h, Subst.at_idRen]
  rfl

/-- Where the family is the identity, so are its witness entries. -/
theorem SubSetup.wit_ren (hs : SubSetup Γ₀ S S' ι E N) (D₀ : Tree)
    (hedge : ∀ k ρ, D₀.edge (k :: ρ) = S.edge (k :: ρ))
    (hr : ∀ ρ r U, (D₀.ctxAt Γ₀ ρ) (.root r) = some U → hs.rootE ρ r = .ren (.root r))
    (hι : ∀ k ρ x, S.edge (k :: ρ) = some (.dia x) → ι x = x) (hok₀ : D₀.OK Γ₀)
    (hopen : ∀ ρ, D₀.opensAt ρ = S.opensAt ρ) (hιo : ∀ ρ, ∀ o ∈ S.opensAt ρ, ι o.2 = o.2) :
    ∀ ρ y X, (D₀.ctxAt Γ₀ ρ).wit y = some X → (hs.Fam ρ).wit y = .ren y
  | [], _, _, _ => by rw [hs.wit_fam]; rfl
  | k :: ρ, y, _, hy => by
      rw [hs.wit_fam, hs.base_wit_cons, hs.viewS_wit, Subst.box_wit,
        hs.at_ren D₀ hedge hr hι hok₀ hopen hιo ρ y _ (Tree.wit_child_opt hy).2]
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
  opens ρ o ho := (hok.opened ρ o ho).mono (Tree.ctxAt_addBirth hv τ T ρ)
  opensT o ho := Or.inl ⟨o, ho, rfl⟩

theorem SubSetup.lf_weaken {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀) (h0 : Γ₀.SlotsFrom 0)
    {v : ℕ} (hv : D.Fresh Γ₀ (.free v)) (τ : Lab) (T : VarType) (L : Seq σ Γ₀ D) :
    L.map (SubSetup.weaken hok hW h0 hv τ T).lf = Seq.mono (Tree.ctxAt_addBirth hv τ T) L := by
  refine List.map_congr_left fun p _ => ?_
  obtain ⟨ρ, ψ⟩ := p
  refine congrArg (Sigma.mk ρ) ?_
  dsimp only
  exact WFF.subst_ren (Tree.ctxAt_addBirth hv τ T ρ) _ _ _ _ _
    ((SubSetup.weaken hok hW h0 hv τ T).at_ren D (fun _ _ => rfl)
      (fun _ _ _ _ => by unfold SubSetup.rootE; split <;> rfl) (fun _ _ _ _ => rfl) hok
      (fun ρ' => rfl) (fun ρ' o ho => rfl) ρ) ψ
    (fun _ => (SubSetup.weaken hok hW h0 hv τ T).wit_ren D (fun _ _ => rfl)
      (fun _ _ _ _ => by unfold SubSetup.rootE; split <;> rfl) (fun _ _ _ _ => rfl) hok
      (fun ρ' => rfl) (fun ρ' o ho => rfl) ρ)

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
  opens ρ o ho := by
    have e : Subst.singleIdx (.free u) (.tm t) o.2 = o.2 := by
      unfold Subst.singleIdx
      rw [if_neg (Tree.opened_rt_ne hok hu ho)]
    rw [e]
    exact hok.opened ρ o ho
  opensT o ho := Or.inl ⟨o, ho, rfl⟩

variable {τ₀ : Lab} {u : ℕ} {T : VarType} {a : Ann T}

/-- Unbinding fixes the roots and witnesses of the tree without the birth. -/
theorem unbind_ren {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀) (h0 : Γ₀.SlotsFrom 0)
    (hu : D.Fresh Γ₀ (.free u)) (t : Term σ (D.ctxAt Γ₀ τ₀) T a) :
    (∀ ρ r U, (D.ctxAt Γ₀ ρ) (.root r) = some U →
      (SubSetup.unbind hok hW h0 hu τ₀ T t).rootE ρ r = .ren (.root r)) ∧
    (∀ k ρ x, (D.addBirth τ₀ (.free u) T).edge (k :: ρ) = some (.dia x) →
      Subst.singleIdx (.free u) (.tm t) x = x) ∧
    (∀ ρ, ∀ o ∈ (D.addBirth τ₀ (.free u) T).opensAt ρ,
      Subst.singleIdx (.free u) (.tm t) o.2 = o.2) := by
  refine ⟨fun ρ r U hr => ?_, fun k ρ x he => ?_, fun ρ o ho => ?_⟩
  rotate_left 2
  · unfold Subst.singleIdx
    rw [if_neg (Tree.opened_rt_ne hok hu ho)]
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
      ((SubSetup.unbind hok hW h0 hu τ₀ T t).at_ren D (fun _ _ => rfl) hren.1 hren.2.1 hok
        (fun ρ' => rfl) hren.2.2 ρ) ψ
      (fun _ => (SubSetup.unbind hok hW h0 hu τ₀ T t).wit_ren D (fun _ _ => rfl) hren.1
        hren.2.1 hok (fun ρ' => rfl) hren.2.2 ρ),
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
    refine Subst.sim_mono_of _ (fun v U hl hv => ?_) (fun y X hy => ?_)
    swap
    · rw [(SubSetup.unbind hok hW h0 hu τ₀ T t).wit_ren D (fun _ _ => rfl) hren.1 hren.2.1 hok
        (fun ρ' => rfl) hren.2.2 τ₀ y X hy]
      rfl
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
        (fun _ _ => rfl) hren.1 hren.2.1 hok (fun ρ' => rfl) hren.2.2 τ₀ v U hl
        (Ctx.insert_ne_some hv hvr)]
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
