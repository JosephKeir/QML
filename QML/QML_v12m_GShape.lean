import QML.QML_v12m_GCanonPath

/-!
# QML v12m — the growing tree: shapes

Under T possible objects carry shapes (`docs/v12-modal-extensions.md` §10.27–10.39).  On the
growing tree a root possibility is named by its address; kept along an arrow it is read by the
leaf-valued root action (`GKeep`, `instRootKeepG`).  This file has the shape-level pieces:

* `GShape`, `GLeaf`: shapes and leaves over the tree's arrows;
* `rootSh`: the generic content shape of a root possibility, as B's and the tree's;
* `dleaf`: a well-formed leaf at every level list;
* `edgeAcc`: the arrow of an edge.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

variable (hF M₀) in
/-- Leaves over the growing tree's arrows. -/
abbrev GLeaf (s : GW hF M₀) : Type := (garrows hF M₀).Leaf (fun _ => VarSymb) s

variable (hF M₀) in
/-- Shapes over the growing tree's arrows. -/
abbrev GShape (s : GW hF M₀) (T : VarType) : Type :=
  Model.Shape (garrows hF M₀) (fun _ => VarSymb) s T

/-! ## Generic shapes -/

/-- The content shape of a root possibility at a path, as in B and the tree (`Canon.rootSh`). -/
def rootSh (s : GW hF M₀) (v : VarSymb) : List Step → (T : VarType) → GShape hF M₀ s T
  | _, .Var => .var
  | _, .VTypeOne => .one
  | π, .VTypeProd A C => .prod (rootSh s v (π ++ [.fst]) A) (rootSh s v (π ++ [.snd]) C)
  | π, .VTypeBox A => .box (rootSh s v (π ++ Step.innerPath) A)
  | π, .VTypeDia A => .dia (.root v π) (rootSh s v (π ++ [.dia]) A)

theorem rootSh_wf (s : GW hF M₀) (v : VarSymb) : ∀ (T : VarType) (π : List Step)
    (lw : List Bool), Step.levels π = lw.length → lw.head? = some false →
      Step.BoxOK lw π → ∀ U : VarType, Step.walkTy U π = some T →
      Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) lw (rootSh s v π T)
  | .Var, _, _, _, _, _, _, _ => trivial
  | .VTypeOne, _, _, _, _, _, _, _ => trivial
  | .VTypeProd A C, π, lw, h, hh, hb, U, hU =>
      ⟨rootSh_wf s v A _ lw (by rw [Step.levels_append, h]; rfl) hh
          (Step.BoxOK_snoc_proj lw π .fst h hb) U (by rw [Step.walkTy_append, hU]; rfl),
        rootSh_wf s v C _ lw (by rw [Step.levels_append, h]; rfl) hh
          (Step.BoxOK_snoc_proj lw π .snd h hb) U (by rw [Step.walkTy_append, hU]; rfl)⟩
  | .VTypeBox A, π, lw, h, hh, hb, U, hU =>
      rootSh_wf s v A _ (lw ++ [true])
        (by rw [Step.levels_append, Canon.Step.levels_innerPath, h]; simp)
        (by cases lw <;> simp_all) (Canon.Step.BoxOK_innerPath lw π h hb)
        U (by rw [Step.walkTy_append, hU]; exact Canon.Step.walkTy_innerPath A)
  | .VTypeDia A, π, lw, h, hh, hb, U, hU =>
      ⟨(Arrows.Leaf.wf_root _ π).mpr ⟨h, by rw [hh]; simp, hb, ⟨U, A, hU⟩⟩,
        rootSh_wf s v A _ (lw ++ [false])
          (by rw [Step.levels_append, h]; simp [Step.levels, Step.isProj])
          (by cases lw <;> simp_all) (Step.BoxOK_snoc_dia lw π h hb)
          U (by rw [Step.walkTy_append, hU]; rfl)⟩

/-! ## Default leaves -/

/-- A leaf for positions nothing constrains, well-formed at the given level list: a root with as
    many level steps as the position, or, at a `□` level, a family of such. -/
def dleaf : List Bool → (s : GW hF M₀) → GLeaf hF M₀ s
  | true :: q, _ => .fam fun b => dleaf q b.1
  | lw, _ => .root (.root (.free 0)) (Step.kindPath lw)

omit [ModalSys] in
theorem levels_replicate_dia : ∀ n : ℕ, Step.levels (List.replicate n Step.dia) = n
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ, Step.levels_cons, if_neg (by decide), levels_replicate_dia n]
      omega

theorem dleaf_wf : ∀ (lw : List Bool) (s : GW hF M₀), Arrows.Leaf.WF lw (dleaf lw s)
  | [], _ =>
      (Arrows.Leaf.wf_root _ _).mpr ⟨Step.levels_kindPath [], by simp, trivial,
        Step.typable_kindPath []⟩
  | false :: q, _ =>
      (Arrows.Leaf.wf_root _ _).mpr ⟨Step.levels_kindPath _, by simp, Step.BoxOK_kindPath _,
        Step.typable_kindPath _⟩
  | true :: q, _ => fun b => dleaf_wf q b.1

/-! ## Edges -/

/-- The arrow of an edge. -/
abbrev edgeAcc {s t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: s.1) : (garrows hF M₀).Acc s :=
  ⟨t, ⟨⟨[c], pathOk_cons, hc⟩⟩⟩

end GArrow

end V12M
