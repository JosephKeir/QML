import QML.QML_v12m_GCanonPath

/-!
# QML v12m — the growing tree: shapes

Under T possible objects carry shapes (`docs/v12-modal-extensions.md` §10.27–10.39).  On the
growing tree a root possibility is named by its address, and kept along an arrow it is the witness
kept along the arrow's path (`instRootKeepG`, `kw`).  Canonical shapes are set by an address's
origin (§3 4, "(B) on paper: shape templates"); this file has the shape-level pieces:

* `GShape`, `GLeaf`: shapes and leaves over the tree's arrows;
* `rootSh`: the generic content shape of a root possibility, as B's and the tree's;
* `dleaf`: a well-formed leaf at every level list;
* ⭐`pbLeaf`, `pbShp`: the pull-back of a shape along an edge to the lifted root — a family is
  read through the edge, a root becomes the lifted root — and `keepAlong_pbLeaf`: keeping the
  pull-back along the edge gives back every leaf whose roots are the edge's kept witness.
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
      Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) lw (rootSh s v π T)
  | .Var, _, _, _, _ => trivial
  | .VTypeOne, _, _, _, _ => trivial
  | .VTypeProd A C, π, lw, h, hh =>
      ⟨rootSh_wf s v A _ lw (by rw [Step.levels_append, h]; rfl) hh,
        rootSh_wf s v C _ lw (by rw [Step.levels_append, h]; rfl) hh⟩
  | .VTypeBox A, π, lw, h, hh =>
      rootSh_wf s v A _ (lw ++ [true])
        (by rw [Step.levels_append, Canon.Step.levels_innerPath, h]; simp)
        (by cases lw <;> simp_all)
  | .VTypeDia A, π, lw, h, hh =>
      ⟨(Arrows.Leaf.wf_root _ π).mpr ⟨h, by rw [hh]; simp⟩,
        rootSh_wf s v A _ (lw ++ [false])
          (by rw [Step.levels_append, h]; simp [Step.levels, Step.isProj])
          (by cases lw <;> simp_all)⟩

/-! ## Default leaves -/

/-- A leaf for positions nothing constrains, well-formed at the given level list: a root with as
    many level steps as the position, or, at a `□` level, a family of such. -/
def dleaf : List Bool → (s : GW hF M₀) → GLeaf hF M₀ s
  | true :: q, _ => .fam fun b => dleaf q b.1
  | lw, _ => .root (.root (.free 0)) (List.replicate lw.length .dia)

omit [ModalSys] in
theorem levels_replicate_dia : ∀ n : ℕ, Step.levels (List.replicate n Step.dia) = n
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ, Step.levels_cons, if_neg (by decide), levels_replicate_dia n]
      omega

theorem dleaf_wf : ∀ (lw : List Bool) (s : GW hF M₀), Arrows.Leaf.WF lw (dleaf lw s)
  | [], _ => (Arrows.Leaf.wf_root _ _).mpr ⟨levels_replicate_dia 0, by simp⟩
  | false :: q, _ => (Arrows.Leaf.wf_root _ _).mpr ⟨levels_replicate_dia _, by simp⟩
  | true :: q, _ => fun b => dleaf_wf q b.1

/-! ## Pulling back along an edge -/

open Classical in
variable (hF M₀) in
/-- ⭐**A leaf pulled back along an edge to the lifted root `m`**: a root becomes `m` with the
    same path; a family is read through the edge at the arrows that go through it, and is a
    default leaf elsewhere. -/
noncomputable def pbLeaf {s t : GW hF M₀} (m : VarSymb) (lw : List Bool) :
    GLeaf hF M₀ t → GLeaf hF M₀ s
  | .root _ p => .root m p
  | .fam f => .fam fun a => if h : GR t a.1 then f ⟨a.1, ⟨h⟩⟩ else dleaf lw.tail a.1

variable (hF M₀) in
/-- A shape pulled back along an edge, leaf by leaf at each position's level list. -/
noncomputable def pbShp {s t : GW hF M₀} (m : VarSymb) :
    List Bool → {T : VarType} → GShape hF M₀ t T → GShape hF M₀ s T
  | _, _, .var => .var
  | _, _, .one => .one
  | lw, _, .prod a b => .prod (pbShp m lw a) (pbShp m lw b)
  | lw, _, .box a => .box (pbShp m (lw ++ [true]) a)
  | lw, _, .dia ℓ a => .dia (pbLeaf hF M₀ m lw ℓ) (pbShp m (lw ++ [false]) a)

open Classical in
/-- Pulling back keeps a leaf well-formed. -/
theorem pbLeaf_wf {s t : GW hF M₀} (m : VarSymb) :
    ∀ (lw : List Bool) (ℓ : GLeaf hF M₀ t), Arrows.Leaf.WF lw ℓ →
      Arrows.Leaf.WF lw (pbLeaf hF M₀ (s := s) m lw ℓ)
  | lw, .root _ p, h => (Arrows.Leaf.wf_root _ p).mpr ((Arrows.Leaf.wf_root _ p).mp h)
  | [], .fam f, h => fun a => by
      change Arrows.Leaf.WF [] (if h' : GR t a.1 then f ⟨a.1, ⟨h'⟩⟩ else dleaf [] a.1)
      split
      · exact h _
      · exact dleaf_wf [] a.1
  | _ :: q, .fam f, h => fun a => by
      change Arrows.Leaf.WF q (if h' : GR t a.1 then f ⟨a.1, ⟨h'⟩⟩ else dleaf q a.1)
      split
      · exact h _
      · exact dleaf_wf q a.1

theorem pbShp_wf {s t : GW hF M₀} (m : VarSymb) : ∀ (lw : List Bool) {T : VarType}
    (S : GShape hF M₀ t T), Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) lw S →
      Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) lw (pbShp hF M₀ (s := s) m lw S)
  | _, _, .var, _ => trivial
  | _, _, .one, _ => trivial
  | lw, _, .prod a b, h => ⟨pbShp_wf m lw a h.1, pbShp_wf m lw b h.2⟩
  | lw, _, .box a, h => pbShp_wf m (lw ++ [true]) a h
  | lw, _, .dia ℓ a, h => ⟨pbLeaf_wf m lw ℓ h.1, pbShp_wf m (lw ++ [false]) a h.2⟩

/-- The arrow of an edge. -/
abbrev edgeAcc {s t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: s.1) : (garrows hF M₀).Acc s :=
  ⟨t, ⟨⟨[c], pathOk_cons, hc⟩⟩⟩

/-- Keeping a root along an edge is the edge's kept witness. -/
theorem rootKeep_edge {s t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: s.1) (m : VarSymb) :
    Arrows.RootKeep.keep (F := garrows hF M₀) (Root := fun _ => VarSymb) hF m (edgeAcc hc) =
      wit t m := by
  change kw s t (pathOf _) _ m = wit t m
  rw [kw_path (P' := [c]) (pathOf_of _ hc) _ hc m]
  rfl

open Classical in
/-- ⭐**Keeping a pulled-back leaf along the edge gives it back**, when its root is the edge's
    kept witness of the lifted root. -/
theorem keepAlong_pbLeaf {s t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: s.1) (m : VarSymb)
    (lw : List Bool) :
    ∀ ℓ : GLeaf hF M₀ t, (∀ r p, ℓ = .root r p → r = wit t m) →
      Arrows.Leaf.keepAlong hF (edgeAcc hc) (pbLeaf hF M₀ (s := s) m lw ℓ) = ℓ
  | .root r p, h => by
      simp only [pbLeaf, Arrows.Leaf.keepAlong]
      rw [rootKeep_edge, h r p rfl]
  | .fam f, _ => by
      change Arrows.Leaf.fam (fun b => (if h' : GR t b.1 then f ⟨b.1, ⟨h'⟩⟩ else dleaf _ b.1)) = _
      congr 1
      funext b
      rw [dif_pos b.2.down]

end GArrow

end V12M
