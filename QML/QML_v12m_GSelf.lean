import QML.QML_v12m_GTemplate

/-!
# QML v12m — the growing tree: self-rooted shapes

A `◇`-shape is **self-rooted** at `y` when every root leaf at its top level (outside families) is
labelled `y` (`ShTop`).  This is what makes the pull-back of a lifted term's shape give the shape
back along the lift edge (`keepAlong_pbShp`), and so (C2) along the lift edge
(`docs/v12-modal-extensions.md` §3 4, "(B) in Lean").

* Inside a `◇` every operation keeps top-level labels (`shTop_shp`, `shTop_termShp`): a `here`
  collapses a level below the top, which keeps a family a family.
* A lifted term `◇_y w` is self-rooted at `y` when `y`'s shape is (`shTop_termShp_dia`): the
  `□`-items of `y`'s view enter as families.
* A construction step's `◇`-shapes are self-rooted at their address (`cStep_top`), and it reads
  projections as the parent's shape does (`cStep_proj`).
* ⭐`liftDiaAt_keep`: a lifted root's template, kept along its lift edge, is its lifted term's
  shape.
-/

namespace V12M

universe uL

/-- Every leaf of a shape satisfies `Q`. -/
def Shp.AllL {L : Type*} (Q : L → Prop) : {A : VarType} → Shp L A → Prop
  | _, .var => True
  | _, .one => True
  | _, .prod a b => Shp.AllL Q a ∧ Shp.AllL Q b
  | _, .box a => Shp.AllL Q a
  | _, .dia ℓ a => Q ℓ ∧ Shp.AllL Q a

namespace Shp

variable {L L' : Type uL} {Q : L → Prop}

theorem allL_map {Q' : L' → Prop} {g : L → L'} (hg : ∀ ℓ, Q ℓ → Q' (g ℓ)) :
    ∀ {A : VarType} (a : Shp L A), a.AllL Q → (a.map g).AllL Q'
  | _, .var, _ => trivial
  | _, .one, _ => trivial
  | _, .prod a b, h => ⟨allL_map hg a h.1, allL_map hg b h.2⟩
  | _, .box a, h => allL_map hg a h
  | _, .dia ℓ a, h => ⟨hg ℓ h.1, allL_map hg a h.2⟩

theorem allL_map_all {Q' : L' → Prop} {g : L → L'} (hg : ∀ ℓ, Q' (g ℓ)) :
    ∀ {A : VarType} (a : Shp L A), (a.map g).AllL Q'
  | _, .var => trivial
  | _, .one => trivial
  | _, .prod a b => ⟨allL_map_all hg a, allL_map_all hg b⟩
  | _, .box a => allL_map_all hg a
  | _, .dia ℓ a => ⟨hg ℓ, allL_map_all hg a⟩

theorem allL_fst {A B : VarType} : ∀ {a : Shp L (.VTypeProd A B)}, a.AllL Q → a.fst.AllL Q
  | .prod _ _, h => h.1

theorem allL_snd {A B : VarType} : ∀ {a : Shp L (.VTypeProd A B)}, a.AllL Q → a.snd.AllL Q
  | .prod _ _, h => h.2

theorem allL_inner {A : VarType} : ∀ {a : Shp L (.VTypeBox A)}, a.AllL Q → a.inner.AllL Q
  | .box _, h => h

theorem allL_body {A : VarType} : ∀ {a : Shp L (.VTypeDia A)}, a.AllL Q → a.body.AllL Q
  | .dia _ _, h => h.2

theorem allL_label {A : VarType} : ∀ {a : Shp L (.VTypeDia A)}, a.AllL Q → Q a.label
  | .dia _ _, h => h.1

theorem allL_mono {Q' : L → Prop} (hq : ∀ ℓ, Q ℓ → Q' ℓ) :
    ∀ {A : VarType} (a : Shp L A), a.AllL Q → a.AllL Q'
  | _, .var, _ => trivial
  | _, .one, _ => trivial
  | _, .prod a b, h => ⟨allL_mono hq a h.1, allL_mono hq b h.2⟩
  | _, .box a, h => allL_mono hq a h
  | _, .dia _ a, h => ⟨hq _ h.1, allL_mono hq a h.2⟩

end Shp

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-! ## Leaves -/

/-- A family, or a root labelled `y`. -/
def LeafTop (y : VarSymb) {s : GW hF M₀} : GLeaf hF M₀ s → Prop
  | .root r _ => r = y
  | .fam _ => True

/-- A family. -/
def IsFam {s : GW hF M₀} : GLeaf hF M₀ s → Prop
  | .root _ _ => False
  | .fam _ => True

theorem leafTop_of_isFam (y : VarSymb) {s : GW hF M₀} : ∀ {ℓ : GLeaf hF M₀ s}, IsFam ℓ →
    LeafTop y ℓ
  | .fam _, _ => trivial

/-- ⭐**Self-rooted at `y`**: every top-level root leaf of the shape is labelled `y`. -/
abbrev ShTop (y : VarSymb) {s : GW hF M₀} {T : VarType} (S : GShape hF M₀ s T) : Prop :=
  S.AllL (LeafTop y)

theorem leafTop_collapse_succ (hT : ModalSys.T = true) (y : VarSymb) (i : ℕ) {s : GW hF M₀} :
    ∀ {ℓ : GLeaf hF M₀ s}, LeafTop y ℓ → LeafTop y (Arrows.Leaf.collapse hT (i + 1) ℓ)
  | .root _ _, h => h
  | .fam _, _ => trivial

theorem leafTop_shift (hF' : ModalSys.Four = true) (y : VarSymb) (j : ℕ) {s : GW hF M₀} :
    ∀ {ℓ : GLeaf hF M₀ s}, LeafTop y ℓ → LeafTop y (Arrows.Leaf.shift hF' j ℓ)
  | .root _ _, h => by cases j <;> exact h
  | .fam _, _ => by cases j <;> trivial

theorem isFam_shift (hF' : ModalSys.Four = true) (j : ℕ) {s : GW hF M₀} :
    ∀ {ℓ : GLeaf hF M₀ s}, IsFam ℓ → IsFam (Arrows.Leaf.shift hF' j ℓ)
  | .fam _, _ => by cases j <;> trivial

theorem leafTop_dk (hF' : ModalSys.Four = true) (y : VarSymb) :
    ∀ (j : ℕ) {s : GW hF M₀} {ℓ : GLeaf hF M₀ s}, LeafTop y ℓ →
      LeafTop y (Arrows.Leaf.dk hF' j ℓ)
  | 0, _, _, _ => trivial
  | _ + 1, _, .root _ _, h => h
  | _ + 1, _, .fam _, _ => trivial

theorem leafTop_dkB (hF' : ModalSys.Four = true) (y : VarSymb) :
    ∀ (j : ℕ) {s : GW hF M₀} {ℓ : GLeaf hF M₀ s}, LeafTop y ℓ →
      LeafTop y (Arrows.Leaf.dkB hF' j ℓ)
  | 0, _, _, _ => trivial
  | _ + 1, _, .root _ _, h => h
  | _ + 1, _, .fam _, _ => trivial

theorem isFam_dk0 (hF' : ModalSys.Four = true) {s : GW hF M₀} (ℓ : GLeaf hF M₀ s) :
    IsFam (Arrows.Leaf.dk hF' 0 ℓ) := trivial

theorem isFam_dkB0 (hF' : ModalSys.Four = true) {s : GW hF M₀} (ℓ : GLeaf hF M₀ s) :
    IsFam (Arrows.Leaf.dkB hF' 0 ℓ) := trivial

/-- Below a `□` at the top, every leaf of a well-formed shape is a family. -/
theorem allL_isFam_of_wf {s : GW hF M₀} :
    ∀ (lw : List Bool) {T : VarType} (S : GShape hF M₀ s T),
      Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) (true :: lw) S → S.AllL IsFam
  | _, _, .var, _ => trivial
  | _, _, .one, _ => trivial
  | lw, _, .prod a b, h => ⟨allL_isFam_of_wf lw a h.1, allL_isFam_of_wf lw b h.2⟩
  | lw, _, .box a, h => allL_isFam_of_wf (lw ++ [true]) a h
  | lw, _, .dia ℓ a, h => by
      refine ⟨?_, allL_isFam_of_wf (lw ++ [false]) a h.2⟩
      match ℓ, h.1 with
      | .root _ _, h₁ => exact absurd ((Arrows.Leaf.wf_root _ _).mp h₁).2 (by simp)
      | .fam _, _ => trivial

/-! ## Inside a `◇` the top level keeps its labels -/

/-- ⭐Below the top, every function's shape keeps top-level labels. -/
theorem shTop_shp (y : VarSymb) {s : GW hF M₀} :
    ∀ {A B : VarType} (f : GFunc σ A B) (j : ℕ), 1 ≤ j → ∀ (a : GShape hF M₀ s A),
      ShTop y a → ShTop y (GFunc.shp f j a)
  | _, _, .id _, _, _, _, h => h
  | _, _, .comp g f, j, hj, a, h => shTop_shp y g j hj _ (shTop_shp y f j hj a h)
  | _, _, .fst, _, _, _, h => Shp.allL_fst h
  | _, _, .snd, _, _, _, h => Shp.allL_snd h
  | _, _, .pair f g, j, hj, a, h => ⟨shTop_shp y f j hj a h, shTop_shp y g j hj a h⟩
  | _, _, .unit _, _, _, _, _ => trivial
  | _, _, .func _ _, _, _, _, _ => trivial
  | _, _, .boxMap f, j, _, a, h => shTop_shp y f (j + 1) (by omega) _ (Shp.allL_inner h)
  | _, _, .boxPair _ _, _, _, _, h =>
      ⟨Shp.allL_inner (Shp.allL_fst h), Shp.allL_inner (Shp.allL_snd h)⟩
  | _, _, .boxUnit, _, _, _, _ => trivial
  | _, _, .diaMap f, j, _, a, h =>
      ⟨Shp.allL_label h, shTop_shp y f (j + 1) (by omega) _ (Shp.allL_body h)⟩
  | _, _, .strength _ _, _, _, _, h =>
      ⟨Shp.allL_label (Shp.allL_snd h), Shp.allL_inner (Shp.allL_fst h),
        Shp.allL_body (Shp.allL_snd h)⟩
  | _, _, .extract hT, j, hj, a, h => by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      exact Shp.allL_map (fun _ => leafTop_collapse_succ hT y i) _ (Shp.allL_inner h)
  | _, _, .dup hF', j, _, _, h =>
      Shp.allL_map (fun _ => leafTop_shift hF' y j) _ (Shp.allL_inner h)
  | _, _, .dkeep hF', j, _, _, h =>
      ⟨leafTop_dk hF' y j (Shp.allL_label h),
        Shp.allL_map (fun _ => leafTop_dkB hF' y j) _ (Shp.allL_body h)⟩

/-- An environment all of whose shapes are self-rooted at `y`. -/
def EnvTop (y : VarSymb) {Γ : Ctx} {s : GW hF M₀}
    (ρ : Model.ShEnv (garrows hF M₀) (fun _ => VarSymb) Γ s) : Prop :=
  ∀ v T h, ShTop y (ρ v T h)

theorem envTop_ref {y : VarSymb} {Γ : Ctx} {s : GW hF M₀}
    {ρ : Model.ShEnv (garrows hF M₀) (fun _ => VarSymb) Γ s} (hρ : EnvTop y ρ) (j : ℕ)
    (hj : 1 ≤ j) : ∀ (v : VarSymb) {T : VarType} (h : Γ.ref v = some T), ShTop y (ρ.ref j v h)
  | .root _, _, h => hρ _ _ h
  | .step v st, T, h => by
      by_cases hs : st.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Γ.ref v = some U := by
          rw [Ctx.ref_step_proj Γ v hs] at h
          cases hU : Γ.ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        rw [Model.ShEnv.ref_proj _ _ hs hU h]
        exact shTop_shp y _ j hj _ (envTop_ref hρ j hj v hU)
      · rw [Model.ShEnv.ref_nonproj _ _ hs h]
        exact hρ _ _ _

theorem envTop_boxPush {y : VarSymb} {Γ : Ctx} {s : GW hF M₀}
    {ρ : Model.ShEnv (garrows hF M₀) (fun _ => VarSymb) Γ s} (hρ : EnvTop y ρ) (j : ℕ)
    (hj : 1 ≤ j) : EnvTop y (ρ.boxPush j) := by
  intro v T h
  match v, h with
  | .step u .box, h => exact Shp.allL_inner (envTop_ref hρ j hj u (Ctx.boxIn_step_box h))
  | .step u .keep, h =>
      exact Shp.allL_inner (shTop_shp y _ j hj _ (envTop_ref hρ j hj u (Ctx.boxIn_keep h).2.1))
  | .root _, h => cases h
  | .step _ .fst, h => cases h
  | .step _ .snd, h => cases h
  | .step _ .dia, h => cases h
  | .step _ .here, h => cases h

theorem envTop_diaPush {y : VarSymb} {Γ : Ctx} {s : GW hF M₀}
    {ρ : Model.ShEnv (garrows hF M₀) (fun _ => VarSymb) Γ s} (hρ : EnvTop y ρ) (j : ℕ)
    (hj : 1 ≤ j) {x : VarSymb} {X : VarType} (hx : Γ.ref x = some (.VTypeDia X)) :
    EnvTop y (ρ.diaPush j x hx) := by
  intro v T h
  match v, h with
  | .step _ .dia, h =>
      have e := Ctx.diaIn_step_dia hx h
      subst e
      exact Shp.allL_body (envTop_ref hρ j hj x hx)
  | .step u .box, h => exact envTop_boxPush hρ j hj (.step u .box) T h
  | .step u .keep, h => exact envTop_boxPush hρ j hj (.step u .keep) T h
  | .root _, h => cases h
  | .step _ .fst, h => cases h
  | .step _ .snd, h => cases h
  | .step _ .here, h => cases h

/-- ⭐**Below the top, a term's shape keeps the environment's top-level labels.** -/
theorem shTop_termShp {y : VarSymb} {s : GW hF M₀} :
    ∀ {Δ : Ctx} {ρ : Model.ShEnv (garrows hF M₀) (fun _ => VarSymb) Δ s}, EnvTop y ρ →
      ∀ (j : ℕ), 1 ≤ j → ∀ {T : VarType} {a : Ann T} (t : Term σ Δ T a),
        ShTop y (Model.termShp ρ j t)
  | _, _, _, _, _, _, _, .var _ _ => trivial
  | _, _, _, _, _, _, _, .func _ => trivial
  | _, _, _, _, _, _, _, .unit => trivial
  | _, _, hρ, j, hj, _, _, .pair u v => ⟨shTop_termShp hρ j hj u, shTop_termShp hρ j hj v⟩
  | _, _, hρ, j, hj, _, _, .boxtm t => shTop_termShp (envTop_boxPush hρ j hj) (j + 1) (by omega) t
  | Δ, ρ, hρ, j, hj, _, _, .diatm x hx t => by
      obtain ⟨X, hr⟩ := hx
      rw [Model.termShp_diatm ρ j hr]
      exact ⟨Shp.allL_label (envTop_ref hρ j hj x hr),
        shTop_termShp (envTop_diaPush hρ j hj hr) (j + 1) (by omega) t⟩

/-- At the top, the `□`-items of a `◇`'s view enter as families. -/
theorem envTop_diaPush_zero {y : VarSymb} {Γ : Ctx} {s : GW hF M₀}
    {ρ : Model.ShEnv (garrows hF M₀) (fun _ => VarSymb) Γ s} (hwf : ρ.WF [])
    {X : VarType} (hy : Γ.ref y = some (.VTypeDia X)) (hty : ShTop y (ρ.ref 0 y hy)) :
    EnvTop y (ρ.diaPush 0 y hy) := by
  intro v T h
  match v, h with
  | .step _ .dia, h =>
      have e := Ctx.diaIn_step_dia hy h
      subst e
      exact Shp.allL_body hty
  | .step u .box, h =>
      have hu := Ctx.boxIn_step_box h
      have hw := Model.ShEnv.wf_ref' (k := 0) hwf rfl u hu
      rw [Shp.box_eta (ρ.ref 0 u hu)] at hw
      exact Shp.allL_mono (fun _ => leafTop_of_isFam y) _ (allL_isFam_of_wf [] _ hw)
  | .step u .keep, h =>
      obtain ⟨hF', hu, hk⟩ := Ctx.boxIn_keep h
      have hw := Model.ShEnv.wf_ref' (k := 0) hwf rfl u hu
      change ShTop y (GFunc.shp (GFunc.keep (σ := σ) hF' hk) 0 (ρ.ref 0 u hu)).inner
      cases T with
      | VTypeBox A =>
          have hw' : Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [true]
              (ρ.ref 0 u hu).inner := by
            rw [Shp.box_eta (ρ.ref 0 u hu)] at hw
            exact hw
          exact Shp.allL_mono (fun _ => leafTop_of_isFam y) _
            (Shp.allL_map (fun _ => isFam_shift hF' 0) _ (allL_isFam_of_wf [] _ hw'))
      | VTypeDia A =>
          change Shp.AllL _ (Shp.dia _ _)
          exact ⟨trivial, Shp.allL_map_all (fun ℓ => leafTop_of_isFam y (isFam_dkB0 hF' ℓ)) _⟩
      | Var => cases hk
      | VTypeOne => cases hk
      | VTypeProd _ _ => cases hk
  | .root _, h => cases h
  | .step _ .fst, h => cases h
  | .step _ .snd, h => cases h
  | .step _ .here, h => cases h

/-- ⭐**A lifted term is self-rooted at its witness** when the witness's shape is. -/
theorem shTop_termShp_dia {Γ : Ctx} {s : GW hF M₀}
    {ρ : Model.ShEnv (garrows hF M₀) (fun _ => VarSymb) Γ s} (hwf : ρ.WF []) {y : VarSymb}
    {X : VarType} (hy : Γ.ref y = some (.VTypeDia X)) (hty : ShTop y (ρ.ref 0 y hy))
    {A : VarType} {a : Ann A} (hx : ∃ X, Γ.ref y = some (.VTypeDia X))
    (t : Term σ (Γ.diaIn y) A a) : ShTop y (Model.termShp ρ 0 (Term.diatm y hx t)) := by
  rw [Model.termShp_diatm ρ 0 hy]
  exact ⟨Shp.allL_label hty, shTop_termShp (envTop_diaPush_zero hwf hy hty) 1 le_rfl t⟩


/-! ## Construction steps -/

theorem boxEnt_path (ρ : ShFam hF M₀) {A : VarType}
    (g : (t : GW hF M₀) → VarSymb → GShape hF M₀ t A) (s : GW hF M₀) (v : VarSymb)
    {P P' : List ℕ} (e : P = P') (t : GW hF M₀) (h : t.1 = nodeOf s.1 P)
    (h' : t.1 = nodeOf s.1 P') : boxEnt ρ g s v P t h = boxEnt ρ g s v P' t h' := by
  subst e
  rfl

/-- A projection step moves a construction step's shape to the projected address's. -/
theorem cStep_proj (ρ : ShFam hF M₀) (s : GW hF M₀) (v : VarSymb)
    {U T : VarType} {st : Step} (hs : st.isProj = true) (h : U.step st = some T) :
    GFunc.shp (GFunc.proj (σ := σ) hs h) 0 (CStep ρ U s v) =
      CStep ρ T s (.step v st) := by
  cases U <;> cases st <;> (try cases hs) <;> (try cases h)
  · rfl
  · rfl
  · obtain ⟨hT, rfl⟩ := VarType.step_here h
    change (Arrows.transposeShp (F := garrows hF M₀) (Root := fun _ => VarSymb) fun a =>
        boxEnt ρ (fun t w => CStep ρ _ t w) s v (pathOf a.2.down) a.1 (pathOf_eq a.2.down)).map
        (Arrows.Leaf.collapse hT 0) = _
    rw [Model.transpose_collapse_zero hT]
    change boxEnt ρ (fun t w => CStep ρ _ t w) s v (pathOf (grefl hT s)) s
      (pathOf_eq (grefl hT s)) = _
    rw [boxEnt_path ρ _ s v (pathOf_refl hT s) s _ rfl]
    rfl

/-! ## A step's `◇`-shapes are self-rooted -/

theorem rootSh_top (s : GW hF M₀) (v : VarSymb) :
    ∀ (π : List Step) (T : VarType), ShTop v (rootSh s v π T)
  | _, .Var => trivial
  | _, .VTypeOne => trivial
  | _, .VTypeProd A C => ⟨rootSh_top s v _ A, rootSh_top s v _ C⟩
  | _, .VTypeBox A => rootSh_top s v _ A
  | _, .VTypeDia A => ⟨rfl, rootSh_top s v _ A⟩

theorem genDia_top (s : GW hF M₀) (v : VarSymb) (A : VarType) : ShTop v (genDia s v A) :=
  ⟨rfl, rootSh_top s v [.dia] A⟩

/-- A pull-back is self-rooted at the lifted root. -/
theorem pbShp_top {s t : GW hF M₀} (m : VarSymb) :
    ∀ (lw : List Bool) {T : VarType} (S : GShape hF M₀ t T),
      ShTop m (pbShp hF M₀ (s := s) m lw S)
  | _, _, .var => trivial
  | _, _, .one => trivial
  | lw, _, .prod a b => ⟨pbShp_top m lw a, pbShp_top m lw b⟩
  | _, _, .box a => pbShp_top m _ a
  | _, _, .dia (.root _ _) a => ⟨rfl, pbShp_top m _ a⟩
  | _, _, .dia (.fam _) a => ⟨trivial, pbShp_top m _ a⟩

theorem liftDiaAt_top (ρ : ShFam hF M₀) (s : GW hF M₀) (z : ℕ) (t : GW hF M₀) (e : LTerm σ)
    (A : VarType) : ShTop (.root (.free z)) (liftDiaAt ρ s z t e A) := by
  unfold liftDiaAt
  split
  · exact pbShp_top _ [] _
  · exact genDia_top _ _ _

/-- The kept witness of an address whose kept item is an address is that address. -/
theorem wit_of_inl {t : GW hF M₀} {x y : VarSymb} (hx : PPath x.path)
    (h : fmapL hF M₀ t.1 (.step x .keep) = .inl y) : wit t x = y := by
  have e := eIdx_item (fmapL hF M₀ t.1) hx (s := .keep) rfl []
  change eIdx _ ((VarSymb.step x .keep).ext []) = _
  rw [e, h]
  rfl

theorem diaT_top (ρ : ShFam hF M₀) :
    ∀ (p : Node) (hp : GBorn hF M₀ p) (v : VarSymb) (A : VarType), ShTop v (diaT ρ p hp v A)
  | [], hp, v, A => by
      unfold diaT
      split
      · rename_i h
        have := liftDiaAt_top ρ ⟨[], hp⟩ h.choose h.choose_spec.2.child h.choose_spec.2.ent A
        exact (congrArg (fun y => ShTop y _) h.choose_spec.1).mpr this
      · exact genDia_top _ _ _
  | c :: p, hp, v, A => by
      unfold diaT
      split
      · rename_i h
        have := liftDiaAt_top ρ ⟨c :: p, hp⟩ h.choose h.choose_spec.2.child
          h.choose_spec.2.ent A
        exact (congrArg (fun y => ShTop y _) h.choose_spec.1).mpr this
      · split
        · rename_i h'
          refine Shp.allL_map (fun ℓ hℓ => ?_) _ (diaT_top ρ p _ _ A)
          match ℓ, hℓ with
          | .root r q, hℓ =>
              change r = _ at hℓ
              subst hℓ
              change Arrows.RootKeep.keep (F := garrows hF M₀) (Root := fun _ => VarSymb) hF _
                (edgeAcc (s := ⟨p, gborn_parent hp⟩) (t := ⟨c :: p, hp⟩) rfl) = _
              rw [rootKeep_edge]
              exact wit_of_inl (fun _ h => by cases h) h'.choose_spec
          | .fam _, _ => trivial
        · exact genDia_top _ _ _

/-- ⭐**A construction step's `◇`-shapes are self-rooted at their address.** -/
theorem cStep_top (ρ : ShFam hF M₀) (s : GW hF M₀) (v : VarSymb)
    (A : VarType) : ShTop v (CStep ρ (.VTypeDia A) s v) := by
  exact diaT_top ρ s.1 s.2 v A

/-! ## The pull-back along the lift edge -/

/-- ⭐**Keeping a pull-back along the edge gives the shape back**, when the shape is self-rooted at
    the edge's kept witness of the lifted root. -/
theorem keepAlong_pbShp {s t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: s.1) (m : VarSymb) :
    ∀ (lw : List Bool) {T : VarType} (S : GShape hF M₀ t T), ShTop (wit t m) S →
      (pbShp hF M₀ (s := s) m lw S).map (Arrows.Leaf.keepAlong hF (edgeAcc hc)) = S
  | _, _, .var, _ => rfl
  | _, _, .one, _ => rfl
  | lw, _, .prod a b, h => by
      simp only [pbShp, Shp.map]
      rw [keepAlong_pbShp hc m lw a h.1, keepAlong_pbShp hc m lw b h.2]
  | _, _, .box a, h => by
      simp only [pbShp, Shp.map]
      rw [keepAlong_pbShp hc m _ a h]
  | lw, _, .dia ℓ a, h => by
      simp only [pbShp, Shp.map]
      rw [keepAlong_pbLeaf hc m lw ℓ (fun r p e => by subst e; exact h.1),
        keepAlong_pbShp hc m _ a h.2]

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem LTerm.diaOf_idx {e : LTerm σ} {A : VarType} {b : Ann (.VTypeDia A)}
    {τ : Term σ (ctxOf e.1) (.VTypeDia A) b} (hd : e.diaOf A = some ⟨b, τ⟩) :
    entIdx (.inr e) [] = b.idxAt [] := by
  obtain ⟨l, T, a, τ₀⟩ := e
  cases T with
  | VTypeDia A' =>
      by_cases h : A' = A
      · subst h
        simp only [LTerm.diaOf, dite_true, Option.some.injEq, Sigma.mk.injEq] at hd
        obtain ⟨rfl, -⟩ := hd
        rfl
      · simp [LTerm.diaOf, h] at hd
  | Var => cases hd
  | VTypeOne => cases hd
  | VTypeProd _ _ => cases hd
  | VTypeBox _ => cases hd

/-- ⭐**(C2) along the lift edge, for templates**: a lifted root's template kept along its lift
    edge is its lifted term's shape. -/
theorem liftDiaAt_keep {ρ : ShFam hF M₀}
    (hwf : ∀ t v T, Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (ρ t v T))
    {s t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: s.1) {z : ℕ} {e : LTerm σ} {A : VarType}
    (href : ∀ (v : VarSymb) (T : VarType) (h : (ctxOf e.1).ref v = some T),
      (famEnv ρ (ctxOf e.1) t).ref 0 v h = ρ t v T)
    (htop : ∀ v X, (ctxOf e.1).ref v = some (.VTypeDia X) → ShTop v (ρ t v (.VTypeDia X)))
    (he : fmapL hF M₀ t.1 (.step (.root (.free z)) .keep) = .inr e)
    {b : Ann (.VTypeDia A)} {τ : Term σ (ctxOf e.1) (.VTypeDia A) b}
    (hd : e.diaOf A = some ⟨b, τ⟩) :
    (liftDiaAt ρ s z t e A).map (Arrows.Leaf.keepAlong hF (edgeAcc hc)) =
      Model.termShp (famEnv ρ (ctxOf e.1) t) 0 τ := by
  have hw : wit t (.root (.free z)) = b.idxAt [] := by
    have e' := eIdx_item (fmapL hF M₀ t.1) (u := .root (.free z)) (fun _ h => by cases h)
      (s := .keep) rfl []
    change eIdx _ ((VarSymb.step (.root (.free z)) .keep).ext []) = _
    rw [e', he]
    exact LTerm.diaOf_idx hd
  unfold liftDiaAt
  rw [hd]
  refine keepAlong_pbShp hc _ [] _ ?_
  rw [hw]
  cases τ with
  | diatm y hy w =>
      obtain ⟨X, hr⟩ := hy
      refine shTop_termShp_dia (famEnv_wf hwf _ t) hr ?_ _ w
      rw [href]
      exact htop y X hr
end GArrow

end V12M
