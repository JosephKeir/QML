import QML.QML_v12m_InterpLemmas

/-!
# QML v12m — semantics: the shapes of values

Under T a possible object carries a **shape**, its semantic annotation (docs §10.27–10.28), and
possible objects are identified only by section *and* shape (`Model.pos_inj`).  So every lemma that
identifies two values of possible terms needs the two shapes to agree.  This file computes them.

The shape of a term's value is computed **symbolically**, by the same recursion as the value but
with shapes in place of objects:

* a **shape environment** (`ShEnv`) gives a shape, anchored at the current world, for each visible
  address, and is pushed into `□` and `◇_x` views (`ShEnv.boxPush`, `ShEnv.diaPush`) without ever
  choosing an arrow — which is what lets it see inside a possible object whose extent is empty;
* `termShp ρ j t` is the shape of `t`, `j` being the number of levels above the current position;
* ⭐`termShp_compile` (S1): compiling a term and moving the shape of its bundle along the compiled
  map (`GFunc.shp`) gives `termShp` — the counterpart of `Term.compile_eval`.
-/

namespace V12M

variable [ModalSys]

universe y

/-! ## Commuting collapses and shifts

The simplicial identities between collapsing and shifting levels, first on paths, then on leaves.
They let a collapse or shift applied to a whole shape environment be moved through `termShp`. -/

namespace Step

omit [ModalSys] in
theorem collapseAt_proj {s : Step} (hs : s.isProj = true) (i : ℕ) (p : List Step) :
    collapseAt i (s :: p) = s :: collapseAt i p := by
  simp only [collapseAt, if_pos hs]

omit [ModalSys] in
theorem shiftAt_proj {s : Step} (hs : s.isProj = true) (i : ℕ) (p : List Step) :
    shiftAt i (s :: p) = s :: shiftAt i p := by
  simp only [shiftAt, if_pos hs]

omit [ModalSys] in
theorem collapseAt_succ {s : Step} (hs : ¬ s.isProj = true) (i : ℕ) (p : List Step) :
    collapseAt (i + 1) (s :: p) = s :: collapseAt i p := by
  simp only [collapseAt, if_neg hs]

omit [ModalSys] in
theorem shiftAt_succ {s : Step} (hs : ¬ s.isProj = true) (i : ℕ) (p : List Step) :
    shiftAt (i + 1) (s :: p) = s :: shiftAt i p := by
  simp only [shiftAt, if_neg hs]

omit [ModalSys] in
theorem collapseAt_zero {s : Step} (hs : ¬ s.isProj = true) (p : List Step) :
    collapseAt 0 (s :: p) = if s = .keep then p else .here :: p := by
  simp only [collapseAt, if_neg hs]

omit [ModalSys] in
theorem shiftAt_zero {s : Step} (hs : ¬ s.isProj = true) (p : List Step) :
    shiftAt 0 (s :: p) = .keep :: s :: p := by
  simp only [shiftAt, if_neg hs]

omit [ModalSys] in
theorem collapseAt_collapseAt : ∀ (j d : ℕ) (p : List Step),
    collapseAt (j + d) (collapseAt j p) = collapseAt j (collapseAt (j + d + 1) p)
  | _, _, [] => rfl
  | j, d, s :: p => by
      by_cases hs : s.isProj = true
      · rw [collapseAt_proj hs, collapseAt_proj hs, collapseAt_proj hs, collapseAt_proj hs,
          collapseAt_collapseAt j d p]
      · cases j with
        | zero =>
            rw [Nat.zero_add, collapseAt_zero hs, collapseAt_succ hs, collapseAt_zero hs]
            split_ifs
            · rfl
            · rw [collapseAt_proj rfl]
        | succ j =>
            rw [collapseAt_succ hs, show j + 1 + d = (j + d) + 1 by omega, collapseAt_succ hs,
              show j + d + 1 + 1 = (j + d + 1) + 1 by omega, collapseAt_succ hs, collapseAt_succ hs,
              collapseAt_collapseAt j d p]

omit [ModalSys] in
theorem shiftAt_collapseAt : ∀ (j d : ℕ) (p : List Step),
    shiftAt (j + d) (collapseAt j p) = collapseAt j (shiftAt (j + d + 1) p)
  | _, _, [] => rfl
  | j, d, s :: p => by
      by_cases hs : s.isProj = true
      · rw [collapseAt_proj hs, shiftAt_proj hs, shiftAt_proj hs, collapseAt_proj hs,
          shiftAt_collapseAt j d p]
      · cases j with
        | zero =>
            rw [Nat.zero_add, collapseAt_zero hs, shiftAt_succ hs, collapseAt_zero hs]
            split_ifs
            · rfl
            · rw [shiftAt_proj rfl]
        | succ j =>
            rw [collapseAt_succ hs, show j + 1 + d = (j + d) + 1 by omega, shiftAt_succ hs,
              show j + d + 1 + 1 = (j + d + 1) + 1 by omega, shiftAt_succ hs, collapseAt_succ hs,
              shiftAt_collapseAt j d p]

omit [ModalSys] in
theorem collapseAt_shiftAt_self : ∀ (j : ℕ) (p : List Step), collapseAt j (shiftAt j p) = p
  | _, [] => rfl
  | j, s :: p => by
      by_cases hs : s.isProj = true
      · rw [shiftAt_proj hs, collapseAt_proj hs, collapseAt_shiftAt_self j p]
      · cases j with
        | zero =>
            rw [shiftAt_zero hs, collapseAt_zero (by decide : ¬ Step.keep.isProj = true),
              if_pos rfl]
        | succ j => rw [shiftAt_succ hs, collapseAt_succ hs, collapseAt_shiftAt_self j p]

omit [ModalSys] in
theorem collapseAt_shiftAt : ∀ (j d : ℕ) (p : List Step),
    collapseAt (j + d + 2) (shiftAt j p) = shiftAt j (collapseAt (j + d + 1) p)
  | _, _, [] => rfl
  | j, d, s :: p => by
      by_cases hs : s.isProj = true
      · rw [shiftAt_proj hs, collapseAt_proj hs, collapseAt_proj hs, shiftAt_proj hs,
          collapseAt_shiftAt j d p]
      · have hk : ¬ Step.keep.isProj = true := by decide
        cases j with
        | zero =>
            rw [shiftAt_zero hs, Nat.zero_add, collapseAt_succ hk, collapseAt_succ hs,
              shiftAt_zero hs]
        | succ j =>
            rw [shiftAt_succ hs, show j + 1 + d + 2 = (j + d + 2) + 1 by omega, collapseAt_succ hs,
              show j + 1 + d + 1 = (j + d + 1) + 1 by omega, collapseAt_succ hs, shiftAt_succ hs,
              collapseAt_shiftAt j d p]

omit [ModalSys] in
theorem shiftAt_shiftAt : ∀ (j d : ℕ) (p : List Step),
    shiftAt (j + d + 2) (shiftAt j p) = shiftAt j (shiftAt (j + d + 1) p)
  | _, _, [] => rfl
  | j, d, s :: p => by
      by_cases hs : s.isProj = true
      · rw [shiftAt_proj hs, shiftAt_proj hs, shiftAt_proj hs, shiftAt_proj hs,
          shiftAt_shiftAt j d p]
      · have hk : ¬ Step.keep.isProj = true := by decide
        cases j with
        | zero =>
            rw [shiftAt_zero hs, Nat.zero_add, shiftAt_succ hk, shiftAt_succ hs, shiftAt_zero hs]
        | succ j =>
            rw [shiftAt_succ hs, show j + 1 + d + 2 = (j + d + 2) + 1 by omega, shiftAt_succ hs,
              show j + 1 + d + 1 = (j + d + 1) + 1 by omega, shiftAt_succ hs, shiftAt_succ hs,
              shiftAt_shiftAt j d p]

omit [ModalSys] in
theorem shiftAt_shiftAt_self : ∀ (j : ℕ) (p : List Step),
    shiftAt (j + 1) (shiftAt j p) = shiftAt j (shiftAt j p)
  | _, [] => rfl
  | j, s :: p => by
      by_cases hs : s.isProj = true
      · simp only [shiftAt_proj hs]
        rw [shiftAt_shiftAt_self j p]
      · have hk : ¬ Step.keep.isProj = true := by decide
        cases j with
        | zero => rw [shiftAt_zero hs, shiftAt_succ hk, shiftAt_zero hs, shiftAt_zero hk]
        | succ j =>
            simp only [shiftAt_succ hs]
            rw [shiftAt_shiftAt_self j p]

end Step

namespace Frame.Leaf

variable {σ : Signature} {F : Frame.{u, v} σ} {Root : F.W → Type u}

theorem collapse_root (hT : ModalSys.T = true) (i : ℕ) {w : F.W} (r : Root w) (p : List Step) :
    collapse hT i (Frame.Leaf.root (F := F) r p) = .root r (Step.collapseAt i p) := by
  cases i <;> rfl

theorem shift_root (hF : ModalSys.Four = true) (i : ℕ) {w : F.W} (r : Root w) (p : List Step) :
    shift hF i (Frame.Leaf.root (F := F) r p) = .root r (Step.shiftAt i p) := by
  cases i <;> rfl

theorem collapse_collapse (hT : ModalSys.T = true) :
    ∀ (j d : ℕ) {w : F.W} (ℓ : Frame.Leaf F Root w),
      collapse hT (j + d) (collapse hT j ℓ) = collapse hT j (collapse hT (j + d + 1) ℓ)
  | j, d, _, .root r p => by
      simp only [collapse_root]
      exact congrArg (Frame.Leaf.root r) (Step.collapseAt_collapseAt j d p)
  | 0, d, w, .fam f => by
      rw [Nat.zero_add]
      rfl
  | j + 1, d, _, .fam f => by
      rw [show j + 1 + d = (j + d) + 1 by omega]
      exact congrArg Frame.Leaf.fam (funext fun s => collapse_collapse hT j d (f s))

theorem shift_collapse (hT : ModalSys.T = true) (hF : ModalSys.Four = true) :
    ∀ (j d : ℕ) {w : F.W} (ℓ : Frame.Leaf F Root w),
      shift hF (j + d) (collapse hT j ℓ) = collapse hT j (shift hF (j + d + 1) ℓ)
  | j, d, _, .root r p => by
      simp only [collapse_root, shift_root]
      exact congrArg (Frame.Leaf.root r) (Step.shiftAt_collapseAt j d p)
  | 0, d, w, .fam f => by
      rw [Nat.zero_add]
      rfl
  | j + 1, d, _, .fam f => by
      rw [show j + 1 + d = (j + d) + 1 by omega]
      exact congrArg Frame.Leaf.fam (funext fun s => shift_collapse hT hF j d (f s))

theorem collapse_shift_self (hT : ModalSys.T = true) (hF : ModalSys.Four = true) :
    ∀ (j : ℕ) {w : F.W} (ℓ : Frame.Leaf F Root w), collapse hT j (shift hF j ℓ) = ℓ
  | j, _, .root r p => by
      simp only [collapse_root, shift_root]
      exact congrArg (Frame.Leaf.root r) (Step.collapseAt_shiftAt_self j p)
  | 0, w, .fam f => by
      refine congrArg Frame.Leaf.fam (funext fun t => ?_)
      change f ⟨t.1, ⟨F.trans hF (F.refl hT w) t.2.down⟩⟩ = f t
      rw [F.refl_trans hT hF]
  | j + 1, _, .fam f =>
      congrArg Frame.Leaf.fam (funext fun s => collapse_shift_self hT hF j (f s))

theorem collapse_shift (hT : ModalSys.T = true) (hF : ModalSys.Four = true) :
    ∀ (j d : ℕ) {w : F.W} (ℓ : Frame.Leaf F Root w),
      collapse hT (j + d + 2) (shift hF j ℓ) = shift hF j (collapse hT (j + d + 1) ℓ)
  | j, d, _, .root r p => by
      simp only [collapse_root, shift_root]
      exact congrArg (Frame.Leaf.root r) (Step.collapseAt_shiftAt j d p)
  | 0, d, w, .fam f => by
      rw [Nat.zero_add]
      rfl
  | j + 1, d, _, .fam f => by
      rw [show j + 1 + d + 2 = (j + d + 2) + 1 by omega,
        show j + 1 + d + 1 = (j + d + 1) + 1 by omega]
      exact congrArg Frame.Leaf.fam (funext fun s => collapse_shift hT hF j d (f s))

theorem shift_shift (hF : ModalSys.Four = true) :
    ∀ (j d : ℕ) {w : F.W} (ℓ : Frame.Leaf F Root w),
      shift hF (j + d + 2) (shift hF j ℓ) = shift hF j (shift hF (j + d + 1) ℓ)
  | j, d, _, .root r p => by
      simp only [shift_root]
      exact congrArg (Frame.Leaf.root r) (Step.shiftAt_shiftAt j d p)
  | 0, d, w, .fam f => by
      rw [Nat.zero_add]
      rfl
  | j + 1, d, _, .fam f => by
      rw [show j + 1 + d + 2 = (j + d + 2) + 1 by omega,
        show j + 1 + d + 1 = (j + d + 1) + 1 by omega]
      exact congrArg Frame.Leaf.fam (funext fun s => shift_shift hF j d (f s))

theorem shift_shift_self (hF : ModalSys.Four = true) :
    ∀ (j : ℕ) {w : F.W} (ℓ : Frame.Leaf F Root w),
      shift hF (j + 1) (shift hF j ℓ) = shift hF j (shift hF j ℓ)
  | j, _, .root r p => by
      simp only [shift_root]
      exact congrArg (Frame.Leaf.root r) (Step.shiftAt_shiftAt_self j p)
  | 0, w, .fam f => by
      refine congrArg Frame.Leaf.fam (funext fun s => congrArg Frame.Leaf.fam
        (funext fun t => congrArg Frame.Leaf.fam (funext fun t' => ?_)))
      change f ⟨t'.1, ⟨F.trans hF s.2.down (F.trans hF t.2.down t'.2.down)⟩⟩ =
        f ⟨t'.1, ⟨F.trans hF (F.trans hF s.2.down t.2.down) t'.2.down⟩⟩
      rw [F.trans_assoc hF]
  | j + 1, _, .fam f =>
      congrArg Frame.Leaf.fam (funext fun s => shift_shift_self hF j (f s))

end Frame.Leaf

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

variable (M) in
/-- Shapes anchored at a world. -/
abbrev Shape (w : M.frame.W) (T : VarType) : Type (max u v) :=
  Shp (M.frame.Leaf M.RootPoss w) T

variable (M) in
/-- A shape environment: a shape, anchored at `w`, for every visible address. -/
abbrev ShEnv (Γ : Ctx) (w : M.frame.W) : Type (max u v) :=
  ∀ v T, Γ v = some T → M.Shape w T

/-- The shape at a reachable address: projection components from the parent, moved as the
    projection moves them (`GFunc.proj`, so a `here` step collapses the level `j`). -/
def ShEnv.ref {Γ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Γ w) (j : ℕ) :
    (v : VarSymb) → {T : VarType} → Γ.ref v = some T → M.Shape w T
  | .root r, _, h => ρ (.root r) _ h
  | .step v s, T, h =>
      if hs : s.isProj = true then
        match hU : Γ.ref v with
        | some _ =>
            GFunc.shp (GFunc.proj (σ := σ) hs (by rw [Ctx.ref_step_proj Γ v hs, hU] at h; exact h))
              j (ShEnv.ref ρ j v hU)
        | none => False.elim (by rw [Ctx.ref_step_proj Γ v hs, hU] at h; cases h)
      else ρ (.step v s) T (by rw [Ctx.ref_step_nonproj Γ v hs] at h; exact h)

/-- Into a `□`: the shapes of the contents, one level further in. -/
def ShEnv.boxPush {Γ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Γ w) (j : ℕ) : M.ShEnv Γ.boxIn w
  | .step u .box, _, h => (ρ.ref j u (Ctx.boxIn_step_box h)).inner
  | .step u .keep, _, h =>
      (GFunc.shp (GFunc.keep (σ := σ) (Ctx.boxIn_keep h).1 (Ctx.boxIn_keep h).2.2) j
        (ρ.ref j u (Ctx.boxIn_keep h).2.1)).inner
  | .root _, _, h => False.elim (by cases h)
  | .step _ .fst, _, h => False.elim (by cases h)
  | .step _ .snd, _, h => False.elim (by cases h)
  | .step _ .dia, _, h => False.elim (by cases h)
  | .step _ .here, _, h => False.elim (by cases h)

/-- Into a `◇_x`: the shape of `x`'s content, and the `□` view as for `boxPush`. -/
def ShEnv.diaPush {Γ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Γ w) (j : ℕ) (x : VarSymb)
    {X : VarType} (hx : Γ.ref x = some (.VTypeDia X)) : M.ShEnv (Γ.diaIn x) w
  | .step _ .dia, _, h => Ctx.diaIn_step_dia hx h ▸ (ρ.ref j x hx).body
  | .step u .box, T, h => ρ.boxPush j (.step u .box) T h
  | .step u .keep, T, h => ρ.boxPush j (.step u .keep) T h
  | .root _, _, h => False.elim (by cases h)
  | .step _ .fst, _, h => False.elim (by cases h)
  | .step _ .snd, _, h => False.elim (by cases h)
  | .step _ .here, _, h => False.elim (by cases h)

/-- The shape of the tuple of a support. -/
def ShEnv.bundle {Δ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Δ w) :
    (L : Supp Δ) → M.Shape w (Supp.ty L)
  | [] => .one
  | e :: L => .prod (ρ e.1 e.2.1 e.2.2) (ShEnv.bundle ρ L)

mutual
  /-- Function terms carry no shape. -/
  def funcShp {Δ : Ctx} {w : M.frame.W} (_ρ : M.ShEnv Δ w) (_j : ℕ) :
      {n : ℕ} → Func σ Δ n → PUnit.{1}
    | _, .F _ => PUnit.unit
    | _, .eval _ _ => PUnit.unit

  /-- ⭐The shape of a term's value, computed symbolically. -/
  def termShp {Δ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Δ w) (j : ℕ) :
      {T : VarType} → {a : Ann T} → Term σ Δ T a → M.Shape w T
    | _, _, .var _ _ => .var
    | _, _, .func _ => .var
    | _, _, .unit => .one
    | _, _, .pair s t => .prod (termShp ρ j s) (termShp ρ j t)
    | _, _, .boxtm t => .box (termShp (ρ.boxPush j) (j + 1) t)
    | _, _, .diatm x hx t =>
        match hr : Δ.ref x with
        | some (.VTypeDia _) =>
            .dia (ρ.ref j x hr).label (termShp (ρ.diaPush j x hr) (j + 1) t)
        | some .Var => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
        | some .VTypeOne => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
        | some (.VTypeProd _ _) => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
        | some (.VTypeBox _) => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
        | none => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
end

/-! ## S1: compilation moves shapes as `termShp` computes them -/

omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.label_dia {L : Type*} {A : VarType} (ℓ : L) (a : Shp L A) :
    (Shp.dia ℓ a).label = ℓ := rfl

omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.body_dia {L : Type*} {A : VarType} (ℓ : L) (a : Shp L A) :
    (Shp.dia ℓ a).body = a := rfl

omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.fst_prod {L : Type*} {A B : VarType} (a : Shp L A)
    (b : Shp L B) : (Shp.prod a b).fst = a := rfl

omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.snd_prod {L : Type*} {A B : VarType} (a : Shp L A)
    (b : Shp L B) : (Shp.prod a b).snd = b := rfl

omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.inner_box {L : Type*} {A : VarType} (a : Shp L A) :
    (Shp.box a).inner = a := rfl

theorem shp_var_eq {w : M.frame.W} : ∀ a b : M.Shape w .Var, a = b
  | .var, .var => rfl

theorem shp_ofEq {w : M.frame.W} {A B : VarType} (h : A = B) (j : ℕ) (a : M.Shape w A) :
    GFunc.shp (GFunc.ofEq (σ := σ) h) j a = cast (congrArg (M.Shape w) h) a := by
  subst h
  rfl

theorem lookup_shp {Δ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Δ w) (j : ℕ) :
    ∀ (L : Supp Δ) (v : VarSymb) {T : VarType} (h : Δ v = some T)
      (hm : v ∈ List.map PSigma.fst L),
      GFunc.shp (Supp.lookup (σ := σ) L v h hm) j (ρ.bundle L) = ρ v T h
  | [], _, _, _, hm => absurd hm List.not_mem_nil
  | ⟨v', T', h'⟩ :: L, v, T, h, hm => by
      by_cases hvv : v' = v
      · subst hvv
        have hT : T' = T := Option.some.inj (h'.symm.trans h)
        subst hT
        rw [Supp.lookup, dif_pos rfl]
        simp only [GFunc.shp, shp_ofEq, cast_eq, ShEnv.bundle, Shp.fst]
      · rw [Supp.lookup, dif_neg hvv]
        simp only [GFunc.shp, ShEnv.bundle, Shp.snd]
        exact lookup_shp ρ j L v h _

theorem refGF_shp {Δ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Δ w) (j : ℕ) (L : Supp Δ) :
    ∀ (v : VarSymb) {T : VarType} (h : Δ.ref v = some T)
      (hm : v.base ∈ List.map PSigma.fst L),
      GFunc.shp (Supp.refGF (σ := σ) L v h hm) j (ρ.bundle L) = ρ.ref j v h
  | .root r, _, h, hm => lookup_shp ρ j L (.root r) h hm
  | .step v s, T, h, hm => by
      by_cases hs : s.isProj = true
      · rw [Supp.refGF, ShEnv.ref, dif_pos hs, dif_pos hs]
        split
        · rename_i U hU
          simp only [GFunc.shp]
          rw [refGF_shp ρ j L v hU]
          split
          · rename_i U' hU'
            have hUU : U = U' := Option.some.inj (hU.symm.trans hU')
            subst hUU
            rfl
          · rename_i hU'
            exfalso
            rw [hU] at hU'
            cases hU'
        · rename_i hU
          exfalso
          rw [Ctx.ref_step_proj Δ v hs, hU] at h
          cases h
      · rw [Supp.refGF, ShEnv.ref, dif_neg hs, dif_neg hs]
        exact lookup_shp ρ j L _ _ _

theorem gatherBox_shp {Δ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Δ w) (j : ℕ) (L : Supp Δ) :
    ∀ (L' : Supp Δ.boxIn) (hL : ∀ e ∈ Supp.outerBox L', e.1 ∈ List.map PSigma.fst L),
      GFunc.shp (Supp.gatherBox (σ := σ) L L' hL) j (ρ.bundle L) =
        .box ((ρ.boxPush j).bundle L')
  | [], _ => rfl
  | ⟨.step u .box, T, h⟩ :: L', hL => by
      simp only [Supp.gatherBox, GFunc.shp, Shp.fst, Shp.snd, Shp.inner]
      rw [refGF_shp, gatherBox_shp ρ j L L']
      rfl
  | ⟨.step u .keep, T, h⟩ :: L', hL => by
      simp only [Supp.gatherBox, GFunc.shp, Shp.fst, Shp.snd, Shp.inner]
      rw [refGF_shp, gatherBox_shp ρ j L L']
      rfl
  | ⟨.root _, _, h⟩ :: _, _ => by cases h
  | ⟨.step _ .fst, _, h⟩ :: _, _ => by cases h
  | ⟨.step _ .snd, _, h⟩ :: _, _ => by cases h
  | ⟨.step _ .dia, _, h⟩ :: _, _ => by cases h

theorem assemble_shp {Δ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Δ w) (j : ℕ) {x : VarSymb}
    {X : VarType} (hr : Δ.ref x = some (.VTypeDia X)) :
    ∀ (L : Supp (Δ.diaIn x)),
      GFunc.shp (Supp.assemble (σ := σ) hr L) (j + 1)
          (.prod ((ρ.boxPush j).bundle (Supp.boxPart L)) (ρ.ref j x hr).body) =
        (ρ.diaPush j x hr).bundle L
  | [] => rfl
  | ⟨.step u .box, T, h⟩ :: L => by
      simp only [Supp.assemble, Supp.boxPart, GFunc.shp, ShEnv.bundle, Shp.fst, Shp.snd]
      rw [assemble_shp ρ j hr L]
      rfl
  | ⟨.step u .keep, T, h⟩ :: L => by
      simp only [Supp.assemble, Supp.boxPart, GFunc.shp, ShEnv.bundle, Shp.fst, Shp.snd]
      rw [assemble_shp ρ j hr L]
      rfl
  | ⟨.step u .dia, T, h⟩ :: L => by
      have hXT := Ctx.diaIn_step_dia hr h
      subst hXT
      simp only [Supp.assemble, Supp.boxPart, GFunc.shp, ShEnv.bundle, Shp.snd]
      rw [assemble_shp ρ j hr L, shp_ofEq, cast_eq]
      rfl
  | ⟨.root _, _, h⟩ :: _ => by cases h
  | ⟨.step _ .fst, _, h⟩ :: _ => by cases h
  | ⟨.step _ .snd, _, h⟩ :: _ => by cases h

/-- ⭐**S1**: compilation is faithful to shapes — the counterpart of `Term.compile_eval`. -/
theorem termShp_compile {Δ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Δ w) (j : ℕ) (L : Supp Δ) :
    ∀ {T : VarType} {a : Ann T} (t : Term σ Δ T a)
      (hL : ∀ e ∈ Term.bases t, e.1 ∈ List.map PSigma.fst L),
      GFunc.shp (Term.compile L t hL) j (ρ.bundle L) = termShp ρ j t
  | _, _, .var _ _, _ => shp_var_eq _ _
  | _, _, .func _, _ => shp_var_eq _ _
  | _, _, .unit, _ => rfl
  | _, _, .pair s t, hL => by
      simp only [Term.compile, GFunc.shp, termShp]
      rw [termShp_compile ρ j L s, termShp_compile ρ j L t]
  | _, _, .boxtm t, hL => by
      simp only [Term.compile, GFunc.shp, termShp]
      rw [gatherBox_shp]
      simp only [Shp.inner]
      rw [termShp_compile (ρ.boxPush j) (j + 1) (Term.bases t) t]
  | _, _, .diatm x hx t, hL => by
      simp only [Term.compile, termShp]
      split
      · rename_i X hr
        split
        · rename_i X' hr'
          obtain rfl : X = X' := by
            rw [hr] at hr'
            cases hr'
            rfl
          simp only [GFunc.shp]
          rw [gatherBox_shp, refGF_shp]
          simp only [Shp.fst_prod, Shp.snd_prod, Shp.inner_box, Shp.label_dia, Shp.body_dia]
          rw [assemble_shp ρ j hr, termShp_compile (ρ.diaPush j x hr) (j + 1) (Term.bases t) t]
        all_goals
          rename_i heq
          exfalso
          rw [hr] at heq
          cases heq
      all_goals
        rename_i heq
        exfalso
        obtain ⟨_, h⟩ := hx
        rw [heq] at h
        cases h

/-! ## Transposition: shapes along every arrow at once -/

omit [ModalSys] in
theorem _root_.V12M.Shp.one_eq {L : Type*} : ∀ a b : Shp L .VTypeOne, a = b
  | .one, .one => rfl

omit [ModalSys] in
theorem _root_.V12M.Shp.prod_eta {L : Type*} {A B : VarType} :
    ∀ a : Shp L (.VTypeProd A B), a = .prod a.fst a.snd
  | .prod _ _ => rfl

omit [ModalSys] in
theorem _root_.V12M.Shp.box_eta {L : Type*} {A : VarType} :
    ∀ a : Shp L (.VTypeBox A), a = .box a.inner
  | .box _ => rfl

omit [ModalSys] in
theorem _root_.V12M.Shp.dia_eta {L : Type*} {A : VarType} :
    ∀ a : Shp L (.VTypeDia A), a = .dia a.label a.body
  | .dia _ _ => rfl


omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.map_fst {L L' : Type y} (g : L → L') {A B : VarType} :
    ∀ a : Shp L (.VTypeProd A B), (a.map g).fst = a.fst.map g
  | .prod _ _ => rfl

omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.map_snd {L L' : Type y} (g : L → L') {A B : VarType} :
    ∀ a : Shp L (.VTypeProd A B), (a.map g).snd = a.snd.map g
  | .prod _ _ => rfl

omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.map_inner {L L' : Type y} (g : L → L') {A : VarType} :
    ∀ a : Shp L (.VTypeBox A), (a.map g).inner = a.inner.map g
  | .box _ => rfl

omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.map_label {L L' : Type y} (g : L → L') {A : VarType} :
    ∀ a : Shp L (.VTypeDia A), (a.map g).label = g a.label
  | .dia _ _ => rfl

omit [ModalSys] in
@[simp] theorem _root_.V12M.Shp.map_body {L L' : Type y} (g : L → L') {A : VarType} :
    ∀ a : Shp L (.VTypeDia A), (a.map g).body = a.body.map g
  | .dia _ _ => rfl

/-- A leaf map that acts on a family member by member passes through transposition. -/
theorem transpose_map {w : M.frame.W} (F : M.frame.Leaf M.RootPoss w → M.frame.Leaf M.RootPoss w)
    (G : ∀ s : M.frame.Acc w, M.frame.Leaf M.RootPoss s.1 → M.frame.Leaf M.RootPoss s.1)
    (hF : ∀ f, F (.fam f) = .fam fun s => G s (f s)) :
    ∀ {A : VarType} (g : (s : M.frame.Acc w) → M.Shape s.1 A),
      (Frame.transposeShp g).map F = Frame.transposeShp fun s => (g s).map (G s)
  | .Var, _ => rfl
  | .VTypeOne, _ => rfl
  | .VTypeProd _ _, g => by
      simp only [Frame.transposeShp, Shp.map]
      rw [transpose_map F G hF, transpose_map F G hF]
      simp only [Shp.map_fst, Shp.map_snd]
  | .VTypeBox _, g => by
      simp only [Frame.transposeShp, Shp.map]
      rw [transpose_map F G hF]
      simp only [Shp.map_inner]
  | .VTypeDia _, g => by
      simp only [Frame.transposeShp, Shp.map]
      rw [transpose_map F G hF, hF]
      simp only [Shp.map_label, Shp.map_body]

/-- Reading a transposed shape at the identity arrow gives the member there. -/
theorem transpose_collapse_zero (hT : ModalSys.T = true) {w : M.frame.W} :
    ∀ {A : VarType} (g : (s : M.frame.Acc w) → M.Shape s.1 A),
      (Frame.transposeShp g).map (Frame.Leaf.collapse hT 0) = g (M.frame.reflAcc hT w)
  | .Var, g => shp_var_eq _ _
  | .VTypeOne, g => Shp.one_eq _ _
  | .VTypeProd _ _, g => by
      simp only [Frame.transposeShp, Shp.map]
      rw [transpose_collapse_zero hT, transpose_collapse_zero hT]
      exact (Shp.prod_eta _).symm
  | .VTypeBox _, g => by
      simp only [Frame.transposeShp, Shp.map]
      rw [transpose_collapse_zero hT]
      exact (Shp.box_eta _).symm
  | .VTypeDia _, g => by
      simp only [Frame.transposeShp, Shp.map]
      rw [transpose_collapse_zero hT]
      exact (Shp.dia_eta _).symm

/-- Keeping a transposed shape: one family per arrow, of the members at the composite arrows. -/
theorem transpose_shift_zero (hF : ModalSys.Four = true) {w : M.frame.W} :
    ∀ {A : VarType} (g : (s : M.frame.Acc w) → M.Shape s.1 A),
      (Frame.transposeShp g).map (Frame.Leaf.shift hF 0) =
        Frame.transposeShp fun s => Frame.transposeShp fun t =>
          g ⟨t.1, ⟨M.frame.trans hF s.2.down t.2.down⟩⟩
  | .Var, _ => rfl
  | .VTypeOne, _ => rfl
  | .VTypeProd _ _, g => by
      simp only [Frame.transposeShp, Shp.map, Shp.fst_prod, Shp.snd_prod]
      rw [transpose_shift_zero hF, transpose_shift_zero hF]
  | .VTypeBox _, g => by
      simp only [Frame.transposeShp, Shp.map, Shp.inner_box]
      rw [transpose_shift_zero hF]
  | .VTypeDia _, g => by
      simp only [Frame.transposeShp, Shp.map, Shp.label_dia, Shp.body_dia]
      rw [transpose_shift_zero hF]
      rfl

/-- ⭐**Every map's shape transport commutes with transposition**, one level further out. -/
theorem shp_transpose {w : M.frame.W} :
    ∀ {A B : VarType} (f : GFunc σ A B) (j : ℕ) (g : (s : M.frame.Acc w) → M.Shape s.1 A),
      GFunc.shp f (j + 1) (Frame.transposeShp g) =
        Frame.transposeShp fun s => GFunc.shp f j (g s)
  | _, _, .id _, _, _ => rfl
  | _, _, .comp g f, j, h => by
      simp only [GFunc.shp]
      rw [shp_transpose f, shp_transpose g]
  | _, _, .fst, _, _ => rfl
  | _, _, .snd, _, _ => rfl
  | _, _, .pair f g, j, h => by
      simp only [GFunc.shp]
      rw [shp_transpose f, shp_transpose g]
      rfl
  | _, _, .unit _, _, _ => rfl
  | _, _, .func _ _, _, _ => rfl
  | _, _, .boxMap f, j, h => by
      simp only [GFunc.shp]
      rw [show (Frame.transposeShp h).inner = Frame.transposeShp fun s => (h s).inner from rfl,
        shp_transpose f]
      rfl
  | _, _, .boxPair _ _, _, _ => rfl
  | _, _, .boxUnit, _, _ => rfl
  | _, _, .diaMap f, j, h => by
      simp only [GFunc.shp]
      rw [show (Frame.transposeShp h).body = Frame.transposeShp fun s => (h s).body from rfl,
        shp_transpose f]
      rfl
  | _, _, .strength _ _, _, _ => rfl
  | _, _, .extract hT, j, h => by
      simp only [GFunc.shp]
      exact transpose_map _ _ (fun _ => rfl) _
  | _, _, .dup hF, j, h => by
      simp only [GFunc.shp]
      rw [show (Frame.transposeShp h).inner = Frame.transposeShp fun s => (h s).inner from rfl,
        transpose_map _ _ (fun _ => rfl)]
      rfl

/-! ### Unfolding lemmas -/

theorem ShEnv.ref_proj {Γ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Γ w) (j : ℕ) {v : VarSymb}
    {s : Step} (hs : s.isProj = true) {U T : VarType} (hU : Γ.ref v = some U)
    (h : Γ.ref (.step v s) = some T) :
    ρ.ref j (.step v s) h =
      GFunc.shp (GFunc.proj (σ := σ) hs (by rw [Ctx.ref_step_proj Γ v hs, hU] at h; exact h)) j
        (ρ.ref j v hU) := by
  rw [ShEnv.ref, dif_pos hs]
  split
  · rename_i U' hU'
    obtain rfl : U = U' := Option.some.inj (hU.symm.trans hU')
    rfl
  · rename_i hU'
    exfalso
    rw [hU] at hU'
    cases hU'

theorem ShEnv.ref_nonproj {Γ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Γ w) (j : ℕ) {v : VarSymb}
    {s : Step} (hs : ¬ s.isProj = true) {T : VarType} (h : Γ.ref (.step v s) = some T) :
    ρ.ref j (.step v s) h = ρ (.step v s) T (by rw [Ctx.ref_step_nonproj Γ v hs] at h; exact h) :=
  by rw [ShEnv.ref, dif_neg hs]

theorem termShp_diatm {Δ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Δ w) (j : ℕ) {x : VarSymb}
    {X : VarType} (hr : Δ.ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (hx : ∃ X, Δ.ref x = some (.VTypeDia X)) (t : Term σ (Δ.diaIn x) A a) :
    termShp ρ j (Term.diatm x hx t) =
      .dia (ρ.ref j x hr).label (termShp (ρ.diaPush j x hr) (j + 1) t) := by
  simp only [termShp]
  split
  · rename_i X' hr'
    obtain rfl : X = X' := by
      rw [hr] at hr'
      cases hr'
      rfl
    rfl
  all_goals
    rename_i heq
    exfalso
    rw [hr] at heq
    cases heq

/-! ### Transposing shape environments -/

theorem ShEnv.ref_transpose {Γ : Ctx} {w : M.frame.W} (τ : M.ShEnv Γ w)
    (ρ : (s : M.frame.Acc w) → M.ShEnv Γ s.1) (j : ℕ)
    (hτ : ∀ v T h, τ v T h = Frame.transposeShp fun s => ρ s v T h) :
    ∀ (v : VarSymb) {T : VarType} (h : Γ.ref v = some T),
      τ.ref (j + 1) v h = Frame.transposeShp fun s => (ρ s).ref j v h
  | .root _, _, h => hτ _ _ h
  | .step v s, T, h => by
      by_cases hs : s.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Γ.ref v = some U := by
          rw [Ctx.ref_step_proj Γ v hs] at h
          cases hU : Γ.ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        rw [ShEnv.ref_proj τ (j + 1) hs hU h, ShEnv.ref_transpose τ ρ j hτ v hU, shp_transpose]
        exact congrArg _ (funext fun s => (ShEnv.ref_proj (ρ s) j hs hU h).symm)
      · rw [ShEnv.ref_nonproj τ (j + 1) hs h, hτ]
        exact congrArg _ (funext fun s => (ShEnv.ref_nonproj (ρ s) j hs h).symm)

theorem ShEnv.boxPush_transpose {Γ : Ctx} {w : M.frame.W} (τ : M.ShEnv Γ w)
    (ρ : (s : M.frame.Acc w) → M.ShEnv Γ s.1) (j : ℕ)
    (hτ : ∀ v T h, τ v T h = Frame.transposeShp fun s => ρ s v T h) :
    ∀ v T h, τ.boxPush (j + 1) v T h = Frame.transposeShp fun s => (ρ s).boxPush j v T h
  | .step u .box, _, h => by
      simp only [ShEnv.boxPush]
      rw [ShEnv.ref_transpose τ ρ j hτ]
      rfl
  | .step u .keep, _, h => by
      simp only [ShEnv.boxPush]
      rw [ShEnv.ref_transpose τ ρ j hτ, shp_transpose]
      rfl
  | .root _, _, h => by cases h
  | .step _ .fst, _, h => by cases h
  | .step _ .snd, _, h => by cases h
  | .step _ .dia, _, h => by cases h
  | .step _ .here, _, h => by cases h

theorem ShEnv.diaPush_transpose {Γ : Ctx} {w : M.frame.W} (τ : M.ShEnv Γ w)
    (ρ : (s : M.frame.Acc w) → M.ShEnv Γ s.1) (j : ℕ)
    (hτ : ∀ v T h, τ v T h = Frame.transposeShp fun s => ρ s v T h) {x : VarSymb} {X : VarType}
    (hx : Γ.ref x = some (.VTypeDia X)) :
    ∀ v T h, τ.diaPush (j + 1) x hx v T h = Frame.transposeShp fun s => (ρ s).diaPush j x hx v T h
  | .step _ .dia, _, h => by
      have e := Ctx.diaIn_step_dia hx h
      subst e
      simp only [ShEnv.diaPush]
      rw [ShEnv.ref_transpose τ ρ j hτ]
      rfl
  | .step u .box, T, h => ShEnv.boxPush_transpose τ ρ j hτ (.step u .box) T h
  | .step u .keep, T, h => ShEnv.boxPush_transpose τ ρ j hτ (.step u .keep) T h
  | .root _, _, h => by cases h
  | .step _ .fst, _, h => by cases h
  | .step _ .snd, _, h => by cases h
  | .step _ .here, _, h => by cases h

/-- ⭐**T**: the shape of a term, one level further out, is the transposed family of its shapes —
    when the environment is the transposed family of environments. -/
theorem termShp_transpose {Δ : Ctx} {w : M.frame.W} (τ : M.ShEnv Δ w)
    (ρ : (s : M.frame.Acc w) → M.ShEnv Δ s.1) (j : ℕ)
    (hτ : ∀ v T h, τ v T h = Frame.transposeShp fun s => ρ s v T h) :
    ∀ {T : VarType} {a : Ann T} (t : Term σ Δ T a),
      termShp τ (j + 1) t = Frame.transposeShp fun s => termShp (ρ s) j t
  | _, _, .var _ _ => rfl
  | _, _, .func _ => rfl
  | _, _, .unit => rfl
  | _, _, .pair s t => by
      simp only [termShp]
      rw [termShp_transpose τ ρ j hτ s, termShp_transpose τ ρ j hτ t]
      rfl
  | _, _, .boxtm t => by
      simp only [termShp]
      rw [termShp_transpose (τ.boxPush (j + 1)) (fun s => (ρ s).boxPush j) (j + 1)
        (ShEnv.boxPush_transpose τ ρ j hτ) t]
      rfl
  | _, _, .diatm x hx t => by
      obtain ⟨X, hr⟩ := id hx
      rw [termShp_diatm τ (j + 1) hr,
        termShp_transpose (τ.diaPush (j + 1) x hr) (fun s => (ρ s).diaPush j x hr) (j + 1)
          (ShEnv.diaPush_transpose τ ρ j hτ hr) t, ShEnv.ref_transpose τ ρ j hτ x hr]
      rw [show (fun s => termShp (ρ s) j (Term.diatm x hx t)) =
          fun s => .dia ((ρ s).ref j x hr).label (termShp ((ρ s).diaPush j x hr) (j + 1) t) from
        funext fun s => termShp_diatm (ρ s) j hr hx t]
      rfl

/-! ## S2: the shape of a value is its symbolic shape -/

/-- The shape of an object, under T. -/
abbrev domSh (hT : ModalSys.T = true) {A : VarType} {w : M.frame.W} (o : M.frame.Dom A w) :
    M.Shape w A :=
  Frame.domShape M.necEval (M.shape hT) o

/-- The shapes of an environment's objects. -/
def envShape (hT : ModalSys.T = true) {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) :
    M.ShEnv Γ w :=
  fun v T h => domSh hT (env v T h)

theorem Env.ref_proj' {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {v : VarSymb} {s : Step}
    (hs : s.isProj = true) {U T : VarType} (hU : Γ.ref v = some U)
    (h : Γ.ref (.step v s) = some T) :
    env.ref (.step v s) h =
      M.stepObj hs (by rw [Ctx.ref_step_proj Γ v hs, hU] at h; exact h) (env.ref v hU) := by
  rw [Env.ref, dif_pos hs]
  split
  · rename_i U' hU'
    obtain rfl : U = U' := Option.some.inj (hU.symm.trans hU')
    rfl
  · rename_i hU'
    exfalso
    rw [hU] at hU'
    cases hU'

theorem Env.ref_nonproj' {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {v : VarSymb} {s : Step}
    (hs : ¬ s.isProj = true) {T : VarType} (h : Γ.ref (.step v s) = some T) :
    env.ref (.step v s) h = env (.step v s) T (by rw [Ctx.ref_step_nonproj Γ v hs] at h; exact h) :=
  by rw [Env.ref, dif_neg hs]

theorem domSh_stepObj (hT : ModalSys.T = true) {w : M.frame.W} {U T : VarType} {s : Step}
    (hs : s.isProj = true) (h : U.step s = some T) (a : M.frame.Dom U w) :
    domSh hT (M.stepObj hs h a) = GFunc.shp (GFunc.proj (σ := σ) hs h) 0 (domSh hT a) := by
  cases U <;> cases s <;> (try cases hs) <;> (try cases h)
  · rfl
  · rfl
  · obtain ⟨hT', rfl⟩ := VarType.step_here h
    change domSh hT (M.necEval a (M.frame.reflAcc hT' w)) =
      (Frame.transposeShp fun s => domSh hT (M.necEval a s)).map (Frame.Leaf.collapse hT' 0)
    exact (transpose_collapse_zero hT' fun s => domSh hT (M.necEval a s)).symm

/-- The symbolic shape at an address is the shape of the object there. -/
theorem ref_envShape (hT : ModalSys.T = true) {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) :
    ∀ (v : VarSymb) {T : VarType} (h : Γ.ref v = some T),
      (envShape hT env).ref 0 v h = domSh hT (env.ref v h)
  | .root _, _, _ => rfl
  | .step v s, T, h => by
      by_cases hs : s.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Γ.ref v = some U := by
          rw [Ctx.ref_step_proj Γ v hs] at h
          cases hU : Γ.ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        rw [ShEnv.ref_proj _ 0 hs hU h, ref_envShape hT env v hU, Env.ref_proj' env hs hU h,
          domSh_stepObj]
      · rw [ShEnv.ref_nonproj _ 0 hs h, Env.ref_nonproj' env hs h]
        rfl

/-- Pushing the shapes of an environment into a `□` is transposing the shapes of the pushed
    environments. -/
theorem boxPush_envShape (hT : ModalSys.T = true) {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) :
    ∀ v T h, (envShape hT env).boxPush 0 v T h =
      Frame.transposeShp fun s => envShape hT (env.boxPush s) v T h
  | .step u .box, _, h => by
      simp only [ShEnv.boxPush]
      rw [ref_envShape]
      rfl
  | .step u .keep, T, h => by
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep h
      simp only [ShEnv.boxPush]
      rw [ref_envShape]
      change Shp.box ((Frame.transposeShp fun s =>
          domSh hT (M.necEval (env.ref u hu) s)).map (Frame.Leaf.shift hF 0)) = _
      rw [transpose_shift_zero]
      change _ = Frame.transposeShp fun s => Shp.box (Frame.transposeShp fun t =>
          domSh hT (M.necEval (M.necEval (M.ops.necDup hF (env.ref u hu)) s) t))
      simp only [M.necDup_eval]
      rfl
  | .root _, _, h => by cases h
  | .step _ .fst, _, h => by cases h
  | .step _ .snd, _, h => by cases h
  | .step _ .dia, _, h => by cases h
  | .step _ .here, _, h => by cases h

theorem domSh_bundle (hT : ModalSys.T = true) {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) :
    ∀ L : Supp Δ, domSh hT (env.bundle L) = (envShape hT env).bundle L
  | [] => rfl
  | _ :: L => by
      change Shp.prod _ (domSh hT (env.bundle L)) = _
      rw [domSh_bundle hT env L]
      rfl

theorem ShEnv.bundle_transpose {Γ : Ctx} {w : M.frame.W} (τ : M.ShEnv Γ w)
    (ρ : (s : M.frame.Acc w) → M.ShEnv Γ s.1)
    (hτ : ∀ v T h, τ v T h = Frame.transposeShp fun s => ρ s v T h) :
    ∀ L : Supp Γ, τ.bundle L = Frame.transposeShp fun s => (ρ s).bundle L
  | [] => rfl
  | e :: L => by
      simp only [ShEnv.bundle]
      rw [hτ, ShEnv.bundle_transpose τ ρ hτ L]
      rfl

theorem interp_diatm {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) {x : VarSymb} {X : VarType}
    (hr : Δ.ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (hx : ∃ X, Δ.ref x = some (.VTypeDia X)) (t : Term σ (Δ.diaIn x) A a) :
    interp env (Term.diatm x hx t) =
      M.ops.posMap (Term.compile (Term.bases t) t (Supp.mem_self _))
        (M.ops.posMap (Supp.assemble hr (Term.bases t))
          (M.ops.posStrength (env.necBundle (Supp.boxPart (Term.bases t))) (env.ref x hr))) := by
  simp only [interp]
  split
  · rename_i X' hr'
    obtain rfl : X = X' := by
      rw [hr] at hr'
      cases hr'
      rfl
    rfl
  all_goals
    rename_i heq
    exfalso
    rw [hr] at heq
    cases heq

/-- ⭐**S2**: the shape of a term's value is its symbolic shape. -/
theorem domSh_interp (hT : ModalSys.T = true) {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) :
    ∀ {T : VarType} {a : Ann T} (t : Term σ Δ T a),
      domSh hT (interp env t) = termShp (envShape hT env) 0 t
  | _, _, .var _ _ => shp_var_eq _ _
  | _, _, .func _ => shp_var_eq _ _
  | _, _, .unit => rfl
  | _, _, .pair s t => by
      change Shp.prod (domSh hT (interp env s)) (domSh hT (interp env t)) = _
      rw [domSh_interp hT env s, domSh_interp hT env t]
      rfl
  | _, _, .boxtm t => by
      change Shp.box (Frame.transposeShp fun s =>
          domSh hT (M.necEval (interp env (Term.boxtm t)) s)) =
        Shp.box (termShp ((envShape hT env).boxPush 0) (0 + 1) t)
      rw [termShp_transpose ((envShape hT env).boxPush 0) (fun s => envShape hT (env.boxPush s)) 0
        (boxPush_envShape hT env)]
      simp only [box_beta, domSh_interp hT _ t]
  | _, _, .diatm x hx t => by
      obtain ⟨X, hr⟩ := id hx
      rw [termShp_diatm _ 0 hr, interp_diatm env hr hx t]
      change M.shape hT _ = _
      simp only [M.shape_posMap, M.shape_posStrength, Shp.label_dia, Shp.body_dia]
      rw [ref_envShape,
        ← termShp_compile ((envShape hT env).diaPush 0 x hr) (0 + 1) (Term.bases t) t
          (Supp.mem_self _),
        ← assemble_shp (envShape hT env) 0 hr,
        ShEnv.bundle_transpose ((envShape hT env).boxPush 0) (fun s => envShape hT (env.boxPush s))
          (boxPush_envShape hT env)]
      simp only [necBundle_eval, domSh_bundle]
      rw [ref_envShape]
      rfl

/-! ## Weakening, and the annotation determines the shape -/

/-- Two shape environments agree along an inclusion of contexts. -/
def ShEnv.Agree {Γ Γ' : Ctx} (h : Γ.Le Γ') {w : M.frame.W} (ρ : M.ShEnv Γ w)
    (ρ' : M.ShEnv Γ' w) : Prop :=
  ∀ v T (hv : Γ v = some T), ρ v T hv = ρ' v T (h v T hv)

theorem ShEnv.ref_agree {Γ Γ' : Ctx} {h : Γ.Le Γ'} {w : M.frame.W} {ρ : M.ShEnv Γ w}
    {ρ' : M.ShEnv Γ' w} (hag : ShEnv.Agree h ρ ρ') (j : ℕ) :
    ∀ (v : VarSymb) {T : VarType} (hv : Γ.ref v = some T), ρ.ref j v hv = ρ'.ref j v (h.ref hv)
  | .root r, _, hv => hag (.root r) _ hv
  | .step v s, T, hv => by
      by_cases hs : s.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Γ.ref v = some U := by
          rw [Ctx.ref_step_proj Γ v hs] at hv
          cases hU : Γ.ref v with
          | none => rw [hU] at hv; cases hv
          | some U => exact ⟨U, rfl⟩
        rw [ShEnv.ref_proj ρ j hs hU hv, ShEnv.ref_proj ρ' j hs (h.ref hU) (h.ref hv),
          ShEnv.ref_agree hag j v hU]
      · rw [ShEnv.ref_nonproj ρ j hs hv, ShEnv.ref_nonproj ρ' j hs (h.ref hv)]
        exact hag _ _ _

theorem ShEnv.boxPush_agree {Γ Γ' : Ctx} {h : Γ.Le Γ'} {w : M.frame.W} {ρ : M.ShEnv Γ w}
    {ρ' : M.ShEnv Γ' w} (hag : ShEnv.Agree h ρ ρ') (j : ℕ) :
    ShEnv.Agree h.boxIn (ρ.boxPush j) (ρ'.boxPush j)
  | .step u .box, _, hv => by
      simp only [ShEnv.boxPush]
      rw [ShEnv.ref_agree hag j u]
  | .step u .keep, _, hv => by
      simp only [ShEnv.boxPush]
      rw [ShEnv.ref_agree hag j u]
  | .root _, _, hv => by cases hv
  | .step _ .fst, _, hv => by cases hv
  | .step _ .snd, _, hv => by cases hv
  | .step _ .dia, _, hv => by cases hv
  | .step _ .here, _, hv => by cases hv

theorem ShEnv.diaPush_agree {Γ Γ' : Ctx} {h : Γ.Le Γ'} {w : M.frame.W} {ρ : M.ShEnv Γ w}
    {ρ' : M.ShEnv Γ' w} (hag : ShEnv.Agree h ρ ρ') (j : ℕ) {x : VarSymb} {X : VarType}
    (hx : Γ.ref x = some (.VTypeDia X)) :
    ShEnv.Agree (h.diaIn x) (ρ.diaPush j x hx) (ρ'.diaPush j x (h.ref hx))
  | .step _ .dia, _, hv => by
      have e := Ctx.diaIn_step_dia hx hv
      subst e
      simp only [ShEnv.diaPush]
      rw [ShEnv.ref_agree hag j x hx]
  | .step u .box, T, hv => ShEnv.boxPush_agree hag j (.step u .box) T hv
  | .step u .keep, T, hv => ShEnv.boxPush_agree hag j (.step u .keep) T hv
  | .root _, _, hv => by cases hv
  | .step _ .fst, _, hv => by cases hv
  | .step _ .snd, _, hv => by cases hv
  | .step _ .here, _, hv => by cases hv

/-- ⭐Shapes are unchanged by weakening. -/
theorem termShp_mono {Γ Γ' : Ctx} {h : Γ.Le Γ'} {w : M.frame.W} {ρ : M.ShEnv Γ w}
    {ρ' : M.ShEnv Γ' w} (hag : ShEnv.Agree h ρ ρ') (j : ℕ) :
    ∀ {T : VarType} {a : Ann T} (t : Term σ Γ T a), termShp ρ' j (Term.mono h t) = termShp ρ j t
  | _, _, .var _ _ => rfl
  | _, _, .func _ => rfl
  | _, _, .unit => rfl
  | _, _, .pair s t => by
      change Shp.prod (termShp ρ' j (Term.mono h s)) (termShp ρ' j (Term.mono h t)) = _
      rw [termShp_mono hag j s, termShp_mono hag j t]
      rfl
  | _, _, .boxtm t => by
      change Shp.box (termShp (ρ'.boxPush j) (j + 1) (Term.mono h.boxIn t)) = _
      rw [termShp_mono (ShEnv.boxPush_agree hag j) (j + 1) t]
      rfl
  | _, _, .diatm x hx t => by
      obtain ⟨X, hr⟩ := id hx
      change termShp ρ' j (Term.diatm x _ (Term.mono (h.diaIn x) t)) = _
      rw [termShp_diatm ρ' j (h.ref hr), termShp_diatm ρ j hr,
        termShp_mono (ShEnv.diaPush_agree hag j hr) (j + 1) t, ShEnv.ref_agree hag j x hr]

/-- ⭐**The annotation determines the shape**: two terms of one annotated type have the same symbolic
    shape.  This is the semantic side of `eqRec` comparing only terms of one annotation. -/
theorem termShp_ann {Δ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Δ w) (j : ℕ) :
    ∀ {T : VarType} {a : Ann T} (t s : Term σ Δ T a), termShp ρ j t = termShp ρ j s
  | .Var, _, _, _ => shp_var_eq _ _
  | .VTypeOne, _, _, _ => Shp.one_eq _ _
  | _, _, .pair t₁ t₂, .pair s₁ s₂ => by
      simp only [termShp]
      rw [termShp_ann ρ j t₁ s₁, termShp_ann ρ j t₂ s₂]
  | _, _, .boxtm t, .boxtm s => by
      simp only [termShp]
      rw [termShp_ann (ρ.boxPush j) (j + 1) t s]
  | _, _, .diatm x hx t, .diatm _ hx' s => by
      obtain ⟨X, hr⟩ := id hx
      rw [termShp_diatm ρ j hr hx, termShp_diatm ρ j hr hx',
        termShp_ann (ρ.diaPush j x hr) (j + 1) t s]

/-! ## Collapsing or shifting a whole shape environment -/

omit [ModalSys] in
theorem _root_.V12M.Shp.map_map {L : Type y} (g g' : L → L) :
    ∀ {A : VarType} (a : Shp L A), (a.map g).map g' = a.map (g' ∘ g)
  | _, .var => rfl
  | _, .one => rfl
  | _, .prod a b => by simp only [Shp.map]; rw [Shp.map_map g g' a, Shp.map_map g g' b]
  | _, .box a => by simp only [Shp.map]; rw [Shp.map_map g g' a]
  | _, .dia _ a => by simp only [Shp.map]; rw [Shp.map_map g g' a]; rfl

omit [ModalSys] in
theorem _root_.V12M.Shp.map_congr {L : Type y} {g g' : L → L} (h : ∀ ℓ, g ℓ = g' ℓ) :
    ∀ {A : VarType} (a : Shp L A), a.map g = a.map g'
  | _, .var => rfl
  | _, .one => rfl
  | _, .prod a b => by simp only [Shp.map]; rw [Shp.map_congr h a, Shp.map_congr h b]
  | _, .box a => by simp only [Shp.map]; rw [Shp.map_congr h a]
  | _, .dia ℓ a => by simp only [Shp.map]; rw [Shp.map_congr h a, h]

omit [ModalSys] in
theorem _root_.V12M.Shp.map_id {L : Type y} : ∀ {A : VarType} (a : Shp L A), a.map id = a
  | _, .var => rfl
  | _, .one => rfl
  | _, .prod a b => by simp only [Shp.map]; rw [Shp.map_id a, Shp.map_id b]
  | _, .box a => by simp only [Shp.map]; rw [Shp.map_id a]
  | _, .dia _ a => by simp only [Shp.map]; rw [Shp.map_id a]; rfl

/-- A collapse at level `j` passes through any map acting at a level below it. -/
theorem shp_mapCollapse (hT : ModalSys.T = true) (j : ℕ) {w : M.frame.W} :
    ∀ {A B : VarType} (f : GFunc σ A B) (d : ℕ) (a : M.Shape w A),
      GFunc.shp f (j + d) (a.map (Frame.Leaf.collapse hT j)) =
        (GFunc.shp f (j + d + 1) a).map (Frame.Leaf.collapse hT j)
  | _, _, .id _, _, _ => rfl
  | _, _, .comp g f, d, a => by
      simp only [GFunc.shp]
      rw [shp_mapCollapse hT j f, shp_mapCollapse hT j g]
  | _, _, .fst, _, a => Shp.map_fst _ a
  | _, _, .snd, _, a => Shp.map_snd _ a
  | _, _, .pair f g, d, a => by
      simp only [GFunc.shp, Shp.map]
      rw [shp_mapCollapse hT j f, shp_mapCollapse hT j g]
  | _, _, .unit _, _, _ => rfl
  | _, _, .func _ _, _, _ => rfl
  | _, _, .boxMap f, d, a => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner]
      rw [show j + d + 1 = j + (d + 1) from rfl, shp_mapCollapse hT j f (d + 1)]
  | _, _, .boxPair _ _, _, a => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner, Shp.map_fst, Shp.map_snd]
  | _, _, .boxUnit, _, _ => rfl
  | _, _, .diaMap f, d, a => by
      simp only [GFunc.shp, Shp.map, Shp.map_label, Shp.map_body]
      rw [show j + d + 1 = j + (d + 1) from rfl, shp_mapCollapse hT j f (d + 1)]
  | _, _, .strength _ _, _, a => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner, Shp.map_fst, Shp.map_snd, Shp.map_label,
        Shp.map_body]
  | _, _, .extract hT', d, a => by
      simp only [GFunc.shp, Shp.map_inner, Shp.map_map]
      exact Shp.map_congr (fun ℓ => Frame.Leaf.collapse_collapse hT j d ℓ) _
  | _, _, .dup hF, d, a => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner, Shp.map_map]
      congr 2
      exact Shp.map_congr (fun ℓ => Frame.Leaf.shift_collapse hT hF j d ℓ) _

/-- A shift at level `j` passes through any map acting at a level below it. -/
theorem shp_mapShift (hF : ModalSys.Four = true) (j : ℕ) {w : M.frame.W} :
    ∀ {A B : VarType} (f : GFunc σ A B) (d : ℕ) (a : M.Shape w A),
      GFunc.shp f (j + d + 2) (a.map (Frame.Leaf.shift hF j)) =
        (GFunc.shp f (j + d + 1) a).map (Frame.Leaf.shift hF j)
  | _, _, .id _, _, _ => rfl
  | _, _, .comp g f, d, a => by
      simp only [GFunc.shp]
      rw [shp_mapShift hF j f, shp_mapShift hF j g]
  | _, _, .fst, _, a => Shp.map_fst _ a
  | _, _, .snd, _, a => Shp.map_snd _ a
  | _, _, .pair f g, d, a => by
      simp only [GFunc.shp, Shp.map]
      rw [shp_mapShift hF j f, shp_mapShift hF j g]
  | _, _, .unit _, _, _ => rfl
  | _, _, .func _ _, _, _ => rfl
  | _, _, .boxMap f, d, a => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner]
      rw [show j + d + 2 + 1 = j + (d + 1) + 2 by omega,
        show j + d + 1 + 1 = j + (d + 1) + 1 by omega, shp_mapShift hF j f (d + 1)]
  | _, _, .boxPair _ _, _, a => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner, Shp.map_fst, Shp.map_snd]
  | _, _, .boxUnit, _, _ => rfl
  | _, _, .diaMap f, d, a => by
      simp only [GFunc.shp, Shp.map, Shp.map_label, Shp.map_body]
      rw [show j + d + 2 + 1 = j + (d + 1) + 2 by omega,
        show j + d + 1 + 1 = j + (d + 1) + 1 by omega, shp_mapShift hF j f (d + 1)]
  | _, _, .strength _ _, _, a => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner, Shp.map_fst, Shp.map_snd, Shp.map_label,
        Shp.map_body]
  | _, _, .extract hT, d, a => by
      simp only [GFunc.shp, Shp.map_inner, Shp.map_map]
      exact Shp.map_congr (fun ℓ => Frame.Leaf.collapse_shift hT hF j d ℓ) _
  | _, _, .dup hF', d, a => by
      simp only [GFunc.shp, Shp.map, Shp.map_inner, Shp.map_map]
      congr 2
      exact Shp.map_congr (fun ℓ => Frame.Leaf.shift_shift hF j d ℓ) _

/-- Apply a leaf map to every shape of an environment. -/
def ShEnv.mapLeaves {Γ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Γ w)
    (g : M.frame.Leaf M.RootPoss w → M.frame.Leaf M.RootPoss w) : M.ShEnv Γ w :=
  fun v T h => (ρ v T h).map g

section MapLeaves

variable {Γ : Ctx} {w : M.frame.W}

theorem ShEnv.ref_mapCollapse (hT : ModalSys.T = true) (j : ℕ) (ρ : M.ShEnv Γ w) (d : ℕ) :
    ∀ (v : VarSymb) {T : VarType} (h : Γ.ref v = some T),
      (ρ.mapLeaves (Frame.Leaf.collapse hT j)).ref (j + d) v h =
        (ρ.ref (j + d + 1) v h).map (Frame.Leaf.collapse hT j)
  | .root _, _, _ => rfl
  | .step v s, T, h => by
      by_cases hs : s.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Γ.ref v = some U := by
          rw [Ctx.ref_step_proj Γ v hs] at h
          cases hU : Γ.ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        rw [ShEnv.ref_proj _ _ hs hU h, ShEnv.ref_proj _ _ hs hU h,
          ShEnv.ref_mapCollapse hT j ρ d v hU, shp_mapCollapse]
      · rw [ShEnv.ref_nonproj _ _ hs h, ShEnv.ref_nonproj _ _ hs h]
        rfl

theorem ShEnv.ref_mapShift (hF : ModalSys.Four = true) (j : ℕ) (ρ : M.ShEnv Γ w) (d : ℕ) :
    ∀ (v : VarSymb) {T : VarType} (h : Γ.ref v = some T),
      (ρ.mapLeaves (Frame.Leaf.shift hF j)).ref (j + d + 2) v h =
        (ρ.ref (j + d + 1) v h).map (Frame.Leaf.shift hF j)
  | .root _, _, _ => rfl
  | .step v s, T, h => by
      by_cases hs : s.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Γ.ref v = some U := by
          rw [Ctx.ref_step_proj Γ v hs] at h
          cases hU : Γ.ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        rw [ShEnv.ref_proj _ _ hs hU h, ShEnv.ref_proj _ _ hs hU h,
          ShEnv.ref_mapShift hF j ρ d v hU, shp_mapShift]
      · rw [ShEnv.ref_nonproj _ _ hs h, ShEnv.ref_nonproj _ _ hs h]
        rfl

theorem ShEnv.boxPush_mapCollapse (hT : ModalSys.T = true) (j : ℕ) (ρ : M.ShEnv Γ w) (d : ℕ) :
    (ρ.mapLeaves (Frame.Leaf.collapse hT j)).boxPush (j + d) =
      (ρ.boxPush (j + d + 1)).mapLeaves (Frame.Leaf.collapse hT j) := by
  funext v T h
  match v with
  | .step u .box =>
      simp only [ShEnv.boxPush, ShEnv.mapLeaves]
      rw [ShEnv.ref_mapCollapse hT j ρ d, Shp.map_inner]
  | .step u .keep =>
      simp only [ShEnv.boxPush, ShEnv.mapLeaves]
      rw [ShEnv.ref_mapCollapse hT j ρ d, shp_mapCollapse, Shp.map_inner]
  | .root _ => cases h
  | .step _ .fst => cases h
  | .step _ .snd => cases h
  | .step _ .dia => cases h
  | .step _ .here => cases h

theorem ShEnv.boxPush_mapShift (hF : ModalSys.Four = true) (j : ℕ) (ρ : M.ShEnv Γ w) (d : ℕ) :
    (ρ.mapLeaves (Frame.Leaf.shift hF j)).boxPush (j + d + 2) =
      (ρ.boxPush (j + d + 1)).mapLeaves (Frame.Leaf.shift hF j) := by
  funext v T h
  match v with
  | .step u .box =>
      simp only [ShEnv.boxPush, ShEnv.mapLeaves]
      rw [ShEnv.ref_mapShift hF j ρ d, Shp.map_inner]
  | .step u .keep =>
      simp only [ShEnv.boxPush, ShEnv.mapLeaves]
      rw [ShEnv.ref_mapShift hF j ρ d, shp_mapShift, Shp.map_inner]
  | .root _ => cases h
  | .step _ .fst => cases h
  | .step _ .snd => cases h
  | .step _ .dia => cases h
  | .step _ .here => cases h

theorem ShEnv.diaPush_mapCollapse (hT : ModalSys.T = true) (j : ℕ) (ρ : M.ShEnv Γ w) (d : ℕ)
    {x : VarSymb} {X : VarType} (hx : Γ.ref x = some (.VTypeDia X)) :
    (ρ.mapLeaves (Frame.Leaf.collapse hT j)).diaPush (j + d) x hx =
      (ρ.diaPush (j + d + 1) x hx).mapLeaves (Frame.Leaf.collapse hT j) := by
  funext v T h
  match v with
  | .step _ .dia =>
      have e := Ctx.diaIn_step_dia hx h
      subst e
      simp only [ShEnv.diaPush, ShEnv.mapLeaves]
      rw [ShEnv.ref_mapCollapse hT j ρ d, Shp.map_body]
  | .step u .box =>
      exact congrFun (congrFun (congrFun (ShEnv.boxPush_mapCollapse hT j ρ d) (.step u .box)) T) h
  | .step u .keep =>
      exact congrFun (congrFun (congrFun (ShEnv.boxPush_mapCollapse hT j ρ d) (.step u .keep)) T) h
  | .root _ => cases h
  | .step _ .fst => cases h
  | .step _ .snd => cases h
  | .step _ .here => cases h

theorem ShEnv.diaPush_mapShift (hF : ModalSys.Four = true) (j : ℕ) (ρ : M.ShEnv Γ w) (d : ℕ)
    {x : VarSymb} {X : VarType} (hx : Γ.ref x = some (.VTypeDia X)) :
    (ρ.mapLeaves (Frame.Leaf.shift hF j)).diaPush (j + d + 2) x hx =
      (ρ.diaPush (j + d + 1) x hx).mapLeaves (Frame.Leaf.shift hF j) := by
  funext v T h
  match v with
  | .step _ .dia =>
      have e := Ctx.diaIn_step_dia hx h
      subst e
      simp only [ShEnv.diaPush, ShEnv.mapLeaves]
      rw [ShEnv.ref_mapShift hF j ρ d, Shp.map_body]
  | .step u .box =>
      exact congrFun (congrFun (congrFun (ShEnv.boxPush_mapShift hF j ρ d) (.step u .box)) T) h
  | .step u .keep =>
      exact congrFun (congrFun (congrFun (ShEnv.boxPush_mapShift hF j ρ d) (.step u .keep)) T) h
  | .root _ => cases h
  | .step _ .fst => cases h
  | .step _ .snd => cases h
  | .step _ .here => cases h

end MapLeaves

/-- ⭐Collapsing a whole environment at level `j` passes through `termShp`. -/
theorem termShp_mapCollapse (hT : ModalSys.T = true) (j : ℕ) :
    ∀ {Γ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Γ w) (d : ℕ) {T : VarType} {a : Ann T}
      (t : Term σ Γ T a),
      termShp (ρ.mapLeaves (Frame.Leaf.collapse hT j)) (j + d) t =
        (termShp ρ (j + d + 1) t).map (Frame.Leaf.collapse hT j)
  | _, _, _, _, _, _, .var _ _ => rfl
  | _, _, _, _, _, _, .func _ => rfl
  | _, _, _, _, _, _, .unit => rfl
  | _, _, ρ, d, _, _, .pair s t => by
      simp only [termShp, Shp.map]
      rw [termShp_mapCollapse hT j ρ d s, termShp_mapCollapse hT j ρ d t]
  | _, _, ρ, d, _, _, .boxtm t => by
      simp only [termShp, Shp.map]
      rw [ShEnv.boxPush_mapCollapse hT j ρ d, show j + d + 1 = j + (d + 1) from rfl,
        termShp_mapCollapse hT j _ (d + 1) t]
  | _, _, ρ, d, _, _, .diatm x hx t => by
      obtain ⟨X, hr⟩ := id hx
      rw [termShp_diatm _ _ hr, termShp_diatm _ _ hr, ShEnv.ref_mapCollapse hT j ρ d,
        ShEnv.diaPush_mapCollapse hT j ρ d hr, show j + d + 1 = j + (d + 1) from rfl,
        termShp_mapCollapse hT j _ (d + 1) t]
      simp only [Shp.map, Shp.map_label]

/-- ⭐Shifting a whole environment at level `j` passes through `termShp`, one level further in. -/
theorem termShp_mapShift (hF : ModalSys.Four = true) (j : ℕ) :
    ∀ {Γ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Γ w) (d : ℕ) {T : VarType} {a : Ann T}
      (t : Term σ Γ T a),
      termShp (ρ.mapLeaves (Frame.Leaf.shift hF j)) (j + d + 2) t =
        (termShp ρ (j + d + 1) t).map (Frame.Leaf.shift hF j)
  | _, _, _, _, _, _, .var _ _ => rfl
  | _, _, _, _, _, _, .func _ => rfl
  | _, _, _, _, _, _, .unit => rfl
  | _, _, ρ, d, _, _, .pair s t => by
      simp only [termShp, Shp.map]
      rw [termShp_mapShift hF j ρ d s, termShp_mapShift hF j ρ d t]
  | _, _, ρ, d, _, _, .boxtm t => by
      simp only [termShp, Shp.map]
      rw [ShEnv.boxPush_mapShift hF j ρ d, show j + d + 2 + 1 = j + (d + 1) + 2 by omega,
        show j + d + 1 + 1 = j + (d + 1) + 1 by omega, termShp_mapShift hF j _ (d + 1) t]
  | _, _, ρ, d, _, _, .diatm x hx t => by
      obtain ⟨X, hr⟩ := id hx
      rw [termShp_diatm _ _ hr, termShp_diatm _ _ hr, ShEnv.ref_mapShift hF j ρ d,
        ShEnv.diaPush_mapShift hF j ρ d hr, show j + d + 2 + 1 = j + (d + 1) + 2 by omega,
        show j + d + 1 + 1 = j + (d + 1) + 1 by omega, termShp_mapShift hF j _ (d + 1) t]
      simp only [Shp.map, Shp.map_label]

end Model

end V12M
