import QML.QML_v12m_CanonWorld

/-!
# QML v12m — the canonical model: shapes

The canonical model stores a possible object's shape with the object (docs §10.34), so shapes are
needed before the model exists.  They live over the **canonical arrows** (`Canon.arrows`): the
worlds, and the chains between them.  A root possibility is named by its address.

* `canonSh w v T`: the shape of what the address `v` names at `w`, by recursion on `T`.  A `◇`
  address is a root possibility: its label is the address itself, and each `◇` position of its
  content is the address with the path to that position, written as the address of that position
  is (`rootSh`, `Step.innerPath`).  A `□` address has, at each
  successor, the shape of its contents' address there (`succAddr`: collapsed at the world itself,
  shifted `d` times `d + 1` levels deeper, as `rden` moves a `□` body).
* `canonEnvF Γ w f`: the shape environment reading each address `v` as `canonSh w (f v)`.  When
  `f` commutes with projections it reads every reachable address that way (`canonEnvF_ref`).
  `cEnv` is the case `f = id`.
* `cEnv_boxPush`: pushing `cEnv` into `□` gives the transposed family of the successors'
  environments read through `succAddr` — what `termShp_transpose` needs for a `□` term.  At the
  world itself and at the far successors those environments are what collapsing and shifting the
  body need (`termShp_collapse_cEnv`, `termShp_shiftIter_cEnv`).
-/

namespace V12M

/-! ## Addresses at successors -/

namespace VarSymb

/-- An address shifted `n` times at the innermost level: what `Term.shiftIter` does to the
    address of an η-expansion. -/
def shiftIter : ℕ → VarSymb → VarSymb
  | 0, v => v
  | n + 1, v => shiftIter n (v.shift 0)

theorem shiftIter_proj : ∀ (n : ℕ) (v : VarSymb) (s : Step), s.isProj = true →
    shiftIter n (.step v s) = .step (shiftIter n v) s
  | 0, _, _, _ => rfl
  | n + 1, v, s, hs => by
      change shiftIter n ((VarSymb.step v s).shift 0) = .step (shiftIter n (v.shift 0)) s
      rw [VarSymb.shift_proj hs]
      exact shiftIter_proj n _ s hs

theorem keepIter_succ' : ∀ (n : ℕ) (v : VarSymb),
    keepIter (n + 1) v = .step (keepIter n v) .keep
  | 0, _ => rfl
  | n + 1, v => keepIter_succ' n (.step v .keep)

theorem keepIter_add : ∀ (m n : ℕ) (v : VarSymb), keepIter m (keepIter n v) = keepIter (n + m) v
  | m, 0, v => by rw [Nat.zero_add]; rfl
  | m, n + 1, v => by
      rw [show n + 1 + m = (n + m) + 1 by omega]
      exact keepIter_add m n (.step v .keep)

/-- Shifting a kept address keeps it once more each time. -/
theorem shiftIter_keep : ∀ (n : ℕ) (v : VarSymb),
    shiftIter n (.step v .keep) = keepIter (n + 1) v
  | 0, _ => rfl
  | n + 1, v => by
      change shiftIter n ((VarSymb.step v .keep).shift 0) = _
      rw [VarSymb.shift_level_zero (s := .keep) rfl]
      exact shiftIter_keep n (.step v .keep)

end VarSymb

variable [ModalSys]

/-- The steps from a necessary address to its contents one view in, as `VarSymb.inner` writes them:
    `box`, or under T and 4 `keep` then `here`. -/
def Step.innerPath : List Step := if ModalSys.keepOnly then [.keep, .here] else [.box]

namespace VarSymb

/-- Shifting a contents address keeps contents of kept objects. -/
theorem shiftIter_inner : ∀ (n : ℕ) (v : VarSymb), shiftIter n v.inner = (keepIter n v).inner
  | 0, _ => rfl
  | n + 1, v => by
      change shiftIter n (v.inner.shift 0) = _
      rw [VarSymb.inner_shift_zero]
      exact shiftIter_inner n (.step v .keep)

/-- The contents of an address extended by a path are the address extended by the path and then
    `Step.innerPath`. -/
theorem inner_ext : ∀ (v : VarSymb) (π : List Step), (v.ext π).inner = v.ext (π ++ Step.innerPath)
  | v, [] => by
    unfold VarSymb.inner Step.innerPath
    split_ifs <;> rfl
  | v, s :: π => inner_ext (.step v s) π

end VarSymb

namespace Canon

variable {σ : Signature} {N₀ : ℕ}

/-! ## The canonical arrows -/

variable (σ N₀) in
/-- ⭐The canonical arrows: the worlds, and chains of proper steps between them. -/
abbrev arrows : Arrows.{0, 0} σ where
  W := World σ N₀
  R := Canon.R
  refl := fun hT w => R.refl hT w
  trans := fun hF => R.trans hF
  refl_trans := fun _ _ _ _ _ => rfl
  trans_refl := fun _ _ _ _ _ => rfl
  trans_assoc := fun _ _ _ _ _ _ _ _ => rfl

/-- The canonical root action: a root possibility kept along an arrow is its address kept once per
    level the arrow crosses.  Depths add along chains, and the identity crosses none, so it is
    lawful.  (Staged: no possible object is kept in a shaped canonical model yet, docs §3 4.) -/
instance instRootKeep : Arrows.RootKeep (arrows σ N₀) (fun _ => VarSymb) :=
  ⟨fun _ {w} r a => VarSymb.keepIter (a.1.depth - w.depth) r⟩

/-- The canonical root action is lawful: depths add along chains, the identity crosses none. -/
instance instRootKeepLaws : Arrows.RootKeepLaws (arrows σ N₀) (fun _ => VarSymb) where
  keep_trans _ {w} r a b := by
    change VarSymb.keepIter (b.1.depth - a.1.depth) (VarSymb.keepIter (a.1.depth - w.depth) r) =
      VarSymb.keepIter (b.1.depth - w.depth) r
    rw [VarSymb.keepIter_add]
    have h₁ := (Succ.chain a).1.depth
    have h₂ := (Succ.chain b).1.depth
    congr 1
    omega
  keep_refl _ _ {w} r := by
    change VarSymb.keepIter (w.depth - w.depth) r = r
    rw [Nat.sub_self]
    rfl

/-- Canonical shapes: a root possibility is named by its address. -/
abbrev CShape (w : World σ N₀) (T : VarType) : Type :=
  Model.Shape (arrows σ N₀) (fun _ => VarSymb) w T

/-- Canonical shape environments. -/
abbrev CShEnv (Γ : Ctx) (w : World σ N₀) : Type :=
  Model.ShEnv (arrows σ N₀) (fun _ => VarSymb) Γ w

/-- Where an address of the `□` view is read at a successor `w'` of `w`: collapsed at the world
    itself, shifted `d` times `d + 1` levels deeper — as `rden` moves a `□` body. -/
def succAddr (w w' : World σ N₀) (v : VarSymb) : VarSymb :=
  match w'.depth - w.depth with
  | 0 => v.collapse 0
  | d + 1 => VarSymb.shiftIter d v

theorem succAddr_zero {w w' : World σ N₀} (h : w'.depth - w.depth = 0) (v : VarSymb) :
    succAddr w w' v = v.collapse 0 := by
  simp only [succAddr, h]

theorem succAddr_succ {w w' : World σ N₀} {d : ℕ} (h : w'.depth - w.depth = d + 1)
    (v : VarSymb) : succAddr w w' v = VarSymb.shiftIter d v := by
  simp only [succAddr, h]

theorem succAddr_proj (w w' : World σ N₀) (v : VarSymb) (s : Step) (hs : s.isProj = true) :
    succAddr w w' (.step v s) = .step (succAddr w w' v) s := by
  rcases h : w'.depth - w.depth with _ | d
  · rw [succAddr_zero h, succAddr_zero h, VarSymb.collapse_proj hs]
  · rw [succAddr_succ h, succAddr_succ h, VarSymb.shiftIter_proj d v s hs]

/-- ⭐Reading a kept object at a successor, and its contents at a successor of that, is reading the
    contents at the composite successor. -/
theorem succAddr_keep (hF : ModalSys.Four = true) {w s t : World σ N₀} (hs : R w s) (ht : R s t)
    (u : VarSymb) :
    succAddr w t u.inner = succAddr s t (succAddr w s (.step u .keep)).inner := by
  have hcs : Chain (s.depth - w.depth) w s := (Succ.chain (⟨s, ⟨hs⟩⟩ : Succ w)).1
  have hct : Chain (t.depth - s.depth) s t := (Succ.chain (⟨t, ⟨ht⟩⟩ : Succ s)).1
  have ht₀ : t.depth - s.depth = 0 → ModalSys.T = true := (Succ.chain (⟨t, ⟨ht⟩⟩ : Succ s)).2.1
  rcases e₁ : s.depth - w.depth with _ | d
  · have hsw : s = w := by
      rw [e₁] at hcs
      exact hcs
    subst hsw
    rw [succAddr_zero e₁, VarSymb.collapse_keep_zero]
  · rw [succAddr_succ e₁, VarSymb.shiftIter_keep]
    rcases e₂ : t.depth - s.depth with _ | d'
    · have hT := ht₀ e₂
      have hts : t = s := by
        rw [e₂] at hct
        exact hct
      subst hts
      have hk : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
      rw [succAddr_succ e₁, succAddr_zero e₂, VarSymb.inner_collapse_zero,
        VarSymb.shiftIter_inner, VarSymb.keepIter_succ', VarSymb.inner_keepOnly hk]
    · have e₃ : t.depth - w.depth = (d + 1 + d') + 1 := by omega
      rw [succAddr_succ e₃, succAddr_succ e₂, VarSymb.shiftIter_inner, VarSymb.shiftIter_inner,
        VarSymb.keepIter_add]

/-! ## Canonical shapes -/

/-- The shape of a root possibility's content at a path: every `◇` position is the root with its
    path to that position.  The path is written as the address of that position is (`Ann.eta`):
    into a `□` by `Step.innerPath`, so `box`, or `keep` then `here` under T and 4 — the leaf
    records the address cut where it leaves the anchor's level (docs §10.39). -/
def rootSh (w : World σ N₀) (v : VarSymb) : List Step → (T : VarType) → CShape w T
  | _, .Var => .var
  | _, .VTypeOne => .one
  | π, .VTypeProd A B => .prod (rootSh w v (π ++ [.fst]) A) (rootSh w v (π ++ [.snd]) B)
  | π, .VTypeBox A => .box (rootSh w v (π ++ Step.innerPath) A)
  | π, .VTypeDia A => .dia (.root v π) (rootSh w v (π ++ [.dia]) A)

/-- ⭐The canonical shape of what an address names: a `◇` address is a root possibility, a `□`
    address has at each successor the shape of its contents' address there. -/
def canonSh : (w : World σ N₀) → VarSymb → (T : VarType) → CShape w T
  | _, _, .Var => .var
  | _, _, .VTypeOne => .one
  | w, v, .VTypeProd A B => .prod (canonSh w (.step v .fst) A) (canonSh w (.step v .snd) B)
  | w, v, .VTypeBox A =>
      .box (Arrows.transposeShp (F := arrows σ N₀) (Root := fun _ => VarSymb) fun s =>
        canonSh s.1 (succAddr w s.1 v.inner) A)
  | w, v, .VTypeDia A => .dia (.root v []) (rootSh w v [.dia] A)

/-- A projection step moves a canonical shape to the projected address's. -/
theorem canonSh_proj (w : World σ N₀) (v : VarSymb) {U T : VarType} {s : Step}
    (hs : s.isProj = true) (h : U.step s = some T) :
    GFunc.shp (GFunc.proj (σ := σ) hs h) 0 (canonSh w v U) = canonSh w (.step v s) T := by
  cases U <;> cases s <;> (try cases hs) <;> (try cases h)
  · rfl
  · rfl
  · obtain ⟨hT, rfl⟩ := VarType.step_here h
    change (Arrows.transposeShp (F := arrows σ N₀) (Root := fun _ => VarSymb) fun s =>
        canonSh s.1 (succAddr w s.1 v.inner) _).map
      (Arrows.Leaf.collapse hT 0) = _
    rw [Model.transpose_collapse_zero hT]
    change canonSh w (succAddr w w v.inner) _ = _
    rw [succAddr_zero (Nat.sub_self _), VarSymb.inner_collapse_zero]

/-! ## Canonical shape environments -/

/-- The shape environment reading each address through an address map. -/
def canonEnvF (Γ : Ctx) (w : World σ N₀) (f : VarSymb → VarSymb) : CShEnv Γ w :=
  fun v T _ => canonSh w (f v) T

/-- ⭐The canonical shape environment. -/
abbrev cEnv (Γ : Ctx) (w : World σ N₀) : CShEnv Γ w := canonEnvF Γ w id

/-- Through a map commuting with projections, every reachable address reads canonically. -/
theorem canonEnvF_ref (Γ : Ctx) (w : World σ N₀) {f : VarSymb → VarSymb}
    (hf : ∀ v s, s.isProj = true → f (.step v s) = .step (f v) s) :
    ∀ (v : VarSymb) {T : VarType} (h : Γ.ref v = some T),
      (canonEnvF Γ w f).ref 0 v h = canonSh w (f v) T
  | .root _, _, _ => rfl
  | .step v s, T, h => by
      by_cases hs : s.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Γ.ref v = some U := by
          rw [Ctx.ref_step_proj Γ v hs] at h
          cases hU : Γ.ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        rw [Model.ShEnv.ref_proj _ 0 hs hU h, canonEnvF_ref Γ w hf v hU, canonSh_proj,
          hf v s hs]
      · rw [Model.ShEnv.ref_nonproj _ 0 hs h]
        rfl

theorem cEnv_ref (Γ : Ctx) (w : World σ N₀) (v : VarSymb) {T : VarType}
    (h : Γ.ref v = some T) : (cEnv Γ w).ref 0 v h = canonSh w v T :=
  canonEnvF_ref Γ w (fun _ _ _ => rfl) v h

/-- A kept address read at a successor: `keep` taken once per level crossed. -/
theorem succAddr_keep_self (w w' : World σ N₀) (u : VarSymb) :
    succAddr w w' (.step u .keep) = VarSymb.keepIter (w'.depth - w.depth) u := by
  rcases h : w'.depth - w.depth with _ | d
  · rw [succAddr_zero h, VarSymb.collapse_keep_zero]
    rfl
  · rw [succAddr_succ h, VarSymb.shiftIter_keep]

/-- A root possibility's content shape restricted along an arrow is the kept root's. -/
theorem rootSh_keepAlong (hF : ModalSys.Four = true) (w : World σ N₀) (v : VarSymb)
    (s : Succ w) : ∀ (π : List Step) (T : VarType),
      (rootSh w v π T).map (Arrows.Leaf.keepAlong (F := arrows σ N₀) (Root := fun _ => VarSymb)
          hF s) = rootSh s.1 (VarSymb.keepIter (s.1.depth - w.depth) v) π T
  | _, .Var => rfl
  | _, .VTypeOne => rfl
  | π, .VTypeProd A B => by
      simp only [rootSh, Shp.map]
      rw [rootSh_keepAlong hF w v s _ A, rootSh_keepAlong hF w v s _ B]
  | π, .VTypeBox A => by
      simp only [rootSh, Shp.map]
      rw [rootSh_keepAlong hF w v s _ A]
  | π, .VTypeDia A => by
      simp only [rootSh, Shp.map]
      rw [rootSh_keepAlong hF w v s _ A]
      rfl

/-- ⭐A possible address kept along an arrow has the kept address's canonical shape there. -/
theorem canonSh_dia_keepAlong (hF : ModalSys.Four = true) (w : World σ N₀) (u : VarSymb)
    (s : Succ w) (A : VarType) :
    (canonSh w u (.VTypeDia A)).map
        (Arrows.Leaf.keepAlong (F := arrows σ N₀) (Root := fun _ => VarSymb) hF s) =
      canonSh s.1 (succAddr w s.1 (.step u .keep)) (.VTypeDia A) := by
  rw [succAddr_keep_self]
  simp only [canonSh, Shp.map]
  rw [rootSh_keepAlong]
  rfl

/-- ⭐Pushing the canonical environment into `□` gives, at each successor, the successor's
    environment read through `succAddr`. -/
theorem cEnv_boxPush (Γ : Ctx) (w : World σ N₀) :
    ∀ v T (h : Γ.boxIn v = some T),
      (cEnv Γ w).boxPush 0 v T h =
        Arrows.transposeShp (F := arrows σ N₀) (Root := fun _ => VarSymb) fun s =>
          canonEnvF Γ.boxIn s.1 (succAddr w s.1) v T h
  | .step u .box, T, h => by
      obtain ⟨hk, _⟩ := Ctx.boxIn_box h
      change ((cEnv Γ w).ref 0 u (Ctx.boxIn_step_box h)).inner = _
      rw [cEnv_ref]
      change Arrows.transposeShp (F := arrows σ N₀) (Root := fun _ => VarSymb) (fun s =>
        canonSh s.1 (succAddr w s.1 u.inner) T) = _
      rw [VarSymb.inner_box hk]
      rfl
  | .step u .keep, T, h => by
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep h
      cases T with
      | VTypeDia A =>
          -- ⭐Kept at every successor: one family of restrictions (`canonSh_dia_keepAlong`).
          change ((cEnv Γ w).ref 0 u hu).map (Arrows.Leaf.dk hF 0) = _
          rw [cEnv_ref]
          change _ = Arrows.transposeShp (F := arrows σ N₀) (Root := fun _ => VarSymb) fun s =>
            canonSh s.1 (succAddr w s.1 (.step u .keep)) (.VTypeDia A)
          rw [show (fun s : Succ w => canonSh s.1 (succAddr w s.1 (.step u .keep)) (.VTypeDia A)) =
              fun s => (canonSh w u (.VTypeDia A)).map
                (Arrows.Leaf.keepAlong (F := arrows σ N₀) (Root := fun _ => VarSymb) hF s) from
            funext fun s => (canonSh_dia_keepAlong hF w u s A).symm, Model.transpose_map_const]
          rfl
      | VTypeBox A =>
      change (GFunc.shp (GFunc.dup (σ := σ) hF) 0 ((cEnv Γ w).ref 0 u hu)).inner = _
      rw [cEnv_ref]
      change Shp.box ((Arrows.transposeShp (F := arrows σ N₀) (Root := fun _ => VarSymb)
        fun s => canonSh s.1 (succAddr w s.1 u.inner) A).map (Arrows.Leaf.shift hF 0)) = _
      rw [Model.transpose_shift_zero hF]
      change _ = Shp.box (Arrows.transposeShp (F := arrows σ N₀) (Root := fun _ => VarSymb)
        fun s => Arrows.transposeShp (F := arrows σ N₀) (Root := fun _ => VarSymb) fun t =>
        canonSh t.1 (succAddr s.1 t.1 (succAddr w s.1 (.step u .keep)).inner) A)
      congr 2
      funext s
      congr 1
      funext t
      rw [← succAddr_keep hF s.2.down t.2.down u]
      | _ => cases hk
  | .root _, _, h => by cases h
  | .step _ .fst, _, h => by cases h
  | .step _ .snd, _, h => by cases h
  | .step _ .dia, _, h => by cases h
  | .step _ .here, _, h => by cases h

/-- At the world itself, a `□` body read through `succAddr` has the shape of its collapse. -/
theorem termShp_collapse_cEnv (hT : ModalSys.T = true) {Γ : Ctx} (w : World σ N₀)
    {A : VarType} {a : Ann A} (t : Term σ Γ.boxIn A a) :
    Model.termShp (cEnv Γ w) 0 (Term.collapse (Ctx.collapses_boxIn_self hT Γ) t) =
      Model.termShp (canonEnvF Γ.boxIn w fun v => v.collapse 0) 0 t := by
  refine Model.termShp_collapse ?_ t
  intro v T hv
  rw [canonEnvF_ref _ _ (fun v s hs => VarSymb.collapse_proj hs), cEnv_ref]

end Canon

end V12M
