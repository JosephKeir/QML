import QML.QML_v12m_GLaws
import QML.QML_v12m_GLiftEnt
import QML.QML_v12m_GViewSubst

/-!
# QML v12m — the growing tree: the leaf calculus

Under T, "tags determine annotations" (`docs/v12-modal-extensions.md` §3 4, "Diagnosis" and D-H3):
terms with one denotation have one annotation, as B's `ann_eq_of_rden` and the staged tree's.

With the `□`-lift on, strong 4 lifts only generators, so every address is labelled faithfully:

* ⭐`cEnv_dia_generic`: every possible address's canonical shape is the generic one (`genDia`) —
  a lifted root copies its η-expanded address's template (`pbShp_genDia`), an image inherits one.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-! ## Every possible template is generic -/

/-- Pulling a generic content shape back to a lifted root gives the root's generic content
    shape. -/
theorem pbShp_rootSh {s t : GW hF M₀} (m z : VarSymb) :
    ∀ (T : VarType) (π : List Step) (lw : List Bool),
      pbShp hF M₀ (s := s) (t := t) m lw (rootSh t z π T) = rootSh s m π T
  | .Var, _, _ => rfl
  | .VTypeOne, _, _ => rfl
  | .VTypeProd A C, π, lw => by
      simp only [rootSh, pbShp]
      rw [pbShp_rootSh m z A, pbShp_rootSh m z C]
  | .VTypeBox A, π, lw => by
      simp only [rootSh, pbShp]
      rw [pbShp_rootSh m z A]
  | .VTypeDia A, π, lw => by
      simp only [rootSh, pbShp, pbLeaf]
      rw [pbShp_rootSh m z A]

theorem pbShp_genDia {s t : GW hF M₀} (m z : VarSymb) (A : VarType) :
    pbShp hF M₀ (s := s) (t := t) m [] (genDia t z A) = genDia s m A := by
  simp only [genDia, pbShp, pbLeaf]
  rw [pbShp_rootSh m z A]

/-- One step: a possible address's template is generic when the templates of lower addresses, and
    of the parent's addresses at the same level, are. -/
theorem cEnv_dia_step (hT : ModalSys.T = true)
    (hS : ModalSys.FourStrongW = true → ModalSys.FourStrong = true)
    (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {v : VarSymb} {X : VarType}
    (hd : DeclAt s v (.VTypeDia X))
    (ihl : ∀ (t : GW hF M₀) (w : VarSymb) (W : VarType), levA t w < levA s v →
      DeclAt t w (.VTypeDia W) → cEnv t w (.VTypeDia W) = genDia t w W)
    (ihp : ∀ (c : ℕ) (p : Node) (hs : s.1 = c :: p) (w : VarSymb) (W : VarType),
      levA ⟨p, gborn_parent (hs ▸ s.2)⟩ w = levA s v →
      DeclAt ⟨p, gborn_parent (hs ▸ s.2)⟩ w (.VTypeDia W) →
      cEnv ⟨p, gborn_parent (hs ▸ s.2)⟩ w (.VTypeDia W) = genDia ⟨p, gborn_parent (hs ▸ s.2)⟩ w W) :
    cEnv s v (.VTypeDia X) = genDia s v X := by
  obtain ⟨i, hv⟩ := hd
  by_cases hroot : ∃ r, v = .root (.free r)
  · obtain ⟨z, rfl⟩ := hroot
    by_cases hL : Lifted s z
    · -- a lifted root: the pull-back of an η-expanded address's template
      obtain ⟨c, e, he⟩ := hL
      let t : GW hF M₀ := ⟨c :: s.1, gborn_of_inr he⟩
      rw [cEnv_lifted hT hM₀ (t := t) rfl hv he]
      obtain ⟨j, hlj⟩ := lift_le hM₀ (t := t) rfl he
      obtain ⟨L, T, a, τ⟩ := e
      cases T with
      | VTypeDia A' =>
          by_cases hA : A' = X
          · subst hA
            obtain ⟨l, hl, z', hz', hτ⟩ := fmapL_dia_eta hS he
            have hsh : Model.termShp (famEnv cEnv (ctxOf L) t) 0 τ = cEnv t z' (.VTypeDia A') := by
              have h₁ := congrArg
                (fun q : Σ b, Term σ (ctxOf L) (.VTypeDia A') b =>
                  Model.termShp (famEnv cEnv (ctxOf L) t) 0 q.2) hτ
              refine h₁.trans ?_
              change Model.termShp (famEnv cEnv (ctxOf L) t) 0
                (Term.mono (ctxOf_le_of_suffix hl) (Term.eta z' (.VTypeDia A') hz')) = _
              rw [Model.termShp_mono (ρ := famEnv cEnv (ctxOf l) t)
                  (ρ' := famEnv cEnv (ctxOf L) t) (fun _ _ _ => rfl),
                Model.termShp_eta,
                cEnv_ref hT hM₀ ((ctxOf_le_of_suffix hl).trans hlj)]
            obtain ⟨j', hj', hlt, -⟩ := ref_rt hz'
            have hlev : levA t z' < levA s (.root (.free z)) := by
              unfold levA
              rw [hj']
              exact lev_lift hM₀ (t := t) rfl he
                (lt_of_lt_of_le hlt (hl.length_le))
            have hdz : DeclAt t z' (.VTypeDia A') :=
              ⟨j, ((ctxOf_le_of_suffix hl).trans hlj).ref hz'⟩
            have hdo : LTerm.diaOf A' (⟨L, .VTypeDia A', a, τ⟩ : LTerm σ) = some ⟨a, τ⟩ := by
              simp [LTerm.diaOf]
            unfold liftDiaAt
            rw [hdo]
            change pbShp hF M₀ (.root (.free z)) []
              (Model.termShp (famEnv cEnv (ctxOf L) t) 0 τ) = _
            rw [hsh, ihl t z' A' hlev hdz, pbShp_genDia]
          · unfold liftDiaAt
            simp only [LTerm.diaOf, dif_neg hA]
      | Var => rfl
      | VTypeOne => rfl
      | VTypeProd _ _ => rfl
      | VTypeBox _ => rfl
    · by_cases himg : ∃ (c : ℕ) (p : Node) (_ : s.1 = c :: p) (u : ℕ),
          fmapL hF M₀ s.1 (.step (.root (.free u)) .keep) = .inl (.root (.free z))
      · -- an image root: its source's template, kept along the edge
        obtain ⟨c, p, hs, u, hu⟩ := himg
        let q : GW hF M₀ := ⟨p, gborn_parent (hs ▸ s.2)⟩
        have hc : s.1 = c :: q.1 := hs
        obtain ⟨V, hdV, hkV⟩ := committed_root_decl hM₀ hc
          (committed_of_decl hu ⟨i, hv⟩)
        obtain ⟨hdy, hlv⟩ := keep_img hM₀ hc hdV hkV hu
        obtain rfl := DeclAt.unique hM₀ hdy ⟨i, hv⟩
        obtain ⟨i', hu'⟩ := hdV
        rw [edge_dia_inl hT hM₀ hc hu' hu, ihp c p hs _ _ hlv.symm ⟨i', hu'⟩, genDia_keep,
          rootKeep_edge, wit_of_inl (by intro _ h; cases h) hu]
      · -- neither: generic
        have hnl : ¬ ∃ z', VarSymb.root (.free z) = .root (.free z') ∧ Lifted s z' := by
          rintro ⟨z', hz', hL'⟩
          injection hz' with h
          injection h with h
          exact hL (h ▸ hL')
        have hni : ∀ c p, s.1 = c :: p →
            ¬ ∃ u, fmapL hF M₀ s.1 (.step (.root (.free u)) .keep) = .inl (.root (.free z)) :=
          fun c p hs ⟨u, hu⟩ => himg ⟨c, p, hs, u, hu⟩
        rw [cEnv_eq hT hM₀ ⟨i, hv⟩]
        exact diaT_eq_genDia hnl hni
  · have hnl : ¬ ∃ z, v = .root (.free z) ∧ Lifted s z := fun ⟨z, hz, _⟩ => hroot ⟨z, hz⟩
    rw [cEnv_eq hT hM₀ ⟨i, hv⟩]
    exact diaT_eq_genDia hnl (not_img_of_nonroot hM₀ hv hroot)

/-- ⭐**With the `□`-lift on, every possible address's canonical shape is generic**: by induction
    on the level, and on the node for images.  A lifted root's template pulls back its lifted
    term's shape, which (D-H3) is an η-expanded possible address's, lower (`lev_lift`); an image
    inherits its source's, kept (`edge_dia_inl`, `genDia_keep`); any other address is generic. -/
theorem cEnv_dia_generic (hT : ModalSys.T = true)
    (hS : ModalSys.FourStrongW = true → ModalSys.FourStrong = true)
    (hM₀ : Theory.IsMCS M₀) :
    ∀ (n : ℕ) (s : GW hF M₀) (v : VarSymb) (X : VarType), levA s v ≤ n →
      DeclAt s v (.VTypeDia X) → cEnv s v (.VTypeDia X) = genDia s v X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s
  obtain ⟨sn, sb⟩ := s
  induction sn with
  | nil =>
      intro v X hn hd
      refine cEnv_dia_step hT hS hM₀ hd
        (fun t w W hlt hdw => ih _ (lt_of_lt_of_le hlt hn) t w W le_rfl hdw) ?_
      intro c p hs
      cases hs
  | cons c p ihp =>
      intro v X hn hd
      refine cEnv_dia_step hT hS hM₀ hd
        (fun t w W hlt hdw => ih _ (lt_of_lt_of_le hlt hn) t w W le_rfl hdw) ?_
      intro c' p' hs w W hlv hdw
      injection hs with hc hp
      subst hc hp
      exact ihp (gborn_parent sb) w W (hlv ▸ hn) hdw

/-! ## Path operations at a path's own level -/

omit [ModalSys] in
theorem keepAt_own : ∀ (p : List Step) (m : ℕ), Step.levels p = m → Step.keepAt m p = p ++ [.keep]
  | [], m, h => by
      change 0 = m at h
      subst h
      rfl
  | s :: p, m, h => by
      change (if s.isProj then 0 else 1) + Step.levels p = m at h
      by_cases hs : s.isProj = true
      · rw [if_pos hs, Nat.zero_add] at h
        cases m <;> simp only [Step.keepAt, hs, if_true, List.cons_append] <;>
          rw [keepAt_own p _ h]
      · rw [if_neg hs] at h
        obtain rfl : m = Step.levels p + 1 := by omega
        simp only [Step.keepAt, hs, Bool.false_eq_true, if_false, List.cons_append]
        rw [keepAt_own p _ rfl]

omit [ModalSys] in
theorem shiftAt_own : ∀ (p : List Step) (m : ℕ) {s : Step} (q : List Step), Step.levels p = m →
    s.isProj = false → Step.shiftAt m (p ++ s :: q) = p ++ .keep :: s :: q
  | [], m, s, q, h, hs => by
      change 0 = m at h
      subst h
      simp [Step.shiftAt, hs]
  | t :: p, m, s, q, h, hs => by
      change (if t.isProj then 0 else 1) + Step.levels p = m at h
      by_cases ht : t.isProj = true
      · rw [if_pos ht, Nat.zero_add] at h
        simp only [List.cons_append, Step.shiftAt, ht, if_true]
        rw [shiftAt_own p m q h hs]
      · rw [if_neg ht] at h
        obtain rfl : m = Step.levels p + 1 := by omega
        simp only [List.cons_append, Step.shiftAt, ht, Bool.false_eq_true, if_false]
        rw [shiftAt_own p _ q rfl hs]

omit [ModalSys] in
theorem collapseAt_own : ∀ (p : List Step) (m : ℕ) (q : List Step), Step.levels p = m →
    Step.collapseAt m (p ++ .keep :: .here :: q) = p ++ .here :: q
  | [], m, q, h => by
      change 0 = m at h
      subst h
      simp [Step.collapseAt, Step.isProj]
  | t :: p, m, q, h => by
      change (if t.isProj then 0 else 1) + Step.levels p = m at h
      by_cases ht : t.isProj = true
      · rw [if_pos ht, Nat.zero_add] at h
        simp only [List.cons_append, Step.collapseAt, ht, if_true]
        rw [collapseAt_own p m q h]
      · rw [if_neg ht] at h
        obtain rfl : m = Step.levels p + 1 := by omega
        simp only [List.cons_append, Step.collapseAt, ht, Bool.false_eq_true, if_false]
        by_cases hc : Step.levels p = 0 ∧ t = .keep ∧ Step.headLvl (p ++ .keep :: .here :: q) = true
        · rw [if_pos hc]
          obtain ⟨hl0, rfl, hh⟩ := hc
          cases p with
          | nil => rfl
          | cons u p' =>
              exfalso
              change (if u.isProj then 0 else 1) + Step.levels p' = 0 at hl0
              have hu : u.isProj = true := by
                by_contra hu
                rw [if_neg hu] at hl0
                omega
              simp [Step.headLvl, hu] at hh
        · rw [if_neg hc, collapseAt_own p _ q rfl]

/-! ## Generic content shapes under keeping and collapsing -/

theorem rootSh_dkB (s : GW hF M₀) (v : VarSymb) {p : List Step} {j : ℕ}
    (hp : Step.levels p = j + 1) :
    ∀ (A : VarType) (r : List Step),
      (rootSh s v (p ++ .dia :: r) A).map (Arrows.Leaf.dkB hF (j + 1)) =
        rootSh s v (p ++ .keep :: .dia :: r) A
  | .Var, _ => rfl
  | .VTypeOne, _ => rfl
  | .VTypeProd A C, r => by
      simp only [rootSh, Shp.map]
      rw [show p ++ .dia :: r ++ [Step.fst] = p ++ .dia :: (r ++ [.fst]) by simp,
        show p ++ .dia :: r ++ [Step.snd] = p ++ .dia :: (r ++ [.snd]) by simp,
        rootSh_dkB s v hp A, rootSh_dkB s v hp C]
      simp
  | .VTypeBox A, r => by
      simp only [rootSh, Shp.map]
      rw [show p ++ .dia :: r ++ Step.innerPath = p ++ .dia :: (r ++ Step.innerPath) by simp,
        rootSh_dkB s v hp A]
      simp
  | .VTypeDia A, r => by
      simp only [rootSh, Shp.map]
      rw [show p ++ .dia :: r ++ [Step.dia] = p ++ .dia :: (r ++ [.dia]) by simp,
        rootSh_dkB s v hp A]
      simp only [Arrows.Leaf.dkB]
      rw [shiftAt_own p _ r hp rfl]
      simp

theorem rootSh_shift (s : GW hF M₀) (v : VarSymb) {p : List Step} {j : ℕ}
    (hp : Step.levels p = j) :
    ∀ (A : VarType) (r : List Step),
      (rootSh s v (p ++ .keep :: r) A).map (Arrows.Leaf.shift hF j) =
        rootSh s v (p ++ .keep :: .keep :: r) A
  | .Var, _ => rfl
  | .VTypeOne, _ => rfl
  | .VTypeProd A C, r => by
      simp only [rootSh, Shp.map]
      rw [show p ++ .keep :: r ++ [Step.fst] = p ++ .keep :: (r ++ [.fst]) by simp,
        show p ++ .keep :: r ++ [Step.snd] = p ++ .keep :: (r ++ [.snd]) by simp,
        rootSh_shift s v hp A, rootSh_shift s v hp C]
      simp
  | .VTypeBox A, r => by
      simp only [rootSh, Shp.map]
      rw [show p ++ .keep :: r ++ Step.innerPath = p ++ .keep :: (r ++ Step.innerPath) by simp,
        rootSh_shift s v hp A]
      simp
  | .VTypeDia A, r => by
      simp only [rootSh, Shp.map]
      rw [show p ++ .keep :: r ++ [Step.dia] = p ++ .keep :: (r ++ [.dia]) by simp,
        rootSh_shift s v hp A]
      simp only [Arrows.Leaf.shift]
      rw [shiftAt_own p _ r hp rfl]
      simp

theorem rootSh_collapse (hT : ModalSys.T = true) (s : GW hF M₀) (v : VarSymb) {p : List Step}
    {j : ℕ} (hp : Step.levels p = j) :
    ∀ (A : VarType) (r : List Step),
      (rootSh s v (p ++ .keep :: .here :: r) A).map (Arrows.Leaf.collapse hT j) =
        rootSh s v (p ++ .here :: r) A
  | .Var, _ => rfl
  | .VTypeOne, _ => rfl
  | .VTypeProd A C, r => by
      simp only [rootSh, Shp.map]
      rw [show p ++ .keep :: .here :: r ++ [Step.fst] = p ++ .keep :: .here :: (r ++ [.fst]) by
          simp,
        show p ++ .keep :: .here :: r ++ [Step.snd] = p ++ .keep :: .here :: (r ++ [.snd]) by
          simp,
        rootSh_collapse hT s v hp A, rootSh_collapse hT s v hp C]
      simp
  | .VTypeBox A, r => by
      simp only [rootSh, Shp.map]
      rw [show p ++ .keep :: .here :: r ++ Step.innerPath =
          p ++ .keep :: .here :: (r ++ Step.innerPath) by simp,
        rootSh_collapse hT s v hp A]
      simp
  | .VTypeDia A, r => by
      simp only [rootSh, Shp.map]
      rw [show p ++ .keep :: .here :: r ++ [Step.dia] = p ++ .keep :: .here :: (r ++ [.dia]) by
          simp,
        rootSh_collapse hT s v hp A]
      simp only [Arrows.Leaf.collapse]
      rw [collapseAt_own p _ r hp]
      simp

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem innerPath_keepOnly (hT : ModalSys.T = true) (hF' : ModalSys.Four = true) :
    Step.innerPath = [.keep, .here] := by
  simp [Step.innerPath, ModalSys.keepOnly, hT, hF']

/-- ⭐**A generic content shape kept** at its own level is the generic shape one keep further. -/
theorem rootSh_keep_shp (hT : ModalSys.T = true) (s : GW hF M₀) (v : VarSymb) {p : List Step}
    {j : ℕ} (hp : Step.levels p = j + 1) :
    ∀ (U : VarType) (hk : U.keepable = true),
      (GFunc.shp (σ := σ) (GFunc.keep hF hk) (j + 1) (rootSh s v p U)).inner =
        rootSh s v (p ++ [.keep]) U
  | .VTypeDia A, _ => by
      change Shp.dia (Arrows.Leaf.dk hF (j + 1) (.root v p))
        ((rootSh s v (p ++ [.dia]) A).map (Arrows.Leaf.dkB hF (j + 1))) = _
      rw [show p ++ [Step.dia] = p ++ .dia :: [] from rfl, rootSh_dkB s v hp A []]
      simp only [Arrows.Leaf.dk]
      rw [keepAt_own p _ hp]
      simp [rootSh]
  | .VTypeBox A, _ => by
      change Shp.box ((rootSh s v (p ++ Step.innerPath) A).map (Arrows.Leaf.shift hF (j + 1))) = _
      rw [innerPath_keepOnly hT hF, rootSh_shift s v hp A [.here]]
      simp [rootSh, innerPath_keepOnly hT hF]
  | .Var, hk => (Bool.false_ne_true hk).elim
  | .VTypeOne, hk => (Bool.false_ne_true hk).elim
  | .VTypeProd _ _, hk => (Bool.false_ne_true hk).elim

/-- A projection of a generic content shape is the generic shape one step further. -/
theorem rootSh_proj (hT : ModalSys.T = true) (s : GW hF M₀) (v : VarSymb) {p : List Step}
    {j : ℕ} (hp : Step.levels p = j) {U T : VarType} {st : Step} (hs : st.isProj = true)
    (h : U.step st = some T) :
    GFunc.shp (GFunc.proj (σ := σ) hs h) j (rootSh s v p U) = rootSh s v (p ++ [st]) T := by
  cases U <;> cases st <;> (try cases hs) <;> (try cases h)
  · rfl
  · rfl
  · rename_i X
    obtain ⟨hT', rfl⟩ := VarType.step_here h
    change (rootSh s v (p ++ Step.innerPath) X).map (Arrows.Leaf.collapse hT' j) = _
    rw [innerPath_keepOnly hT hF, rootSh_collapse hT' s v hp X []]

/-! ## The canonical environment pushed into views -/

variable (hF M₀) in
/-- ⭐The canonical shape environment of a stage of a world's language, pushed into views. -/
inductive Pushed (s : GW hF M₀) (i : ℕ) : (Δ : Ctx) → GEnv hF M₀ Δ s → ℕ → Prop
  | base : Pushed s i (ctxOf (glat s i)) (famEnv cEnv (ctxOf (glat s i)) s) 0
  | box {Δ : Ctx} {ρ : GEnv hF M₀ Δ s} {j : ℕ} :
      Pushed s i Δ ρ j → Pushed s i Δ.boxIn (ρ.boxPush j) (j + 1)
  | dia {Δ : Ctx} {ρ : GEnv hF M₀ Δ s} {j : ℕ} {x : VarSymb} {X : VarType}
      (hx : Δ.ref x = some (.VTypeDia X)) :
      Pushed s i Δ ρ j → Pushed s i (Δ.diaIn x) (ρ.diaPush j x hx) (j + 1)

/-- Reachable addresses have the levels of the declared ones. -/
theorem levels_of_decl {Δ : Ctx} {j : ℕ}
    (h : ∀ v T, v.lastProj = false → Δ v = some T → Step.levels v.path = j) :
    ∀ (y : VarSymb) {T : VarType}, Δ.ref y = some T → Step.levels y.path = j
  | .root r, T, hy => h _ T rfl hy
  | .step v st, T, hy => by
      by_cases hs : st.isProj = true
      · rw [Ctx.ref_step_proj _ v hs] at hy
        cases hU : Δ.ref v with
        | none => rw [hU] at hy; cases hy
        | some U =>
            change Step.levels (v.path ++ [st]) = j
            rw [Step.levels_append, levels_of_decl h v hU]
            simp [Step.levels, hs]
      · exact h _ T (Bool.eq_false_iff.mpr hs) (by rwa [Ctx.ref_step_nonproj _ v hs] at hy)

/-- ⭐**Exactness**: in the canonical environment pushed `j` views in, every reachable address has
    `j` level steps. -/
theorem Pushed.levels {s : GW hF M₀} {i : ℕ} {Δ : Ctx} {ρ : GEnv hF M₀ Δ s} {j : ℕ}
    (hP : Pushed hF M₀ s i Δ ρ j) : ∀ (y : VarSymb) {T : VarType}, Δ.ref y = some T →
      Step.levels y.path = j := by
  induction hP with
  | base =>
      refine levels_of_decl fun v T _ hv => ?_
      obtain ⟨r, rfl⟩ := ctxOf_decl hv
      rfl
  | @box Δ ρ j hP ih =>
      refine levels_of_decl fun v T _ hv => ?_
      match v, hv with
      | .step u .keep, hv =>
          change Step.levels (u.path ++ [.keep]) = j + 1
          rw [Step.levels_append, ih u (Ctx.boxIn_keep hv).2.1]
          rfl
      | .step u .box, hv =>
          change Step.levels (u.path ++ [.box]) = j + 1
          rw [Step.levels_append, ih u (Ctx.boxIn_step_box hv)]
          rfl
      | .root _, hv => cases hv
      | .step _ .fst, hv => cases hv
      | .step _ .snd, hv => cases hv
      | .step _ .dia, hv => cases hv
      | .step _ .here, hv => cases hv
  | @dia Δ ρ j x X hx hP ih =>
      refine levels_of_decl fun v T _ hv => ?_
      match v, hv with
      | .step u .dia, hv =>
          change (if u = x then _ else none) = some T at hv
          split_ifs at hv with h
          subst h
          change Step.levels (u.path ++ [.dia]) = j + 1
          rw [Step.levels_append, ih u hx]
          rfl
      | .step u .keep, hv =>
          change Step.levels (u.path ++ [.keep]) = j + 1
          rw [Step.levels_append, ih u (Ctx.boxIn_keep hv).2.1]
          rfl
      | .step u .box, hv =>
          change Step.levels (u.path ++ [.box]) = j + 1
          rw [Step.levels_append, ih u (Ctx.boxIn_step_box hv)]
          rfl
      | .root _, hv => cases hv
      | .step _ .fst, hv => cases hv
      | .step _ .snd, hv => cases hv
      | .step _ .here, hv => cases hv

/-! ## Inside a possible root's content: the generic shapes -/

omit [ModalSys] in
/-- Cutting an address that runs through a root's content at its last step. -/
theorem ext_dia_eq_step {pre v : VarSymb} {q : List Step} {st : Step}
    (h : pre.ext (.dia :: q) = .step v st) :
    (q = [] ∧ v = pre ∧ st = .dia) ∨ ∃ q', q = q' ++ [st] ∧ v = pre.ext (.dia :: q') := by
  rcases List.eq_nil_or_concat q with rfl | ⟨q', b, rfl⟩
  · left
    change VarSymb.step pre .dia = _ at h
    injection h with h₁ h₂
    exact ⟨rfl, h₁.symm, h₂.symm⟩
  · right
    rw [List.concat_eq_append, ← List.cons_append, ext_append_step] at h
    injection h with h₁ h₂
    subst h₂
    exact ⟨q', List.concat_eq_append .., h₁.symm⟩

/-- Reachable addresses inside a root's content read generically when the declared ones do. -/
theorem ref_rootSh_of_decl (hT : ModalSys.T = true) {s : GW hF M₀} {Δ : Ctx}
    {ρ : GEnv hF M₀ Δ s} {j : ℕ} (hlv : ∀ (y : VarSymb) {T : VarType}, Δ.ref y = some T →
      Step.levels y.path = j) (pre : VarSymb) (hpre : PPath pre.path)
    (hdecl : ∀ (v : VarSymb) (T : VarType) (hv : Δ v = some T) (q : List Step),
      v = pre.ext (.dia :: q) → ρ v T hv = rootSh s pre (.dia :: q) T) :
    ∀ (y : VarSymb) {T : VarType} (h : Δ.ref y = some T) (q : List Step),
      y = pre.ext (.dia :: q) → ρ.ref j y h = rootSh s pre (.dia :: q) T
  | .root r, T, h, q, hy => by
      exfalso
      rcases List.eq_nil_or_concat q with rfl | ⟨q', b, rfl⟩
      · cases hy
      · rw [List.concat_eq_append, ← List.cons_append, ext_append_step] at hy
        cases hy
  | .step v st, T, h, q, hy => by
      by_cases hs : st.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Δ.ref v = some U := by
          rw [Ctx.ref_step_proj Δ v hs] at h
          cases hU : Δ.ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        rcases ext_dia_eq_step hy.symm with ⟨-, -, rfl⟩ | ⟨q', rfl, rfl⟩
        · cases hs
        · rw [Model.ShEnv.ref_proj ρ j hs hU h,
            ref_rootSh_of_decl hT hlv pre hpre hdecl _ hU q' rfl]
          have hl := hlv _ hU
          rw [VarSymb.ext_path, Step.levels_append, levels_ppath hpre, Nat.zero_add] at hl
          rw [rootSh_proj hT s pre hl hs]
          simp
      · rw [Model.ShEnv.ref_nonproj ρ j hs h]
        exact hdecl _ T _ q hy

end GArrow

end V12M

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-- ⭐**Inside a possible root's content the pushed canonical environment is generic**: with the
    `□`-lift on, every address `pre.dia.q` reads `rootSh s pre (dia :: q)` — the root's template
    is generic (`cEnv_dia_generic`), and keeping and projecting move generic shapes to generic
    shapes (`rootSh_keep_shp`, `rootSh_proj`). -/
theorem Pushed.rootSh (hT : ModalSys.T = true)
    (hS : ModalSys.FourStrongW = true → ModalSys.FourStrong = true)
    (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {i : ℕ} {Δ : Ctx} {ρ : GEnv hF M₀ Δ s} {j : ℕ}
    (hP : Pushed hF M₀ s i Δ ρ j) (pre : VarSymb) (hpre : PPath pre.path) :
    ∀ (y : VarSymb) {T : VarType} (h : Δ.ref y = some T) (q : List Step),
      y = pre.ext (.dia :: q) → ρ.ref j y h = rootSh s pre (.dia :: q) T := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  induction hP with
  | base =>
      refine ref_rootSh_of_decl hT (Pushed.base (i := i)).levels pre hpre fun v T hv q hvq => ?_
      obtain ⟨r, rfl⟩ := ctxOf_decl hv
      rcases List.eq_nil_or_concat q with rfl | ⟨q', b, rfl⟩
      · cases hvq
      · rw [List.concat_eq_append, ← List.cons_append, ext_append_step] at hvq
        cases hvq
  | @box Δ ρ j hP ih =>
      refine ref_rootSh_of_decl hT hP.box.levels pre hpre fun v T hv q hvq => ?_
      match v, hv with
      | .step u .keep, hv =>
          obtain ⟨-, hu, hk⟩ := Ctx.boxIn_keep hv
          rcases ext_dia_eq_step hvq.symm with ⟨-, -, h⟩ | ⟨q', rfl, huq⟩
          · cases h
          · change (GFunc.shp (GFunc.keep (σ := σ) hF hk) j (ρ.ref j u hu)).inner = _
            rw [ih u hu q' huq]
            have hl := hP.levels _ hu
            rw [huq, VarSymb.ext_path, Step.levels_append, levels_ppath hpre,
              Nat.zero_add] at hl
            obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 :=
              ⟨Step.levels q', by
                rw [← hl]; change 1 + Step.levels q' = Step.levels q' + 1; omega⟩
            rw [rootSh_keep_shp hT s pre hl _ hk]
            simp
      | .step u .box, hv =>
          rw [(Ctx.boxIn_box hv).1] at hko
          cases hko
      | .root _, hv => cases hv
      | .step _ .fst, hv => cases hv
      | .step _ .snd, hv => cases hv
      | .step _ .dia, hv => cases hv
      | .step _ .here, hv => cases hv
  | @dia Δ ρ j x X hx hP ih =>
      refine ref_rootSh_of_decl hT (hP.dia hx).levels pre hpre fun v T hv q hvq => ?_
      match v, hv with
      | .step u .dia, hv =>
          have hux : u = x := by
            change (if u = x then _ else none) = some T at hv
            split_ifs at hv with h
            exact h
          subst hux
          have hXT := Ctx.diaIn_step_dia hx hv
          subst hXT
          change (ρ.ref j _ hx).body = _
          rcases ext_dia_eq_step hvq.symm with ⟨rfl, rfl, -⟩ | ⟨q', rfl, rfl⟩
          · -- the root's own content: its template is generic
            have hl := hP.levels _ hx
            rw [levels_ppath hpre] at hl
            subst hl
            cases hP with
            | base =>
                rw [cEnv_ref hT hM₀ (Ctx.Le.refl _) _ hx,
                  cEnv_dia_generic hT hS hM₀ _ s _ X le_rfl ⟨i, hx⟩]
                rfl
          · rw [ih _ hx q' rfl]
            rfl
      | .step u .keep, hv =>
          obtain ⟨-, hu, hk⟩ := Ctx.boxIn_keep (Γ := Δ) hv
          rcases ext_dia_eq_step hvq.symm with ⟨-, -, h⟩ | ⟨q', rfl, huq⟩
          · cases h
          · change (GFunc.shp (GFunc.keep (σ := σ) hF hk) j (ρ.ref j u hu)).inner = _
            rw [ih u hu q' huq]
            have hl := hP.levels _ hu
            rw [huq, VarSymb.ext_path, Step.levels_append, levels_ppath hpre,
              Nat.zero_add] at hl
            obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 :=
              ⟨Step.levels q', by
                rw [← hl]; change 1 + Step.levels q' = Step.levels q' + 1; omega⟩
            rw [rootSh_keep_shp hT s pre hl _ hk]
            simp
      | .step u .box, hv =>
          rw [(Ctx.boxIn_box (Γ := Δ) hv).1] at hko
          cases hko
      | .root _, hv => cases hv
      | .step _ .fst, hv => cases hv
      | .step _ .snd, hv => cases hv
      | .step _ .here, hv => cases hv

end GArrow

end V12M
