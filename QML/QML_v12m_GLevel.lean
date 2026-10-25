import QML.QML_v12m_GOrigin

/-!
# QML v12m — the growing tree: levels of roots

The canonical shapes of T + 4 are defined by recursion on a **level** of each root
(`docs/v12-modal-extensions.md` §3 4, "(B) in Lean"): a lifted root's template reads its lifted
term's variables, which must be lower, and an image's shape is its source's, at the same level.
The levels are ghost data, computed alongside the chain (`glev`), not stored in the network:

* an image root has its source root's level (`levRealF`, `childLev`, the residual in `levLift`);
* a lifted root is one above every variable of the child it is lifted from (`levLift`);
* every other root keeps whatever level it has (Henkin witnesses: none is read).

`LevOk` states the two facts of a network and its levels; every operation keeps them
(`LevOk.applyOp`), and no operation changes an existing root's level (`levOp_old`).  In the limit:
⭐`lev_img` (an image root's level is its source's) and ⭐`lev_lift` (a lifted term's variables
are below the lifted root).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature}

namespace GNetSt

/-- Levels of the roots of each node. -/
abbrev Lev : Type := Node → ℕ → ℕ

/-- The largest level of the roots below `n` of `k`. -/
def levMax (lv : Lev) (k : Node) : ℕ → ℕ
  | 0 => 0
  | n + 1 => max (lv k n) (levMax lv k n)

omit [ModalSys] in
theorem lev_le_levMax (lv : Lev) (k : Node) : ∀ {n j : ℕ}, j < n → lv k j ≤ levMax lv k n
  | n + 1, j, h => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
      · exact (lev_le_levMax lv k h).trans (le_max_right _ _)
      · exact le_max_left _ _

/-- Set the level of root `z` of `k`. -/
def setLev (lv : Lev) (k : Node) (z m : ℕ) : Lev :=
  Function.update lv k (Function.update (lv k) z m)

omit [ModalSys] in
theorem setLev_self (lv : Lev) (k : Node) (z m : ℕ) : setLev lv k z m k z = m := by
  simp [setLev]

omit [ModalSys] in
theorem setLev_ne (lv : Lev) {k k' : Node} {z z' : ℕ} (m : ℕ) (h : ¬ (k' = k ∧ z' = z)) :
    setLev lv k z m k' z' = lv k' z' := by
  unfold setLev
  by_cases hk : k' = k
  · subst hk
    rw [Function.update_self, Function.update_of_ne (fun e => h ⟨rfl, e⟩)]
  · rw [Function.update_of_ne hk]

variable (hF : ModalSys.Four = true)

/-- Levels after realising forward along the edge into `k`: the new image takes its source's. -/
def levRealF (N : GNetSt σ) (lv : Lev) : Node → Lev
  | [] => lv
  | c :: p =>
      if (N.fcl (c :: p)).length < (N.st p).l.length then
        setLev lv (c :: p) (N.st (c :: p)).l.length (lv p (N.fcl (c :: p)).length)
      else lv

/-- The levels of a new child's roots: the parent's, and for the content its witness's. -/
def childLev (N : GNetSt σ) (lv : Lev) (s : Node) (kd : Option VarSymb) (r : ℕ) : ℕ :=
  if r < (N.st s).l.length then lv s r
  else
    match kd with
    | some x =>
        match x.rt with
        | .free rx => lv s rx
        | .bnd _ => 0
    | none => 0

/-- Levels after a child step: the new child's, if one was made. -/
noncomputable def levMk (N : GNetSt σ) (lv : Lev) (s : Node)
    (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : Lev :=
  if (N.mkChild hF s o).nch s = N.nch s then lv
  else Function.update lv (N.nch s :: s) (childLev N lv s ((N.mkChild hF s o).kind (N.nch s :: s)))

open Classical in
/-- Levels after a lift: the lifted root is one above every variable of the child, and its
    residual is at the same level. -/
noncomputable def levLift (N : GNetSt σ) (lv : Lev) : Node → LTerm σ → Lev
  | [], _ => lv
  | c :: p, ⟨l, T, a, t⟩ =>
      if N.fcl (c :: p) = (N.st p).l ∧ l <:+ (N.st (c :: p)).l ∧ T.liftable = true ∧
          LiftAdm hF ⟨l, T, a, t⟩ then
        setLev (setLev lv p (N.st p).l.length (levMax lv (c :: p) (N.st (c :: p)).l.length + 1))
          (c :: p) (N.st (c :: p)).l.length (levMax lv (c :: p) (N.st (c :: p)).l.length + 1)
      else lv

/-- One realisation step, with levels. -/
noncomputable def stepRF (k : Node) (P : GNetSt σ × Lev) : GNetSt σ × Lev :=
  (P.1.realF hF k, levRealF P.1 P.2 k)

theorem stepRF_fst (k : Node) : ∀ (j : ℕ) (P : GNetSt σ × Lev),
    ((stepRF hF k)^[j] P).1 = (fun N' => N'.realF hF k)^[j] P.1
  | 0, _ => rfl
  | j + 1, P => by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, stepRF_fst k j]
      rfl

/-- Levels after catching up. -/
noncomputable def levCatchUp (N : GNetSt σ) (lv : Lev) : Node → Lev
  | [] => lv
  | c :: p => ((stepRF hF (c :: p))^[(N.st p).l.length - (N.fcl (c :: p)).length] (N, lv)).2

open Classical in
/-- Levels after an operation. -/
noncomputable def levOp (N : GNetSt σ) (lv : Lev) : GOp σ → Lev
  | .inl _ => lv
  | .inr (.inl (s, o)) => if N.Live s then levMk hF N lv s o else lv
  | .inr (.inr (.inl k)) => if N.Live k then levRealF N lv k else lv
  | .inr (.inr (.inr (k, n))) =>
      if N.Live k then levLift hF (N.catchUp hF k) (levCatchUp hF N lv k) k n else lv

variable {hF}

/-! ## The facts -/

/-- ⭐**Levels of a network**: an image root's is its source root's, and a lifted root's is above
    every variable of the term it is lifted to. -/
structure LevOk (N : GNetSt σ) (lv : Lev) : Prop where
  img : ∀ c p, N.Live (c :: p) → ∀ w y, N.InView (c :: p) w → N.fmap (c :: p) w = .inl y →
    ∀ r u, y.rt = .free r → w.rt = .free u → lv (c :: p) r = lv p u
  lifted : ∀ c p, N.Live (c :: p) → ∀ w e, N.InView (c :: p) w →
    N.fmap (c :: p) w = .inr e →
    ∀ r, w = .step (.root (.free r)) .keep → ∀ j < e.1.length, lv (c :: p) j < lv p r

variable {N : GNetSt σ}

/-- A good network's term entries are over the child's variables. -/
theorem Good.ent_lt (hN : N.Good) {c : ℕ} {p : Node} (hk : N.Live (c :: p)) {w : VarSymb}
    {e : LTerm σ} (hv : N.InView (c :: p) w) (he : N.fmap (c :: p) w = .inr e) :
    e.1.length ≤ (N.st (c :: p)).l.length := by
  classical
  obtain ⟨T, hT⟩ := hv
  obtain ⟨-, -, hf, -⟩ := hN.fwd c p hk
  have h := hf w T (kView_lastProj hT) hT
  rw [he] at h
  obtain ⟨l, U, a, τ⟩ := e
  change (entOf (ctxOf (N.st (c :: p)).l) (.inr ⟨l, U, a, τ⟩)).OkRef T at h
  simp only [entOf] at h
  split_ifs at h with hle
  · change l.length ≤ _
    by_contra hlt
    have hr : (ctxOf l).ref (.root (.free (N.st (c :: p)).l.length)) =
        some (rootTy l (N.st (c :: p)).l.length) := ctxOf_root_lt (by omega)
    have := hle.ref hr
    obtain ⟨r, hr', hlt', -⟩ := ref_rt this
    cases hr'
    exact lt_irrefl _ hlt'
  · exact h.elim

theorem LevOk.setSt {lv : Lev} (hL : N.LevOk lv) (s : Node) (t : NodeSt σ) :
    (N.setSt s t).LevOk lv :=
  ⟨fun c p hk => hL.img c p ((live_setSt N s t _).mp hk),
    fun c p hk => hL.lifted c p ((live_setSt N s t _).mp hk)⟩


/-! ## Old roots keep their levels -/

theorem levRealF_old (lv : Lev) {k : Node} {k' : Node} {z : ℕ}
    (hk' : N.Live k') (hz : z < (N.st k').l.length) : levRealF N lv k k' z = lv k' z := by
  match k with
  | [] => rfl
  | c :: p =>
      simp only [levRealF]
      split_ifs
      · refine setLev_ne lv _ fun ⟨e₁, e₂⟩ => ?_
        subst e₁ e₂
        exact lt_irrefl _ hz
      · rfl

theorem levLift_old {N : GNetSt σ} (lv : Lev) {k : Node} (o : LTerm σ) {k' : Node} {z : ℕ}
    (hz : z < (N.st k').l.length) : levLift hF N lv k o k' z = lv k' z := by
  match k, o with
  | [], _ => rfl
  | c :: p, ⟨l, T, _, _⟩ =>
      simp only [levLift]
      split_ifs
      · rw [setLev_ne _ _ (fun ⟨e₁, e₂⟩ => by subst e₁ e₂; exact lt_irrefl _ hz),
          setLev_ne _ _ (fun ⟨e₁, e₂⟩ => by subst e₁ e₂; exact lt_irrefl _ hz)]
      · rfl

theorem stepRF_old (k : Node) :
    ∀ (j : ℕ) {N : GNetSt σ} (lv : Lev), N.Good → N.Live k → ∀ {k' : Node} {z : ℕ},
      N.Live k' → z < (N.st k').l.length → ((stepRF hF k)^[j] (N, lv)).2 k' z = lv k' z
  | 0, _, _, _, _, _, _, _, _ => rfl
  | j + 1, N, lv, hN, hk, k', z, hk', hz => by
      rw [Function.iterate_succ_apply]
      change ((stepRF hF k)^[j] (N.realF hF k, levRealF N lv k)).2 k' z = _
      rw [stepRF_old k j _ (hN.realF hF hk) ((live_of_nch (nch_realF hF N k) k).mpr hk)
          ((live_of_nch (nch_realF hF N k) k').mpr hk')
          (lt_of_lt_of_le hz ((Ext.realF hF hN hk).grows k' hk').suf.length_le),
        levRealF_old lv hk' hz]

theorem levCatchUp_old (hN : N.Good) (lv : Lev) {k : Node} (hk : N.Live k) {k' : Node} {z : ℕ}
    (hk' : N.Live k') (hz : z < (N.st k').l.length) : levCatchUp hF N lv k k' z = lv k' z := by
  match k with
  | [] => rfl
  | c :: p => exact stepRF_old (c :: p) _ lv hN hk hk' hz

theorem levMk_old (lv : Lev) {s : Node} (o : Σ l : List VarType, WFF σ (ctxOf l) 0)
    {k' : Node} {z : ℕ} (hk' : N.Live k') : levMk hF N lv s o k' z = lv k' z := by
  unfold levMk
  split_ifs
  · rfl
  · rw [Function.update_of_ne (fun e => not_live_new s (e ▸ hk'))]

/-- ⭐No operation changes an existing root's level. -/
theorem levOp_old (hN : N.Good) (lv : Lev) (o : GOp σ) {k : Node} {z : ℕ} (hk : N.Live k)
    (hz : z < (N.st k).l.length) : levOp hF N lv o k z = lv k z := by
  rcases o with ⟨s, o⟩ | ⟨s, o⟩ | k₀ | ⟨k₀, n⟩
  · rfl
  · simp only [levOp]
    split_ifs
    · exact levMk_old lv o hk
    · rfl
  · simp only [levOp]
    split_ifs
    · exact levRealF_old lv hk hz
    · rfl
  · simp only [levOp]
    split_ifs with h
    · obtain ⟨-, -, he⟩ := hN.catchUp hF h
      rw [levLift_old _ _ (lt_of_lt_of_le hz (he.grows k hk).suf.length_le),
        levCatchUp_old hN lv h hk hz]
    · rfl

/-! ## Each operation keeps the facts -/

/-- Realising forward keeps the facts. -/
theorem LevOk.realF {lv : Lev} (hL : N.LevOk lv) (hN : N.Good) {k : Node} (hk : N.Live k) :
    (N.realF hF k).LevOk (levRealF N lv k) := by
  match k with
  | [] => exact hL
  | c :: p =>
      simp only [GNetSt.realF, levRealF]
      split_ifs with hlt
      swap
      · exact hL
      set N' := (N.setSt (c :: p) (grealStep hF (N.st p) (N.st (c :: p)) (N.kind (c :: p))
        (N.fcl (c :: p)) (N.fmap (c :: p)))).setFwd (c :: p)
        (nextTy (N.st p).l (N.fcl (c :: p)) :: (N.fcl (c :: p)))
        (gextF (N.fmap (c :: p)) (nextTy (N.st p).l (N.fcl (c :: p))) (N.fcl (c :: p)).length
          (N.st (c :: p)).l.length)
      have hpk : (p : Node) ≠ c :: p := fun e => NetSt.ne_parent c p e.symm
      have hlive : ∀ k', N'.Live k' ↔ N.Live k' := fun k' =>
        (live_setFwd _ _ _ _ k').trans (live_setSt _ _ _ _)
      -- old roots keep their levels
      have hold : ∀ {k' : Node} {x : ℕ}, x < (N.st k').l.length →
          setLev lv (c :: p) (N.st (c :: p)).l.length (lv p (N.fcl (c :: p)).length) k' x =
            lv k' x := by
        intro k' x hx
        refine setLev_ne lv _ fun ⟨e₁, e₂⟩ => ?_
        subst e₁ e₂
        exact lt_irrefl _ hx
      have hfcl : ∀ k', k' ≠ c :: p → N'.fcl k' = N.fcl k' :=
        fun k' h => Function.update_of_ne h _ _
      have hfm : ∀ k', k' ≠ c :: p → N'.fmap k' = N.fmap k' :=
        fun k' h => Function.update_of_ne h _ _
      have hview : ∀ k', k' ≠ c :: p → ∀ v, N'.InView k' v ↔ N.InView k' v := by
        intro k' h v
        change (∃ T, (ctxOf (N'.fcl k')).kView (N.kind k') v = some T) ↔ _
        rw [hfcl k' h]
        rfl
      have hfm' : N'.fmap (c :: p) =
          gextF (N.fmap (c :: p)) (nextTy (N.st p).l (N.fcl (c :: p))) (N.fcl (c :: p)).length
            (N.st (c :: p)).l.length := Function.update_self _ _ _
      have hcases : ∀ v, N'.InView (c :: p) v →
          v.rt = .free (N.fcl (c :: p)).length ∨ N.InView (c :: p) v := by
        intro v ⟨T, hT⟩
        change (ctxOf (Function.update N.fcl (c :: p)
          (nextTy (N.st p).l (N.fcl (c :: p)) :: (N.fcl (c :: p))) (c :: p))).kView
          (N.kind (c :: p)) v = some T at hT
        rw [Function.update_self] at hT
        rcases kView_new_or_old hT with h | h
        · exact Or.inl h
        · exact Or.inr ⟨T, h⟩
      have hold_rt : ∀ v, N.InView (c :: p) v → ¬ v.rt = .free (N.fcl (c :: p)).length := by
        intro v ⟨T, hT⟩ h
        obtain ⟨r, hr, hlt'⟩ := kView_rt hT
        rw [h] at hr
        cases hr
        exact lt_irrefl _ hlt'
      have hgold : ∀ v, N.InView (c :: p) v → N'.fmap (c :: p) v = N.fmap (c :: p) v := by
        intro v hv
        rw [hfm']
        obtain ⟨u, s, rfl, -, -⟩ := kView_item hv.choose_spec
        exact gextF_old (u := u) (hold_rt (.step u s) hv) s
      refine ⟨fun c₁ p₁ hk₁ w y hw hy r u hr hu => ?_,
        fun c₁ p₁ hk₁ w e hw he r hwr j hj => ?_⟩
      · have hk₁' := (hlive _).mp hk₁
        by_cases h₁ : (c₁ :: p₁ : Node) = c :: p
        · obtain ⟨hc₁, hp₁⟩ := List.cons.inj h₁
          subst c₁ p₁
          rcases hcases w hw with hn | hwo
          · -- the new image and its source
            obtain ⟨u', s', rfl, -, -⟩ := kView_item hw.choose_spec
            have hn' : u'.rt = .free (N.fcl (c :: p)).length := hn
            rw [hfm', gextF_new (u := u') hn' s'] at hy
            cases hy
            rw [VarSymb.ext_rt] at hr
            cases hr
            change u'.rt = _ at hu
            rw [hn'] at hu
            cases hu
            have hne : ¬ (p = c :: p ∧ (N.fcl (c :: p)).length = (N.st (c :: p)).l.length) :=
              fun ⟨e, _⟩ => hpk e
            rw [setLev_self, setLev_ne _ _ hne]
          · rw [hgold w hwo] at hy
            obtain ⟨r', hr', hlt'⟩ := hN.img_lt hk hwo hy
            have hrr : r' = r := Root.free.inj (hr'.symm.trans hr)
            subst r'
            obtain ⟨u', hu', hlt''⟩ := hN.inView_lt hk hwo
            have huu : u' = u := Root.free.inj (hu'.symm.trans hu)
            subst u'
            rw [hold hlt', hold hlt'']
            exact hL.img c p hk w y hwo hy r u hr' hu'
        · rw [hview _ h₁] at hw
          rw [hfm _ h₁] at hy
          obtain ⟨r', hr', hlt'⟩ := hN.img_lt hk₁' hw hy
          have hrr : r' = r := Root.free.inj (hr'.symm.trans hr)
          subst r'
          obtain ⟨u', hu', hlt''⟩ := hN.inView_lt hk₁' hw
          have huu : u' = u := Root.free.inj (hu'.symm.trans hu)
          subst u'
          rw [hold hlt', hold hlt'']
          exact hL.img c₁ p₁ hk₁' w y hw hy r u hr' hu'
      · have hk₁' := (hlive _).mp hk₁
        have hw' : N.InView (c₁ :: p₁) w ∧ N.fmap (c₁ :: p₁) w = .inr e := by
          by_cases h₁ : (c₁ :: p₁ : Node) = c :: p
          · rw [h₁] at hw he ⊢
            rcases hcases w hw with hn | hwo
            · exfalso
              obtain ⟨u', s', rfl, -, -⟩ := kView_item hw.choose_spec
              have hn' : u'.rt = .free (N.fcl (c :: p)).length := hn
              rw [hfm', gextF_new (u := u') hn' s'] at he
              cases he
            · exact ⟨hwo, (hgold w hwo).symm.trans he⟩
          · rw [hview _ h₁] at hw
            rw [hfm _ h₁] at he
            exact ⟨hw, he⟩
        have hlt' := lt_of_lt_of_le hj (hN.ent_lt hk₁' hw'.1 hw'.2)
        obtain ⟨u', hu', hlt''⟩ := hN.inView_lt hk₁' hw'.1
        have huu : u' = r := by
          rw [hwr] at hu'
          exact (Root.free.inj hu').symm
        subst u'
        rw [hold hlt', hold hlt'']
        exact hL.lifted c₁ p₁ hk₁' w e hw'.1 hw'.2 r hwr j hj

theorem LevOk.iterate_realF (k : Node) :
    ∀ (j : ℕ) {N : GNetSt σ} {lv : Lev}, N.LevOk lv → N.Good → N.Live k →
      ((stepRF hF k)^[j] (N, lv)).1.LevOk ((stepRF hF k)^[j] (N, lv)).2
  | 0, _, _, hL, _, _ => hL
  | j + 1, N, lv, hL, hN, hk => by
      rw [Function.iterate_succ_apply]
      exact LevOk.iterate_realF k j (hL.realF hN hk) (hN.realF hF hk)
        ((live_of_nch (nch_realF hF N k) k).mpr hk)

theorem LevOk.catchUp {lv : Lev} (hL : N.LevOk lv) (hN : N.Good) {k : Node} (hk : N.Live k) :
    (N.catchUp hF k).LevOk (levCatchUp hF N lv k) := by
  match k with
  | [] => exact hL
  | c :: p =>
      have := LevOk.iterate_realF (hF := hF) (c :: p)
        ((N.st p).l.length - (N.fcl (c :: p)).length) hL hN hk
      rw [stepRF_fst] at this
      exact this

/-- Lifting keeps the facts. -/
theorem LevOk.lift {lv : Lev} (hL : N.LevOk lv) (hN : N.Good) {k : Node} (hk : N.Live k)
    (o : LTerm σ) : (N.lift hF k o).LevOk (levLift hF N lv k o) := by
  match k, o with
  | [], _ => exact hL
  | c :: p, ⟨l, T, a, t⟩ =>
      by_cases hcond : N.fcl (c :: p) = (N.st p).l ∧ l <:+ (N.st (c :: p)).l ∧
        T.liftable = true ∧ LiftAdm hF ⟨l, T, a, t⟩
      swap
      · have hlv : levLift hF N lv (c :: p) ⟨l, T, a, t⟩ = lv := by
          simp only [levLift, if_neg hcond]
        rw [hlv]
        by_cases hcl : N.fcl (c :: p) = (N.st p).l
        · by_cases h : l <:+ (N.st (c :: p)).l
          · by_cases hl : T.liftable = true
            · have hv : ¬ LiftAdm hF ⟨l, T, a, t⟩ := fun hv => hcond ⟨hcl, h, hl, hv⟩
              simp only [GNetSt.lift, if_pos hcl, dif_pos h, dif_pos hl, if_neg hv]
              exact hL
            · simp only [GNetSt.lift, if_pos hcl, dif_pos h, dif_neg hl]
              exact hL
          · simp only [GNetSt.lift, if_pos hcl, dif_neg h]
            exact hL
        · simp only [GNetSt.lift, if_neg hcl]
          exact hL
      obtain ⟨hcl, h, hl, hv⟩ := hcond
      rw [lift_spec hF hcl h hl hv]
      have hlv : levLift hF N lv (c :: p) ⟨l, T, a, t⟩ =
          setLev (setLev lv p (N.st p).l.length
              (levMax lv (c :: p) (N.st (c :: p)).l.length + 1))
            (c :: p) (N.st (c :: p)).l.length
              (levMax lv (c :: p) (N.st (c :: p)).l.length + 1) := by
        simp only [levLift, if_pos (And.intro hcl (And.intro h (And.intro hl hv)))]
      rw [hlv]
      have hpk : (p : Node) ≠ c :: p := fun e => NetSt.ne_parent c p e.symm
      set N₁ := (N.setSt p (liftPar hF (N.st p) (N.st (c :: p)) (N.kind (c :: p)) (N.fmap (c :: p))
          (Term.mono (ctxOf_le_of_suffix h) t) hl)).setSt (c :: p)
          (liftChild hF (N.st p) (N.st (c :: p)) (N.kind (c :: p)) (N.fmap (c :: p))
            (Term.mono (ctxOf_le_of_suffix h) t) hl)
      set N' := N₁.setFwd (c :: p) (T :: (N.st p).l) (gliftG (N.fmap (c :: p)) T (N.st p).l.length
        (.inr ⟨(N.st (c :: p)).l, T, a, Term.mono (ctxOf_le_of_suffix h) t⟩)
        (.free (N.st (c :: p)).l.length))
      have hlive : ∀ k', N'.Live k' ↔ N.Live k' := fun k' =>
        (live_setFwd _ _ _ _ k').trans ((live_setSt _ _ _ _).trans (live_setSt _ _ _ _))
      have hold : ∀ {k' : Node} {x : ℕ}, x < (N.st k').l.length →
          setLev (setLev lv p (N.st p).l.length (levMax lv (c :: p) (N.st (c :: p)).l.length + 1))
            (c :: p) (N.st (c :: p)).l.length (levMax lv (c :: p) (N.st (c :: p)).l.length + 1)
            k' x = lv k' x := by
        intro k' x hx
        have h₁ : ¬ (k' = c :: p ∧ x = (N.st (c :: p)).l.length) := fun ⟨e₁, e₂⟩ => by
          subst e₁ e₂
          exact lt_irrefl _ hx
        have h₂ : ¬ (k' = p ∧ x = (N.st p).l.length) := fun ⟨e₁, e₂⟩ => by
          subst e₁ e₂
          exact lt_irrefl _ hx
        rw [setLev_ne _ _ h₁, setLev_ne _ _ h₂]
      have hfcl : ∀ k', k' ≠ c :: p → N'.fcl k' = N.fcl k' :=
        fun k' h => Function.update_of_ne h _ _
      have hfm : ∀ k', k' ≠ c :: p → N'.fmap k' = N.fmap k' :=
        fun k' h => Function.update_of_ne h _ _
      have hview : ∀ k', k' ≠ c :: p → ∀ v, N'.InView k' v ↔ N.InView k' v := by
        intro k' h v
        change (∃ T, (ctxOf (N'.fcl k')).kView (N.kind k') v = some T) ↔ _
        rw [hfcl k' h]
        rfl
      have hfm' : N'.fmap (c :: p) = (gliftG (N.fmap (c :: p)) T (N.st p).l.length
        (.inr ⟨(N.st (c :: p)).l, T, a, Term.mono (ctxOf_le_of_suffix h) t⟩)
        (.free (N.st (c :: p)).l.length)) := Function.update_self _ _ _
      have hcases : ∀ v, N'.InView (c :: p) v →
          v.rt = .free (N.st p).l.length ∨ N.InView (c :: p) v := by
        intro v ⟨T', hT⟩
        change (ctxOf (Function.update N.fcl (c :: p) (T :: (N.st p).l) (c :: p))).kView
          (N.kind (c :: p)) v = some T' at hT
        rw [Function.update_self] at hT
        rcases kView_new_or_old hT with h' | h'
        · exact Or.inl h'
        · rw [← hcl] at h'
          exact Or.inr ⟨T', h'⟩
      have hold_rt : ∀ v, N.InView (c :: p) v → ¬ v.rt = .free (N.st p).l.length := by
        intro v ⟨T', hT⟩ h'
        obtain ⟨r, hr, hlt'⟩ := kView_rt hT
        rw [h'] at hr
        cases hr
        rw [hcl] at hlt'
        exact lt_irrefl _ hlt'
      have hgold : ∀ v, N.InView (c :: p) v → N'.fmap (c :: p) v = N.fmap (c :: p) v := by
        intro v hv
        rw [hfm']
        obtain ⟨u, s, rfl, -, -⟩ := kView_item hv.choose_spec
        exact gliftG_old (u := u) (hold_rt (.step u s) hv)
      refine ⟨fun c₁ p₁ hk₁ w y hw hy r u hr hu => ?_,
        fun c₁ p₁ hk₁ w e hw he r hwr j hj => ?_⟩
      · have hk₁' := (hlive _).mp hk₁
        by_cases h₁ : (c₁ :: p₁ : Node) = c :: p
        · obtain ⟨hc₁, hp₁⟩ := List.cons.inj h₁
          subst c₁ p₁
          rcases hcases w hw with hn | hwo
          · obtain ⟨u', s', rfl, -, -⟩ := kView_item hw.choose_spec
            have hn' : u'.rt = .free (N.st p).l.length := hn
            by_cases hnk : u' = .root (.free (N.st p).l.length) ∧ s' = .keep
            · obtain ⟨rfl, rfl⟩ := hnk
              rw [hfm', gliftG_keep] at hy
              cases hy
            · rw [hfm', gliftG_res (u := u') hn' hnk] at hy
              cases hy
              rw [VarSymb.ext_rt] at hr
              cases hr
              change u'.rt = _ at hu
              rw [hn'] at hu
              cases hu
              have hne : ¬ (p = c :: p ∧ (N.st p).l.length = (N.st (c :: p)).l.length) :=
                fun ⟨e, _⟩ => hpk e
              rw [setLev_self, setLev_ne _ _ hne, setLev_self]
          · rw [hgold w hwo] at hy
            obtain ⟨r', hr', hlt'⟩ := hN.img_lt hk hwo hy
            have hrr : r' = r := Root.free.inj (hr'.symm.trans hr)
            subst r'
            obtain ⟨u', hu', hlt''⟩ := hN.inView_lt hk hwo
            have huu : u' = u := Root.free.inj (hu'.symm.trans hu)
            subst u'
            rw [hold hlt', hold hlt'']
            exact hL.img c p hk w y hwo hy r u hr' hu'
        · rw [hview _ h₁] at hw
          rw [hfm _ h₁] at hy
          obtain ⟨r', hr', hlt'⟩ := hN.img_lt hk₁' hw hy
          have hrr : r' = r := Root.free.inj (hr'.symm.trans hr)
          subst r'
          obtain ⟨u', hu', hlt''⟩ := hN.inView_lt hk₁' hw
          have huu : u' = u := Root.free.inj (hu'.symm.trans hu)
          subst u'
          rw [hold hlt', hold hlt'']
          exact hL.img c₁ p₁ hk₁' w y hw hy r u hr' hu'
      · have hk₁' := (hlive _).mp hk₁
        by_cases h₁ : (c₁ :: p₁ : Node) = c :: p
        · obtain ⟨hc₁, hp₁⟩ := List.cons.inj h₁
          subst c₁ p₁
          rcases hcases w hw with hn | hwo
          · -- the new lift
            subst hwr
            cases hn
            rw [hfm', gliftG_keep] at he
            cases he
            change j < (N.st (c :: p)).l.length at hj
            have h₁ : ¬ (c :: p = c :: p ∧ j = (N.st (c :: p)).l.length) :=
              fun ⟨_, e⟩ => by
              subst e
              exact lt_irrefl _ hj
            have h₂ : ¬ (c :: p = p ∧ j = (N.st p).l.length) := fun ⟨e, _⟩ => hpk e.symm
            have h₃ : ¬ (p = c :: p ∧ (N.st p).l.length = (N.st (c :: p)).l.length) :=
              fun ⟨e, _⟩ => hpk e
            rw [setLev_ne _ _ h₁, setLev_ne _ _ h₂, setLev_ne _ _ h₃, setLev_self]
            exact Nat.lt_succ_of_le (lev_le_levMax lv _ hj)
          · rw [hgold w hwo] at he
            have hlt' := lt_of_lt_of_le hj (hN.ent_lt hk hwo he)
            obtain ⟨u', hu', hlt''⟩ := hN.inView_lt hk hwo
            have huu : u' = r := by
              rw [hwr] at hu'
              exact (Root.free.inj hu').symm
            subst u'
            rw [hold hlt', hold hlt'']
            exact hL.lifted c p hk w e hwo he r hwr j hj
        · rw [hview _ h₁] at hw
          rw [hfm _ h₁] at he
          have hlt' := lt_of_lt_of_le hj (hN.ent_lt hk₁' hw he)
          obtain ⟨u', hu', hlt''⟩ := hN.inView_lt hk₁' hw
          have huu : u' = r := by
            rw [hwr] at hu'
            exact (Root.free.inj hu').symm
          subst u'
          rw [hold hlt', hold hlt'']
          exact hL.lifted c₁ p₁ hk₁' w e hw he r hwr j hj

/-- A new child keeps the facts, with its roots at their sources' levels. -/
theorem LevOk.newChild {lv : Lev} (hL : N.LevOk lv) {s : Node} (hs : N.Live s)
    (kd : Option VarSymb) (t : NodeSt σ) :
    (N.newChild s kd t (ofRen (gchildMap (N.st s).l kd))).LevOk
      (Function.update lv (N.nch s :: s) (childLev N lv s kd)) := by
  set N' := N.newChild s kd t (ofRen (gchildMap (N.st s).l kd))
  have hne : ∀ k, N.Live k → k ≠ N.nch s :: s := fun k hk h => not_live_new s (h ▸ hk)
  have hold : ∀ k, N.Live k → Function.update lv (N.nch s :: s) (childLev N lv s kd) k = lv k :=
    fun k hk => Function.update_of_ne (hne k hk) _ _
  have hfcl : ∀ k, k ≠ N.nch s :: s → N'.fcl k = N.fcl k :=
    fun k h => Function.update_of_ne h _ _
  have hknd : ∀ k, k ≠ N.nch s :: s → N'.kind k = N.kind k :=
    fun k h => Function.update_of_ne h _ _
  have hfm : ∀ k, k ≠ N.nch s :: s → N'.fmap k = N.fmap k :=
    fun k h => Function.update_of_ne h _ _
  have hview : ∀ k, k ≠ N.nch s :: s → ∀ v, N'.InView k v ↔ N.InView k v := by
    intro k h v
    change (∃ T, (ctxOf (N'.fcl k)).kView (N'.kind k) v = some T) ↔ _
    rw [hfcl k h, hknd k h]
    rfl
  have hnew_fm : N'.fmap (N.nch s :: s) = ofRen (gchildMap (N.st s).l kd) :=
    Function.update_self _ _ _
  have hnew_view : ∀ v, N'.InView (N.nch s :: s) v →
      ∃ T, (ctxOf (N.st s).l).kView kd v = some T := by
    intro v ⟨T, hT⟩
    change (ctxOf (Function.update N.fcl _ (N.st s).l _)).kView
      (Function.update N.kind _ kd _) v = some T at hT
    rw [Function.update_self, Function.update_self] at hT
    exact ⟨T, hT⟩
  have hlv : ∀ c p, N'.Live (c :: p) → (c :: p : Node) ≠ N.nch s :: s → N.Live (c :: p) :=
    fun c p hk h => ((live_newChild hs kd t _ _).mp hk).resolve_right h
  refine ⟨fun c p hk w y hw hy r u hr hu => ?_, fun c p hk w e hw he r hwr j hj => ?_⟩
  · by_cases hkc : (c :: p : Node) = N.nch s :: s
    · obtain ⟨rfl, rfl⟩ := List.cons.inj hkc
      rw [hnew_fm] at hy
      cases hy
      obtain ⟨T, hT⟩ := hnew_view w hw
      rw [Function.update_self, hold _ hs]
      obtain ⟨u', hu', hlt'⟩ := kView_rt hT
      rw [hu] at hu'
      cases hu'
      rcases gchildMap_rt _ kd hT with h₁ | ⟨⟨x, rfl, rfl⟩, h₁⟩
      · rw [hr, hu] at h₁
        cases h₁
        unfold childLev
        rw [if_pos hlt']
      · rw [hr] at h₁
        cases h₁
        unfold childLev
        rw [if_neg (lt_irrefl _)]
        change x.rt = _ at hu
        simp only [hu]
    · rw [hview _ hkc] at hw
      rw [hfm _ hkc] at hy
      have hk' := hlv c p hk hkc
      rw [hold _ hk', hold _ hk'.1]
      exact hL.img c p hk' w y hw hy r u hr hu
  · by_cases hkc : (c :: p : Node) = N.nch s :: s
    · rw [hkc, hnew_fm] at he
      cases he
    · rw [hview _ hkc] at hw
      rw [hfm _ hkc] at he
      have hk' := hlv c p hk hkc
      rw [hold _ hk', hold _ hk'.1]
      exact hL.lifted c p hk' w e hw he r hwr j hj

theorem LevOk.mkChild {lv : Lev} (hL : N.LevOk lv) {s : Node} (hs : N.Live s)
    (o : Σ l : List VarType, WFF σ (ctxOf l) 0) :
    (N.mkChild hF s o).LevOk (levMk hF N lv s o) := by
  have hsame : (N.mkChild hF s o = N) ∨ ∃ kd t, N.mkChild hF s o =
      N.newChild s kd t (ofRen (gchildMap (N.st s).l kd)) := by
    obtain ⟨l, φ⟩ := o
    simp only [GNetSt.mkChild]
    split_ifs
    · split
      · split_ifs
        · exact Or.inl rfl
        · exact Or.inr ⟨_, _, rfl⟩
      · split_ifs
        · split
          · exact Or.inr ⟨_, _, rfl⟩
          · exact Or.inl rfl
        · exact Or.inl rfl
      · exact Or.inl rfl
    · exact Or.inl rfl
  unfold levMk
  rcases hsame with he | ⟨kd, t, he⟩
  · rw [if_pos (by rw [he]), he]
    exact hL
  · have hnch : (N.mkChild hF s o).nch s ≠ N.nch s := by
      rw [he]
      change Function.update (Function.update N.nch s (N.nch s + 1)) (N.nch s :: s) 0 s ≠ _
      rw [Function.update_of_ne (NetSt.ne_parent _ s).symm, Function.update_self]
      omega
    have hkd : (N.mkChild hF s o).kind (N.nch s :: s) = kd := by
      rw [he]
      exact Function.update_self _ _ _
    rw [if_neg hnch, hkd, he]
    exact hL.newChild hs kd t

theorem LevOk.henk {lv : Lev} (hL : N.LevOk lv) (s : Node)
    (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : (N.henk s o).LevOk lv := by
  obtain ⟨l, φ⟩ := o
  simp only [GNetSt.henk]
  split_ifs
  · split
    · split_ifs
      · exact hL.setSt _ _
      · exact hL
    · split_ifs
      · exact hL.setSt _ _
      · exact hL
    · exact hL
  · exact hL

/-- ⭐Every operation keeps the facts. -/
theorem LevOk.applyOp {lv : Lev} (hL : N.LevOk lv) (hN : N.Good) (o : GOp σ) :
    (N.applyOp hF o).LevOk (levOp hF N lv o) := by
  rcases o with ⟨s, o⟩ | ⟨s, o⟩ | k | ⟨k, n⟩
  · simp only [GNetSt.applyOp, levOp]
    split_ifs
    · exact hL.henk s o
    · exact hL
  · simp only [GNetSt.applyOp, levOp]
    split_ifs with h
    · exact hL.mkChild h o
    · exact hL
  · simp only [GNetSt.applyOp, levOp]
    split_ifs with h
    · exact hL.realF hN h
    · exact hL
  · simp only [GNetSt.applyOp, levOp]
    split_ifs with h
    · obtain ⟨h₁, h₂, -⟩ := hN.catchUp hF h
      exact (hL.catchUp hN h).lift h₁ h₂ n
    · exact hL

theorem levOk_init {l₀ : List VarType} (M₀ : Set (WFF σ (ctxOf l₀) 0)) :
    (init M₀).LevOk (fun _ _ => 0) :=
  ⟨fun _ _ hk => absurd (init_live hk) (by simp), fun _ _ hk => absurd (init_live hk) (by simp)⟩

end GNetSt

variable {hF : ModalSys.Four = true}

/-! ## The chain's levels -/

section Chain

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

variable (hF) in
/-- ⭐The levels along the chain. -/
noncomputable def glev {l₀ : List VarType} (M₀ : Set (WFF σ (ctxOf l₀) 0)) :
    ℕ → GNetSt.Lev
  | 0 => fun _ _ => 0
  | n + 1 => GNetSt.levOp hF (gnet hF M₀ n) (glev M₀ n) (gsched n)

theorem levOk_gnet {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}
    (h : Theory.IsMCS M₀) :
    ∀ n, (gnet hF M₀ n).LevOk (glev hF M₀ n)
  | 0 => GNetSt.levOk_init M₀
  | n + 1 => (levOk_gnet h n).applyOp (good_gnet hF h n) (gsched n)

/-- An existing root keeps its level along the chain. -/
theorem glev_stable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}
    (h : Theory.IsMCS M₀) {k : Node} {z m : ℕ} (hk : (gnet hF M₀ m).Live k)
    (hz : z < ((gnet hF M₀ m).st k).l.length) :
    ∀ {m'}, m ≤ m' → glev hF M₀ m' k z = glev hF M₀ m k z := by
  intro m' hmm
  induction hmm with
  | refl => rfl
  | step hle ih =>
      have he := ext_gnet hF h hle
      rw [← ih]
      exact GNetSt.levOp_old (good_gnet hF h _) _ _ (he.live k hk)
        (lt_of_lt_of_le hz (he.grows k hk).suf.length_le)

end Chain

/-! ## In the limit -/

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

open Classical in
/-- ⭐**The level of a root** of a world: its level from the round it exists at on. -/
noncomputable def lev (s : GW hF M₀) (z : ℕ) : ℕ :=
  if h : ∃ m, (gnet hF M₀ m).Live s.1 ∧ z < ((gnet hF M₀ m).st s.1).l.length then
    glev hF M₀ (Nat.find h) s.1 z
  else 0

theorem lev_at (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {z m : ℕ}
    (hk : (gnet hF M₀ m).Live s.1)
    (hz : z < ((gnet hF M₀ m).st s.1).l.length) : lev s z = glev hF M₀ m s.1 z := by
  classical
  have h : ∃ m, (gnet hF M₀ m).Live s.1 ∧ z < ((gnet hF M₀ m).st s.1).l.length :=
    ⟨m, hk, hz⟩
  rw [lev, dif_pos h]
  obtain ⟨hk', hz'⟩ := Nat.find_spec h
  exact (glev_stable hM₀ hk' hz' (Nat.find_min' h ⟨hk, hz⟩)).symm

/-- ⭐**An image root is at its source root's level.** -/
theorem lev_img (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: s.1)
    {w y : VarSymb} (hw : GCommitted hF M₀ t.1 w) (hy : fmapL hF M₀ t.1 w = .inl y) {r u : ℕ}
    (hr : y.rt = .free r) (hu : w.rt = .free u) : lev t r = lev s u := by
  obtain ⟨m, hk, hv⟩ := hw
  rw [hc] at hk hv hy
  rw [fmapL_at hM₀ hk hv] at hy
  have hN := good_gnet hF hM₀ m
  obtain ⟨r', hr', hlt'⟩ := hN.img_lt hk hv hy
  rw [hr] at hr'
  cases hr'
  obtain ⟨u', hu', hlt''⟩ := hN.inView_lt hk hv
  rw [hu] at hu'
  cases hu'
  rw [lev_at hM₀ (s := t) (hc ▸ hk) (hc ▸ hlt'), lev_at hM₀ (s := s) hk.1 hlt'', hc]
  exact (levOk_gnet hM₀ m).img c s.1 hk w y hv hy r u hr hu

/-- ⭐**A lifted term's variables are below the lifted root.** -/
theorem lev_lift (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: s.1)
    {r : ℕ}
    {e : LTerm σ} (he : fmapL hF M₀ t.1 (.step (.root (.free r)) .keep) = .inr e) {j : ℕ}
    (hj : j < e.1.length) : lev t j < lev s r := by
  obtain ⟨m, hk, hv⟩ := fmapL_committed he
  rw [hc] at hk hv he
  rw [fmapL_at hM₀ hk hv] at he
  have hN := good_gnet hF hM₀ m
  have hlt' := lt_of_lt_of_le hj (hN.ent_lt hk hv he)
  obtain ⟨u', hu', hlt''⟩ := hN.inView_lt hk hv
  cases hu'
  rw [lev_at hM₀ (s := t) (hc ▸ hk) (hc ▸ hlt'), lev_at hM₀ (s := s) hk.1 hlt'', hc]
  exact (levOk_gnet hM₀ m).lifted c s.1 hk _ e hv he r rfl j hj

end GArrow

end V12M
