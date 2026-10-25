import QML.QML_v12m_GLimit

/-!
# QML v12m — the growing tree: where an edge's entries come from

The shape templates of T + 4 (`docs/v12-modal-extensions.md` §3 4, "(B) in Lean") read an
address's origin off the edges' entries.  They need, of every edge:

* (N1) its **term entries** are kept items of roots (the roots lifted along it);
* (N3) an **image root has one source root**: two items whose entries are addresses with one root
  are items of one root;
* a root is **lifted along one edge** only.

`OrigOk` states them of a network.  Every operation keeps them (`OrigOk.applyOp`), so every network
of the chain has them (`origOk_gnet`), and so has the limit's entry map (`fmapL_term`,
`fmapL_inj`, `fmapL_lift1`).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature}

/-- An item of a view ends in a level step. -/
theorem kView_lastProj {Γ : Ctx} {k : Option VarSymb} {v : VarSymb} {T : VarType}
    (h : Γ.kView k v = some T) : v.lastProj = false := by
  have hb : ∀ {v : VarSymb}, Γ.boxIn v = some T → v.lastProj = false := by
    intro v hv
    match v, hv with
    | .step _ .box, _ => rfl
    | .step _ .keep, _ => rfl
    | .step _ .dia, hv => cases hv
    | .step _ .fst, hv => cases hv
    | .step _ .snd, hv => cases hv
    | .step _ .here, hv => cases hv
    | .root _, hv => cases hv
  cases k with
  | none => exact hb h
  | some x =>
      match v, h with
      | .step _ .dia, _ => rfl
      | .step _ .box, _ => rfl
      | .step _ .keep, _ => rfl
      | .step _ .fst, h => exact hb h
      | .step _ .snd, h => exact hb h
      | .step _ .here, h => exact hb h
      | .root _, h => exact hb h

/-- An item of a committed view is an item of one of the committed variables. -/
theorem kView_rt {l : List VarType} {k : Option VarSymb} {v : VarSymb} {T : VarType}
    (h : (ctxOf l).kView k v = some T) : ∃ r, v.rt = .free r ∧ r < l.length := by
  obtain ⟨u, s, rfl, -, U, hU⟩ := kView_item h
  obtain ⟨r, hr, hlt, -⟩ := ref_rt hU
  exact ⟨r, hr, hlt⟩

namespace GNetSt

/-- An item of the committed view of the edge into `k`. -/
def InView (N : GNetSt σ) (k : Node) (v : VarSymb) : Prop :=
  ∃ T, (ctxOf (N.fcl k)).kView (N.kind k) v = some T

/-- ⭐**Where an edge's entries come from** (docs §3 4, "(B) in Lean", (N1), (N3)). -/
structure OrigOk (N : GNetSt σ) : Prop where
  /-- A term entry is a root's kept item. -/
  term : ∀ c p, N.Live (c :: p) → ∀ v, N.InView (c :: p) v → ∀ e, N.fmap (c :: p) v = .inr e →
    ∃ r, v = .step (.root (.free r)) .keep
  /-- Two items whose entries have one root are items of one root. -/
  inj : ∀ c p, N.Live (c :: p) → ∀ v v', N.InView (c :: p) v → N.InView (c :: p) v' →
    ∀ y y', N.fmap (c :: p) v = .inl y → N.fmap (c :: p) v' = .inl y' → y.rt = y'.rt →
      v.rt = v'.rt
  /-- A root is lifted along one edge. -/
  lift1 : ∀ c c' p, N.Live (c :: p) → N.Live (c' :: p) → ∀ r,
    N.InView (c :: p) (.step (.root (.free r)) .keep) →
    N.InView (c' :: p) (.step (.root (.free r)) .keep) →
    ∀ e e', N.fmap (c :: p) (.step (.root (.free r)) .keep) = .inr e →
      N.fmap (c' :: p) (.step (.root (.free r)) .keep) = .inr e' → c = c'
  /-- An image root is not lifted. -/
  imgNL : ∀ c p, N.Live (c :: p) → ∀ w y, N.InView (c :: p) w → N.fmap (c :: p) w = .inl y →
    ∀ z, y.rt = .free z → ∀ c', N.Live (c' :: c :: p) →
      N.InView (c' :: c :: p) (.step (.root (.free z)) .keep) →
      ∀ e, N.fmap (c' :: c :: p) (.step (.root (.free z)) .keep) ≠ .inr e
  /-- A possible root's kept item goes to a root. -/
  rootKeep : ∀ c p, N.Live (c :: p) → ∀ r X,
    (ctxOf (N.fcl (c :: p))).kView (N.kind (c :: p)) (.step (.root (.free r)) .keep) =
      some (.VTypeDia X) →
    ∀ y, N.fmap (c :: p) (.step (.root (.free r)) .keep) = .inl y → ∃ z, y = .root (.free z)

variable {N : GNetSt σ}

/-- The committed images of a good network's edge are variables of the child. -/
theorem Good.img_lt (hN : N.Good) {c : ℕ} {p : Node} (hk : N.Live (c :: p)) {v y : VarSymb}
    (hv : N.InView (c :: p) v) (hy : N.fmap (c :: p) v = .inl y) :
    ∃ r, y.rt = .free r ∧ r < (N.st (c :: p)).l.length := by
  obtain ⟨T, hT⟩ := hv
  obtain ⟨-, -, hf, -⟩ := hN.fwd c p hk
  have h := hf v T (kView_lastProj hT) hT
  rw [hy] at h
  obtain ⟨r, hr, hlt, -⟩ := ref_rt (show (ctxOf (N.st (c :: p)).l).ref y = some T from h)
  exact ⟨r, hr, hlt⟩

/-- A good network's edges commit variables of the parent. -/
theorem Good.inView_lt (hN : N.Good) {c : ℕ} {p : Node} (hk : N.Live (c :: p)) {v : VarSymb}
    (hv : N.InView (c :: p) v) : ∃ r, v.rt = .free r ∧ r < (N.st p).l.length := by
  obtain ⟨T, hT⟩ := hv
  obtain ⟨r, hr, hlt⟩ := kView_rt hT
  obtain ⟨hsuf, -⟩ := hN.fwd c p hk
  exact ⟨r, hr, lt_of_lt_of_le hlt hsuf.length_le⟩

/-! ## Each operation keeps the facts -/

theorem OrigOk.setSt (hO : N.OrigOk) (s : Node) (t : NodeSt σ) : (N.setSt s t).OrigOk :=
  ⟨fun c p hk => hO.term c p ((live_setSt N s t _).mp hk),
    fun c p hk => hO.inj c p ((live_setSt N s t _).mp hk),
    fun c c' p hk hk' => hO.lift1 c c' p ((live_setSt N s t _).mp hk)
      ((live_setSt N s t _).mp hk'),
    fun c p hk w y hw hy z hz c' hk' => hO.imgNL c p ((live_setSt N s t _).mp hk) w y hw hy z hz c'
      ((live_setSt N s t _).mp hk'),
    fun c p hk => hO.rootKeep c p ((live_setSt N s t _).mp hk)⟩

/-- An item of a view extended by a variable is new, or an item of the old view. -/
theorem kView_new_or_old {A : VarType} {l : List VarType} {k : Option VarSymb} {v : VarSymb}
    {T : VarType} (h : (ctxOf (A :: l)).kView k v = some T) :
    v.rt = .free l.length ∨ (ctxOf l).kView k v = some T := by
  obtain ⟨u, s, rfl, -, -⟩ := kView_item h
  by_cases hrt : u.rt = .free l.length
  · exact Or.inl hrt
  · rw [kView_old hrt] at h
    exact Or.inr h

/-- ⭐**Recommitting an edge** to a map that keeps the old entries and sends the new variable's
    items to a fresh root — or, for a lift, its kept item to a term, the variable being new to the
    parent's other edges — keeps the facts. -/
theorem OrigOk.setFwd {M : GNetSt σ} (hO : M.OrigOk) {c : ℕ} {p : Node} {A : VarType}
    {cl : List VarType} (hcl : M.fcl (c :: p) = cl) {g : VarSymb → LEnt σ} {B z : ℕ}
    (hB : ∀ v y, M.InView (c :: p) v → M.fmap (c :: p) v = .inl y →
      ∃ r, y.rt = .free r ∧ r < B)
    (hz : B ≤ z)
    (hchild : ∀ c', M.Live (c' :: c :: p) → ∀ w, M.InView (c' :: c :: p) w →
      ∃ r, w.rt = .free r ∧ r < B)
    (hold : ∀ v, M.InView (c :: p) v → g v = M.fmap (c :: p) v)
    (hnew : ∀ v T, (ctxOf (A :: cl)).kView (M.kind (c :: p)) v = some T →
      v.rt = .free cl.length →
        (∃ y, g v = .inl y ∧ y.rt = .free z) ∨
          (v = .step (.root (.free cl.length)) .keep ∧ (∃ e, g v = .inr e) ∧
            (∀ c', c' ≠ c → M.Live (c' :: p) → ¬ M.InView (c' :: p) v) ∧
            ∀ c₀ p₀, p = c₀ :: p₀ → M.Live p → ∀ w y, M.InView p w → M.fmap p w = .inl y →
              y.rt ≠ .free cl.length))
    (hrk : ∀ X, (ctxOf (A :: cl)).kView (M.kind (c :: p))
        (.step (.root (.free cl.length)) .keep) = some (.VTypeDia X) →
      ∀ y, g (.step (.root (.free cl.length)) .keep) = .inl y → ∃ z, y = .root (.free z)) :
    (M.setFwd (c :: p) (A :: cl) g).OrigOk := by
  subst hcl
  set M' := M.setFwd (c :: p) (A :: M.fcl (c :: p)) g
  have hlive : ∀ k, M'.Live k ↔ M.Live k := live_setFwd _ _ _ _
  have hfcl : ∀ k, k ≠ c :: p → M'.fcl k = M.fcl k := fun k h => Function.update_of_ne h _ _
  have hfm : ∀ k, k ≠ c :: p → M'.fmap k = M.fmap k := fun k h => Function.update_of_ne h _ _
  have hfm' : M'.fmap (c :: p) = g := Function.update_self _ _ _
  have hview : ∀ k, k ≠ c :: p → ∀ v, M'.InView k v ↔ M.InView k v := by
    intro k h v
    change (∃ T, (ctxOf (M'.fcl k)).kView (M.kind k) v = some T) ↔ _
    rw [hfcl k h]
    rfl
  -- the edge's view: new items, or old ones
  have hcases : ∀ v, M'.InView (c :: p) v →
      (∃ T, (ctxOf (A :: M.fcl (c :: p))).kView (M.kind (c :: p)) v = some T ∧
        v.rt = .free (M.fcl (c :: p)).length) ∨ M.InView (c :: p) v := by
    intro v ⟨T, hT⟩
    change (ctxOf (Function.update M.fcl (c :: p) (A :: M.fcl (c :: p)) (c :: p))).kView
      (M.kind (c :: p)) v = some T at hT
    rw [Function.update_self] at hT
    rcases kView_new_or_old hT with h | h
    · exact Or.inl ⟨T, hT, h⟩
    · exact Or.inr ⟨T, h⟩
  have hold_rt : ∀ v, M.InView (c :: p) v → ¬ v.rt = .free (M.fcl (c :: p)).length := by
    intro v ⟨T, hT⟩ h
    obtain ⟨r, hr, hlt⟩ := kView_rt hT
    rw [h] at hr
    cases hr
    exact lt_irrefl _ hlt
  refine ⟨fun c₁ p₁ hk v hv e he => ?_, fun c₁ p₁ hk v v' hv hv' y y' hy hy' hr => ?_,
    fun c₁ c₂ p₁ hk₁ hk₂ r hv₁ hv₂ e₁ e₂ he₁ he₂ => ?_,
    fun c₁ p₁ hk₁ w y hw hy z' hz' c' hk' hv' e he' => ?_,
    fun c₁ p₁ hk₁ r X hv y hy => ?_⟩
  · -- term entries
    by_cases hkc : (c₁ :: p₁ : Node) = c :: p
    · rw [hkc] at hv he
      rw [hfm'] at he
      rcases hcases v hv with ⟨T, hT, hn⟩ | hvo
      · rcases hnew v T hT hn with ⟨y, hy, -⟩ | ⟨hv', -, -, -⟩
        · rw [hy] at he; cases he
        · exact ⟨_, hv'⟩
      · rw [hold v hvo] at he
        rw [← hkc] at hvo he
        exact hO.term c₁ p₁ ((hlive _).mp hk) v hvo e he
    · rw [hview _ hkc] at hv
      rw [hfm _ hkc] at he
      exact hO.term c₁ p₁ ((hlive _).mp hk) v hv e he
  · -- one source root
    by_cases hkc : (c₁ :: p₁ : Node) = c :: p
    · rw [hkc] at hv hv' hy hy'
      rw [hfm'] at hy hy'
      have hk' : M.Live (c :: p) := (hlive _).mp (hkc ▸ hk)
      -- the image of a new item is the fresh root
      have hnewimg : ∀ w T y, (ctxOf (A :: M.fcl (c :: p))).kView (M.kind (c :: p)) w = some T →
          w.rt = .free (M.fcl (c :: p)).length → g w = .inl y → y.rt = .free z := by
        intro w T y hT hn hy
        rcases hnew w T hT hn with ⟨y', hy', hrt⟩ | ⟨-, ⟨e, he⟩, -, -⟩
        · rw [hy'] at hy; cases hy; exact hrt
        · rw [he] at hy; cases hy
      rcases hcases v hv with ⟨T, hT, hn⟩ | hvo <;> rcases hcases v' hv' with ⟨T', hT', hn'⟩ | hvo'
      · rw [hn, hn']
      · exfalso
        have h₁ := hnewimg v T y hT hn hy
        rw [hold v' hvo'] at hy'
        obtain ⟨r, hr', hlt⟩ := hB v' y' hvo' hy'
        rw [h₁, hr'] at hr
        cases hr
        omega
      · exfalso
        have h₁ := hnewimg v' T' y' hT' hn' hy'
        rw [hold v hvo] at hy
        obtain ⟨r, hr', hlt⟩ := hB v y hvo hy
        rw [h₁, hr'] at hr
        cases hr
        omega
      · rw [hold v hvo] at hy
        rw [hold v' hvo'] at hy'
        exact hO.inj c p hk' v v' hvo hvo' y y' hy hy' hr
    · rw [hview _ hkc] at hv hv'
      rw [hfm _ hkc] at hy hy'
      exact hO.inj c₁ p₁ ((hlive _).mp hk) v v' hv hv' y y' hy hy' hr
  · -- one lift edge
    have hk₁' := (hlive _).mp hk₁
    have hk₂' := (hlive _).mp hk₂
    -- along the recommitted edge, a term entry is old, or the new kept item
    have hside : ∀ e, M'.InView (c :: p) (.step (.root (.free r)) .keep) →
        M'.fmap (c :: p) (.step (.root (.free r)) .keep) = .inr e →
          (M.InView (c :: p) (.step (.root (.free r)) .keep) ∧
            M.fmap (c :: p) (.step (.root (.free r)) .keep) = .inr e) ∨
          ∀ c', c' ≠ c → M.Live (c' :: p) →
            ¬ M.InView (c' :: p) (.step (.root (.free r)) .keep) := by
      intro e hv he
      rw [hfm'] at he
      rcases hcases _ hv with ⟨T, hT, hn⟩ | hvo
      · rcases hnew _ T hT hn with ⟨y, hy, -⟩ | ⟨-, -, hno, -⟩
        · rw [hy] at he; cases he
        · exact Or.inr hno
      · exact Or.inl ⟨hvo, (hold _ hvo).symm.trans he⟩
    by_cases h₁ : (c₁ :: p₁ : Node) = c :: p <;> by_cases h₂ : (c₂ :: p₁ : Node) = c :: p
    · exact (List.cons.inj h₁).1.trans (List.cons.inj h₂).1.symm
    · obtain ⟨rfl, rfl⟩ := List.cons.inj h₁
      rw [hview _ h₂] at hv₂
      rw [hfm _ h₂] at he₂
      rcases hside e₁ hv₁ he₁ with ⟨hvo, heo⟩ | hno
      · exact hO.lift1 c₁ c₂ p₁ hk₁' hk₂' r hvo hv₂ e₁ e₂ heo he₂
      · exact absurd hv₂ (hno c₂ (fun h => h₂ (h ▸ rfl)) hk₂')
    · obtain ⟨rfl, rfl⟩ := List.cons.inj h₂
      rw [hview _ h₁] at hv₁
      rw [hfm _ h₁] at he₁
      rcases hside e₂ hv₂ he₂ with ⟨hvo, heo⟩ | hno
      · exact hO.lift1 c₁ c₂ p₁ hk₁' hk₂' r hv₁ hvo e₁ e₂ he₁ heo
      · exact absurd hv₁ (hno c₁ (fun h => h₁ (h ▸ rfl)) hk₁')
    · rw [hview _ h₁] at hv₁
      rw [hview _ h₂] at hv₂
      rw [hfm _ h₁] at he₁
      rw [hfm _ h₂] at he₂
      exact hO.lift1 c₁ c₂ p₁ hk₁' hk₂' r hv₁ hv₂ e₁ e₂ he₁ he₂
  · -- an image root is not lifted
    have hk₁' := (hlive _).mp hk₁
    have hk'' := (hlive _).mp hk'
    by_cases hA : (c₁ :: p₁ : Node) = c :: p
    · obtain ⟨hc₁, hp₁⟩ := List.cons.inj hA
      subst c₁ p₁
      have hne : (c' :: c :: p : Node) ≠ c :: p := List.cons_ne_self _ _
      rw [hview _ hne] at hv'
      rw [hfm _ hne] at he'
      rw [hfm'] at hy
      rcases hcases w hw with ⟨T, hT, hn⟩ | hwo
      · rcases hnew w T hT hn with ⟨y', hy', hrt⟩ | ⟨-, ⟨e₀, he₀⟩, -, -⟩
        · rw [hy'] at hy
          cases hy
          rw [hrt] at hz'
          cases hz'
          obtain ⟨r, hr, hlt⟩ := hchild c' hk'' _ hv'
          cases hr
          omega
        · rw [he₀] at hy
          cases hy
      · rw [hold w hwo] at hy
        exact hO.imgNL c p hk₁' w y hwo hy z' hz' c' hk'' hv' e he'
    · by_cases hB' : (c' :: c₁ :: p₁ : Node) = c :: p
      · obtain ⟨hcc, hpp⟩ := List.cons.inj hB'
        subst c'
        subst hpp
        rw [hview _ hA] at hw
        rw [hfm _ hA] at hy
        rw [hfm'] at he'
        rcases hcases _ hv' with ⟨T, hT, hn⟩ | hvo
        · rcases hnew _ T hT hn with ⟨y', hy', -⟩ | ⟨hveq, -, -, hni⟩
          · rw [hy'] at he'
            cases he'
          · have hzz : z' = (M.fcl (c :: c₁ :: p₁)).length := by
              have := (VarSymb.step.inj hveq).1
              injection this with h
              injection h
            exact hni c₁ p₁ rfl hk₁' w y hw hy (hzz ▸ hz')
        · rw [hold _ hvo] at he'
          exact hO.imgNL c₁ p₁ hk₁' w y hw hy z' hz' c hk'' hvo e he'
      · rw [hview _ hA] at hw
        rw [hfm _ hA] at hy
        rw [hview _ hB'] at hv'
        rw [hfm _ hB'] at he'
        exact hO.imgNL c₁ p₁ hk₁' w y hw hy z' hz' c' hk'' hv' e he'
  · -- a possible root's kept item goes to a root
    have hk₁' := (hlive _).mp hk₁
    by_cases hA : (c₁ :: p₁ : Node) = c :: p
    · obtain ⟨hc₁, hp₁⟩ := List.cons.inj hA
      subst c₁ p₁
      rw [hfm'] at hy
      change (ctxOf (Function.update M.fcl (c :: p) (A :: M.fcl (c :: p)) (c :: p))).kView
        (M.kind (c :: p)) _ = _ at hv
      rw [Function.update_self] at hv
      rcases kView_new_or_old hv with hn | hvo
      · cases hn
        exact hrk X hv y hy
      · rw [hold _ ⟨_, hvo⟩] at hy
        exact hO.rootKeep c p hk₁' r X hvo y hy
    · rw [hfm _ hA] at hy
      have hv' : (ctxOf (M.fcl (c₁ :: p₁))).kView (M.kind (c₁ :: p₁))
          (.step (.root (.free r)) .keep) = some (.VTypeDia X) := by
        rw [← hfcl _ hA]
        exact hv
      exact hO.rootKeep c₁ p₁ hk₁' r X hv' y hy

/-- A possible root of a view extended by a variable: its type. -/
theorem kView_keep_new {A X : VarType} {cl : List VarType} {k : Option VarSymb}
    (h : (ctxOf (A :: cl)).kView k (.step (.root (.free cl.length)) .keep) =
      some (.VTypeDia X)) : A = .VTypeDia X := by
  have hbox : (ctxOf (A :: cl)).boxIn (.step (.root (.free cl.length)) .keep) =
      some (.VTypeDia X) := by
    cases k with
    | none => exact h
    | some x => exact h
  obtain ⟨-, hu, -⟩ := Ctx.boxIn_keep hbox
  rw [ctxOf_ref_new] at hu
  exact Option.some.inj hu

/-- Realising forward keeps the facts. -/
theorem OrigOk.realF (hF : ModalSys.Four = true) (hO : N.OrigOk) (hN : N.Good) {k : Node}
    (hk : N.Live k) : (N.realF hF k).OrigOk := by
  match k with
  | [] => exact hO
  | c :: p =>
      simp only [GNetSt.realF]
      split_ifs with hlt
      · refine (hO.setSt (c :: p) _).setFwd rfl (B := (N.st (c :: p)).l.length)
          (fun v y hv hy => hN.img_lt hk hv hy) le_rfl
          (fun c' hk' w hw => hN.inView_lt ((live_setSt _ _ _ _).mp hk') hw)
          (fun v hv => ?_) (fun v T hT hn => ?_) (fun X hX y hy => ?_)
        · obtain ⟨u, s, rfl, -, -⟩ := kView_item hv.choose_spec
          have hn : ¬ u.rt = .free (N.fcl (c :: p)).length := by
            intro h
            obtain ⟨r, hr, hlt⟩ := kView_rt hv.choose_spec
            change u.rt = _ at hr
            rw [h] at hr
            cases hr
            exact lt_irrefl _ hlt
          exact gextF_old hn s
        · left
          obtain ⟨u, s, rfl, -, -⟩ := kView_item hT
          refine ⟨_, gextF_new (u := u) hn s, ?_⟩
          exact VarSymb.ext_rt _ _
        · have hy' : gextF (N.fmap (c :: p)) (nextTy (N.st p).l (N.fcl (c :: p)))
              (N.fcl (c :: p)).length (N.st (c :: p)).l.length
              (.step (.root (.free (N.fcl (c :: p)).length)) .keep) = .inl y := hy
          have hX' : (ctxOf (nextTy (N.st p).l (N.fcl (c :: p)) :: N.fcl (c :: p))).kView
              (N.kind (c :: p)) (.step (.root (.free (N.fcl (c :: p)).length)) .keep) =
                some (.VTypeDia X) := hX
          rw [gextF_new (u := .root (.free (N.fcl (c :: p)).length)) rfl] at hy'
          cases hy'
          rw [kView_keep_new hX']
          exact ⟨_, rfl⟩
      · exact hO

theorem OrigOk.iterate_realF (hF : ModalSys.Four = true) (k : Node) :
    ∀ (j : ℕ) {N : GNetSt σ}, N.OrigOk → N.Good → N.Live k →
      ((fun N' => N'.realF hF k)^[j] N).OrigOk
  | 0, _, hO, _, _ => hO
  | j + 1, N, hO, hN, hk => by
      rw [Function.iterate_succ_apply]
      exact OrigOk.iterate_realF hF k j (hO.realF hF hN hk) (hN.realF hF hk)
        ((live_of_nch (nch_realF hF N k) k).mpr hk)

theorem OrigOk.catchUp (hF : ModalSys.Four = true) (hO : N.OrigOk) (hN : N.Good) {k : Node}
    (hk : N.Live k) : (N.catchUp hF k).OrigOk := by
  match k with
  | [] => exact hO
  | c :: p => exact OrigOk.iterate_realF hF (c :: p) _ hO hN hk

/-- Lifting keeps the facts. -/
theorem OrigOk.lift (hF : ModalSys.Four = true) (hO : N.OrigOk) (hN : N.Good) {k : Node}
    (hk : N.Live k) (o : LTerm σ) : (N.lift hF k o).OrigOk := by
  match k, o with
  | [], _ => exact hO
  | c :: p, ⟨l, T, a, t⟩ =>
      by_cases hcl : N.fcl (c :: p) = (N.st p).l
      · by_cases h : l <:+ (N.st (c :: p)).l
        · by_cases hl : T.liftable = true
          · by_cases hv : LiftAdm hF ⟨l, T, a, t⟩
            swap
            · simp only [GNetSt.lift, if_pos hcl, dif_pos h, dif_pos hl, if_neg hv]
              exact hO
            rw [lift_spec hF hcl h hl hv]
            have hpk : (p : Node) ≠ c :: p := fun e => NetSt.ne_parent c p e.symm
            refine ((hO.setSt p _).setSt (c :: p) _).setFwd hcl
              (B := (N.st (c :: p)).l.length) (fun v y hv hy => hN.img_lt hk hv hy) le_rfl
              (fun c' hk' w hw => hN.inView_lt
                ((live_setSt _ _ _ _).mp ((live_setSt _ _ _ _).mp hk')) hw)
              (fun v hv => ?_) (fun v T' hT hn => ?_) (fun X hX y hy => ?_)
            · obtain ⟨u, s, rfl, -, -⟩ := kView_item hv.choose_spec
              have hn : ¬ u.rt = .free (N.st p).l.length := by
                intro h'
                obtain ⟨r, hr, hlt⟩ := kView_rt hv.choose_spec
                change u.rt = _ at hr
                rw [h', ← hcl] at hr
                cases hr
                exact lt_irrefl _ hlt
              exact gliftG_old hn
            · obtain ⟨u, s, rfl, -, -⟩ := kView_item hT
              by_cases hnk : u = .root (.free (N.st p).l.length) ∧ s = .keep
              · obtain ⟨rfl, rfl⟩ := hnk
                right
                refine ⟨rfl, ⟨_, gliftG_keep _ _ _ _ _⟩, fun c' hc' hk' hv' => ?_,
                  fun c₀ p₀ hp hk₀ w y hw hy => ?_⟩
                · have hk'' : N.Live (c' :: p) :=
                    (live_setSt _ _ _ _).mp ((live_setSt _ _ _ _).mp hk')
                  obtain ⟨r, hr, hlt⟩ := hN.inView_lt hk'' hv'
                  cases hr
                  exact lt_irrefl _ hlt
                · subst hp
                  have hk₀' : N.Live (c₀ :: p₀) :=
                    (live_setSt _ _ _ _).mp ((live_setSt _ _ _ _).mp hk₀)
                  obtain ⟨r, hr, hlt⟩ := hN.img_lt hk₀' hw hy
                  rw [hr]
                  intro e
                  cases e
                  exact lt_irrefl _ hlt
              · left
                refine ⟨_, gliftG_res (u := u) hn hnk, ?_⟩
                exact VarSymb.ext_rt _ _
            · rw [gliftG_keep] at hy
              cases hy
          · simp only [GNetSt.lift, if_pos hcl, dif_pos h, dif_neg hl]
            exact hO
        · simp only [GNetSt.lift, if_pos hcl, dif_neg h]
          exact hO
      · simp only [GNetSt.lift, if_neg hcl]
        exact hO

/-- The item map of a new child: an item's image has the item's root, but `x.dia`'s, which is the
    content variable after the world's. -/
theorem gchildMap_rt (l : List VarType) (kd : Option VarSymb) {v : VarSymb} {T : VarType}
    (hv : (ctxOf l).kView kd v = some T) :
    (gchildMap l kd v).rt = v.rt ∨
      ((∃ x, kd = some x ∧ v = .step x .dia) ∧ (gchildMap l kd v).rt = .free l.length) := by
  obtain ⟨u, s, rfl, -, U, hU⟩ := kView_item hv
  obtain ⟨r, hr, -, -⟩ := ref_rt hU
  have himg : (gImg l id (.step u s)).rt = (VarSymb.step u s).rt := by
    rw [gImg_item l id hr]
    exact (VarSymb.ext_rt _ _).trans hr.symm
  cases kd with
  | none => exact Or.inl himg
  | some x =>
      have e : gchildMap l (some x) (.step u s) = if VarSymb.step u s = .step x .dia then
          .root (.free l.length) else gImg l id (.step u s) := rfl
      rw [e]
      split_ifs with hx
      · exact Or.inr ⟨⟨x, rfl, hx⟩, rfl⟩
      · exact Or.inl himg

/-- A new child keeps the facts. -/
theorem OrigOk.newChild (hO : N.OrigOk) {s : Node} (hs : N.Live s) (kd : Option VarSymb)
    (t : NodeSt σ) : (N.newChild s kd t (ofRen (gchildMap (N.st s).l kd))).OrigOk := by
  set N' := N.newChild s kd t (ofRen (gchildMap (N.st s).l kd))
  have hold : ∀ k, N.Live k → k ≠ N.nch s :: s := fun k hk h => not_live_new s (h ▸ hk)
  have hfcl : ∀ k, k ≠ N.nch s :: s → N'.fcl k = N.fcl k := fun k h => Function.update_of_ne h _ _
  have hknd : ∀ k, k ≠ N.nch s :: s → N'.kind k = N.kind k :=
    fun k h => Function.update_of_ne h _ _
  have hfm : ∀ k, k ≠ N.nch s :: s → N'.fmap k = N.fmap k := fun k h => Function.update_of_ne h _ _
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
  refine ⟨fun c p hk v hv e he => ?_, fun c p hk v v' hv hv' y y' hy hy' hr => ?_,
    fun c₁ c₂ p hk₁ hk₂ r hv₁ hv₂ e₁ e₂ he₁ he₂ => ?_,
    fun c p hk w y hw hy z hz c' hk' hv' e he' => ?_,
    fun c p hk r X hv y hy => ?_⟩
  · by_cases hkc : (c :: p : Node) = N.nch s :: s
    · rw [hkc, hnew_fm] at he
      cases he
    · rw [hview _ hkc] at hv
      rw [hfm _ hkc] at he
      exact hO.term c p (((live_newChild hs kd t _ _).mp hk).resolve_right hkc) v hv e he
  · by_cases hkc : (c :: p : Node) = N.nch s :: s
    · rw [hkc] at hv hv' hy hy'
      rw [hnew_fm] at hy hy'
      cases hy
      cases hy'
      obtain ⟨T, hT⟩ := hnew_view v hv
      obtain ⟨T', hT'⟩ := hnew_view v' hv'
      have hlt : ∀ w {W}, (ctxOf (N.st s).l).kView kd w = some W →
          ¬ (∃ x, kd = some x ∧ w = .step x .dia) → ∃ r, w.rt = .free r ∧ r < (N.st s).l.length :=
        fun w W hw _ => kView_rt hw
      rcases gchildMap_rt _ kd hT with h₁ | ⟨⟨x, hx, rfl⟩, h₁⟩ <;>
        rcases gchildMap_rt _ kd hT' with h₂ | ⟨⟨x', hx', rfl⟩, h₂⟩
      · rw [← h₁, ← h₂]
        exact hr
      · exfalso
        obtain ⟨r, hr', hlt'⟩ := kView_rt hT
        rw [h₁, h₂, hr'] at hr
        cases hr
        exact lt_irrefl _ hlt'
      · exfalso
        obtain ⟨r, hr', hlt'⟩ := kView_rt hT'
        rw [h₁, h₂, hr'] at hr
        cases hr
        exact lt_irrefl _ hlt'
      · rw [hx] at hx'
        cases hx'
        rfl
    · rw [hview _ hkc] at hv hv'
      rw [hfm _ hkc] at hy hy'
      exact hO.inj c p (((live_newChild hs kd t _ _).mp hk).resolve_right hkc) v v' hv hv' y y'
        hy hy' hr
  · have hlv : ∀ c, N'.Live (c :: p) → (c :: p : Node) ≠ N.nch s :: s →
        N.Live (c :: p) := fun c hk h => ((live_newChild hs kd t _ _).mp hk).resolve_right h
    by_cases h₁ : (c₁ :: p : Node) = N.nch s :: s
    · rw [h₁, hnew_fm] at he₁
      cases he₁
    by_cases h₂ : (c₂ :: p : Node) = N.nch s :: s
    · rw [h₂, hnew_fm] at he₂
      cases he₂
    rw [hview _ h₁] at hv₁
    rw [hview _ h₂] at hv₂
    rw [hfm _ h₁] at he₁
    rw [hfm _ h₂] at he₂
    exact hO.lift1 c₁ c₂ p (hlv _ hk₁ h₁) (hlv _ hk₂ h₂) r hv₁ hv₂ e₁ e₂ he₁ he₂
  · have hlv : ∀ k, N'.Live k → k ≠ N.nch s :: s → N.Live k :=
      fun k hk h => ((live_newChild hs kd t _ _).mp hk).resolve_right h
    by_cases h₁ : (c :: p : Node) = N.nch s :: s
    · exfalso
      rcases (live_newChild hs kd t _ _).mp hk' with h' | h'
      · rw [h₁] at h'
        exact not_live_new s h'.1
      · rw [h₁] at h'
        exact List.cons_ne_self _ _ h'
    by_cases h₂ : (c' :: c :: p : Node) = N.nch s :: s
    · rw [h₂, hnew_fm] at he'
      cases he'
    rw [hview _ h₁] at hw
    rw [hfm _ h₁] at hy
    rw [hview _ h₂] at hv'
    rw [hfm _ h₂] at he'
    exact hO.imgNL c p (hlv _ hk h₁) w y hw hy z hz c' (hlv _ hk' h₂) hv' e he'
  · by_cases hkc : (c :: p : Node) = N.nch s :: s
    · rw [hkc, hnew_fm] at hy
      cases hy
      rw [hkc] at hv
      change (ctxOf (Function.update N.fcl _ (N.st s).l _)).kView
        (Function.update N.kind _ kd _) _ = _ at hv
      rw [Function.update_self, Function.update_self] at hv
      have hbox : (ctxOf (N.st s).l).boxIn (.step (.root (.free r)) .keep) =
          some (.VTypeDia X) := by
        cases kd with
        | none => exact hv
        | some x => exact hv
      obtain ⟨-, hu, -⟩ := Ctx.boxIn_keep hbox
      obtain ⟨r', hr', hlt, -⟩ := ref_rt hu
      cases hr'
      have hty : rootTy (N.st s).l r = .VTypeDia X :=
        Option.some.inj ((ref_root_lt hlt).symm.trans hu)
      have himg : gImg (N.st s).l id (.step (.root (.free r)) .keep) = .root (.free r) := by
        rw [gImg_item _ id (rfl : (VarSymb.root (.free r)).rt = _), hty]
        rfl
      cases kd with
      | none => exact ⟨_, himg⟩
      | some x =>
          refine ⟨r, ?_⟩
          change gImgX (N.st s).l id x (N.st s).l.length _ = _
          unfold gImgX
          rw [if_neg (fun e => by cases e), himg]
    · rw [hfm _ hkc] at hy
      have hv' : (ctxOf (N.fcl (c :: p))).kView (N.kind (c :: p))
          (.step (.root (.free r)) .keep) = some (.VTypeDia X) := by
        rw [← hfcl _ hkc, ← hknd _ hkc]
        exact hv
      exact hO.rootKeep c p (((live_newChild hs kd t _ _).mp hk).resolve_right hkc) r X hv' y hy

theorem OrigOk.henk (hO : N.OrigOk) (s : Node) (o : Σ l : List VarType, WFF σ (ctxOf l) 0) :
    (N.henk s o).OrigOk := by
  obtain ⟨l, φ⟩ := o
  simp only [GNetSt.henk]
  split_ifs
  · split
    · split_ifs
      · exact hO.setSt _ _
      · exact hO
    · split_ifs
      · exact hO.setSt _ _
      · exact hO
    · exact hO
  · exact hO

theorem OrigOk.mkChild (hF : ModalSys.Four = true) (hO : N.OrigOk) {s : Node} (hs : N.Live s)
    (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : (N.mkChild hF s o).OrigOk := by
  obtain ⟨l, φ⟩ := o
  simp only [GNetSt.mkChild]
  split_ifs
  · split
    · split_ifs
      · exact hO
      · exact hO.newChild hs _ _
    · split_ifs
      · split
        · exact hO.newChild hs _ _
        · exact hO
      · exact hO
    · exact hO
  · exact hO

/-- ⭐Every operation keeps the facts. -/
theorem OrigOk.applyOp (hF : ModalSys.Four = true) (hO : N.OrigOk) (hN : N.Good) (o : GOp σ) :
    (N.applyOp hF o).OrigOk := by
  rcases o with ⟨s, o⟩ | ⟨s, o⟩ | k | ⟨k, n⟩
  · simp only [GNetSt.applyOp]
    split_ifs
    · exact hO.henk s o
    · exact hO
  · simp only [GNetSt.applyOp]
    split_ifs with h
    · exact hO.mkChild hF h o
    · exact hO
  · simp only [GNetSt.applyOp]
    split_ifs with h
    · exact hO.realF hF hN h
    · exact hO
  · simp only [GNetSt.applyOp]
    split_ifs with h
    · obtain ⟨h₁, h₂, -⟩ := hN.catchUp hF h
      exact (hO.catchUp hF hN h).lift hF h₁ h₂ n
    · exact hO

theorem origOk_init {l₀ : List VarType} (M₀ : Set (WFF σ (ctxOf l₀) 0)) : (init M₀).OrigOk :=
  ⟨fun _ _ hk => absurd (init_live hk) (by simp),
    fun _ _ hk => absurd (init_live hk) (by simp),
    fun _ _ _ hk => absurd (init_live hk) (by simp),
    fun _ _ hk => absurd (init_live hk) (by simp),
    fun _ _ hk => absurd (init_live hk) (by simp)⟩

end GNetSt

/-- ⭐Every network of the chain has the facts. -/
theorem origOk_gnet [Countable σ.FuncSyms] [Countable σ.RelSyms] (hF : ModalSys.Four = true)
    {l₀ : List VarType}
    {M₀ : Set (WFF σ (ctxOf l₀) 0)} (h : Theory.IsMCS M₀) : ∀ n, (gnet hF M₀ n).OrigOk
  | 0 => GNetSt.origOk_init M₀
  | n + 1 => (origOk_gnet hF h n).applyOp hF (good_gnet hF h n) (gsched n)

/-! ## In the limit -/

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

variable (hF M₀) in
/-- An item committed along the edge into `k` at some round. -/
def GCommitted (k : Node) (v : VarSymb) : Prop :=
  ∃ m, (gnet hF M₀ m).Live k ∧ (gnet hF M₀ m).InView k v

/-- A committed item stays committed. -/
theorem GCommitted.mono (hM₀ : Theory.IsMCS M₀) {k : Node} {v : VarSymb} {m m' : ℕ}
    (hmm : m ≤ m') (hk : (gnet hF M₀ m).Live k) (hv : (gnet hF M₀ m).InView k v) :
    (gnet hF M₀ m').Live k ∧ (gnet hF M₀ m').InView k v := by
  have he := ext_gnet hF hM₀ hmm
  obtain ⟨T, hT⟩ := hv
  refine ⟨he.live k hk, T, ?_⟩
  rw [he.kind k hk]
  exact ((ctxOf_le_of_suffix (he.fcl k hk)).kView _) v T hT

/-- The limit's entry of a committed item is the entry at any round it is committed at. -/
theorem fmapL_at (hM₀ : Theory.IsMCS M₀) {k : Node} {v : VarSymb} {m : ℕ}
    (hk : (gnet hF M₀ m).Live k) (hv : (gnet hF M₀ m).InView k v) :
    fmapL hF M₀ k v = (gnet hF M₀ m).fmap k v :=
  fmapL_eq hM₀ hk hv.choose_spec

/-- Only a committed item has a term entry. -/
theorem fmapL_committed {k : Node} {v : VarSymb} {e : LTerm σ}
    (h : fmapL hF M₀ k v = .inr e) : GCommitted hF M₀ k v := by
  by_contra hc
  have hc' : ¬ ∃ m, (gnet hF M₀ m).Live k ∧
      ∃ T, (ctxOf ((gnet hF M₀ m).fcl k)).kView ((gnet hF M₀ m).kind k) v = some T := hc
  rw [fmapL, dif_neg hc'] at h
  cases h

/-- ⭐(N1) **A term entry is a root's kept item.** -/
theorem fmapL_term (hM₀ : Theory.IsMCS M₀) {c : ℕ} {p : Node} {v : VarSymb} {e : LTerm σ}
    (h : fmapL hF M₀ (c :: p) v = .inr e) : ∃ r, v = .step (.root (.free r)) .keep := by
  obtain ⟨m, hk, hv⟩ := fmapL_committed h
  rw [fmapL_at hM₀ hk hv] at h
  exact (origOk_gnet hF hM₀ m).term c p hk v hv e h

/-- ⭐(N3) **An image root has one source root.** -/
theorem fmapL_inj (hM₀ : Theory.IsMCS M₀) {c : ℕ} {p : Node} {v v' y y' : VarSymb}
    (hv : GCommitted hF M₀ (c :: p) v) (hv' : GCommitted hF M₀ (c :: p) v')
    (hy : fmapL hF M₀ (c :: p) v = .inl y) (hy' : fmapL hF M₀ (c :: p) v' = .inl y')
    (hr : y.rt = y'.rt) : v.rt = v'.rt := by
  obtain ⟨m, hk, hvm⟩ := hv
  obtain ⟨m', hk', hvm'⟩ := hv'
  obtain ⟨hk₁, hv₁⟩ := GCommitted.mono hM₀ (le_max_left m m') hk hvm
  obtain ⟨-, hv₂⟩ := GCommitted.mono hM₀ (le_max_right m m') hk' hvm'
  rw [fmapL_at hM₀ hk₁ hv₁] at hy
  rw [fmapL_at hM₀ hk₁ hv₂] at hy'
  exact (origOk_gnet hF hM₀ _).inj c p hk₁ v v' hv₁ hv₂ y y' hy hy' hr

/-- ⭐**A root is lifted along one edge.** -/
theorem fmapL_lift1 (hM₀ : Theory.IsMCS M₀) {c c' : ℕ} {p : Node} {r : ℕ} {e e' : LTerm σ}
    (h : fmapL hF M₀ (c :: p) (.step (.root (.free r)) .keep) = .inr e)
    (h' : fmapL hF M₀ (c' :: p) (.step (.root (.free r)) .keep) = .inr e') : c = c' := by
  obtain ⟨m, hk, hv⟩ := fmapL_committed h
  obtain ⟨m', hk', hv'⟩ := fmapL_committed h'
  obtain ⟨hk₁, hv₁⟩ := GCommitted.mono hM₀ (le_max_left m m') hk hv
  obtain ⟨hk₂, hv₂⟩ := GCommitted.mono hM₀ (le_max_right m m') hk' hv'
  rw [fmapL_at hM₀ hk₁ hv₁] at h
  rw [fmapL_at hM₀ hk₂ hv₂] at h'
  exact (origOk_gnet hF hM₀ _).lift1 c c' p hk₁ hk₂ r hv₁ hv₂ e e' h h'

/-- ⭐**An image root is not lifted.** -/
theorem fmapL_imgNL (hM₀ : Theory.IsMCS M₀) {c : ℕ} {p : Node} {w y : VarSymb}
    (hw : GCommitted hF M₀ (c :: p) w) (hy : fmapL hF M₀ (c :: p) w = .inl y) {z : ℕ}
    (hz : y.rt = .free z) (c' : ℕ) (e : LTerm σ) :
    fmapL hF M₀ (c' :: c :: p) (.step (.root (.free z)) .keep) ≠ .inr e := by
  intro he
  obtain ⟨m, hk, hvm⟩ := hw
  obtain ⟨m', hk', hvm'⟩ := fmapL_committed he
  obtain ⟨hk₁, hv₁⟩ := GCommitted.mono hM₀ (le_max_left m m') hk hvm
  obtain ⟨hk₂, hv₂⟩ := GCommitted.mono hM₀ (le_max_right m m') hk' hvm'
  rw [fmapL_at hM₀ hk₁ hv₁] at hy
  rw [fmapL_at hM₀ hk₂ hv₂] at he
  exact (origOk_gnet hF hM₀ _).imgNL c p hk₁ w y hv₁ hy z hz c' hk₂ hv₂ e he

end GArrow

end V12M
