import QML.QML_v12m_GSelf

/-!
# QML v12m — the growing tree: the canonical shapes' equation

`cEnv` is one construction step with its templates read in the canonical shapes of *lower*
addresses only (`docs/v12-modal-extensions.md` §3 4, "(B) in Lean").  A construction step at a
declared address reads its family only below the address's level (⭐`cStep_local`): a `□`
address's value along an edge is its image's (same level, `keep_img`) or its lifted term's, whose
variables are lower (`lift_root`); a `◇`-root's template reads its lifted term, and an image's
shape its source's (same level).  Hence ⭐`cEnv_eq`: at a declared address the canonical shape is
one construction step read in the canonical shapes.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-- An address declared at some stage of a world, at a type. -/
def DeclAt (s : GW hF M₀) (v : VarSymb) (T : VarType) : Prop :=
  ∃ i, (ctxOf (glat s i)).ref v = some T

/-- Two families agree at the declared addresses below a level. -/
def AgreeBelow (K : ℕ) (ρ ρ' : ShFam hF M₀) : Prop :=
  ∀ t w W, DeclAt t w W → levA t w < K → ρ t w W = ρ' t w W

theorem AgreeBelow.mono {K K' : ℕ} {ρ ρ' : ShFam hF M₀} (h : AgreeBelow K ρ ρ')
    (hK : K' ≤ K) : AgreeBelow K' ρ ρ' :=
  fun t w W hd hl => h t w W hd (lt_of_lt_of_le hl hK)

theorem levA_step (s : GW hF M₀) (v : VarSymb) (st : Step) :
    levA s (.step v st) = levA s v := rfl

theorem DeclAt.rt {s : GW hF M₀} {v : VarSymb} {T : VarType} (h : DeclAt s v T) :
    ∃ r, v.rt = .free r ∧ levA s v = lev s r := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨r, hr, -, -⟩ := ref_rt hi
  refine ⟨r, hr, ?_⟩
  unfold levA
  rw [hr]

/-- The round of a world's stage. -/
theorem glat_round (t : GW hF M₀) {m : ℕ}
    (hm : (gnet hF M₀ m).Live t.1) :
    glat t (m - gbirth hF M₀ t.2) = ((gnet hF M₀ m).st t.1).l := by
  have := gbirth_le hF t.2 hm
  change ((gnet hF M₀ (gbirth hF M₀ t.2 + (m - gbirth hF M₀ t.2))).st t.1).l = _
  rw [show gbirth hF M₀ t.2 + (m - gbirth hF M₀ t.2) = m by omega]

/-- An item of a stage's `□` view is committed along every edge out. -/
theorem gcommitted_box (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: s.1)
    {i : ℕ} {w : VarSymb} {T : VarType} (hw : (ctxOf (glat s i)).kView none w = some T) :
    GCommitted hF M₀ t.1 w := by
  obtain ⟨hsuf, -, -⟩ := gfwd_at hM₀ hc i
  refine ⟨grnd s t i, live_gbirth hF hM₀ t.2 (Nat.le_add_right _ _), T, ?_⟩
  rw [kind_at hM₀ t (Nat.le_add_right _ _)]
  exact ((ctxOf_le_of_suffix hsuf).kView _) w T (Ctx.le_boxIn_kView _ _ w T hw)

/-- ⭐**An address's kept item sent to an address**: the image is declared at the child, at the
    same type and level. -/
theorem keep_img (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: s.1)
    {v : VarSymb} {U : VarType} (hv : DeclAt s v U) (hk : U.keepable = true) {y : VarSymb}
    (hy : fmapL hF M₀ t.1 (.step v .keep) = .inl y) : DeclAt t y U ∧ levA t y = levA s v := by
  obtain ⟨i, hi⟩ := hv
  have hitem : (ctxOf (glat s i)).kView none (.step v .keep) = some U :=
    Ctx.boxIn_keep_of' hF hi hk
  have h := gentOk_box hM₀ ⟨c, hc⟩ i (.step v .keep) U rfl hitem
  rw [hy] at h
  have hy' : (ctxOf (glat t (glstg s t i))).ref y = some U := h
  refine ⟨⟨_, hy'⟩, ?_⟩
  obtain ⟨r, hr, -, -⟩ := ref_rt hy'
  obtain ⟨u, hu, -, -⟩ := ref_rt hi
  unfold levA
  rw [hr, hu]
  exact lev_img hM₀ hc (gcommitted_box hM₀ hc hitem) hy hr hu

/-- ⭐**A lifted term's variables are declared at the child, below the lifted root.** -/
theorem lift_root (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: s.1)
    {z : ℕ} {e : LTerm σ} (he : fmapL hF M₀ t.1 (.step (.root (.free z)) .keep) = .inr e)
    {j : ℕ} {W : VarType} (hj : ctxOf e.1 (.root (.free j)) = some W) :
    DeclAt t (.root (.free j)) W ∧ levA t (.root (.free j)) < lev s z := by
  classical
  have hjl : j < e.1.length := by
    rw [ctxOf_root] at hj
    by_contra hn
    rw [List.getElem?_eq_none (by simpa using hn)] at hj
    cases hj
  refine ⟨?_, lev_lift hM₀ hc he hjl⟩
  obtain ⟨m, hk, ⟨T, hT⟩⟩ := fmapL_committed he
  have hfa := fmapL_at hM₀ hk ⟨T, hT⟩
  obtain ⟨-, -, hf, -⟩ := (good_gnet hF hM₀ m).fwd c s.1 (hc ▸ hk)
  rw [← hc] at hf
  have h := hf _ T (kView_lastProj hT) hT
  rw [← hfa, he] at h
  obtain ⟨l, U, a, τ⟩ := e
  change (if h : (ctxOf l).Le (ctxOf ((gnet hF M₀ m).st t.1).l) then
    SubE.tm (Term.mono h τ) else SubE.hide).OkRef T at h
  split_ifs at h with hle
  · refine ⟨m - gbirth hF M₀ t.2, ?_⟩
    rw [glat_round t hk]
    exact hle.ref (by rw [Ctx.ref_nonproj _ rfl]; exact hj)
  · exact h.elim

/-- A declared address keeps its declaration at later stages. -/
theorem DeclAt.at_le (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {v : VarSymb} {T : VarType} {i i' : ℕ}
    (h : (ctxOf (glat s i)).ref v = some T) (hii : i ≤ i') : (ctxOf (glat s i')).ref v = some T :=
  (ctxOf_le_of_suffix (gnet_lang_suffix hF hM₀ (by omega)
    (live_gbirth hF hM₀ s.2 (Nat.le_add_right _ i)))).ref h

/-- An address is declared at one type. -/
theorem DeclAt.unique (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {v : VarSymb} {T T' : VarType}
    (h : DeclAt s v T) (h' : DeclAt s v T') : T = T' := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨i', hi'⟩ := h'
  have e₁ := DeclAt.at_le hM₀ hi (le_max_left i i')
  have e₂ := DeclAt.at_le hM₀ hi' (le_max_right i i')
  rw [e₁] at e₂
  exact Option.some.inj e₂

omit [ModalSys] in
theorem ctxOf_step : ∀ (l : List VarType) (v : VarSymb) (st : Step), ctxOf l (.step v st) = none
  | [], _, _ => rfl
  | A :: l, v, st => by
      rw [ctxOf_cons]
      change (if VarSymb.step v st = .root (.free l.length) then some A else ctxOf l _) = none
      rw [if_neg (by simp)]
      exact ctxOf_step l v st

omit [ModalSys] in
theorem ctxOf_bnd : ∀ (l : List VarType) (n : ℕ), ctxOf l (.root (.bnd n)) = none
  | [], _ => rfl
  | A :: l, n => by
      rw [ctxOf_cons]
      change (if VarSymb.root (.bnd n) = .root (.free l.length) then some A else ctxOf l _) = none
      rw [if_neg (by simp)]
      exact ctxOf_bnd l n

/-- Environments of a world's own variables agree when the families agree at its roots. -/
theorem famEnv_agree {ρ ρ' : ShFam hF M₀} {l : List VarType} {t : GW hF M₀}
    (h : ∀ j W, ctxOf l (.root (.free j)) = some W →
      ρ t (.root (.free j)) W = ρ' t (.root (.free j)) W) :
    famEnv ρ (ctxOf l) t = famEnv ρ' (ctxOf l) t := by
  funext w W hw
  match w with
  | .root (.free j) => exact h j W hw
  | .root (.bnd _) => rw [ctxOf_bnd] at hw; cases hw
  | .step _ _ => rw [ctxOf_step] at hw; cases hw

/-- A lifted term's environment reads the family only below the lifted root. -/
theorem famEnv_lift (hM₀ : Theory.IsMCS M₀) {ρ ρ' : ShFam hF M₀} {s t : GW hF M₀} {c : ℕ}
    (hc : t.1 = c :: s.1) {z : ℕ} {e : LTerm σ}
    (he : fmapL hF M₀ t.1 (.step (.root (.free z)) .keep) = .inr e)
    (hag : AgreeBelow (lev s z) ρ ρ') : famEnv ρ (ctxOf e.1) t = famEnv ρ' (ctxOf e.1) t :=
  famEnv_agree fun _ W hj =>
    hag t _ W (lift_root hM₀ hc he hj).1 (lift_root hM₀ hc he hj).2

/-- The source of an image `◇`-root is declared at the parent, at the same type and level. -/
theorem inherit_src (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: s.1)
    {u : ℕ} {v : VarSymb} {A : VarType} (hz : DeclAt t v (.VTypeDia A))
    (h : fmapL hF M₀ t.1 (.step (.root (.free u)) .keep) = .inl v) :
    DeclAt s (.root (.free u)) (.VTypeDia A) ∧ lev s u = levA t v := by
  classical
  have hcom : GCommitted hF M₀ t.1 (.step (.root (.free u)) .keep) := by
    by_contra hn
    have hn' : ¬ ∃ m, (gnet hF M₀ m).Live t.1 ∧ ∃ T, (ctxOf ((gnet hF M₀ m).fcl t.1)).kView
        ((gnet hF M₀ m).kind t.1) (.step (.root (.free u)) .keep) = some T := hn
    rw [fmapL, dif_neg hn'] at h
    cases h
    obtain ⟨i, hi⟩ := hz
    rw [Ctx.ref_step_nonproj _ _ (by decide), ctxOf_step] at hi
    cases hi
  obtain ⟨m, hk, ⟨U, hU⟩⟩ := hcom
  have hbox : (ctxOf ((gnet hF M₀ m).fcl t.1)).boxIn (.step (.root (.free u)) .keep) = some U := by
    cases hkd : (gnet hF M₀ m).kind t.1 with
    | none => rw [hkd] at hU; exact hU
    | some x => rw [hkd] at hU; exact hU
  obtain ⟨-, hu, -⟩ := Ctx.boxIn_keep hbox
  have hN := good_gnet hF hM₀ m
  obtain ⟨hsuf, -, hf, -⟩ := hN.fwd c s.1 (hc ▸ hk)
  rw [← hc] at hsuf hf
  have hent := hf _ U (kView_lastProj hU) hU
  rw [← fmapL_at hM₀ hk ⟨U, hU⟩, h] at hent
  have hzU : DeclAt t v U := ⟨m - gbirth hF M₀ t.2, by
    rw [glat_round t hk]; exact hent⟩
  obtain rfl := DeclAt.unique hM₀ hz hzU
  obtain ⟨r, hr, hlv⟩ := hz.rt
  refine ⟨⟨m - gbirth hF M₀ s.2, ?_⟩, hlv ▸ (lev_img hM₀ hc ⟨m, hk, ⟨_, hU⟩⟩ h hr rfl).symm⟩
  have hk' : (gnet hF M₀ m).Live (c :: s.1) := hc ▸ hk
  rw [glat_round s hk'.1]
  exact (ctxOf_le_of_suffix hsuf).ref hu

/-! ## Locality -/

/-- ⭐**A `□` address's value along a path reads the family only below the address.** -/
theorem boxEnt_local (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {ρ ρ' : ShFam hF M₀}
    {A : VarType} {g g' : (t : GW hF M₀) → VarSymb → GShape hF M₀ t A} :
    ∀ (P : List ℕ) (s : GW hF M₀) (v : VarSymb) (t : GW hF M₀) (h : t.1 = nodeOf s.1 P),
      DeclAt s v (.VTypeBox A) → AgreeBelow (levA s v) ρ ρ' →
      (∀ t w, DeclAt t w A → levA t w ≤ levA s v → g t w = g' t w) →
        boxEnt ρ g s v P t h = boxEnt ρ' g' s v P t h
  | [], s, v, t, h, hd, _, hg => by
      change g t (.step v .here) = g' t (.step v .here)
      obtain rfl : t = s := gw_eq h
      obtain ⟨i, hi⟩ := hd
      exact hg t _ ⟨i, Ctx.ref_here_of hT hi⟩ le_rfl
  | c :: Q, s, v, t, h, hd, hag, hg => by
      have hc : (stepW s c (born_step h)).1 = c :: s.1 := rfl
      cases he : fmapL hF M₀ (c :: s.1) (.step v .keep) with
      | inl y =>
          have e₁ : boxEnt ρ g s v (c :: Q) t h = boxEnt ρ g (stepW s c (born_step h)) y Q t h := by
            simp only [boxEnt, he]
          have e₂ : boxEnt ρ' g' s v (c :: Q) t h =
              boxEnt ρ' g' (stepW s c (born_step h)) y Q t h := by
            simp only [boxEnt, he]
          rw [e₁, e₂]
          obtain ⟨hdy, hly⟩ := keep_img hM₀ hc hd rfl he
          exact boxEnt_local hT hM₀ Q _ y t h hdy (hly ▸ hag)
            (fun t w hw hl => hg t w hw (hly ▸ hl))
      | inr e =>
          obtain ⟨z, hz⟩ := fmapL_term hM₀ he
          obtain rfl : v = .root (.free z) := (VarSymb.step.inj hz).1
          have hfam := famEnv_lift (ρ := ρ) (ρ' := ρ') hM₀ hc he hag
          simp only [boxEnt, he]
          rw [hfam]

/-- ⭐**A `◇`-root's shape reads the family only below the root.** -/
theorem diaT_local (hM₀ : Theory.IsMCS M₀) {ρ ρ' : ShFam hF M₀} :
    ∀ (p : Node) (hp : GBorn hF M₀ p) (v : VarSymb) (A : VarType),
      DeclAt ⟨p, hp⟩ v (.VTypeDia A) → AgreeBelow (levA ⟨p, hp⟩ v) ρ ρ' →
        diaT ρ p hp v A = diaT ρ' p hp v A
  | [], hp, v, A, _, hag => by
      unfold diaT
      split_ifs with h
      · have hl : levA ⟨[], hp⟩ v = lev ⟨[], hp⟩ h.choose :=
          congrArg (levA _) h.choose_spec.1
        unfold liftDia liftDiaAt
        rw [famEnv_lift hM₀ (t := h.choose_spec.2.child) (e := h.choose_spec.2.ent) rfl
          h.choose_spec.2.choose_spec.choose_spec (hl ▸ hag)]
      · rfl
  | c :: p, hp, v, A, hd, hag => by
      unfold diaT
      split_ifs with h h'
      · have hl : levA ⟨c :: p, hp⟩ v = lev ⟨c :: p, hp⟩ h.choose :=
          congrArg (levA _) h.choose_spec.1
        unfold liftDia liftDiaAt
        rw [famEnv_lift hM₀ (t := h.choose_spec.2.child) (e := h.choose_spec.2.ent) rfl
          h.choose_spec.2.choose_spec.choose_spec (hl ▸ hag)]
      · obtain ⟨hds, hl⟩ := inherit_src hM₀ (s := ⟨p, gborn_parent hp⟩) (t := ⟨c :: p, hp⟩) rfl hd
          h'.choose_spec
        rw [diaT_local hM₀ p (gborn_parent hp) _ A hds (hl ▸ hag)]
      · rfl

/-- ⭐**Locality**: at a declared address, a construction step reads its family only below the
    address's level. -/
theorem cStep_local (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {ρ ρ' : ShFam hF M₀} :
    ∀ (T : VarType) (s : GW hF M₀) (v : VarSymb), DeclAt s v T → AgreeBelow (levA s v) ρ ρ' →
      CStep ρ T s v = CStep ρ' T s v
  | .Var, _, _, _, _ => rfl
  | .VTypeOne, _, _, _, _ => rfl
  | .VTypeProd A C, s, v, ⟨i, hi⟩, hag => by
      change Shp.prod _ _ = Shp.prod _ _
      rw [cStep_local hT hM₀ A s _ ⟨i, Ctx.ref_fst_of hi⟩ hag,
        cStep_local hT hM₀ C s _ ⟨i, Ctx.ref_snd_of hi⟩ hag]
  | .VTypeBox A, s, v, hd, hag => by
      change Shp.box _ = Shp.box _
      congr 2
      funext a
      exact boxEnt_local hT hM₀ _ s v a.1 _ hd hag
        (fun t w hw hl => cStep_local hT hM₀ A t w hw (hag.mono hl))
  | .VTypeDia A, s, v, hd, hag => diaT_local hM₀ s.1 s.2 v A hd hag

/-- ⭐**The canonical shapes' equation**: at a declared address, the canonical shape is one
    construction step read in the canonical shapes. -/
theorem cEnv_eq (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {v : VarSymb}
    {T : VarType} (hd : DeclAt s v T) : cEnv s v T = CStep cEnv T s v := by
  rw [cEnv]
  refine cStep_local hT hM₀ T s v hd fun t w W _ hl => ?_
  simp only [hl, if_true]

end GArrow

end V12M
