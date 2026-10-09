import QML.QML_v12m_BNetChain

/-!
# QML v12m — B's arrow model: the chain only grows

`Ext N N'`: every live node of `N` stays live in `N'`, its world grows, its kind is kept, and its
arrows' commitments only extend, keeping the images already given.  ⭐`ext_net`: along the chain,
later networks extend earlier ones — so each node has a limit.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

namespace NetSt

/-- ⭐`N'` extends `N`. -/
structure Ext (N N' : NetSt σ) : Prop where
  live : ∀ k, N.Live k → N'.Live k
  grows : ∀ k, N.Live k → Grows (N.st k) (N'.st k)
  kind : ∀ k, N.Live k → N'.kind k = N.kind k
  cx : ∀ k, N.Live k → N'.cx k = N.cx k
  fcl : ∀ k, N.Live k → N.fcl k <:+ N'.fcl k
  fimg : ∀ k, N.Live k → ∀ r < (N.fcl k).length, N'.fimg k r = N.fimg k r
  bcl : ∀ k, N.Live k → N.bcl k <:+ N'.bcl k
  bimg : ∀ k, N.Live k → ∀ r < (N.bcl k).length, N'.bimg k r = N.bimg k r

theorem Ext.refl (N : NetSt σ) : Ext N N :=
  ⟨fun _ h => h, fun _ _ => Grows.refl _, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => List.suffix_refl _, fun _ _ _ _ => rfl, fun _ _ => List.suffix_refl _,
    fun _ _ _ _ => rfl⟩

theorem Ext.trans {N N' N'' : NetSt σ} (h₁ : Ext N N') (h₂ : Ext N' N'') : Ext N N'' where
  live k hk := h₂.live k (h₁.live k hk)
  grows k hk := (h₁.grows k hk).trans (h₂.grows k (h₁.live k hk))
  kind k hk := (h₂.kind k (h₁.live k hk)).trans (h₁.kind k hk)
  cx k hk := (h₂.cx k (h₁.live k hk)).trans (h₁.cx k hk)
  fcl k hk := (h₁.fcl k hk).trans (h₂.fcl k (h₁.live k hk))
  fimg k hk r hr := (h₂.fimg k (h₁.live k hk) r
    (lt_of_lt_of_le hr (h₁.fcl k hk).length_le)).trans (h₁.fimg k hk r hr)
  bcl k hk := (h₁.bcl k hk).trans (h₂.bcl k (h₁.live k hk))
  bimg k hk r hr := (h₂.bimg k (h₁.live k hk) r
    (lt_of_lt_of_le hr (h₁.bcl k hk).length_le)).trans (h₁.bimg k hk r hr)

theorem Ext.setSt {N : NetSt σ} {s : Node} {t : NodeSt σ} (hg : Grows (N.st s) t) :
    Ext N (N.setSt s t) where
  live k hk := (live_setSt N s t k).mpr hk
  grows k _ := by
    by_cases hks : k = s
    · subst hks
      rw [setSt_self]
      exact hg
    · rw [setSt_ne _ _ hks]
      exact Grows.refl _
  kind _ _ := rfl
  cx _ _ := rfl
  fcl _ _ := List.suffix_refl _
  fimg _ _ _ _ := rfl
  bcl _ _ := List.suffix_refl _
  bimg _ _ _ _ := rfl

omit [ModalSys] in
theorem extImg_lt {img : ℕ → ℕ} {c z r : ℕ} (h : r < c) : extImg img c z r = img r :=
  if_neg (by omega)

theorem Ext.setFwd {N : NetSt σ} {k : Node} {A : VarType} (z : ℕ) :
    Ext N (N.setFwd k (A :: N.fcl k) (extImg (N.fimg k) (N.fcl k).length z)) where
  live k' hk := (live_setFwd _ _ _ _ k').mpr hk
  grows _ _ := Grows.refl _
  kind _ _ := rfl
  cx _ _ := rfl
  fcl k' _ := by
    by_cases h : k' = k
    · subst h
      change N.fcl k' <:+ Function.update N.fcl k' _ k'
      rw [Function.update_self]
      exact List.suffix_cons _ _
    · change N.fcl k' <:+ Function.update N.fcl k _ k'
      rw [Function.update_of_ne h]
  fimg k' _ r hr := by
    by_cases h : k' = k
    · subst h
      change Function.update N.fimg k' _ k' r = _
      rw [Function.update_self]
      exact extImg_lt hr
    · change Function.update N.fimg k _ k' r = _
      rw [Function.update_of_ne h]
  bcl _ _ := List.suffix_refl _
  bimg _ _ _ _ := rfl

theorem Ext.setBack {N : NetSt σ} {k : Node} {A : VarType} (z : ℕ) :
    Ext N (N.setBack k (A :: N.bcl k) (extImg (N.bimg k) (N.bcl k).length z)) where
  live k' hk := (live_setBack _ _ _ _ k').mpr hk
  grows _ _ := Grows.refl _
  kind _ _ := rfl
  cx _ _ := rfl
  fcl _ _ := List.suffix_refl _
  fimg _ _ _ _ := rfl
  bcl k' _ := by
    by_cases h : k' = k
    · subst h
      change N.bcl k' <:+ Function.update N.bcl k' _ k'
      rw [Function.update_self]
      exact List.suffix_cons _ _
    · change N.bcl k' <:+ Function.update N.bcl k _ k'
      rw [Function.update_of_ne h]
  bimg k' _ r hr := by
    by_cases h : k' = k
    · subst h
      change Function.update N.bimg k' _ k' r = _
      rw [Function.update_self]
      exact extImg_lt hr
    · change Function.update N.bimg k _ k' r = _
      rw [Function.update_of_ne h]

theorem Ext.newChild {N : NetSt σ} {s : Node} (hs : N.Live s) (kd : Option (VarSymb × VarType))
    (cx : ℕ) (t : NodeSt σ) : Ext N (N.newChild s kd cx t) := by
  have hold : ∀ k, N.Live k → k ≠ N.nch s :: s := fun k hk h => not_live_new s (h ▸ hk)
  refine ⟨fun k hk => (live_newChild hs kd cx t k).mpr (Or.inl hk), fun k hk => ?_,
    fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk r _ => ?_, fun k hk => ?_,
    fun k hk r _ => ?_⟩
  · change Grows (N.st k) (Function.update N.st _ t k)
    rw [Function.update_of_ne (hold k hk)]
    exact Grows.refl _
  · exact Function.update_of_ne (hold k hk) _ _
  · exact Function.update_of_ne (hold k hk) _ _
  · change N.fcl k <:+ Function.update N.fcl _ _ k
    rw [Function.update_of_ne (hold k hk)]
  · change Function.update N.fimg _ _ k r = _
    rw [Function.update_of_ne (hold k hk)]
  · change N.bcl k <:+ Function.update N.bcl _ _ k
    rw [Function.update_of_ne (hold k hk)]
  · change Function.update N.bimg _ _ k r = _
    rw [Function.update_of_ne (hold k hk)]

/-! ## Each operation extends -/

theorem Ext.realF [ModalSys.NoFour] {N : NetSt σ} (hN : N.Good) {k : Node} (hk : N.Live k) :
    Ext N (N.realF k) := by
  match k with
  | [] => exact Ext.refl N
  | c :: p =>
      simp only [NetSt.realF]
      split_ifs with hlt
      · obtain ⟨_, hg, _⟩ := fwdStep_ok hN hk hlt
        exact (Ext.setSt hg).trans (Ext.setFwd _)
      · exact Ext.refl N

theorem Ext.realB [ModalSys.NoFour] {N : NetSt σ} (hN : N.Good) {k : Node} (hk : N.Live k) :
    Ext N (N.realB k) := by
  match k with
  | [] => exact Ext.refl N
  | c :: p =>
      simp only [NetSt.realB]
      split_ifs with hlt
      · have hb := hN.back c p hk
        unfold BackOk BackData at hb
        obtain ⟨hsuf, himg, htr⟩ := hb
        obtain ⟨_, hg, _⟩ := realStep_ok (hN.mcs _ hk) (hN.mcs p hk.1) hsuf himg htr hlt
        exact (Ext.setSt hg).trans (Ext.setBack _)
      · exact Ext.refl N

theorem Ext.henk [ModalSys.NoFour] {N : NetSt σ} (hN : N.Good) {s : Node} (hs : N.Live s)
    (o : Obl σ) : Ext N (N.henk s o) := by
  obtain ⟨l, φ⟩ := o
  simp only [NetSt.henk]
  split_ifs with h
  · have hM := hN.mcs s hs
    match φ with
    | .ex A ψ =>
        simp only
        split_ifs with hmem
        · exact Ext.setSt (henk_grow hM (Theory.Derives.of_mem hmem)).2
        · exact Ext.refl N
    | .imp (.all A ψ) .bot =>
        simp only
        split_ifs with hmem
        · have hex : Theory.Derives (N.st s).M
              (.ex A (WFF.mono ((ctxOf_le_of_suffix h).insert _ A) ψ).neg) :=
            ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hmem,
              ⟨Proof.exNeg_of_negAll _⟩⟩
          exact Ext.setSt (henk_grow hM hex).2
        · exact Ext.refl N
    | .atom _ => exact Ext.refl N
    | .eq _ _ => exact Ext.refl N
    | .top => exact Ext.refl N
    | .bot => exact Ext.refl N
    | .and _ _ => exact Ext.refl N
    | .or _ _ => exact Ext.refl N
    | .imp (.atom _) _ => exact Ext.refl N
    | .imp (.eq _ _) _ => exact Ext.refl N
    | .imp .top _ => exact Ext.refl N
    | .imp .bot _ => exact Ext.refl N
    | .imp (.and _ _) _ => exact Ext.refl N
    | .imp (.or _ _) _ => exact Ext.refl N
    | .imp (.imp _ _) _ => exact Ext.refl N
    | .imp (.ex _ _) _ => exact Ext.refl N
    | .imp (.box _) _ => exact Ext.refl N
    | .imp (.dia _ _ _) _ => exact Ext.refl N
    | .imp (.here _ _ _) _ => exact Ext.refl N
    | .imp (.back _ _ _ _) _ => exact Ext.refl N
    | .imp (.retS _ _ _ _) _ => exact Ext.refl N
    | .imp (.retxS _ _ _ _ _ _) _ => exact Ext.refl N
    | .imp (.all _ _) (.atom _) => exact Ext.refl N
    | .imp (.all _ _) (.eq _ _) => exact Ext.refl N
    | .imp (.all _ _) .top => exact Ext.refl N
    | .imp (.all _ _) (.and _ _) => exact Ext.refl N
    | .imp (.all _ _) (.or _ _) => exact Ext.refl N
    | .imp (.all _ _) (.imp _ _) => exact Ext.refl N
    | .imp (.all _ _) (.all _ _) => exact Ext.refl N
    | .imp (.all _ _) (.ex _ _) => exact Ext.refl N
    | .imp (.all _ _) (.box _) => exact Ext.refl N
    | .imp (.all _ _) (.dia _ _ _) => exact Ext.refl N
    | .imp (.all _ _) (.here _ _ _) => exact Ext.refl N
    | .imp (.all _ _) (.back _ _ _ _) => exact Ext.refl N
    | .imp (.all _ _) (.retS _ _ _ _) => exact Ext.refl N
    | .imp (.all _ _) (.retxS _ _ _ _ _ _) => exact Ext.refl N
    | .all _ _ => exact Ext.refl N
    | .box _ => exact Ext.refl N
    | .dia _ _ _ => exact Ext.refl N
    | .here _ _ _ => exact Ext.refl N
    | .back _ _ _ _ => exact Ext.refl N
    | .retS _ _ _ _ => exact Ext.refl N
    | .retxS _ _ _ _ _ _ => exact Ext.refl N
  · exact Ext.refl N

theorem Ext.mkChild [ModalSys.NoFour] {N : NetSt σ} {s : Node} (hs : N.Live s) (o : Obl σ) :
    Ext N (N.mkChild s o) := by
  obtain ⟨l, φ⟩ := o
  simp only [NetSt.mkChild]
  split_ifs with h
  · match φ with
    | .box ψ =>
        simp only
        split_ifs
        · exact Ext.refl N
        · exact Ext.newChild hs _ _ _
    | .dia x hx ψ =>
        simp only
        split_ifs
        · split
          · exact Ext.newChild hs _ _ _
          · exact Ext.refl N
        · exact Ext.refl N
    | .atom _ => exact Ext.refl N
    | .eq _ _ => exact Ext.refl N
    | .top => exact Ext.refl N
    | .bot => exact Ext.refl N
    | .and _ _ => exact Ext.refl N
    | .or _ _ => exact Ext.refl N
    | .imp _ _ => exact Ext.refl N
    | .all _ _ => exact Ext.refl N
    | .ex _ _ => exact Ext.refl N
    | .here _ _ _ => exact Ext.refl N
    | .back _ _ _ _ => exact Ext.refl N
    | .retS _ _ _ _ => exact Ext.refl N
    | .retxS _ _ _ _ _ _ => exact Ext.refl N
  · exact Ext.refl N

theorem Ext.applyOp [ModalSys.NoFour] {N : NetSt σ} (hN : N.Good) (o : Op σ) :
    Ext N (N.applyOp o) := by
  rcases o with ⟨s, o⟩ | ⟨s, o⟩ | k | k
  · simp only [NetSt.applyOp]
    split_ifs with h
    · exact Ext.henk hN h o
    · exact Ext.refl N
  · simp only [NetSt.applyOp]
    split_ifs with h
    · exact Ext.mkChild h o
    · exact Ext.refl N
  · simp only [NetSt.applyOp]
    split_ifs with h
    · exact Ext.realF hN h
    · exact Ext.refl N
  · simp only [NetSt.applyOp]
    split_ifs with h
    · exact Ext.realB hN h
    · exact Ext.refl N

end NetSt

section Chain

variable [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoFour]

/-- ⭐Along the chain, later networks extend earlier ones. -/
theorem ext_net (hB : ModalSys.B = true) {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}
    (h : Theory.IsMCS M₀) {n m : ℕ} (hnm : n ≤ m) : NetSt.Ext (net M₀ n) (net M₀ m) := by
  induction hnm with
  | refl => exact NetSt.Ext.refl _
  | step _ ih => exact ih.trans (NetSt.Ext.applyOp (good_net hB h _) _)

end Chain

end BArrow

end V12M
