import QML.QML_v12m_GNetOps
import QML.QML_v12m_BNetChain

/-!
# QML v12m — the growing tree: the chain and its fairness

As B's `BNetMono`, `BNetChain` and `BFair`, for the growing tree.

* `Ext N N'`: every live node of `N` stays live in `N'`, its world grows, its kind is kept, and
  its edge's commitments only extend, keeping the images of the items already committed.
* The operations (`GOp`): a Henkin step or a child at a node, realising forward along an edge,
  and ⭐a **lift** of an address of a child along its edge.  A lift first catches the edge up
  (`catchUp`: realise forward until the parent is fully committed), then lifts (`GNetSt.lift`),
  as paper check 1 has it: the parent's other edges and its Henkin steps may grow it at any time,
  so the catching up belongs to the operation.
* `gnet`: the chain under a fair schedule, each network good (`good_gnet`) and extending the
  earlier ones (`ext_gnet`).
* ⭐`GFairChain`: what the limit needs — every variable of a parent is eventually committed
  (`fwd_total`), every existential and failing universal witnessed (`henk_ex`, `henk_negAll`),
  every failing `□φ` and true `◇_x φ` given a child (`child_box`, `child_dia`), and every
  liftable address of a child lifted (`lift_total`).  `fairChain` is the chain's.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature}

namespace GNetSt

/-! ## Extension -/

/-- ⭐`N'` extends `N`. -/
structure Ext (N N' : GNetSt σ) : Prop where
  live : ∀ k, N.Live k → N'.Live k
  grows : ∀ k, N.Live k → Grows (N.st k) (N'.st k)
  kind : ∀ k, N.Live k → N'.kind k = N.kind k
  fcl : ∀ k, N.Live k → N.fcl k <:+ N'.fcl k
  fmap : ∀ k, N.Live k → ∀ v T, (ctxOf (N.fcl k)).kView (N.kind k) v = some T →
    N'.fmap k v = N.fmap k v

theorem Ext.refl (N : GNetSt σ) : Ext N N :=
  ⟨fun _ h => h, fun _ _ => Grows.refl _, fun _ _ => rfl, fun _ _ => List.suffix_refl _,
    fun _ _ _ _ _ => rfl⟩

theorem Ext.trans {N N' N'' : GNetSt σ} (h₁ : Ext N N') (h₂ : Ext N' N'') : Ext N N'' where
  live k hk := h₂.live k (h₁.live k hk)
  grows k hk := (h₁.grows k hk).trans (h₂.grows k (h₁.live k hk))
  kind k hk := (h₂.kind k (h₁.live k hk)).trans (h₁.kind k hk)
  fcl k hk := (h₁.fcl k hk).trans (h₂.fcl k (h₁.live k hk))
  fmap k hk v T hv := by
    refine (h₂.fmap k (h₁.live k hk) v T ?_).trans (h₁.fmap k hk v T hv)
    rw [h₁.kind k hk]
    exact ((ctxOf_le_of_suffix (h₁.fcl k hk)).kView _) v T hv

theorem Ext.setSt {N : GNetSt σ} {s : Node} {t : NodeSt σ} (hg : Grows (N.st s) t) :
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
  fcl _ _ := List.suffix_refl _
  fmap _ _ _ _ _ := rfl

/-- The items of a committed view have older roots than the next variable. -/
theorem kView_rt_lt {cl : List VarType} {k : Option VarSymb} {u : VarSymb} {s : Step}
    {T : VarType} (h : (ctxOf cl).kView k (.step u s) = some T) : ¬ u.rt = .free cl.length := by
  obtain ⟨u', s', e, -, U, hU⟩ := kView_item h
  cases e
  obtain ⟨r, hr, hlt, -⟩ := ref_rt hU
  rw [hr]
  exact fun h => by cases h; omega

/-- Recommitting an edge to an extension of its map extends. -/
theorem Ext.setFwd {N : GNetSt σ} {k : Node} {A : VarType} {f : VarSymb → LEnt σ}
    (hf : ∀ v T, (ctxOf (N.fcl k)).kView (N.kind k) v = some T → f v = N.fmap k v) :
    Ext N (N.setFwd k (A :: N.fcl k) f) where
  live k' hk := (live_setFwd _ _ _ _ k').mpr hk
  grows _ _ := Grows.refl _
  kind _ _ := rfl
  fcl k' _ := by
    by_cases h : k' = k
    · subst h
      change N.fcl k' <:+ Function.update N.fcl k' _ k'
      rw [Function.update_self]
      exact List.suffix_cons _ _
    · change N.fcl k' <:+ Function.update N.fcl k _ k'
      rw [Function.update_of_ne h]
  fmap k' _ v T hv := by
    by_cases h : k' = k
    · subst h
      change Function.update N.fmap k' _ k' v = _
      rw [Function.update_self]
      exact hf v T hv
    · change Function.update N.fmap k _ k' v = _
      rw [Function.update_of_ne h]

theorem Ext.newChild {N : GNetSt σ} {s : Node} (hs : N.Live s) (kd : Option VarSymb)
    (t : NodeSt σ) (f : VarSymb → LEnt σ) : Ext N (N.newChild s kd t f) := by
  have hold : ∀ k, N.Live k → k ≠ N.nch s :: s := fun k hk h => not_live_new s (h ▸ hk)
  refine ⟨fun k hk => (live_newChild hs kd t f k).mpr (Or.inl hk), fun k hk => ?_,
    fun k hk => ?_, fun k hk => ?_, fun k hk v _ _ => ?_⟩
  · change Grows (N.st k) (Function.update N.st _ t k)
    rw [Function.update_of_ne (hold k hk)]
    exact Grows.refl _
  · exact Function.update_of_ne (hold k hk) _ _
  · change N.fcl k <:+ Function.update N.fcl _ _ k
    rw [Function.update_of_ne (hold k hk)]
  · change Function.update N.fmap _ _ k v = _
    rw [Function.update_of_ne (hold k hk)]

/-! ## Each operation extends -/

theorem Ext.realF (hF : ModalSys.Four = true) {N : GNetSt σ} (hN : N.Good) {k : Node}
    (hk : N.Live k) : Ext N (N.realF hF k) := by
  match k with
  | [] => exact Ext.refl N
  | c :: p =>
      simp only [GNetSt.realF]
      split_ifs with hlt
      · obtain ⟨_, hg, _⟩ := grealStep_ok hF (hN.mcs p hk.1) (hN.mcs _ hk) (hN.fwd c p hk) hlt
        refine (Ext.setSt hg).trans (Ext.setFwd fun v T hv => ?_)
        obtain ⟨u, s, rfl, -, -⟩ := kView_item hv
        exact gextF_old (kView_rt_lt hv) s
      · exact Ext.refl N

theorem Ext.henk {N : GNetSt σ} (hN : N.Good) {s : Node} (hs : N.Live s) (o : Obl σ) :
    Ext N (N.henk s o) := by
  obtain ⟨l, φ⟩ := o
  simp only [GNetSt.henk]
  split_ifs with h
  · have hM := hN.mcs s hs
    match φ with
    | .ex A ψ =>
        simp only
        split_ifs with hmem
        · exact Ext.setSt (NetSt.henk_grow hM (Theory.Derives.of_mem hmem)).2
        · exact Ext.refl N
    | .imp (.all A ψ) .bot =>
        simp only
        split_ifs with hmem
        · have hex : Theory.Derives (N.st s).M
              (.ex A (WFF.mono ((ctxOf_le_of_suffix h).insert _ A) ψ).neg) :=
            ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hmem,
              ⟨Proof.exNeg_of_negAll _⟩⟩
          exact Ext.setSt (NetSt.henk_grow hM hex).2
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

theorem Ext.mkChild (hF : ModalSys.Four = true) {N : GNetSt σ} {s : Node} (hs : N.Live s)
    (o : Obl σ) : Ext N (N.mkChild hF s o) := by
  obtain ⟨l, φ⟩ := o
  simp only [GNetSt.mkChild]
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

/-! ## Catching up, then lifting -/

theorem nch_realF (hF : ModalSys.Four = true) (N : GNetSt σ) (k : Node) :
    (N.realF hF k).nch = N.nch := by
  match k with
  | [] => rfl
  | c :: p =>
      simp only [GNetSt.realF]
      split_ifs <;> rfl

theorem realF_st_par (hF : ModalSys.Four = true) (N : GNetSt σ) (c : ℕ) (p : Node) :
    (N.realF hF (c :: p)).st p = N.st p := by
  simp only [GNetSt.realF]
  split_ifs
  · exact setSt_ne _ _ (fun h => NetSt.ne_parent c p h.symm)
  · rfl

theorem realF_fcl (hF : ModalSys.Four = true) (N : GNetSt σ) (c : ℕ) (p : Node) :
    (N.realF hF (c :: p)).fcl (c :: p) =
      if (N.fcl (c :: p)).length < (N.st p).l.length then
        nextTy (N.st p).l (N.fcl (c :: p)) :: N.fcl (c :: p)
      else N.fcl (c :: p) := by
  simp only [GNetSt.realF]
  split_ifs
  · exact Function.update_self _ _ _
  · rfl

/-- Realise forward along the edge into `k` until its parent is fully committed. -/
noncomputable def catchUp (hF : ModalSys.Four = true) (N : GNetSt σ) : Node → GNetSt σ
  | [] => N
  | c :: p => (fun N' => N'.realF hF (c :: p))^[(N.st p).l.length - (N.fcl (c :: p)).length] N

theorem iterate_realF (hF : ModalSys.Four = true) (c : ℕ) (p : Node) :
    ∀ (j : ℕ) (N : GNetSt σ), (N.fcl (c :: p)).length + j ≤ (N.st p).l.length →
      ((fun N' => N'.realF hF (c :: p))^[j] N).st p = N.st p ∧
        (((fun N' => N'.realF hF (c :: p))^[j] N).fcl (c :: p)).length =
          (N.fcl (c :: p)).length + j
  | 0, _, _ => ⟨rfl, rfl⟩
  | j + 1, N, h => by
      rw [Function.iterate_succ_apply]
      have hlt : (N.fcl (c :: p)).length < (N.st p).l.length := by omega
      have h₁ := realF_st_par hF N c p
      have h₂ : ((N.realF hF (c :: p)).fcl (c :: p)).length = (N.fcl (c :: p)).length + 1 := by
        rw [realF_fcl, if_pos hlt, List.length_cons]
      obtain ⟨ih₁, ih₂⟩ := iterate_realF hF c p j (N.realF hF (c :: p)) (by rw [h₁, h₂]; omega)
      exact ⟨ih₁.trans h₁, by rw [ih₂, h₂]; omega⟩

theorem Good.iterate_realF (hF : ModalSys.Four = true) (k : Node) :
    ∀ (j : ℕ) {N : GNetSt σ}, N.Good → N.Live k →
      ((fun N' => N'.realF hF k)^[j] N).Good ∧ ((fun N' => N'.realF hF k)^[j] N).Live k ∧
        Ext N ((fun N' => N'.realF hF k)^[j] N)
  | 0, _, hN, hk => ⟨hN, hk, Ext.refl _⟩
  | j + 1, N, hN, hk => by
      rw [Function.iterate_succ_apply]
      have hN' := hN.realF hF hk
      have hk' : (N.realF hF k).Live k := (live_of_nch (nch_realF hF N k) k).mpr hk
      obtain ⟨h₁, h₂, h₃⟩ := Good.iterate_realF hF k j hN' hk'
      exact ⟨h₁, h₂, (Ext.realF hF hN hk).trans h₃⟩

theorem Good.catchUp (hF : ModalSys.Four = true) {N : GNetSt σ} (hN : N.Good) {k : Node}
    (hk : N.Live k) :
    (N.catchUp hF k).Good ∧ (N.catchUp hF k).Live k ∧ Ext N (N.catchUp hF k) := by
  match k with
  | [] => exact ⟨hN, hk, Ext.refl N⟩
  | c :: p => exact Good.iterate_realF hF (c :: p) _ hN hk

/-- ⭐After catching up, the parent is fully committed along the edge. -/
theorem catchUp_full (hF : ModalSys.Four = true) {N : GNetSt σ} (hN : N.Good) {c : ℕ}
    {p : Node} (hk : N.Live (c :: p)) :
    (N.catchUp hF (c :: p)).fcl (c :: p) = ((N.catchUp hF (c :: p)).st p).l := by
  obtain ⟨hsuf, -⟩ := hN.fwd c p hk
  have hle := hsuf.length_le
  obtain ⟨h₁, h₂⟩ := iterate_realF hF c p ((N.st p).l.length - (N.fcl (c :: p)).length) N
    (by omega)
  obtain ⟨hN', hk', -⟩ := hN.catchUp hF hk
  obtain ⟨hsuf', -⟩ := hN'.fwd c p hk'
  change ((fun N' => N'.realF hF (c :: p))^[_] N).fcl (c :: p) <:+
    (((fun N' => N'.realF hF (c :: p))^[_] N).st p).l at hsuf'
  change ((fun N' => N'.realF hF (c :: p))^[_] N).fcl (c :: p) =
    (((fun N' => N'.realF hF (c :: p))^[_] N).st p).l
  refine hsuf'.eq_of_length ?_
  rw [h₂, h₁]
  omega

theorem nch_lift (hF : ModalSys.Four = true) (N : GNetSt σ) (k : Node) (o : LTerm σ) :
    (N.lift hF k o).nch = N.nch := by
  match k, o with
  | [], _ => rfl
  | c :: p, ⟨l, T, a, t⟩ =>
      simp only [GNetSt.lift]
      split_ifs <;> rfl

/-- What a lift does, when it applies. -/
theorem lift_spec (hF : ModalSys.Four = true) {N : GNetSt σ} {c : ℕ} {p : Node}
    {l : List VarType} {T : VarType} {a : Ann T} {t : Term σ (ctxOf l) T a}
    (hcl : N.fcl (c :: p) = (N.st p).l) (h : l <:+ (N.st (c :: p)).l) (hl : T.liftable = true)
    (hv : LiftAdm hF ⟨l, T, a, t⟩ ∧
      (ModalSys.Five = true → N.OriginAdm (c :: p) ⟨l, T, a, t⟩)) :
    N.lift hF (c :: p) ⟨l, T, a, t⟩ = ((N.setSt p (liftPar hF (N.st p) (N.st (c :: p))
        (N.kind (c :: p)) (N.fmap (c :: p)) (Term.mono (ctxOf_le_of_suffix h) t) hl)).setSt
        (c :: p) (liftChild hF (N.st p) (N.st (c :: p)) (N.kind (c :: p)) (N.fmap (c :: p))
          (Term.mono (ctxOf_le_of_suffix h) t) hl)).setFwd
      (c :: p) (T :: (N.st p).l)
      (gliftG (N.fmap (c :: p)) T (N.st p).l.length
        (.inr ⟨(N.st (c :: p)).l, T, a, Term.mono (ctxOf_le_of_suffix h) t⟩)
        (.free (N.st (c :: p)).l.length)) := by
  simp only [GNetSt.lift, if_pos hcl, dif_pos h, dif_pos hl, if_pos hv]

theorem Ext.lift (hF : ModalSys.Four = true) {N : GNetSt σ} (hN : N.Good) {k : Node}
    (hk : N.Live k) (o : LTerm σ) : Ext N (N.lift hF k o) := by
  match k, o with
  | [], _ => exact Ext.refl N
  | c :: p, ⟨l, T, a, t⟩ =>
      by_cases hcl : N.fcl (c :: p) = (N.st p).l
      · by_cases h : l <:+ (N.st (c :: p)).l
        · by_cases hl : T.liftable = true
          · by_cases hv : LiftAdm hF ⟨l, T, a, t⟩ ∧
                (ModalSys.Five = true → N.OriginAdm (c :: p) ⟨l, T, a, t⟩)
            swap
            · simp only [GNetSt.lift, if_pos hcl, dif_pos h, dif_pos hl, if_neg hv]
              exact Ext.refl N
            rw [lift_spec hF hcl h hl hv]
            have hd := hN.fwd c p hk
            unfold FwdOk at hd
            rw [hcl] at hd
            obtain ⟨-, hgp, -, hgk, -⟩ := lift_ok hF (Term.mono (ctxOf_le_of_suffix h) t) hl
              (hN.mcs p hk.1) (hN.mcs _ hk) hd
            have e₁ := Ext.setSt (N := N) hgp
            have e₂ := Ext.setSt (N := N.setSt p (liftPar hF (N.st p) (N.st (c :: p))
              (N.kind (c :: p)) (N.fmap (c :: p)) (Term.mono (ctxOf_le_of_suffix h) t) hl))
              (s := c :: p)
              (t := liftChild hF (N.st p) (N.st (c :: p)) (N.kind (c :: p)) (N.fmap (c :: p))
                (Term.mono (ctxOf_le_of_suffix h) t) hl)
              (by rw [setSt_ne _ _ (NetSt.ne_parent c p)]; exact hgk)
            refine e₁.trans (e₂.trans ?_)
            have e₃ := Ext.setFwd (N := (N.setSt p (liftPar hF (N.st p) (N.st (c :: p))
              (N.kind (c :: p)) (N.fmap (c :: p)) (Term.mono (ctxOf_le_of_suffix h) t) hl)).setSt
              (c :: p) (liftChild hF (N.st p) (N.st (c :: p)) (N.kind (c :: p))
                (N.fmap (c :: p)) (Term.mono (ctxOf_le_of_suffix h) t) hl)) (k := c :: p) (A := T)
              (f := gliftG (N.fmap (c :: p)) T (N.st p).l.length
                (.inr ⟨(N.st (c :: p)).l, T, a, Term.mono (ctxOf_le_of_suffix h) t⟩)
                (.free (N.st (c :: p)).l.length)) (fun v T' hv => by
                change (ctxOf (N.fcl (c :: p))).kView (N.kind (c :: p)) v = some T' at hv
                obtain ⟨u, s, rfl, -, -⟩ := kView_item hv
                rw [hcl] at hv
                exact gliftG_old (kView_rt_lt hv))
            change Ext _ (GNetSt.setFwd _ (c :: p) (T :: N.fcl (c :: p)) _) at e₃
            rw [hcl] at e₃
            exact e₃
          · simp only [GNetSt.lift, if_pos hcl, dif_pos h, dif_neg hl]
            exact Ext.refl N
        · simp only [GNetSt.lift, if_pos hcl, dif_neg h]
          exact Ext.refl N
      · simp only [GNetSt.lift, if_neg hcl]
        exact Ext.refl N

/-! ## The chain -/

/-- An operation: a Henkin witness or a child for an obligation at a node, realising forward
    along an edge, or lifting a term of a child along its edge. -/
abbrev GOp (σ : Signature) := (Node × Obl σ) ⊕ (Node × Obl σ) ⊕ Node ⊕ (Node × LTerm σ)

instance : Nonempty (GOp σ) := ⟨.inr (.inr (.inl []))⟩

open Classical in
/-- Perform one operation, at a live node only. -/
noncomputable def applyOp (hF : ModalSys.Four = true) (N : GNetSt σ) : GOp σ → GNetSt σ
  | .inl (s, o) => if N.Live s then N.henk s o else N
  | .inr (.inl (s, o)) => if N.Live s then N.mkChild hF s o else N
  | .inr (.inr (.inl k)) => if N.Live k then N.realF hF k else N
  | .inr (.inr (.inr (k, n))) => if N.Live k then (N.catchUp hF k).lift hF k n else N

theorem Good.applyOp (hF : ModalSys.Four = true) {N : GNetSt σ} (hN : N.Good) (o : GOp σ) :
    (N.applyOp hF o).Good := by
  rcases o with ⟨s, o⟩ | ⟨s, o⟩ | k | ⟨k, n⟩
  · simp only [GNetSt.applyOp]
    split_ifs with h
    · exact hN.henk h o
    · exact hN
  · simp only [GNetSt.applyOp]
    split_ifs with h
    · exact hN.mkChild hF h o
    · exact hN
  · simp only [GNetSt.applyOp]
    split_ifs with h
    · exact hN.realF hF h
    · exact hN
  · simp only [GNetSt.applyOp]
    split_ifs with h
    · obtain ⟨h₁, h₂, -⟩ := hN.catchUp hF h
      exact h₁.lift hF h₂ n
    · exact hN

theorem Ext.applyOp (hF : ModalSys.Four = true) {N : GNetSt σ} (hN : N.Good) (o : GOp σ) :
    Ext N (N.applyOp hF o) := by
  rcases o with ⟨s, o⟩ | ⟨s, o⟩ | k | ⟨k, n⟩
  · simp only [GNetSt.applyOp]
    split_ifs with h
    · exact Ext.henk hN h o
    · exact Ext.refl N
  · simp only [GNetSt.applyOp]
    split_ifs with h
    · exact Ext.mkChild hF h o
    · exact Ext.refl N
  · simp only [GNetSt.applyOp]
    split_ifs with h
    · exact Ext.realF hF hN h
    · exact Ext.refl N
  · simp only [GNetSt.applyOp]
    split_ifs with h
    · obtain ⟨h₁, h₂, h₃⟩ := hN.catchUp hF h
      exact h₃.trans (Ext.lift hF h₁ h₂ n)
    · exact Ext.refl N

/-- The network of one world with theory `M₀`. -/
def init {l₀ : List VarType} (M₀ : Set (WFF σ (ctxOf l₀) 0)) : GNetSt σ where
  st := fun _ => ⟨l₀, M₀⟩
  nch := fun _ => 0
  kind := fun _ => none
  fcl := fun _ => []
  fmap := fun _ => ofRen id

theorem init_live {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} :
    ∀ {k : Node}, (init M₀).Live k → k = []
  | [], _ => rfl
  | _ :: _, h => absurd h.2 (Nat.not_lt_zero _)

theorem Good.init {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} (h : Theory.IsMCS M₀) :
    (init M₀).Good :=
  ⟨fun _ _ => h, fun _ _ hk => absurd (init_live hk) (by simp)⟩

end GNetSt

section Chain

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- An enumeration of the operations. -/
noncomputable def enumGOp : ℕ → GNetSt.GOp σ :=
  Classical.choose (exists_surjective_nat (GNetSt.GOp σ))

theorem enumGOp_surjective : Function.Surjective (enumGOp (σ := σ)) :=
  Classical.choose_spec (exists_surjective_nat (GNetSt.GOp σ))

/-- ⭐The schedule: round `n` performs operation `n.unpair.1`, so each recurs forever. -/
noncomputable def gsched (n : ℕ) : GNetSt.GOp σ := enumGOp n.unpair.1

theorem gsched_after (o : GNetSt.GOp σ) (m : ℕ) : ∃ n, m ≤ n ∧ gsched n = o := by
  obtain ⟨e, he⟩ := enumGOp_surjective o
  refine ⟨Nat.pair e m, Nat.right_le_pair e m, ?_⟩
  simp [gsched, Nat.unpair_pair, he]

/-- ⭐The chain of growing trees from a root theory `M₀`. -/
noncomputable def gnet (hF : ModalSys.Four = true) {l₀ : List VarType}
    (M₀ : Set (WFF σ (ctxOf l₀) 0)) : ℕ → GNetSt σ
  | 0 => GNetSt.init M₀
  | n + 1 => (gnet hF M₀ n).applyOp hF (gsched n)

/-- ⭐Every network of the chain is good. -/
theorem good_gnet (hF : ModalSys.Four = true) {l₀ : List VarType}
    {M₀ : Set (WFF σ (ctxOf l₀) 0)} (h : Theory.IsMCS M₀) : ∀ n, (gnet hF M₀ n).Good
  | 0 => GNetSt.Good.init h
  | n + 1 => (good_gnet hF h n).applyOp hF (gsched n)

/-- ⭐Along the chain, later networks extend earlier ones. -/
theorem ext_gnet (hF : ModalSys.Four = true) {l₀ : List VarType}
    {M₀ : Set (WFF σ (ctxOf l₀) 0)} (h : Theory.IsMCS M₀) {n m : ℕ} (hnm : n ≤ m) :
    GNetSt.Ext (gnet hF M₀ n) (gnet hF M₀ m) := by
  induction hnm with
  | refl => exact GNetSt.Ext.refl _
  | step _ ih => exact ih.trans (GNetSt.Ext.applyOp hF (good_gnet hF h _) _)

theorem gnet_succ_of (hF : ModalSys.Four = true) {l₀ : List VarType}
    {M₀ : Set (WFF σ (ctxOf l₀) 0)} {n : ℕ} {o : GNetSt.GOp σ} (h : gsched n = o) :
    gnet hF M₀ (n + 1) = (gnet hF M₀ n).applyOp hF o := by
  rw [← h]
  rfl

end Chain

end GArrow

end V12M
