import QML.QML_v12m_GFair

/-!
# QML v12m — the growing tree: what the chain achieves

For the chain `gnet hF M₀` (as B's `BFair`):

* ⭐`fwd_total`: every variable of a parent is eventually committed along each edge;
* ⭐`henk_ex`, `henk_negAll`: every existential, and every failing universal, of a node's theory
  eventually has a witness;
* ⭐`child_box`, `child_dia`: every failing `□φ`, and every true `◇_x φ`, eventually has a child;
* ⭐`lift_total`: every term of a child of a liftable type is eventually lifted — the parent
  gets a root `r` of that type with `r.keep ↦` the term along the edge (D5 (a)).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  (hF : ModalSys.Four = true) {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}
  (hM₀ : Theory.IsMCS M₀)

include hM₀

theorem gnet_live_mono {n m : ℕ} (hnm : n ≤ m) {k : Node} (h : (gnet hF M₀ n).Live k) :
    (gnet hF M₀ m).Live k :=
  (ext_gnet hF hM₀ hnm).live k h

theorem gnet_lang_suffix {n m : ℕ} (hnm : n ≤ m) {k : Node} (h : (gnet hF M₀ n).Live k) :
    ((gnet hF M₀ n).st k).l <:+ ((gnet hF M₀ m).st k).l :=
  ((ext_gnet hF hM₀ hnm).grows k h).suf

/-! ## Forward totality -/

/-- ⭐Every variable of a parent is eventually committed along the edge into a child. -/
theorem fwd_total {n c : ℕ} {p : Node} (hk : (gnet hF M₀ n).Live (c :: p)) {r : ℕ}
    (hr : r < ((gnet hF M₀ n).st p).l.length) :
    ∃ m, n ≤ m ∧ r < ((gnet hF M₀ m).fcl (c :: p)).length := by
  have key : ∀ j, ∃ m, n ≤ m ∧ min j (r + 1) ≤ ((gnet hF M₀ m).fcl (c :: p)).length := by
    intro j
    induction j with
    | zero => exact ⟨n, le_rfl, by simp⟩
    | succ j ih =>
        obtain ⟨m, hnm, hm⟩ := ih
        by_cases hdone : r + 1 ≤ ((gnet hF M₀ m).fcl (c :: p)).length
        · exact ⟨m, hnm, (min_le_right _ _).trans hdone⟩
        obtain ⟨m', hm'm, hs⟩ := gsched_after (σ := σ) (.inr (.inr (.inl (c :: p)))) m
        have hlm' := gnet_live_mono hF hM₀ (hnm.trans hm'm) hk
        have hmono : ((gnet hF M₀ m).fcl (c :: p)).length ≤
            ((gnet hF M₀ m').fcl (c :: p)).length :=
          ((ext_gnet hF hM₀ hm'm).fcl _ (gnet_live_mono hF hM₀ hnm hk)).length_le
        by_cases hdone' : r + 1 ≤ ((gnet hF M₀ m').fcl (c :: p)).length
        · exact ⟨m', hnm.trans hm'm, (min_le_right _ _).trans hdone'⟩
        have hlp : ((gnet hF M₀ n).st p).l.length ≤ ((gnet hF M₀ m').st p).l.length :=
          (gnet_lang_suffix hF hM₀ (hnm.trans hm'm) hk.1).length_le
        have hlt : ((gnet hF M₀ m').fcl (c :: p)).length < ((gnet hF M₀ m').st p).l.length := by
          omega
        refine ⟨m' + 1, by omega, ?_⟩
        rw [gnet_succ_of hF hs]
        simp only [GNetSt.applyOp, if_pos hlm']
        rw [GNetSt.realF_fcl, if_pos hlt, List.length_cons]
        omega
  obtain ⟨m, hnm, hm⟩ := key (r + 1)
  exact ⟨m, hnm, by simp at hm; omega⟩

/-! ## Henkin witnesses -/

/-- ⭐Every existential of a node's theory eventually has a witness. -/
theorem henk_ex {n : ℕ} {s : Node} (hs : (gnet hF M₀ n).Live s) {A : VarType}
    {ψ : WFF σ ((ctxOf ((gnet hF M₀ n).st s).l).insert (.bnd 0) A) 1}
    (hmem : WFF.ex A ψ ∈ ((gnet hF M₀ n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ (hle : (ctxOf ((gnet hF M₀ n).st s).l).Le (ctxOf ((gnet hF M₀ m).st s).l))
      (c : ℕ) (hc : (ctxOf ((gnet hF M₀ m).st s).l).ref (.root (.free c)) = some A),
      WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free c)) A hc)
        (WFF.mono (hle.insert _ A) ψ) ∈ ((gnet hF M₀ m).st s).M := by
  obtain ⟨m, hnm, hs'⟩ := gsched_after (σ := σ) (.inl (s, ⟨((gnet hF M₀ n).st s).l, .ex A ψ⟩)) n
  have hlm := gnet_live_mono hF hM₀ hnm hs
  have hsuf := gnet_lang_suffix hF hM₀ hnm hs
  have hg := (ext_gnet hF hM₀ hnm).grows s hs
  have hin : WFF.mono (ctxOf_le_of_suffix hsuf) (WFF.ex A ψ) ∈ ((gnet hF M₀ m).st s).M :=
    hg.sub _ hmem
  have hM := (good_gnet hF hM₀ m).mcs s hlm
  obtain ⟨hS, -⟩ := complete_spec (henkin_consistent hM.1 (Theory.Derives.of_mem hin)
    (ctxOf_fresh (l := ((gnet hF M₀ m).st s).l) le_rfl))
  have hst : (gnet hF M₀ (m + 1)).st s = ⟨A :: ((gnet hF M₀ m).st s).l, complete
      (WFF.mono (ctxOf_le_append [A] ((gnet hF M₀ m).st s).l) '' ((gnet hF M₀ m).st s).M ∪
        {WFF.openFree ((gnet hF M₀ m).st s).l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots
          (WFF.mono ((ctxOf_le_of_suffix hsuf).insert _ A) ψ)})⟩ := by
    rw [gnet_succ_of hF hs']
    simp only [GNetSt.applyOp, if_pos hlm, GNetSt.henk, dif_pos hsuf, if_pos hin]
    exact GNetSt.setSt_self _ _ _
  refine ⟨m + 1, by omega, ?_⟩
  rw [hst]
  refine ⟨(ctxOf_le_of_suffix hsuf).trans (ctxOf_le_append [A] _), _,
    Ctx.ref_insert_root _ _ A, ?_⟩
  refine hS (Or.inr ?_)
  rw [Set.mem_singleton_iff, ← WFF.instantiate_eta_openFree _ (ctxOf_fresh le_rfl)
    Ctx.NoSlots.slots Ctx.NoSlots.slots, WFF.mono_mono]

/-- ⭐Every failing universal of a node's theory eventually has a counter-instance. -/
theorem henk_negAll {n : ℕ} {s : Node} (hs : (gnet hF M₀ n).Live s) {A : VarType}
    {ψ : WFF σ ((ctxOf ((gnet hF M₀ n).st s).l).insert (.bnd 0) A) 1}
    (hmem : (WFF.all A ψ).neg ∈ ((gnet hF M₀ n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ (hle : (ctxOf ((gnet hF M₀ n).st s).l).Le (ctxOf ((gnet hF M₀ m).st s).l))
      (a : Ann A) (t : Term σ (ctxOf ((gnet hF M₀ m).st s).l) A a),
      (WFF.instantiate Ctx.NoSlots.slots t (WFF.mono (hle.insert _ A) ψ)).neg ∈
        ((gnet hF M₀ m).st s).M := by
  obtain ⟨m, hnm, hs'⟩ := gsched_after (σ := σ)
    (.inl (s, ⟨((gnet hF M₀ n).st s).l, .imp (.all A ψ) .bot⟩)) n
  have hlm := gnet_live_mono hF hM₀ hnm hs
  have hsuf := gnet_lang_suffix hF hM₀ hnm hs
  have hg := (ext_gnet hF hM₀ hnm).grows s hs
  have hin : WFF.mono (ctxOf_le_of_suffix hsuf) (.imp (.all A ψ) .bot) ∈
      ((gnet hF M₀ m).st s).M :=
    hg.sub _ hmem
  have hM := (good_gnet hF hM₀ m).mcs s hlm
  have hex : Theory.Derives ((gnet hF M₀ m).st s).M
      (.ex A (WFF.mono ((ctxOf_le_of_suffix hsuf).insert _ A) ψ).neg) :=
    ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hin, ⟨Proof.exNeg_of_negAll _⟩⟩
  obtain ⟨hS, -⟩ := complete_spec (henkin_consistent hM.1 hex
    (ctxOf_fresh (l := ((gnet hF M₀ m).st s).l) le_rfl))
  have hst : (gnet hF M₀ (m + 1)).st s = ⟨A :: ((gnet hF M₀ m).st s).l, complete
      (WFF.mono (ctxOf_le_append [A] ((gnet hF M₀ m).st s).l) '' ((gnet hF M₀ m).st s).M ∪
        {WFF.openFree ((gnet hF M₀ m).st s).l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots
          (WFF.mono ((ctxOf_le_of_suffix hsuf).insert _ A) ψ).neg})⟩ := by
    rw [gnet_succ_of hF hs']
    simp only [GNetSt.applyOp, if_pos hlm, GNetSt.henk, dif_pos hsuf, if_pos hin]
    exact GNetSt.setSt_self _ _ _
  refine ⟨m + 1, by omega, ?_⟩
  rw [hst]
  refine ⟨(ctxOf_le_of_suffix hsuf).trans (ctxOf_le_append [A] _), _,
    Term.eta (.root (.free ((gnet hF M₀ m).st s).l.length)) A (Ctx.ref_insert_root _ _ A), ?_⟩
  refine hS (Or.inr ?_)
  rw [Set.mem_singleton_iff, ← WFF.instantiate_eta_openFree _ (ctxOf_fresh le_rfl)
    Ctx.NoSlots.slots Ctx.NoSlots.slots]
  change _ = (WFF.instantiate _ _ (WFF.mono _ (WFF.mono _ ψ))).neg
  rw [WFF.mono_mono]

/-! ## Children -/

/-- ⭐Every failing `□φ` of a node's theory eventually has a child refuting `φ`. -/
theorem child_box {n : ℕ} {s : Node} (hs : (gnet hF M₀ n).Live s)
    {ψ : WFF σ (ctxOf ((gnet hF M₀ n).st s).l).boxIn 0}
    (hψ : WFF.box ψ ∉ ((gnet hF M₀ n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ (hsuf : ((gnet hF M₀ n).st s).l <:+ ((gnet hF M₀ m).st s).l)
      (M' : Set (WFF σ (ctxOf (childL ((gnet hF M₀ m).st s).l none .VTypeOne)) 0)),
      ¬ (gnet hF M₀ m).Live ((gnet hF M₀ m).nch s :: s) ∧
      (gnet hF M₀ (m + 1)).Live ((gnet hF M₀ m).nch s :: s) ∧
      (gnet hF M₀ (m + 1)).st ((gnet hF M₀ m).nch s :: s) =
        ⟨childL ((gnet hF M₀ m).st s).l none .VTypeOne, M'⟩ ∧
      (gnet hF M₀ (m + 1)).kind ((gnet hF M₀ m).nch s :: s) = none ∧
      (gnet hF M₀ (m + 1)).fcl ((gnet hF M₀ m).nch s :: s) = ((gnet hF M₀ m).st s).l ∧
      (gnet hF M₀ (m + 1)).fmap ((gnet hF M₀ m).nch s :: s) =
        ofRen (gchildMap ((gnet hF M₀ m).st s).l none) ∧
      gchildArrow hF ((gnet hF M₀ m).st s).l (kContent_none _ .VTypeOne)
        (WFF.mono (ctxOf_le_of_suffix hsuf).boxIn ψ).neg ∈ M' := by
  obtain ⟨m, hnm, hs'⟩ := gsched_after (σ := σ)
    (.inr (.inl (s, ⟨((gnet hF M₀ n).st s).l, .box ψ⟩))) n
  have hlm := gnet_live_mono hF hM₀ hnm hs
  have hsuf := gnet_lang_suffix hF hM₀ hnm hs
  have hg := (ext_gnet hF hM₀ hnm).grows s hs
  have hM := (good_gnet hF hM₀ m).mcs s hlm
  have hnin : WFF.mono (ctxOf_le_of_suffix hsuf) (.box ψ) ∉ ((gnet hF M₀ m).st s).M := fun h =>
    hψ (mem_of_mono_mem _ ((good_gnet hF hM₀ n).mcs s hs) hM hg.sub h)
  obtain ⟨hS, -⟩ := complete_spec (gchild_consistent hF hM (kContent_none _ .VTypeOne)
    (GNetSt.kDia_neg_of_not_box hM hnin))
  have hst : gnet hF M₀ (m + 1) = (gnet hF M₀ m).newChild s none
      ⟨childL ((gnet hF M₀ m).st s).l none .VTypeOne, complete
        (GNetSt.childSeed hF ((gnet hF M₀ m).st s).l ((gnet hF M₀ m).st s).M
          (kContent_none _ .VTypeOne) (WFF.mono (ctxOf_le_of_suffix hsuf).boxIn ψ).neg)⟩
      (ofRen (gchildMap ((gnet hF M₀ m).st s).l none)) := by
    rw [gnet_succ_of hF hs']
    simp only [GNetSt.applyOp, if_pos hlm, GNetSt.mkChild, dif_pos hsuf, if_neg hnin]
  refine ⟨m, hnm, hsuf, _, GNetSt.not_live_new s, ?_, ?_, ?_, ?_, ?_, hS (Or.inl rfl)⟩
  · rw [hst]
    exact (GNetSt.live_newChild hlm _ _ _ _).mpr (Or.inr rfl)
  all_goals rw [hst]; exact Function.update_self _ _ _

/-- ⭐Every true `◇_x φ` of a node's theory eventually has a child in the extent of `x` where
    `φ` holds. -/
theorem child_dia {n : ℕ} {s : Node} (hs : (gnet hF M₀ n).Live s) {x : VarSymb}
    {hx : ∃ X, (ctxOf ((gnet hF M₀ n).st s).l).ref x = some (.VTypeDia X)}
    {ψ : WFF σ ((ctxOf ((gnet hF M₀ n).st s).l).diaIn x) 0}
    (hψ : WFF.dia x hx ψ ∈ ((gnet hF M₀ n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ (hsuf : ((gnet hF M₀ n).st s).l <:+ ((gnet hF M₀ m).st s).l) (X : VarType)
      (hX : KContent (ctxOf ((gnet hF M₀ m).st s).l) (some x) X)
      (M' : Set (WFF σ (ctxOf (childL ((gnet hF M₀ m).st s).l (some x) X)) 0)),
      ¬ (gnet hF M₀ m).Live ((gnet hF M₀ m).nch s :: s) ∧
      (gnet hF M₀ (m + 1)).Live ((gnet hF M₀ m).nch s :: s) ∧
      (gnet hF M₀ (m + 1)).st ((gnet hF M₀ m).nch s :: s) =
        ⟨childL ((gnet hF M₀ m).st s).l (some x) X, M'⟩ ∧
      (gnet hF M₀ (m + 1)).kind ((gnet hF M₀ m).nch s :: s) = some x ∧
      (gnet hF M₀ (m + 1)).fcl ((gnet hF M₀ m).nch s :: s) = ((gnet hF M₀ m).st s).l ∧
      (gnet hF M₀ (m + 1)).fmap ((gnet hF M₀ m).nch s :: s) =
        ofRen (gchildMap ((gnet hF M₀ m).st s).l (some x)) ∧
      gchildArrow hF ((gnet hF M₀ m).st s).l hX
        (WFF.mono ((ctxOf_le_of_suffix hsuf).diaIn x) ψ) ∈ M' := by
  obtain ⟨m, hnm, hs'⟩ := gsched_after (σ := σ)
    (.inr (.inl (s, ⟨((gnet hF M₀ n).st s).l, .dia x hx ψ⟩))) n
  have hlm := gnet_live_mono hF hM₀ hnm hs
  have hsuf := gnet_lang_suffix hF hM₀ hnm hs
  have hg := (ext_gnet hF hM₀ hnm).grows s hs
  have hM := (good_gnet hF hM₀ m).mcs s hlm
  have hin : WFF.mono (ctxOf_le_of_suffix hsuf) (.dia x hx ψ) ∈ ((gnet hF M₀ m).st s).M :=
    hg.sub _ hψ
  obtain ⟨X, hX₀⟩ := hx
  have hX : (ctxOf ((gnet hF M₀ m).st s).l).ref x = some (.VTypeDia X) :=
    (ctxOf_le_of_suffix hsuf).ref hX₀
  have hk : KContent (ctxOf ((gnet hF M₀ m).st s).l) (some x) X := fun _ e => by
    cases e; exact hX
  obtain ⟨hS, -⟩ := complete_spec (gchild_consistent hF hM hk
    (φ := WFF.mono ((ctxOf_le_of_suffix hsuf).diaIn x) ψ) hin)
  have hst : gnet hF M₀ (m + 1) = (gnet hF M₀ m).newChild s (some x)
      ⟨childL ((gnet hF M₀ m).st s).l (some x) X, complete
        (GNetSt.childSeed hF ((gnet hF M₀ m).st s).l ((gnet hF M₀ m).st s).M hk
          (WFF.mono ((ctxOf_le_of_suffix hsuf).diaIn x) ψ))⟩
      (ofRen (gchildMap ((gnet hF M₀ m).st s).l (some x))) := by
    rw [gnet_succ_of hF hs']
    simp only [GNetSt.applyOp, if_pos hlm, GNetSt.mkChild, dif_pos hsuf, if_pos hin]
    split
    · rename_i X' hX'
      have e : X' = X := by
        rw [hX] at hX'
        exact (VarType.VTypeDia.inj (Option.some.inj hX')).symm
      subst e
      rfl
    · rename_i hne
      exact absurd hX (hne X)
  refine ⟨m, hnm, hsuf, X, hk, _, GNetSt.not_live_new s, ?_, ?_, ?_, ?_, ?_, hS (Or.inl rfl)⟩
  · rw [hst]
    exact (GNetSt.live_newChild hlm _ _ _ _).mpr (Or.inr rfl)
  all_goals rw [hst]; exact Function.update_self _ _ _

/-! ## Lifts -/

/-- ⭐**Every liftable term of a child is eventually lifted**: its parent gets a root `r` of the
    term's type, committed along the edge with `r.keep ↦` the term (weakened to the child's
    variables then). -/
theorem lift_total {n c : ℕ} {p : Node} (hk : (gnet hF M₀ n).Live (c :: p)) {T : VarType}
    {a : Ann T} (t : Term σ (ctxOf ((gnet hF M₀ n).st (c :: p)).l) T a)
    (hl : T.liftable = true) (hv : LiftAdm hF ⟨_, T, a, t⟩) :
    ∃ m, n ≤ m ∧
      ∃ (_ : ((gnet hF M₀ n).st (c :: p)).l <:+ ((gnet hF M₀ (m + 1)).st (c :: p)).l)
      (r : ℕ), r < ((gnet hF M₀ (m + 1)).fcl (c :: p)).length ∧
      rootTy ((gnet hF M₀ (m + 1)).st p).l r = T ∧
      ∃ (L : List VarType) (hL : ((gnet hF M₀ n).st (c :: p)).l <:+ L),
        (gnet hF M₀ (m + 1)).fmap (c :: p) (.step (.root (.free r)) .keep) =
          .inr ⟨L, T, a, Term.mono (ctxOf_le_of_suffix hL) t⟩ ∧
        L <:+ ((gnet hF M₀ (m + 1)).st (c :: p)).l := by
  obtain ⟨m, hnm, hs⟩ := gsched_after (σ := σ)
    (.inr (.inr (.inr (c :: p, ⟨_, T, a, t⟩)))) n
  have hlm := gnet_live_mono hF hM₀ hnm hk
  have hN := good_gnet hF hM₀ m
  obtain ⟨-, hk₁, he₁⟩ := hN.catchUp hF hlm
  have hcl := GNetSt.catchUp_full hF hN hlm
  have h₁ : ((gnet hF M₀ n).st (c :: p)).l <:+
      (((gnet hF M₀ m).catchUp hF (c :: p)).st (c :: p)).l :=
    ((ext_gnet hF hM₀ hnm).grows _ hk).suf.trans (he₁.grows _ hlm).suf
  have hst : gnet hF M₀ (m + 1) =
      ((gnet hF M₀ m).catchUp hF (c :: p)).lift hF (c :: p) ⟨_, T, a, t⟩ := by
    rw [gnet_succ_of hF hs]
    simp only [GNetSt.applyOp, if_pos hlm]
  have hgrow := ((ext_gnet hF hM₀ (Nat.le_succ m)).grows _ hlm).suf
  refine ⟨m, hnm, ((ext_gnet hF hM₀ (hnm.trans (Nat.le_succ m))).grows _ hk).suf,
    (((gnet hF M₀ m).catchUp hF (c :: p)).st p).l.length, ?_, ?_,
    (((gnet hF M₀ m).catchUp hF (c :: p)).st (c :: p)).l, h₁, ?_, ?_⟩
  · rw [hst, GNetSt.lift_spec hF hcl h₁ hl hv]
    simp only [GNetSt.setFwd, Function.update_self, List.length_cons]
    omega
  · rw [hst, GNetSt.lift_spec hF hcl h₁ hl hv]
    change rootTy ((((GNetSt.setSt _ p _).setSt (c :: p) _)).st p).l _ = T
    rw [GNetSt.setSt_ne _ _ (fun h => NetSt.ne_parent c p h.symm), GNetSt.setSt_self]
    exact rootTy_new T _
  · rw [hst, GNetSt.lift_spec hF hcl h₁ hl hv]
    simp only [GNetSt.setFwd, Function.update_self]
    exact gliftG_keep _ _ _ _ _
  · rw [hst, GNetSt.lift_spec hF hcl h₁ hl hv]
    change _ <:+ ((((GNetSt.setSt _ p _).setSt (c :: p) _)).st (c :: p)).l
    rw [GNetSt.setSt_self]
    exact List.suffix_cons _ _

end GArrow

end V12M
