import QML.QML_v12m_BNetMono

/-!
# QML v12m — B's arrow model: fairness

Every obligation of the chain is eventually met:

* ⭐`fwd_total`, ⭐`back_total`: every variable of a parent (of a child) eventually has an image
  in the child (in the parent);
* ⭐`henk_ex`, `henk_negAll`: every existential, and every failing universal, of a node's theory
  eventually has a witness;
* ⭐`child_box`, `child_dia`: every failing `□φ`, and every true `◇_x φ`, eventually has a child.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoTFour]
  (hB : ModalSys.B = true) {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}
  (hM₀ : Theory.IsMCS M₀)

include hB hM₀

omit hB hM₀ in
theorem net_succ (n : ℕ) : net M₀ (n + 1) = (net M₀ n).applyOp (sched n) := rfl

omit hB hM₀ in
theorem net_succ_of {n : ℕ} {o : Op σ} (h : sched n = o) :
    net M₀ (n + 1) = (net M₀ n).applyOp o := by
  rw [← h]
  rfl

theorem live_mono {n m : ℕ} (hnm : n ≤ m) {k : Node} (h : (net M₀ n).Live k) :
    (net M₀ m).Live k :=
  (ext_net hB hM₀ hnm).live k h

theorem lang_suffix {n m : ℕ} (hnm : n ≤ m) {k : Node} (h : (net M₀ n).Live k) :
    ((net M₀ n).st k).l <:+ ((net M₀ m).st k).l :=
  ((ext_net hB hM₀ hnm).grows k h).suf

/-! ## Forward and back totality -/

omit hB hM₀ [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem realF_fcl (N : NetSt σ) (c : ℕ) (p : Node) :
    (N.realF (c :: p)).fcl (c :: p) =
      if (N.fcl (c :: p)).length < (N.st p).l.length then
        nextTy (N.st p).l (N.fcl (c :: p)) :: N.fcl (c :: p)
      else N.fcl (c :: p) := by
  simp only [NetSt.realF]
  split_ifs
  · exact Function.update_self _ _ _
  · rfl

omit hB hM₀ [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem realB_bcl (N : NetSt σ) (c : ℕ) (p : Node) :
    (N.realB (c :: p)).bcl (c :: p) =
      if (N.bcl (c :: p)).length < (N.st (c :: p)).l.length then
        nextTy (N.st (c :: p)).l (N.bcl (c :: p)) :: N.bcl (c :: p)
      else N.bcl (c :: p) := by
  simp only [NetSt.realB]
  split_ifs
  · exact Function.update_self _ _ _
  · rfl

/-- ⭐Every variable of a parent eventually has an image in a child. -/
theorem fwd_total {n c : ℕ} {p : Node} (hk : (net M₀ n).Live (c :: p)) {r : ℕ}
    (hr : r < ((net M₀ n).st p).l.length) :
    ∃ m, n ≤ m ∧ r < ((net M₀ m).fcl (c :: p)).length := by
  have key : ∀ j, ∃ m, n ≤ m ∧ min j (r + 1) ≤ ((net M₀ m).fcl (c :: p)).length := by
    intro j
    induction j with
    | zero => exact ⟨n, le_rfl, by simp⟩
    | succ j ih =>
        obtain ⟨m, hnm, hm⟩ := ih
        by_cases hdone : r + 1 ≤ ((net M₀ m).fcl (c :: p)).length
        · exact ⟨m, hnm, (min_le_right _ _).trans hdone⟩
        obtain ⟨m', hm'm, hs⟩ := sched_after (σ := σ) (.inr (.inr (.inl (c :: p)))) m
        have hlm' := live_mono hB hM₀ (hnm.trans hm'm) hk
        have hmono : ((net M₀ m).fcl (c :: p)).length ≤ ((net M₀ m').fcl (c :: p)).length :=
          ((ext_net hB hM₀ hm'm).fcl _ (live_mono hB hM₀ hnm hk)).length_le
        by_cases hdone' : r + 1 ≤ ((net M₀ m').fcl (c :: p)).length
        · exact ⟨m', hnm.trans hm'm, (min_le_right _ _).trans hdone'⟩
        have hlp : ((net M₀ n).st p).l.length ≤ ((net M₀ m').st p).l.length :=
          (lang_suffix hB hM₀ (hnm.trans hm'm) hk.1).length_le
        have hlt : ((net M₀ m').fcl (c :: p)).length < ((net M₀ m').st p).l.length := by omega
        refine ⟨m' + 1, by omega, ?_⟩
        rw [net_succ_of hs]
        simp only [NetSt.applyOp, if_pos hlm']
        rw [realF_fcl, if_pos hlt, List.length_cons]
        omega
  obtain ⟨m, hnm, hm⟩ := key (r + 1)
  exact ⟨m, hnm, by simp at hm; omega⟩

/-- ⭐Every variable of a child eventually has an image in its parent. -/
theorem back_total {n c : ℕ} {p : Node} (hk : (net M₀ n).Live (c :: p)) {r : ℕ}
    (hr : r < ((net M₀ n).st (c :: p)).l.length) :
    ∃ m, n ≤ m ∧ r < ((net M₀ m).bcl (c :: p)).length := by
  have key : ∀ j, ∃ m, n ≤ m ∧ min j (r + 1) ≤ ((net M₀ m).bcl (c :: p)).length := by
    intro j
    induction j with
    | zero => exact ⟨n, le_rfl, by simp⟩
    | succ j ih =>
        obtain ⟨m, hnm, hm⟩ := ih
        by_cases hdone : r + 1 ≤ ((net M₀ m).bcl (c :: p)).length
        · exact ⟨m, hnm, (min_le_right _ _).trans hdone⟩
        obtain ⟨m', hm'm, hs⟩ := sched_after (σ := σ) (.inr (.inr (.inr (c :: p)))) m
        have hlm' := live_mono hB hM₀ (hnm.trans hm'm) hk
        have hmono : ((net M₀ m).bcl (c :: p)).length ≤ ((net M₀ m').bcl (c :: p)).length :=
          ((ext_net hB hM₀ hm'm).bcl _ (live_mono hB hM₀ hnm hk)).length_le
        by_cases hdone' : r + 1 ≤ ((net M₀ m').bcl (c :: p)).length
        · exact ⟨m', hnm.trans hm'm, (min_le_right _ _).trans hdone'⟩
        have hlk : ((net M₀ n).st (c :: p)).l.length ≤ ((net M₀ m').st (c :: p)).l.length :=
          (lang_suffix hB hM₀ (hnm.trans hm'm) hk).length_le
        have hlt : ((net M₀ m').bcl (c :: p)).length < ((net M₀ m').st (c :: p)).l.length := by
          omega
        refine ⟨m' + 1, by omega, ?_⟩
        rw [net_succ_of hs]
        simp only [NetSt.applyOp, if_pos hlm']
        rw [realB_bcl, if_pos hlt, List.length_cons]
        omega
  obtain ⟨m, hnm, hm⟩ := key (r + 1)
  exact ⟨m, hnm, by simp at hm; omega⟩

/-! ## Henkin witnesses -/

/-- ⭐Every existential of a node's theory eventually has a witness. -/
theorem henk_ex {n : ℕ} {s : Node} (hs : (net M₀ n).Live s) {A : VarType}
    {ψ : WFF σ ((ctxOf ((net M₀ n).st s).l).insert (.bnd 0) A) 1}
    (hmem : WFF.ex A ψ ∈ ((net M₀ n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ (hle : (ctxOf ((net M₀ n).st s).l).Le (ctxOf ((net M₀ m).st s).l))
      (a : Ann A) (t : Term σ (ctxOf ((net M₀ m).st s).l) A a),
      WFF.instantiate Ctx.NoSlots.slots t (WFF.mono (hle.insert _ A) ψ) ∈ ((net M₀ m).st s).M := by
  obtain ⟨m, hnm, hsch⟩ := sched_after (σ := σ) (.inl (s, ⟨((net M₀ n).st s).l, .ex A ψ⟩)) n
  have hlm := live_mono hB hM₀ hnm hs
  have hsuf := lang_suffix hB hM₀ hnm hs
  have hg := (ext_net hB hM₀ hnm).grows s hs
  have hin : WFF.mono (ctxOf_le_of_suffix hsuf) (WFF.ex A ψ) ∈ ((net M₀ m).st s).M := hg.sub _ hmem
  have hM := (good_net hB hM₀ m).mcs s hlm
  obtain ⟨hS, -⟩ := complete_spec (henkin_consistent hM.1 (Theory.Derives.of_mem hin)
    (ctxOf_fresh (l := ((net M₀ m).st s).l) le_rfl))
  have hst : (net M₀ (m + 1)).st s = ⟨A :: ((net M₀ m).st s).l, complete
      (WFF.mono (ctxOf_le_append [A] ((net M₀ m).st s).l) '' ((net M₀ m).st s).M ∪
        {WFF.openFree ((net M₀ m).st s).l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots
          (WFF.mono ((ctxOf_le_of_suffix hsuf).insert _ A) ψ)})⟩ := by
    rw [net_succ_of hsch]
    simp only [NetSt.applyOp, if_pos hlm, NetSt.henk, dif_pos hsuf, if_pos hin]
    exact NetSt.setSt_self _ _ _
  refine ⟨m + 1, by omega, ?_⟩
  rw [hst]
  refine ⟨(ctxOf_le_of_suffix hsuf).trans (ctxOf_le_append [A] _), _,
    Term.eta (.root (.free ((net M₀ m).st s).l.length)) A (Ctx.ref_insert_root _ _ A), ?_⟩
  refine hS (Or.inr ?_)
  rw [Set.mem_singleton_iff, ← WFF.instantiate_eta_openFree _ (ctxOf_fresh le_rfl)
    Ctx.NoSlots.slots Ctx.NoSlots.slots, WFF.mono_mono]

/-- ⭐Every failing universal of a node's theory eventually has a counter-instance. -/
theorem henk_negAll {n : ℕ} {s : Node} (hs : (net M₀ n).Live s) {A : VarType}
    {ψ : WFF σ ((ctxOf ((net M₀ n).st s).l).insert (.bnd 0) A) 1}
    (hmem : (WFF.all A ψ).neg ∈ ((net M₀ n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ (hle : (ctxOf ((net M₀ n).st s).l).Le (ctxOf ((net M₀ m).st s).l))
      (a : Ann A) (t : Term σ (ctxOf ((net M₀ m).st s).l) A a),
      (WFF.instantiate Ctx.NoSlots.slots t (WFF.mono (hle.insert _ A) ψ)).neg ∈
        ((net M₀ m).st s).M := by
  obtain ⟨m, hnm, hsch⟩ :=
    sched_after (σ := σ) (.inl (s, ⟨((net M₀ n).st s).l, .imp (.all A ψ) .bot⟩)) n
  have hlm := live_mono hB hM₀ hnm hs
  have hsuf := lang_suffix hB hM₀ hnm hs
  have hg := (ext_net hB hM₀ hnm).grows s hs
  have hin : WFF.mono (ctxOf_le_of_suffix hsuf) (.imp (.all A ψ) .bot) ∈ ((net M₀ m).st s).M :=
    hg.sub _ hmem
  have hM := (good_net hB hM₀ m).mcs s hlm
  have hex : Theory.Derives ((net M₀ m).st s).M
      (.ex A (WFF.mono ((ctxOf_le_of_suffix hsuf).insert _ A) ψ).neg) :=
    ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hin, ⟨Proof.exNeg_of_negAll _⟩⟩
  obtain ⟨hS, -⟩ := complete_spec (henkin_consistent hM.1 hex
    (ctxOf_fresh (l := ((net M₀ m).st s).l) le_rfl))
  have hst : (net M₀ (m + 1)).st s = ⟨A :: ((net M₀ m).st s).l, complete
      (WFF.mono (ctxOf_le_append [A] ((net M₀ m).st s).l) '' ((net M₀ m).st s).M ∪
        {WFF.openFree ((net M₀ m).st s).l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots
          (WFF.mono ((ctxOf_le_of_suffix hsuf).insert _ A) ψ).neg})⟩ := by
    rw [net_succ_of hsch]
    simp only [NetSt.applyOp, if_pos hlm, NetSt.henk, dif_pos hsuf, if_pos hin]
    exact NetSt.setSt_self _ _ _
  refine ⟨m + 1, by omega, ?_⟩
  rw [hst]
  refine ⟨(ctxOf_le_of_suffix hsuf).trans (ctxOf_le_append [A] _), _,
    Term.eta (.root (.free ((net M₀ m).st s).l.length)) A (Ctx.ref_insert_root _ _ A), ?_⟩
  refine hS (Or.inr ?_)
  rw [Set.mem_singleton_iff, ← WFF.instantiate_eta_openFree _ (ctxOf_fresh le_rfl)
    Ctx.NoSlots.slots Ctx.NoSlots.slots]
  change _ = (WFF.instantiate _ _ (WFF.mono _ (WFF.mono _ ψ))).neg
  rw [WFF.mono_mono]

/-! ## Children -/

omit hB hM₀ [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoTFour] in
theorem newChild_st (N : NetSt σ) (s : Node) (kd : Option (VarSymb × VarType)) (cx : ℕ)
    (t : NodeSt σ) : (N.newChild s kd cx t).st (N.nch s :: s) = t :=
  Function.update_self _ _ _

/-- ⭐Every failing `□φ` of a node's theory eventually has a child refuting `φ`. -/
theorem child_box {n : ℕ} {s : Node} (hs : (net M₀ n).Live s)
    {ψ : WFF σ (ctxOf ((net M₀ n).st s).l).boxIn 0} (hψ : WFF.box ψ ∉ ((net M₀ n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ (hsuf : ((net M₀ n).st s).l <:+ ((net M₀ m).st s).l)
      (M' : Set (WFF σ (ctxOf (((net M₀ m).st s).l.map VarType.bc)) 0)),
      ¬ (net M₀ m).Live ((net M₀ m).nch s :: s) ∧
      (net M₀ (m + 1)).Live ((net M₀ m).nch s :: s) ∧
      (net M₀ (m + 1)).st ((net M₀ m).nch s :: s) = ⟨((net M₀ m).st s).l.map VarType.bc, M'⟩ ∧
      (net M₀ (m + 1)).kind ((net M₀ m).nch s :: s) = none ∧
      (net M₀ (m + 1)).fcl ((net M₀ m).nch s :: s) = ((net M₀ m).st s).l ∧
      (net M₀ (m + 1)).fimg ((net M₀ m).nch s :: s) = id ∧
      (childArrow ((net M₀ m).st s).l (WFF.mono (ctxOf_le_of_suffix hsuf).boxIn ψ)).neg ∈ M' := by
  obtain ⟨m, hnm, hsch⟩ := sched_after (σ := σ) (.inr (.inl (s, ⟨((net M₀ n).st s).l, .box ψ⟩))) n
  have hlm := live_mono hB hM₀ hnm hs
  have hsuf := lang_suffix hB hM₀ hnm hs
  have hg := (ext_net hB hM₀ hnm).grows s hs
  have hM := (good_net hB hM₀ m).mcs s hlm
  have hnin : WFF.mono (ctxOf_le_of_suffix hsuf) (.box ψ) ∉ ((net M₀ m).st s).M := fun h =>
    hψ (mem_of_mono_mem _ ((good_net hB hM₀ n).mcs s hs) hM hg.sub h)
  obtain ⟨hS, -⟩ := complete_spec (child_consistent hM
    (φ := WFF.mono (ctxOf_le_of_suffix hsuf).boxIn ψ) hnin)
  have hstep : net M₀ (m + 1) = (net M₀ m).newChild s none 0
      ⟨((net M₀ m).st s).l.map VarType.bc, complete
        ({(childArrow ((net M₀ m).st s).l (WFF.mono (ctxOf_le_of_suffix hsuf).boxIn ψ)).neg} ∪
          {χ | ∃ ψ', WFF.mono (Ctx.Le.refl _) (.box ψ') ∈ ((net M₀ m).st s).M ∧
            χ = childArrow ((net M₀ m).st s).l ψ'})⟩ := by
    rw [net_succ_of hsch]
    simp only [NetSt.applyOp, if_pos hlm, NetSt.mkChild, dif_pos hsuf, if_neg hnin]
  refine ⟨m, hnm, hsuf, _, NetSt.not_live_new s, ?_, ?_, ?_, ?_, ?_, hS (Or.inl rfl)⟩
  · rw [hstep]
    exact (NetSt.live_newChild hlm _ _ _ _).mpr (Or.inr rfl)
  · rw [hstep]
    exact newChild_st _ _ _ _ _
  · rw [hstep]
    exact Function.update_self _ _ _
  · rw [hstep]
    exact Function.update_self _ _ _
  · rw [hstep]
    exact Function.update_self _ _ _

/-- ⭐Every true `◇_x φ` of a node's theory eventually has a child in the extent of `x` where
    `φ` holds. -/
theorem child_dia {n : ℕ} {s : Node} (hs : (net M₀ n).Live s) {x : VarSymb}
    {hx : ∃ X, (ctxOf ((net M₀ n).st s).l).ref x = some (.VTypeDia X)}
    {ψ : WFF σ ((ctxOf ((net M₀ n).st s).l).diaIn x) 0}
    (hψ : WFF.dia x hx ψ ∈ ((net M₀ n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ (hsuf : ((net M₀ n).st s).l <:+ ((net M₀ m).st s).l) (X : VarType)
      (hX : (ctxOf ((net M₀ m).st s).l).ref x = some (.VTypeDia X))
      (M' : Set (WFF σ (ctxOf (X :: ((net M₀ m).st s).l.map VarType.bc)) 0)),
      ¬ (net M₀ m).Live ((net M₀ m).nch s :: s) ∧
      (net M₀ (m + 1)).Live ((net M₀ m).nch s :: s) ∧
      (net M₀ (m + 1)).st ((net M₀ m).nch s :: s) =
        ⟨X :: ((net M₀ m).st s).l.map VarType.bc, M'⟩ ∧
      (net M₀ (m + 1)).kind ((net M₀ m).nch s :: s) = some (x, X) ∧
      (net M₀ (m + 1)).cx ((net M₀ m).nch s :: s) = ((net M₀ m).st s).l.length ∧
      (net M₀ (m + 1)).fcl ((net M₀ m).nch s :: s) = ((net M₀ m).st s).l ∧
      (net M₀ (m + 1)).fimg ((net M₀ m).nch s :: s) = id ∧
      childXArrow ((net M₀ m).st s).l hX (WFF.mono ((ctxOf_le_of_suffix hsuf).diaIn x) ψ) ∈ M' := by
  obtain ⟨m, hnm, hsch⟩ :=
    sched_after (σ := σ) (.inr (.inl (s, ⟨((net M₀ n).st s).l, .dia x hx ψ⟩))) n
  have hlm := live_mono hB hM₀ hnm hs
  have hsuf := lang_suffix hB hM₀ hnm hs
  have hg := (ext_net hB hM₀ hnm).grows s hs
  have hM := (good_net hB hM₀ m).mcs s hlm
  have hin : WFF.mono (ctxOf_le_of_suffix hsuf) (.dia x hx ψ) ∈ ((net M₀ m).st s).M := hg.sub _ hψ
  obtain ⟨X, hX₀⟩ := hx
  have hX : (ctxOf ((net M₀ m).st s).l).ref x = some (.VTypeDia X) :=
    (ctxOf_le_of_suffix hsuf).ref hX₀
  obtain ⟨hS, -⟩ := complete_spec (childX_consistent hM hX
    (φ := WFF.mono ((ctxOf_le_of_suffix hsuf).diaIn x) ψ) hin)
  have hstep : net M₀ (m + 1) = (net M₀ m).newChild s (some (x, X)) ((net M₀ m).st s).l.length
      ⟨X :: ((net M₀ m).st s).l.map VarType.bc, complete
        ({childXArrow ((net M₀ m).st s).l hX (WFF.mono ((ctxOf_le_of_suffix hsuf).diaIn x) ψ)} ∪
          {χ | ∃ ψ', WFF.mono (Ctx.Le.refl _) (WFF.boxx x ⟨X, hX⟩ ψ') ∈ ((net M₀ m).st s).M ∧
            χ = childXArrow ((net M₀ m).st s).l hX ψ'})⟩ := by
    rw [net_succ_of hsch]
    simp only [NetSt.applyOp, if_pos hlm, NetSt.mkChild, dif_pos hsuf, if_pos hin]
    split
    · rename_i X' hX'
      have e : X' = X := by
        rw [hX] at hX'
        exact (VarType.VTypeDia.inj (Option.some.inj hX')).symm
      subst e
      rfl
    · rename_i hne
      exact absurd hX (hne X)
  refine ⟨m, hnm, hsuf, X, hX, _, NetSt.not_live_new s, ?_, ?_, ?_, ?_, ?_, ?_, hS (Or.inl rfl)⟩
  · rw [hstep]
    exact (NetSt.live_newChild hlm _ _ _ _).mpr (Or.inr rfl)
  · rw [hstep]
    exact newChild_st _ _ _ _ _
  · rw [hstep]
    exact Function.update_self _ _ _
  · rw [hstep]
    exact Function.update_self _ _ _
  · rw [hstep]
    exact Function.update_self _ _ _
  · rw [hstep]
    exact Function.update_self _ _ _

end BArrow

end V12M
