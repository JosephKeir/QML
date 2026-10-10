import QML.QML_v12m_BNetInj

/-!
# QML v12m — B's arrow model: fairness

What the limit needs of a chain of networks (`FairChain`): every network is good, later ones
extend earlier ones, and every obligation is eventually met —

* ⭐`fwd_total`, ⭐`back_total`: every variable of a parent (of a child) eventually has an image
  in the child (in the parent);
* ⭐`henk_ex`, `henk_negAll`: every existential, and every failing universal, of a node's theory
  eventually has a witness;
* ⭐`child_box`, `child_dia`: every failing `□φ`, and every true `◇_x φ`, eventually has a child.

They are proved once for any chain whose rounds perform every Henkin step, child creation and
realisation step infinitely often (`OpChain`, ⭐`OpChain.toFair`); weak B's chain is one
(`weakChain`), and strong B's another (`QML_v12m_BFairS`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour] {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-! ## Fair chains -/

/-- ⭐**What the limit needs of a chain of networks** from a root theory `M₀`. -/
structure FairChain (M₀ : Set (WFF σ (ctxOf l₀) 0)) where
  net : ℕ → NetSt σ
  zero : net 0 = NetSt.init M₀
  good : ∀ n, (net n).Good
  /-- Every arrow's images are injective (`NetSt.InjOk`): the T-free decoder's `ImgInj`. -/
  inj : ∀ n, (net n).InjOk
  ext : ∀ {n m : ℕ}, n ≤ m → NetSt.Ext (net n) (net m)
  fwd_total : ∀ {n c : ℕ} {p : Node}, (net n).Live (c :: p) → ∀ {r : ℕ},
    r < ((net n).st p).l.length → ∃ m, n ≤ m ∧ r < ((net m).fcl (c :: p)).length
  back_total : ∀ {n c : ℕ} {p : Node}, (net n).Live (c :: p) → ∀ {r : ℕ},
    r < ((net n).st (c :: p)).l.length → ∃ m, n ≤ m ∧ r < ((net m).bcl (c :: p)).length
  henk_ex : ∀ {n : ℕ} {s : Node}, (net n).Live s → ∀ {A : VarType}
    {ψ : WFF σ ((ctxOf ((net n).st s).l).insert (.bnd 0) A) 1},
    WFF.ex A ψ ∈ ((net n).st s).M →
    ∃ m, n ≤ m ∧ ∃ (hle : (ctxOf ((net n).st s).l).Le (ctxOf ((net m).st s).l))
      (c : ℕ) (hc : (ctxOf ((net m).st s).l).ref (.root (.free c)) = some A),
      WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free c)) A hc)
        (WFF.mono (hle.insert _ A) ψ) ∈ ((net m).st s).M
  henk_negAll : ∀ {n : ℕ} {s : Node}, (net n).Live s → ∀ {A : VarType}
    {ψ : WFF σ ((ctxOf ((net n).st s).l).insert (.bnd 0) A) 1},
    (WFF.all A ψ).neg ∈ ((net n).st s).M →
    ∃ m, n ≤ m ∧ ∃ (hle : (ctxOf ((net n).st s).l).Le (ctxOf ((net m).st s).l))
      (a : Ann A) (t : Term σ (ctxOf ((net m).st s).l) A a),
      (WFF.instantiate Ctx.NoSlots.slots t (WFF.mono (hle.insert _ A) ψ)).neg ∈
        ((net m).st s).M
  child_box : ∀ {n : ℕ} {s : Node}, (net n).Live s →
    ∀ {ψ : WFF σ (ctxOf ((net n).st s).l).boxIn 0}, WFF.box ψ ∉ ((net n).st s).M →
    ∃ m, n ≤ m ∧ ∃ (hsuf : ((net n).st s).l <:+ ((net m).st s).l)
      (M' : Set (WFF σ (ctxOf (((net m).st s).l.map VarType.bc)) 0)),
      ¬ (net m).Live ((net m).nch s :: s) ∧
      (net (m + 1)).Live ((net m).nch s :: s) ∧
      (net (m + 1)).st ((net m).nch s :: s) = ⟨((net m).st s).l.map VarType.bc, M'⟩ ∧
      (net (m + 1)).kind ((net m).nch s :: s) = none ∧
      (net (m + 1)).fcl ((net m).nch s :: s) = ((net m).st s).l ∧
      (net (m + 1)).fimg ((net m).nch s :: s) = id ∧
      (childArrow ((net m).st s).l (WFF.mono (ctxOf_le_of_suffix hsuf).boxIn ψ)).neg ∈ M'
  child_dia : ∀ {n : ℕ} {s : Node}, (net n).Live s → ∀ {x : VarSymb}
    {hx : ∃ X, (ctxOf ((net n).st s).l).ref x = some (.VTypeDia X)}
    {ψ : WFF σ ((ctxOf ((net n).st s).l).diaIn x) 0},
    WFF.dia x hx ψ ∈ ((net n).st s).M →
    ∃ m, n ≤ m ∧ ∃ (hsuf : ((net n).st s).l <:+ ((net m).st s).l) (X : VarType)
      (hX : (ctxOf ((net m).st s).l).ref x = some (.VTypeDia X))
      (M' : Set (WFF σ (ctxOf (X :: ((net m).st s).l.map VarType.bc)) 0)),
      ¬ (net m).Live ((net m).nch s :: s) ∧
      (net (m + 1)).Live ((net m).nch s :: s) ∧
      (net (m + 1)).st ((net m).nch s :: s) =
        ⟨X :: ((net m).st s).l.map VarType.bc, M'⟩ ∧
      (net (m + 1)).kind ((net m).nch s :: s) = some (x, X) ∧
      (net (m + 1)).cx ((net m).nch s :: s) = ((net m).st s).l.length ∧
      (net (m + 1)).fcl ((net m).nch s :: s) = ((net m).st s).l ∧
      (net (m + 1)).fimg ((net m).nch s :: s) = id ∧
      childXArrow ((net m).st s).l hX (WFF.mono ((ctxOf_le_of_suffix hsuf).diaIn x) ψ) ∈ M'

namespace FairChain

variable (C : FairChain M₀)

theorem live_mono {n m : ℕ} (hnm : n ≤ m) {k : Node} (h : (C.net n).Live k) :
    (C.net m).Live k :=
  (C.ext hnm).live k h

theorem lang_suffix {n m : ℕ} (hnm : n ≤ m) {k : Node} (h : (C.net n).Live k) :
    ((C.net n).st k).l <:+ ((C.net m).st k).l :=
  ((C.ext hnm).grows k h).suf

end FairChain

/-! ## The steps -/

theorem realF_fcl (N : NetSt σ) (c : ℕ) (p : Node) :
    (N.realF (c :: p)).fcl (c :: p) =
      if (N.fcl (c :: p)).length < (N.st p).l.length then
        nextTy (N.st p).l (N.fcl (c :: p)) :: N.fcl (c :: p)
      else N.fcl (c :: p) := by
  simp only [NetSt.realF]
  split_ifs
  · exact Function.update_self _ _ _
  · rfl

theorem realB_bcl (N : NetSt σ) (c : ℕ) (p : Node) :
    (N.realB (c :: p)).bcl (c :: p) =
      if (N.bcl (c :: p)).length < (N.st (c :: p)).l.length then
        nextTy (N.st (c :: p)).l (N.bcl (c :: p)) :: N.bcl (c :: p)
      else N.bcl (c :: p) := by
  simp only [NetSt.realB]
  split_ifs
  · exact Function.update_self _ _ _
  · rfl

omit [ModalSys.NoFour] in
theorem newChild_st (N : NetSt σ) (s : Node) (kd : Option (VarSymb × VarType)) (cx : ℕ)
    (t : NodeSt σ) : (N.newChild s kd cx t).st (N.nch s :: s) = t :=
  Function.update_self _ _ _

/-! ## Chains of operations -/

/-- ⭐**A chain whose rounds perform every step infinitely often**: from any round on, each Henkin
    step and each child creation at a node, and each realisation step forward and back along a
    child's arrows, is performed at some later round (if its node is alive then). -/
structure OpChain (M₀ : Set (WFF σ (ctxOf l₀) 0)) where
  net : ℕ → NetSt σ
  zero : net 0 = NetSt.init M₀
  good : ∀ n, (net n).Good
  inj : ∀ n, (net n).InjOk
  ext : ∀ {n m : ℕ}, n ≤ m → NetSt.Ext (net n) (net m)
  henk : ∀ (s : Node) (o : Obl σ) (m : ℕ), ∃ n, m ≤ n ∧
    ((net n).Live s → net (n + 1) = (net n).henk s o)
  child : ∀ (s : Node) (o : Obl σ) (m : ℕ), ∃ n, m ≤ n ∧
    ((net n).Live s → net (n + 1) = (net n).mkChild s o)
  fwd : ∀ (c : ℕ) (p : Node) (m : ℕ), ∃ n, m ≤ n ∧ ((net n).Live (c :: p) →
    (net (n + 1)).fcl (c :: p) =
      if ((net n).fcl (c :: p)).length < ((net n).st p).l.length then
        nextTy ((net n).st p).l ((net n).fcl (c :: p)) :: (net n).fcl (c :: p)
      else (net n).fcl (c :: p))
  back : ∀ (c : ℕ) (p : Node) (m : ℕ), ∃ n, m ≤ n ∧ ((net n).Live (c :: p) →
    (net (n + 1)).bcl (c :: p) =
      if ((net n).bcl (c :: p)).length < ((net n).st (c :: p)).l.length then
        nextTy ((net n).st (c :: p)).l ((net n).bcl (c :: p)) :: (net n).bcl (c :: p)
      else (net n).bcl (c :: p))

namespace OpChain

variable (C : OpChain M₀)

theorem live_mono {n m : ℕ} (hnm : n ≤ m) {k : Node} (h : (C.net n).Live k) :
    (C.net m).Live k :=
  (C.ext hnm).live k h

theorem lang_suffix {n m : ℕ} (hnm : n ≤ m) {k : Node} (h : (C.net n).Live k) :
    ((C.net n).st k).l <:+ ((C.net m).st k).l :=
  ((C.ext hnm).grows k h).suf

/-! ### Forward and back totality -/

/-- ⭐Every variable of a parent eventually has an image in a child. -/
theorem fwd_total {n c : ℕ} {p : Node} (hk : (C.net n).Live (c :: p)) {r : ℕ}
    (hr : r < ((C.net n).st p).l.length) :
    ∃ m, n ≤ m ∧ r < ((C.net m).fcl (c :: p)).length := by
  have key : ∀ j, ∃ m, n ≤ m ∧ min j (r + 1) ≤ ((C.net m).fcl (c :: p)).length := by
    intro j
    induction j with
    | zero => exact ⟨n, le_rfl, by simp⟩
    | succ j ih =>
        obtain ⟨m, hnm, hm⟩ := ih
        by_cases hdone : r + 1 ≤ ((C.net m).fcl (c :: p)).length
        · exact ⟨m, hnm, (min_le_right _ _).trans hdone⟩
        obtain ⟨m', hm'm, hstep⟩ := C.fwd c p m
        have hlm' := C.live_mono (hnm.trans hm'm) hk
        have hmono : ((C.net m).fcl (c :: p)).length ≤ ((C.net m').fcl (c :: p)).length :=
          ((C.ext hm'm).fcl _ (C.live_mono hnm hk)).length_le
        by_cases hdone' : r + 1 ≤ ((C.net m').fcl (c :: p)).length
        · exact ⟨m', hnm.trans hm'm, (min_le_right _ _).trans hdone'⟩
        have hlp : ((C.net n).st p).l.length ≤ ((C.net m').st p).l.length :=
          (C.lang_suffix (hnm.trans hm'm) hk.1).length_le
        have hlt : ((C.net m').fcl (c :: p)).length < ((C.net m').st p).l.length := by omega
        refine ⟨m' + 1, by omega, ?_⟩
        rw [hstep hlm', if_pos hlt, List.length_cons]
        omega
  obtain ⟨m, hnm, hm⟩ := key (r + 1)
  exact ⟨m, hnm, by simp at hm; omega⟩

/-- ⭐Every variable of a child eventually has an image in its parent. -/
theorem back_total {n c : ℕ} {p : Node} (hk : (C.net n).Live (c :: p)) {r : ℕ}
    (hr : r < ((C.net n).st (c :: p)).l.length) :
    ∃ m, n ≤ m ∧ r < ((C.net m).bcl (c :: p)).length := by
  have key : ∀ j, ∃ m, n ≤ m ∧ min j (r + 1) ≤ ((C.net m).bcl (c :: p)).length := by
    intro j
    induction j with
    | zero => exact ⟨n, le_rfl, by simp⟩
    | succ j ih =>
        obtain ⟨m, hnm, hm⟩ := ih
        by_cases hdone : r + 1 ≤ ((C.net m).bcl (c :: p)).length
        · exact ⟨m, hnm, (min_le_right _ _).trans hdone⟩
        obtain ⟨m', hm'm, hstep⟩ := C.back c p m
        have hlm' := C.live_mono (hnm.trans hm'm) hk
        have hmono : ((C.net m).bcl (c :: p)).length ≤ ((C.net m').bcl (c :: p)).length :=
          ((C.ext hm'm).bcl _ (C.live_mono hnm hk)).length_le
        by_cases hdone' : r + 1 ≤ ((C.net m').bcl (c :: p)).length
        · exact ⟨m', hnm.trans hm'm, (min_le_right _ _).trans hdone'⟩
        have hlk : ((C.net n).st (c :: p)).l.length ≤ ((C.net m').st (c :: p)).l.length :=
          (C.lang_suffix (hnm.trans hm'm) hk).length_le
        have hlt : ((C.net m').bcl (c :: p)).length < ((C.net m').st (c :: p)).l.length := by
          omega
        refine ⟨m' + 1, by omega, ?_⟩
        rw [hstep hlm', if_pos hlt, List.length_cons]
        omega
  obtain ⟨m, hnm, hm⟩ := key (r + 1)
  exact ⟨m, hnm, by simp at hm; omega⟩

/-! ### Henkin witnesses -/

/-- ⭐Every existential of a node's theory eventually has a witness. -/
theorem henk_ex {n : ℕ} {s : Node} (hs : (C.net n).Live s) {A : VarType}
    {ψ : WFF σ ((ctxOf ((C.net n).st s).l).insert (.bnd 0) A) 1}
    (hmem : WFF.ex A ψ ∈ ((C.net n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ (hle : (ctxOf ((C.net n).st s).l).Le (ctxOf ((C.net m).st s).l))
      (c : ℕ) (hc : (ctxOf ((C.net m).st s).l).ref (.root (.free c)) = some A),
      WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free c)) A hc)
        (WFF.mono (hle.insert _ A) ψ) ∈ ((C.net m).st s).M := by
  obtain ⟨m, hnm, hstep⟩ := C.henk s ⟨((C.net n).st s).l, .ex A ψ⟩ n
  have hlm := C.live_mono hnm hs
  have hsuf := C.lang_suffix hnm hs
  have hg := (C.ext hnm).grows s hs
  have hin : WFF.mono (ctxOf_le_of_suffix hsuf) (WFF.ex A ψ) ∈ ((C.net m).st s).M :=
    hg.sub _ hmem
  have hM := (C.good m).mcs s hlm
  obtain ⟨hS, -⟩ := complete_spec (henkin_consistent hM.1 (Theory.Derives.of_mem hin)
    (ctxOf_fresh (l := ((C.net m).st s).l) le_rfl))
  have hst : (C.net (m + 1)).st s = ⟨A :: ((C.net m).st s).l, complete
      (WFF.mono (ctxOf_le_append [A] ((C.net m).st s).l) '' ((C.net m).st s).M ∪
        {WFF.openFree ((C.net m).st s).l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots
          (WFF.mono ((ctxOf_le_of_suffix hsuf).insert _ A) ψ)})⟩ := by
    rw [hstep hlm]
    simp only [NetSt.henk, dif_pos hsuf, if_pos hin]
    exact NetSt.setSt_self _ _ _
  refine ⟨m + 1, by omega, ?_⟩
  rw [hst]
  refine ⟨(ctxOf_le_of_suffix hsuf).trans (ctxOf_le_append [A] _), _,
    Ctx.ref_insert_root _ _ A, ?_⟩
  refine hS (Or.inr ?_)
  rw [Set.mem_singleton_iff, ← WFF.instantiate_eta_openFree _ (ctxOf_fresh le_rfl)
    Ctx.NoSlots.slots Ctx.NoSlots.slots, WFF.mono_mono]

/-- ⭐Every failing universal of a node's theory eventually has a counter-instance. -/
theorem henk_negAll {n : ℕ} {s : Node} (hs : (C.net n).Live s) {A : VarType}
    {ψ : WFF σ ((ctxOf ((C.net n).st s).l).insert (.bnd 0) A) 1}
    (hmem : (WFF.all A ψ).neg ∈ ((C.net n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ (hle : (ctxOf ((C.net n).st s).l).Le (ctxOf ((C.net m).st s).l))
      (a : Ann A) (t : Term σ (ctxOf ((C.net m).st s).l) A a),
      (WFF.instantiate Ctx.NoSlots.slots t (WFF.mono (hle.insert _ A) ψ)).neg ∈
        ((C.net m).st s).M := by
  obtain ⟨m, hnm, hstep⟩ := C.henk s ⟨((C.net n).st s).l, .imp (.all A ψ) .bot⟩ n
  have hlm := C.live_mono hnm hs
  have hsuf := C.lang_suffix hnm hs
  have hg := (C.ext hnm).grows s hs
  have hin : WFF.mono (ctxOf_le_of_suffix hsuf) (.imp (.all A ψ) .bot) ∈ ((C.net m).st s).M :=
    hg.sub _ hmem
  have hM := (C.good m).mcs s hlm
  have hex : Theory.Derives ((C.net m).st s).M
      (.ex A (WFF.mono ((ctxOf_le_of_suffix hsuf).insert _ A) ψ).neg) :=
    ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hin, ⟨Proof.exNeg_of_negAll _⟩⟩
  obtain ⟨hS, -⟩ := complete_spec (henkin_consistent hM.1 hex
    (ctxOf_fresh (l := ((C.net m).st s).l) le_rfl))
  have hst : (C.net (m + 1)).st s = ⟨A :: ((C.net m).st s).l, complete
      (WFF.mono (ctxOf_le_append [A] ((C.net m).st s).l) '' ((C.net m).st s).M ∪
        {WFF.openFree ((C.net m).st s).l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots
          (WFF.mono ((ctxOf_le_of_suffix hsuf).insert _ A) ψ).neg})⟩ := by
    rw [hstep hlm]
    simp only [NetSt.henk, dif_pos hsuf, if_pos hin]
    exact NetSt.setSt_self _ _ _
  refine ⟨m + 1, by omega, ?_⟩
  rw [hst]
  refine ⟨(ctxOf_le_of_suffix hsuf).trans (ctxOf_le_append [A] _), _,
    Term.eta (.root (.free ((C.net m).st s).l.length)) A (Ctx.ref_insert_root _ _ A), ?_⟩
  refine hS (Or.inr ?_)
  rw [Set.mem_singleton_iff, ← WFF.instantiate_eta_openFree _ (ctxOf_fresh le_rfl)
    Ctx.NoSlots.slots Ctx.NoSlots.slots]
  change _ = (WFF.instantiate _ _ (WFF.mono _ (WFF.mono _ ψ))).neg
  rw [WFF.mono_mono]

/-! ### Children -/

/-- ⭐Every failing `□φ` of a node's theory eventually has a child refuting `φ`. -/
theorem child_box {n : ℕ} {s : Node} (hs : (C.net n).Live s)
    {ψ : WFF σ (ctxOf ((C.net n).st s).l).boxIn 0} (hψ : WFF.box ψ ∉ ((C.net n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ (hsuf : ((C.net n).st s).l <:+ ((C.net m).st s).l)
      (M' : Set (WFF σ (ctxOf (((C.net m).st s).l.map VarType.bc)) 0)),
      ¬ (C.net m).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).st ((C.net m).nch s :: s) =
        ⟨((C.net m).st s).l.map VarType.bc, M'⟩ ∧
      (C.net (m + 1)).kind ((C.net m).nch s :: s) = none ∧
      (C.net (m + 1)).fcl ((C.net m).nch s :: s) = ((C.net m).st s).l ∧
      (C.net (m + 1)).fimg ((C.net m).nch s :: s) = id ∧
      (childArrow ((C.net m).st s).l (WFF.mono (ctxOf_le_of_suffix hsuf).boxIn ψ)).neg ∈
        M' := by
  obtain ⟨m, hnm, hstep⟩ := C.child s ⟨((C.net n).st s).l, .box ψ⟩ n
  have hlm := C.live_mono hnm hs
  have hsuf := C.lang_suffix hnm hs
  have hg := (C.ext hnm).grows s hs
  have hM := (C.good m).mcs s hlm
  have hnin : WFF.mono (ctxOf_le_of_suffix hsuf) (.box ψ) ∉ ((C.net m).st s).M := fun h =>
    hψ (mem_of_mono_mem _ ((C.good n).mcs s hs) hM hg.sub h)
  obtain ⟨hS, -⟩ := complete_spec (child_consistent hM
    (φ := WFF.mono (ctxOf_le_of_suffix hsuf).boxIn ψ) hnin)
  have hst : C.net (m + 1) = (C.net m).newChild s none 0
      ⟨((C.net m).st s).l.map VarType.bc, complete
        ({(childArrow ((C.net m).st s).l (WFF.mono (ctxOf_le_of_suffix hsuf).boxIn ψ)).neg} ∪
          {χ | ∃ ψ', WFF.mono (Ctx.Le.refl _) (.box ψ') ∈ ((C.net m).st s).M ∧
            χ = childArrow ((C.net m).st s).l ψ'})⟩ := by
    rw [hstep hlm]
    simp only [NetSt.mkChild, dif_pos hsuf, if_neg hnin]
  refine ⟨m, hnm, hsuf, _, NetSt.not_live_new s, ?_, ?_, ?_, ?_, ?_, hS (Or.inl rfl)⟩
  · rw [hst]
    exact (NetSt.live_newChild hlm _ _ _ _).mpr (Or.inr rfl)
  · rw [hst]
    exact newChild_st _ _ _ _ _
  · rw [hst]
    exact Function.update_self _ _ _
  · rw [hst]
    exact Function.update_self _ _ _
  · rw [hst]
    exact Function.update_self _ _ _

/-- ⭐Every true `◇_x φ` of a node's theory eventually has a child in the extent of `x` where
    `φ` holds. -/
theorem child_dia {n : ℕ} {s : Node} (hs : (C.net n).Live s) {x : VarSymb}
    {hx : ∃ X, (ctxOf ((C.net n).st s).l).ref x = some (.VTypeDia X)}
    {ψ : WFF σ ((ctxOf ((C.net n).st s).l).diaIn x) 0}
    (hψ : WFF.dia x hx ψ ∈ ((C.net n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ (hsuf : ((C.net n).st s).l <:+ ((C.net m).st s).l) (X : VarType)
      (hX : (ctxOf ((C.net m).st s).l).ref x = some (.VTypeDia X))
      (M' : Set (WFF σ (ctxOf (X :: ((C.net m).st s).l.map VarType.bc)) 0)),
      ¬ (C.net m).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).st ((C.net m).nch s :: s) =
        ⟨X :: ((C.net m).st s).l.map VarType.bc, M'⟩ ∧
      (C.net (m + 1)).kind ((C.net m).nch s :: s) = some (x, X) ∧
      (C.net (m + 1)).cx ((C.net m).nch s :: s) = ((C.net m).st s).l.length ∧
      (C.net (m + 1)).fcl ((C.net m).nch s :: s) = ((C.net m).st s).l ∧
      (C.net (m + 1)).fimg ((C.net m).nch s :: s) = id ∧
      childXArrow ((C.net m).st s).l hX
        (WFF.mono ((ctxOf_le_of_suffix hsuf).diaIn x) ψ) ∈ M' := by
  obtain ⟨m, hnm, hstep⟩ := C.child s ⟨((C.net n).st s).l, .dia x hx ψ⟩ n
  have hlm := C.live_mono hnm hs
  have hsuf := C.lang_suffix hnm hs
  have hg := (C.ext hnm).grows s hs
  have hM := (C.good m).mcs s hlm
  have hin : WFF.mono (ctxOf_le_of_suffix hsuf) (.dia x hx ψ) ∈ ((C.net m).st s).M :=
    hg.sub _ hψ
  obtain ⟨X, hX₀⟩ := hx
  have hX : (ctxOf ((C.net m).st s).l).ref x = some (.VTypeDia X) :=
    (ctxOf_le_of_suffix hsuf).ref hX₀
  obtain ⟨hS, -⟩ := complete_spec (childX_consistent hM hX
    (φ := WFF.mono ((ctxOf_le_of_suffix hsuf).diaIn x) ψ) hin)
  have hst : C.net (m + 1) = (C.net m).newChild s (some (x, X)) ((C.net m).st s).l.length
      ⟨X :: ((C.net m).st s).l.map VarType.bc, complete
        ({childXArrow ((C.net m).st s).l hX (WFF.mono ((ctxOf_le_of_suffix hsuf).diaIn x) ψ)} ∪
          {χ | ∃ ψ', WFF.mono (Ctx.Le.refl _) (WFF.boxx x ⟨X, hX⟩ ψ') ∈ ((C.net m).st s).M ∧
            χ = childXArrow ((C.net m).st s).l hX ψ'})⟩ := by
    rw [hstep hlm]
    simp only [NetSt.mkChild, dif_pos hsuf, if_pos hin]
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
  · rw [hst]
    exact (NetSt.live_newChild hlm _ _ _ _).mpr (Or.inr rfl)
  · rw [hst]
    exact newChild_st _ _ _ _ _
  · rw [hst]
    exact Function.update_self _ _ _
  · rw [hst]
    exact Function.update_self _ _ _
  · rw [hst]
    exact Function.update_self _ _ _
  · rw [hst]
    exact Function.update_self _ _ _

/-- ⭐A chain performing every step infinitely often is fair. -/
def toFair : FairChain M₀ where
  net := C.net
  zero := C.zero
  good := C.good
  inj := C.inj
  ext := C.ext
  fwd_total := C.fwd_total
  back_total := C.back_total
  henk_ex := C.henk_ex
  henk_negAll := C.henk_negAll
  child_box := C.child_box
  child_dia := C.child_dia

end OpChain

/-! ## Weak B's chain -/

section Weak

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- Every network of weak B's chain has injective images. -/
theorem inj_net (hB : ModalSys.B = true) (hM₀ : Theory.IsMCS M₀) : ∀ n, (net M₀ n).InjOk
  | 0 => NetSt.InjOk.init M₀
  | n + 1 => (inj_net hB hM₀ n).applyOp (good_net hB hM₀ n) (sched n)

theorem net_succ_of {n : ℕ} {o : Op σ} (h : sched n = o) :
    net M₀ (n + 1) = (net M₀ n).applyOp o := by
  rw [← h]
  rfl

/-- Weak B's chain performs every step infinitely often. -/
noncomputable def weakOpChain (hB : ModalSys.B = true) (hM₀ : Theory.IsMCS M₀) : OpChain M₀ where
  net := net M₀
  zero := rfl
  good := good_net hB hM₀
  inj := inj_net hB hM₀
  ext := ext_net hB hM₀
  henk s o m := by
    obtain ⟨n, hmn, hs⟩ := sched_after (σ := σ) (.inl (s, o)) m
    exact ⟨n, hmn, fun hl => by rw [net_succ_of hs]; simp only [NetSt.applyOp, if_pos hl]⟩
  child s o m := by
    obtain ⟨n, hmn, hs⟩ := sched_after (σ := σ) (.inr (.inl (s, o))) m
    exact ⟨n, hmn, fun hl => by rw [net_succ_of hs]; simp only [NetSt.applyOp, if_pos hl]⟩
  fwd c p m := by
    obtain ⟨n, hmn, hs⟩ := sched_after (σ := σ) (.inr (.inr (.inl (c :: p)))) m
    refine ⟨n, hmn, fun hl => ?_⟩
    rw [net_succ_of hs]
    simp only [NetSt.applyOp, if_pos hl]
    exact realF_fcl _ _ _
  back c p m := by
    obtain ⟨n, hmn, hs⟩ := sched_after (σ := σ) (.inr (.inr (.inr (c :: p)))) m
    refine ⟨n, hmn, fun hl => ?_⟩
    rw [net_succ_of hs]
    simp only [NetSt.applyOp, if_pos hl]
    exact realB_bcl _ _ _

/-- ⭐Weak B's chain is fair. -/
noncomputable def weakChain (hB : ModalSys.B = true) (hM₀ : Theory.IsMCS M₀) : FairChain M₀ :=
  (weakOpChain hB hM₀).toFair

end Weak

end BArrow

end V12M
