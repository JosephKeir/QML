import QML.QML_v12m_GNet
import QML.QML_v12m_BNetOps

/-!
# QML v12m — the growing tree: Henkin witnesses, children and lifts

The operations on a growing tree besides `realF`, each preserving `Good`:

* `henk`: a Henkin witness for an existential, or a counter-instance for a failing universal, of
  one node's theory (as B's);
* `mkChild`: a new child for a failing `□φ` or a true `◇_x φ`, its seed from
  `gchild_consistent`;
* ⭐`lift`: strong 4.  For an edge into `k` whose parent `p` is fully committed and an address `n`
  of `k` of a liftable type `T`, `p` gets a fresh root `m : T` holding the seed
  (`glift_consistent`), `k` a fresh variable for `m`'s residual (`gliftRealise_consistent`), and
  the edge sends `m.keep ↦ n` (`gliftG`).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature}

namespace GNetSt

variable {N : GNetSt σ}

/-! ## Henkin witnesses -/

open Classical in
/-- ⭐A Henkin witness for an existential, or a counter-instance for a failing universal, of the
    node `s`'s theory — given as a formula over an earlier list of its variables. -/
noncomputable def henk (N : GNetSt σ) (s : Node) :
    (Σ l : List VarType, WFF σ (ctxOf l) 0) → GNetSt σ
  | ⟨l, φ⟩ =>
      if h : l <:+ (N.st s).l then
        match φ with
        | .ex A ψ =>
            if WFF.mono (ctxOf_le_of_suffix h) (.ex A ψ) ∈ (N.st s).M then
              N.setSt s ⟨A :: (N.st s).l, complete
                (WFF.mono (ctxOf_le_append [A] (N.st s).l) '' (N.st s).M ∪
                  {WFF.openFree (N.st s).l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots
                    (WFF.mono ((ctxOf_le_of_suffix h).insert _ A) ψ)})⟩
            else N
        | .imp (.all A ψ) .bot =>
            if WFF.mono (ctxOf_le_of_suffix h) (.imp (.all A ψ) .bot) ∈ (N.st s).M then
              N.setSt s ⟨A :: (N.st s).l, complete
                (WFF.mono (ctxOf_le_append [A] (N.st s).l) '' (N.st s).M ∪
                  {WFF.openFree (N.st s).l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots
                    (WFF.mono ((ctxOf_le_of_suffix h).insert _ A) ψ).neg})⟩
            else N
        | _ => N
      else N

/-- ⭐Henkin witnesses preserve the invariants. -/
theorem Good.henk (hN : N.Good) {s : Node} (hs : N.Live s)
    (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : (N.henk s o).Good := by
  obtain ⟨l, φ⟩ := o
  simp only [GNetSt.henk]
  split_ifs with h
  · have hM := hN.mcs s hs
    match φ with
    | .ex A ψ =>
        simp only
        split_ifs with hmem
        · obtain ⟨h₁, h₂⟩ := NetSt.henk_grow hM (Theory.Derives.of_mem hmem)
          exact hN.setSt hs h₂ h₁
        · exact hN
    | .imp (.all A ψ) .bot =>
        simp only
        split_ifs with hmem
        · have hex : Theory.Derives (N.st s).M
              (.ex A (WFF.mono ((ctxOf_le_of_suffix h).insert _ A) ψ).neg) :=
            ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hmem,
              ⟨Proof.exNeg_of_negAll _⟩⟩
          obtain ⟨h₁, h₂⟩ := NetSt.henk_grow hM hex
          exact hN.setSt hs h₂ h₁
        · exact hN
    | .atom _ => exact hN
    | .eq _ _ => exact hN
    | .top => exact hN
    | .bot => exact hN
    | .and _ _ => exact hN
    | .or _ _ => exact hN
    | .imp (.atom _) _ => exact hN
    | .imp (.eq _ _) _ => exact hN
    | .imp .top _ => exact hN
    | .imp .bot _ => exact hN
    | .imp (.and _ _) _ => exact hN
    | .imp (.or _ _) _ => exact hN
    | .imp (.imp _ _) _ => exact hN
    | .imp (.ex _ _) _ => exact hN
    | .imp (.box _) _ => exact hN
    | .imp (.dia _ _ _) _ => exact hN
    | .imp (.here _ _ _) _ => exact hN
    | .imp (.back _ _ _ _) _ => exact hN
    | .imp (.retS _ _ _ _) _ => exact hN
    | .imp (.retxS _ _ _ _ _ _) _ => exact hN
    | .imp (.all _ _) (.atom _) => exact hN
    | .imp (.all _ _) (.eq _ _) => exact hN
    | .imp (.all _ _) .top => exact hN
    | .imp (.all _ _) (.and _ _) => exact hN
    | .imp (.all _ _) (.or _ _) => exact hN
    | .imp (.all _ _) (.imp _ _) => exact hN
    | .imp (.all _ _) (.all _ _) => exact hN
    | .imp (.all _ _) (.ex _ _) => exact hN
    | .imp (.all _ _) (.box _) => exact hN
    | .imp (.all _ _) (.dia _ _ _) => exact hN
    | .imp (.all _ _) (.here _ _ _) => exact hN
    | .imp (.all _ _) (.back _ _ _ _) => exact hN
    | .imp (.all _ _) (.retS _ _ _ _) => exact hN
    | .imp (.all _ _) (.retxS _ _ _ _ _ _) => exact hN
    | .all _ _ => exact hN
    | .box _ => exact hN
    | .dia _ _ _ => exact hN
    | .here _ _ _ => exact hN
    | .back _ _ _ _ => exact hN
    | .retS _ _ _ _ => exact hN
    | .retxS _ _ _ _ _ _ => exact hN
  · exact hN

/-! ## Children -/

/-- ⭐The network with a new child of `s` of kind `kd` in state `t`, all of `s`'s variables
    committed by `f`. -/
def newChild (N : GNetSt σ) (s : Node) (kd : Option VarSymb) (t : NodeSt σ)
    (f : VarSymb → LEnt σ) : GNetSt σ where
  st := Function.update N.st (N.nch s :: s) t
  nch := Function.update (Function.update N.nch s (N.nch s + 1)) (N.nch s :: s) 0
  kind := Function.update N.kind (N.nch s :: s) kd
  fcl := Function.update N.fcl (N.nch s :: s) (N.st s).l
  fmap := Function.update N.fmap (N.nch s :: s) f

theorem not_live_new {N : GNetSt σ} (s : Node) : ¬ N.Live (N.nch s :: s) :=
  fun h => lt_irrefl _ h.2

theorem not_live_below_new {N : GNetSt σ} (s : Node) (d : ℕ) :
    ¬ N.Live (d :: N.nch s :: s) := fun h => not_live_new s h.1

/-- The live nodes after adding a child: the old ones and the new one. -/
theorem live_newChild {N : GNetSt σ} {s : Node} (hs : N.Live s) (kd : Option VarSymb)
    (t : NodeSt σ) (f : VarSymb → LEnt σ) :
    ∀ k, (N.newChild s kd t f).Live k ↔ N.Live k ∨ k = N.nch s :: s
  | [] => by simp [Live]
  | d :: p => by
      have ih := live_newChild hs kd t f p
      change (N.newChild s kd t f).Live p ∧ d < (N.newChild s kd t f).nch p ↔ _
      by_cases hpk : p = N.nch s :: s
      · subst hpk
        have e : (N.newChild s kd t f).nch (N.nch s :: s) = 0 := Function.update_self _ _ _
        rw [e]
        simp only [Nat.not_lt_zero, and_false, false_iff, not_or]
        exact ⟨not_live_below_new s d, fun h => by
          have := congrArg List.length h
          simp at this⟩
      · have hnch : (N.newChild s kd t f).nch p = Function.update N.nch s (N.nch s + 1) p :=
          Function.update_of_ne hpk _ _
        rw [hnch, ih]
        simp only [hpk, or_false]
        by_cases hps : p = s
        · subst hps
          simp only [Function.update_self]
          change N.Live p ∧ d < N.nch p + 1 ↔ (N.Live p ∧ d < N.nch p) ∨ d :: p = N.nch p :: p
          simp only [List.cons.injEq, and_true, hs, true_and]
          omega
        · rw [Function.update_of_ne hps]
          change _ ↔ (N.Live p ∧ d < N.nch p) ∨ _
          simp only [List.cons.injEq, hps, and_false, or_false]

/-- ⭐A new child with a good edge keeps the invariants. -/
theorem Good.newChild (hN : N.Good) {s : Node} (hs : N.Live s) {kd : Option VarSymb}
    {t : NodeSt σ} {f : VarSymb → LEnt σ} (ht : Theory.IsMCS t.M)
    (hf : FwdData (N.st s) t kd (N.st s).l f) : (N.newChild s kd t f).Good := by
  have hks : (N.nch s :: s : Node) ≠ s := NetSt.ne_parent _ s
  have hold : ∀ k, N.Live k → k ≠ N.nch s :: s := fun k hk h => not_live_new s (h ▸ hk)
  refine ⟨fun k hk => ?_, fun c p hk => ?_⟩
  · rcases (live_newChild hs kd t f k).mp hk with hk | rfl
    · change Theory.IsMCS (Function.update N.st _ t k).M
      rw [Function.update_of_ne (hold k hk)]
      exact hN.mcs k hk
    · change Theory.IsMCS (Function.update N.st _ t _).M
      rw [Function.update_self]
      exact ht
  · rcases (live_newChild hs kd t f _).mp hk with hk | he
    · have hne := hold _ hk
      have hpne := hold p hk.1
      have := hN.fwd c p hk
      unfold FwdOk at this ⊢
      change FwdData (Function.update N.st _ t p) (Function.update N.st _ t (c :: p))
        (Function.update N.kind _ kd (c :: p)) (Function.update N.fcl _ (N.st s).l (c :: p))
        (Function.update N.fmap _ f (c :: p))
      simp only [Function.update_of_ne hne, Function.update_of_ne hpne]
      exact this
    · obtain ⟨rfl, rfl⟩ := List.cons.inj he
      unfold FwdOk
      change FwdData (Function.update N.st _ t p) (Function.update N.st _ t (N.nch p :: p))
        (Function.update N.kind _ kd _) (Function.update N.fcl _ (N.st p).l _)
        (Function.update N.fmap _ f _)
      simp only [Function.update_self, Function.update_of_ne hks.symm]
      exact hf

/-- A failing necessity gives the possibility of the negation. -/
theorem kDia_neg_of_not_box {Γ : Ctx} {M : Set (WFF σ Γ 0)} (hM : Theory.IsMCS M)
    {ψ : WFF σ Γ.boxIn 0} (h : WFF.box ψ ∉ M) :
    kDia none (kDecl_none Γ) (Γ := Γ) ψ.neg ∈ M :=
  hM.neg_mem_iff.mpr fun hb => h (hM.closed ⟨[_], fun x hx => by
    rw [List.mem_singleton.mp hx]; exact hb,
    Provable.mono (fun y hy => by rw [List.mem_singleton.mp hy]; exact List.mem_cons_self)
      ⟨Proof.K_box (Δ := [ψ.neg.neg]) (Proof.byContra (.imp_elim
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
        (Proof.lookup List.mem_cons_self)))⟩⟩)

/-- The seed of a child of kind `k` for `φ`. -/
noncomputable def childSeed (hF : ModalSys.Four = true) (L : List VarType)
    (M : Set (WFF σ (ctxOf L) 0))
    {k : Option VarSymb} {X : VarType} (hk : KContent (ctxOf L) k X)
    (φ : WFF σ ((ctxOf L).kView k) 0) : Set (WFF σ (ctxOf (childL L k X)) 0) :=
  {gchildArrow hF L hk φ} ∪
    {χ | ∃ ψ, kBox k (kDecl_of_kContent hk) ψ ∈ M ∧ χ = gchildArrow hF L hk ψ}

open Classical in
/-- ⭐A new child for a failing `□φ`, or a true `◇_x φ`, of the node `s`'s theory — given as a
    formula over an earlier list of its variables. -/
noncomputable def mkChild (hF : ModalSys.Four = true) (N : GNetSt σ) (s : Node) :
    (Σ l : List VarType, WFF σ (ctxOf l) 0) → GNetSt σ
  | ⟨l, φ⟩ =>
      if h : l <:+ (N.st s).l then
        match φ with
        | .box ψ =>
            if WFF.mono (ctxOf_le_of_suffix h) (.box ψ) ∈ (N.st s).M then N else
              N.newChild s none ⟨childL (N.st s).l none .VTypeOne, complete
                (childSeed hF (N.st s).l (N.st s).M (kContent_none _ .VTypeOne)
                  (WFF.mono (ctxOf_le_of_suffix h).boxIn ψ).neg)⟩
                (ofRen (gchildMap (N.st s).l none))
        | .dia x hx ψ =>
            if WFF.mono (ctxOf_le_of_suffix h) (.dia x hx ψ) ∈ (N.st s).M then
              match hX : (ctxOf (N.st s).l).ref x with
              | some (.VTypeDia X) =>
                  N.newChild s (some x) ⟨childL (N.st s).l (some x) X, complete
                    (childSeed hF (N.st s).l (N.st s).M (k := some x)
                      (fun _ e => by cases e; exact hX)
                      (WFF.mono ((ctxOf_le_of_suffix h).diaIn x) ψ))⟩
                    (ofRen (gchildMap (N.st s).l (some x)))
              | _ => N
            else N
        | _ => N
      else N

/-- A child's seed, completed, is a good edge. -/
theorem childSeed_ok (hF : ModalSys.Four = true) {L : List VarType}
    {M : Set (WFF σ (ctxOf L) 0)} (hM : Theory.IsMCS M) {k : Option VarSymb} {X : VarType}
    (hk : KContent (ctxOf L) k X) {φ : WFF σ ((ctxOf L).kView k) 0}
    (hφ : kDia k (kDecl_of_kContent hk) φ ∈ M) :
    Theory.IsMCS (complete (childSeed hF L M hk φ)) ∧
      FwdData ⟨L, M⟩ ⟨childL L k X, complete (childSeed hF L M hk φ)⟩ k L
        (ofRen (gchildMap L k)) := by
  obtain ⟨hS, ht⟩ := complete_spec (gchild_consistent hF hM hk hφ)
  refine ⟨ht, List.suffix_refl _, kDecl_of_kContent hk, entOk_ofRen (itemOk_gchild hF L hk), ?_⟩
  intro ψ hψ
  rw [WFF.mono_refl] at hψ
  exact hS (Or.inr ⟨ψ, hψ, rfl⟩)

/-- ⭐Creating a child preserves the invariants. -/
theorem Good.mkChild (hF : ModalSys.Four = true) (hN : N.Good) {s : Node} (hs : N.Live s)
    (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : (N.mkChild hF s o).Good := by
  obtain ⟨l, φ⟩ := o
  simp only [GNetSt.mkChild]
  split_ifs with h
  · have hM := hN.mcs s hs
    match φ with
    | .box ψ =>
        simp only
        split_ifs with hmem
        · exact hN
        · obtain ⟨ht, hf⟩ := childSeed_ok hF hM (kContent_none _ .VTypeOne)
            (kDia_neg_of_not_box hM hmem)
          exact hN.newChild hs ht hf
    | .dia x hx ψ =>
        simp only
        split_ifs with hmem
        · split
          · rename_i X hX
            obtain ⟨ht, hf⟩ := childSeed_ok hF hM (k := some x) (φ :=
              WFF.mono ((ctxOf_le_of_suffix h).diaIn x) ψ) (fun _ e => by cases e; exact hX) hmem
            exact hN.newChild hs ht hf
          · exact hN
        · exact hN
    | .atom _ => exact hN
    | .eq _ _ => exact hN
    | .top => exact hN
    | .bot => exact hN
    | .and _ _ => exact hN
    | .or _ _ => exact hN
    | .imp _ _ => exact hN
    | .all _ _ => exact hN
    | .ex _ _ => exact hN
    | .here _ _ _ => exact hN
    | .back _ _ _ _ => exact hN
    | .retS _ _ _ _ => exact hN
    | .retxS _ _ _ _ _ _ => exact hN
  · exact hN

/-! ## Lifts -/

/-- The seed of a lifted root, over every proof of the edge's data. -/
noncomputable def liftSeedE (hF : ModalSys.Four = true) (tp tk : NodeSt σ) (k : Option VarSymb)
    (f : VarSymb → LEnt σ) {T : VarType} {a : Ann T} (t : Term σ (ctxOf tk.l) T a)
    (hl : T.liftable = true) : Set (WFF σ ((ctxOf tp.l).insert (.free tp.l.length) T) 0) :=
  {φ | ∃ (hk : KDecl (ctxOf tp.l) k) (hf : EntOk ((ctxOf tp.l).kView k) (ctxOf tk.l) f),
    φ ∈ liftSeed hF hl hk hf t tk.M}

/-- What the lifted root's residual puts into the child. -/
noncomputable def liftRealSet (hF : ModalSys.Four = true) (tp tk : NodeSt σ)
    (k : Option VarSymb) (f : VarSymb → LEnt σ) {T : VarType} {a : Ann T}
    (t : Term σ (ctxOf tk.l) T a) (hl : T.liftable = true)
    (Mp : Set (WFF σ (ctxOf (T :: tp.l)) 0)) : Set (WFF σ (ctxOf (T.lr :: tk.l)) 0) :=
  {φ | ∃ (hk : KDecl (ctxOf tp.l) k) (hf : EntOk ((ctxOf tp.l).kView k) (ctxOf tk.l) f)
    (ψ : WFF σ ((ctxOf (T :: tp.l)).kView k) 0),
    kBox k (kDecl_mono (ctxOf_le_append [T] tp.l) hk) ψ ∈ Mp ∧
      φ = gliftArrow hF (VarType.keepable_of_liftable hl) (kOld_of_kDecl hk) hf t ψ}

/-- The lifted parent. -/
noncomputable def liftPar (hF : ModalSys.Four = true) (tp tk : NodeSt σ) (k : Option VarSymb)
    (f : VarSymb → LEnt σ) {T : VarType} {a : Ann T} (t : Term σ (ctxOf tk.l) T a)
    (hl : T.liftable = true) : NodeSt σ :=
  ⟨T :: tp.l, complete (WFF.weaken (ctxOf_fresh (l := tp.l) le_rfl).root T '' tp.M ∪
    liftSeedE hF tp tk k f t hl)⟩

/-- The child grown by the lifted root's residual. -/
noncomputable def liftChild (hF : ModalSys.Four = true) (tp tk : NodeSt σ) (k : Option VarSymb)
    (f : VarSymb → LEnt σ) {T : VarType} {a : Ann T} (t : Term σ (ctxOf tk.l) T a)
    (hl : T.liftable = true) : NodeSt σ :=
  ⟨T.lr :: tk.l, complete (WFF.mono (ctxOf_le_append [T.lr] tk.l) '' tk.M ∪
    liftRealSet hF tp tk k f t hl (liftPar hF tp tk k f t hl).M)⟩

/-- ⭐One lift of a term along an edge whose parent is fully committed. -/
theorem lift_ok (hF : ModalSys.Four = true) {tp tk : NodeSt σ} {k : Option VarSymb}
    {f : VarSymb → LEnt σ} {T : VarType} {a : Ann T} (t : Term σ (ctxOf tk.l) T a)
    (hl : T.liftable = true) (hp : Theory.IsMCS tp.M) (ht : Theory.IsMCS tk.M)
    (hd : FwdData tp tk k tp.l f) :
    Theory.IsMCS (liftPar hF tp tk k f t hl).M ∧ Grows tp (liftPar hF tp tk k f t hl) ∧
      Theory.IsMCS (liftChild hF tp tk k f t hl).M ∧ Grows tk (liftChild hF tp tk k f t hl) ∧
      FwdData (liftPar hF tp tk k f t hl) (liftChild hF tp tk k f t hl) k (T :: tp.l)
        (gliftG f T tp.l.length (.inr ⟨tk.l, T, a, t⟩) (.free tk.l.length)) := by
  obtain ⟨_, hk, hf, htr⟩ := hd
  have hseed : liftSeedE hF tp tk k f t hl = liftSeed hF hl hk hf t tk.M := by
    ext φ
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hk, hf, h⟩⟩
  obtain ⟨hS₁, hmcs₁⟩ := complete_spec (show Theory.Consistent
    (WFF.weaken (ctxOf_fresh (l := tp.l) le_rfl).root T '' tp.M ∪ liftSeedE hF tp tk k f t hl) by
      rw [hseed]
      exact glift_consistent hF hl hp ht hk hf htr t)
  have hreal := gliftRealise_consistent hF hl ht hk hf t (M' := (liftPar hF tp tk k f t hl).M)
    hmcs₁ (fun φ h => hS₁ (Or.inr (hseed ▸ h)))
  obtain ⟨hS₂, hmcs₂⟩ := complete_spec (show Theory.Consistent
    (WFF.mono (ctxOf_le_append [T.lr] tk.l) '' tk.M ∪
      liftRealSet hF tp tk k f t hl (liftPar hF tp tk k f t hl).M) from
    hreal.mono (by
      rintro φ (h | ⟨_, _, ψ, h₁, h₂⟩)
      · exact Or.inl h
      · exact Or.inr ⟨ψ, h₁, h₂⟩))
  refine ⟨hmcs₁, ⟨⟨[T], rfl⟩, fun φ hφ => hS₁ (Or.inl ⟨φ, hφ, rfl⟩)⟩, hmcs₂,
    ⟨⟨[T.lr], rfl⟩, fun φ hφ => hS₂ (Or.inl ⟨φ, hφ, rfl⟩)⟩, List.suffix_refl _,
    kDecl_mono (ctxOf_le_append [T] tp.l) hk,
    itemOk_gliftZ hF (VarType.keepable_of_liftable hl) (kOld_of_kDecl hk) hf t, ?_⟩
  intro ψ hψ
  rw [WFF.mono_refl] at hψ
  exact hS₂ (Or.inr ⟨hk, hf, ψ, hψ, rfl⟩)

/-- ⭐**Lift** a term of the child `c :: p` along its edge, if the parent is fully committed along
    it, the term is over the child's variables, and its type is liftable: the edge then sends
    the new root's kept item to the term (docs §3 4, D5 (a)). -/
noncomputable def lift (hF : ModalSys.Four = true) (N : GNetSt σ) : Node → LTerm σ → GNetSt σ
  | [], _ => N
  | c :: p, ⟨l, T, a, t⟩ =>
      if N.fcl (c :: p) = (N.st p).l then
        if h : l <:+ (N.st (c :: p)).l then
          if hl : T.liftable = true then
            ((N.setSt p (liftPar hF (N.st p) (N.st (c :: p)) (N.kind (c :: p)) (N.fmap (c :: p))
                (Term.mono (ctxOf_le_of_suffix h) t) hl)).setSt (c :: p)
              (liftChild hF (N.st p) (N.st (c :: p)) (N.kind (c :: p)) (N.fmap (c :: p))
                (Term.mono (ctxOf_le_of_suffix h) t) hl)).setFwd
              (c :: p) (T :: (N.st p).l)
              (gliftG (N.fmap (c :: p)) T (N.st p).l.length
                (.inr ⟨(N.st (c :: p)).l, T, a, Term.mono (ctxOf_le_of_suffix h) t⟩)
                (.free (N.st (c :: p)).l.length))
          else N
        else N
      else N

/-- ⭐Lifting preserves the invariants. -/
theorem Good.lift (hF : ModalSys.Four = true) (hN : N.Good) {k : Node} (hk : N.Live k)
    (o : LTerm σ) : (N.lift hF k o).Good := by
  match k, o with
  | [], _ => exact hN
  | c :: p, ⟨l, T, a, t⟩ =>
      simp only [GNetSt.lift]
      split_ifs with hcl h hl
      · have hd := hN.fwd c p hk
        unfold FwdOk at hd
        rw [hcl] at hd
        obtain ⟨hmp, hgp, hmk, hgk, hfd⟩ :=
          lift_ok hF (Term.mono (ctxOf_le_of_suffix h) t) hl (hN.mcs p hk.1) (hN.mcs _ hk) hd
        have hN₁ := hN.setSt hk.1 hgp hmp
        have hk₁ : (N.setSt p (liftPar hF (N.st p) (N.st (c :: p)) (N.kind (c :: p))
            (N.fmap (c :: p)) (Term.mono (ctxOf_le_of_suffix h) t) hl)).Live (c :: p) :=
          (live_setSt _ _ _ _).mpr hk
        have hN₂ := hN₁.setSt hk₁ (by
          rw [setSt_ne _ _ (NetSt.ne_parent c p)]
          exact hgk) hmk
        refine hN₂.setFwd ?_
        change FwdData ((((N.setSt p _).setSt (c :: p) _)).st p)
          (((N.setSt p _).setSt (c :: p) _).st (c :: p)) _ _ _
        rw [setSt_ne _ _ (fun h => NetSt.ne_parent c p h.symm), setSt_self, setSt_self]
        exact hfd
      · exact hN
      · exact hN
      · exact hN

end GNetSt

end GArrow

end V12M
