import QML.QML_v12m_BRetChild
import QML.QML_v12m_RetKX

/-!
# QML v12m — strong B on the network: the child of a returning possibility along `x` (T off)

The second kind of returning successor (docs §11.20): an atom `◇_x[d ↦ y] Φ` of a node gets a
**witness child** along `x`, whose way home is committed to `y`.  Its variables are those of
`rcl` (`c : □A` oldest, the parent's one up) with `x`'s content `cx` newest; the parent's roots
are committed forward under `succ` with `x ⇝ cx`, and `c` back to `y`.

* `retSeedX`: the atom's body read at the child (`liftBodyX`), and `¬Θ` for every
  `¬◇_x[d ↦ y] Θ` of the parent.
* ⭐`retSeedX_consistent`: by the K-law along `x` (`Proof.retx_K_node`) and the pull-back into
  `x`'s view with the slot opened (`retPullS` at `x`'s view, `cx ↦ x.dia`;
  ⭐`subst_retPull_liftBodyX`), refuted by `Proof.retx_refute`.
* ⭐`RetData.retBirthX`: born with `RetInvW` forward (`ret_unitW` with `u := x.dia`, read at the
  child by `liftBodyX_unitBodyW`) and `RetInvX` home (by the seed).
* `NetSt.mkRetX`, ⭐`GoodS.mkRetX`, `Ext.mkRetX`: the network operation.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## The witness child's variables -/

section Layout

variable (l : List VarType) (A X : VarType)

theorem rclX_suffix : [VarType.VTypeBox A] <:+ X :: rcl l A :=
  (rcl_suffix l A).trans (List.suffix_cons _ _)

/-- The parent's roots go one up in the witness child. -/
theorem rclXImg : ImgOk l (ctxOf (X :: rcl l A)) Nat.succ := fun r hr =>
  (ctxOf_le_append [X] (rcl l A)).ref (rclImg l A r hr)

/-- `x`'s content is the witness child's newest root. -/
theorem rclX_cx : (ctxOf (X :: rcl l A)).ref (.root (.free (l.length + 1))) = some X := by
  have := ctxOf_ref_new X (rcl l A)
  rwa [length_rcl] at this

end Layout

variable [ModalSys.NoFour]

/-! ## Pulling the witness child back into `x`'s view -/

section Pull

variable (hT : ModalSys.T = false) (l : List VarType) (A : VarType) {x : VarSymb} {X : VarType}
  (hX : (ctxOf l).ref x = some (.VTypeDia X))

omit [ModalSys.NoFour] in
theorem pullCtxX_fresh (x : VarSymb) : ((ctxOf l).diaIn x).RootFresh (.free l.length) :=
  (ctxOf_fresh le_rfl).diaIn x

omit [ModalSys.NoFour] in
include hX in
/-- The content root goes to `x.dia`. -/
theorem okRef_dia :
    (SubE.ren (.step x .dia) : SubE σ (pullCtx ((ctxOf l).diaIn x) l A)).OkRef X :=
  (Ctx.le_insert (pullCtxX_fresh l x).root _).ref (Ctx.ref_diaIn_of hX)

include hX in
theorem ok_retPullSX :
    Subst.Ok (ctxOf (X :: rcl l A)) (retPullS hT σ l A (Ctx.le_boxIn_diaIn _ x)
      (pullCtxX_fresh l x) (.ren (.step x .dia))) :=
  ok_retPullS_X hT l A _ _ _ (okRef_dia l A hX)

/-- ⭐**Pulling back opens the slot, along `x`**: a witness body read at the witness child, pulled
    back into `x`'s view, is the body with its slot opened at `u`; the content root goes back to
    `x.dia`. -/
theorem subst_retPull_liftBodyX (Ξ : WFF σ (bodyCtxX [.VTypeBox A] l x) 1) :
    WFF.subst (retPullIdx hT σ l A (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x)
          (.ren (.step x .dia)))
        (retPullS hT σ l A (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x) (.ren (.step x .dia)))
        (ok_retPullSX hT l A hX) (coh_retPullS_of hT l A _ _ _ (ok_retPullSX hT l A hX))
        Ctx.NoSlots.slots Ctx.NoSlots.slots
        (liftBodyX (rclX_suffix l A X) (rclXImg l A X) hX (rclX_cx l A X) Ξ) =
      WFF.openFree l.length (pullCtxX_fresh l x) Ctx.NoSlots.slots Ξ := by
  unfold liftBodyX WFF.openFree
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Ξ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = .VTypeBox (bcT [.VTypeBox A]) := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    rw [Subst.toFree_root]
    dsimp only [Subst.comp]
    rw [Subst.set_root]
    dsimp only [SubE.comp]
    rw [subE_tm_sig (subst_retPull_entry hT l A _ _ _ (rclX_suffix l A X) _ _)]
    exact .ren_eta _ _
  · rw [Subst.toFree_ne _ _ _ _ hvr]
    dsimp only [Subst.comp]
    rw [Subst.set_ne _ _ hvr]
    rcases bodyX_item hv hvr with ⟨w, rfl, hw⟩ | ⟨rfl, _⟩
    · change SubE.Sim T (((Subst.idRen _) (.step w .box)).mono _)
        ((retPullS hT σ l A (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x)
          (.ren (.step x .dia))).at (itemAt (imgRoot Nat.succ w.rt) w))
      rw [at_retPull_item hT l A _ _ _ hw]
      exact .ren_eta _ _
    · change SubE.Sim T (((Subst.idRen _) (.step x .dia)).mono _)
        ((if x = x then SubE.ren (.root (.free (l.length + 1))) else .hide).comp _ _ _)
      rw [if_pos rfl]
      change SubE.Sim T _ (retPullS hT σ l A (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x)
        (.ren (.step x .dia)) (.root (.free (l.length + 1))))
      rw [retPull_last]
      exact .refl _

end Pull

omit [ModalSys.NoFour] in
/-- A returning possibility along `x` whose body `x`'s view refutes is absurd. -/
def Proof.retx_refute {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)}
    (hS : ModalSys.BStrong = true) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    {B : VarType} {b : Ann B} (t : Term σ Γ B b)
    (Ξ : WFF σ ((Γ.diaIn x).insert (.bnd 0) (.VTypeBox B)) 1)
    (q : Proof σ (Γ.diaIn x) [WFF.ex (.VTypeBox B) Ξ] .bot)
    (p : Proof σ Γ Δ (WFF.retx hS x hx t Ξ)) : Proof σ Γ Δ .bot :=
  Proof.dia_bot x hx (Proof.imp_elim (Proof.ofSubset (fun _ h => by simp at h)
    (Proof.imp_intro (Proof.K_dia x hx (Δ₁ := []) (Δ₂ := []) q)))
    (Proof.ret_dia hS (.pos x hx) t _ p))

/-! ## The seed and its consistency -/

section Seed

variable (hS : ModalSys.BStrong = true) {l : List VarType} {A : VarType} {y : ℕ}
  (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) {x : VarSymb}
  {X : VarType} (hX : (ctxOf l).ref x = some (.VTypeDia X))

/-- ⭐The seed of the witness child of `◇_x[d ↦ y] Φ`: the atom's body, and `¬Θ` for every
    `¬◇_x[d ↦ y] Θ` of the parent, read at the child. -/
def retSeedX (M : Set (WFF σ (ctxOf l) 0)) (Φ : WFF σ (bodyCtxX [.VTypeBox A] l x) 1) :
    Set (WFF σ (ctxOf (X :: rcl l A)) 0) :=
  {liftBodyX (rclX_suffix l A X) (rclXImg l A X) hX (rclX_cx l A X) Φ} ∪
    {φ | ∃ Θ, WFF.neg (WFF.retx hS x ⟨X, hX⟩
        (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg l A hy)).2 Θ) ∈ M ∧
      φ = liftBodyX (rclX_suffix l A X) (rclXImg l A X) hX (rclX_cx l A X) (WFF.neg Θ)}

/-- Finitely many seed formulas reduce to one body with a returning possibility along `x` at the
    parent, by the K-law along `x`. -/
theorem retSeedX_list {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.IsMCS M)
    {Φ : WFF σ (bodyCtxX [.VTypeBox A] l x) 1}
    (hΦ : WFF.retx hS x ⟨X, hX⟩ (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg l A hy)).2 Φ
      ∈ M) :
    ∀ L : List (WFF σ (ctxOf (X :: rcl l A)) 0), (∀ δ ∈ L, δ ∈ retSeedX hS hy hX M Φ) →
      ∃ Ξ, WFF.retx hS x ⟨X, hX⟩ (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg l A hy)).2 Ξ
          ∈ M ∧
        Theory.Derives {liftBodyX (rclX_suffix l A X) (rclXImg l A X) hX (rclX_cx l A X) Ξ}
          (liftBodyX (rclX_suffix l A X) (rclXImg l A X) hX (rclX_cx l A X) Φ) ∧
        ∀ δ ∈ L, Theory.Derives
          {liftBodyX (rclX_suffix l A X) (rclXImg l A X) hX (rclX_cx l A X) Ξ} δ
  | [], _ => ⟨Φ, hΦ, Theory.Derives.of_mem rfl, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨Ξ₀, hΞ₀, hΦ₀, hL⟩ := retSeedX_list hM hΦ L
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      rcases h δ List.mem_cons_self with hδ | ⟨Θ, hΘ, rfl⟩
      · refine ⟨Ξ₀, hΞ₀, hΦ₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · rw [Set.mem_singleton_iff.mp hδ]
          exact hΦ₀
        · exact hL d hd
      · have hand : ∀ φ, Proof σ _
            [liftBodyX (rclX_suffix l A X) (rclXImg l A X) hX (rclX_cx l A X) (Ξ₀.and Θ.neg)] φ →
            Theory.Derives
              {liftBodyX (rclX_suffix l A X) (rclXImg l A X) hX (rclX_cx l A X)
                (Ξ₀.and Θ.neg)} φ :=
          fun φ p => ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; rfl, ⟨p⟩⟩
        have h₀ := hand _ (Proof.and_elim_l
          (ψ := liftBodyX (rclX_suffix l A X) (rclXImg l A X) hX (rclX_cx l A X) Θ.neg)
          (Proof.lookup List.mem_cons_self))
        have h₁ := hand _ (Proof.and_elim_r
          (φ := liftBodyX (rclX_suffix l A X) (rclXImg l A X) hX (rclX_cx l A X) Ξ₀)
          (Proof.lookup List.mem_cons_self))
        have htr : ∀ d, Theory.Derives
            {liftBodyX (rclX_suffix l A X) (rclXImg l A X) hX (rclX_cx l A X) Ξ₀} d →
            Theory.Derives
              {liftBodyX (rclX_suffix l A X) (rclXImg l A X) hX (rclX_cx l A X)
                (Ξ₀.and Θ.neg)} d :=
          fun d hd => Derives.trans (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact h₀) hd
        refine ⟨Ξ₀.and Θ.neg, hM.closed ⟨[_, _], fun x hx => ?_,
          ⟨Proof.retx_K_node hS hX _ Ξ₀ Θ (Proof.lookup List.mem_cons_self)
            (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩,
          htr _ hΦ₀, fun d hd => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hΞ₀
          · rw [List.mem_singleton.mp hx]; exact hΘ
        rcases List.mem_cons.mp hd with rfl | hd
        · exact h₁
        · exact htr d (hL d hd)

/-- ⭐**The witness child's seed is consistent** (T off): finitely many seed formulas reduce to
    one body `Ξ` with `◇_x[d ↦ y] Ξ` at the parent (`retSeedX_list`); a refutation of `Ξ` read at
    the child pulls back to one of `Ξ` with its slot opened in `x`'s view
    (`subst_retPull_liftBodyX`), against `◇_x ∃d. Ξ` (`Proof.retx_refute`). -/
theorem retSeedX_consistent (hT : ModalSys.T = false) {M : Set (WFF σ (ctxOf l) 0)}
    (hM : Theory.IsMCS M) {Φ : WFF σ (bodyCtxX [.VTypeBox A] l x) 1}
    (hΦ : WFF.retx hS x ⟨X, hX⟩ (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg l A hy)).2 Φ
      ∈ M) :
    Theory.Consistent (retSeedX hS hy hX M Φ) := by
  rintro ⟨L, hL, hp⟩
  obtain ⟨Ξ, hΞ, -, hder⟩ := retSeedX_list hS hy hX hM hΦ L hL
  obtain ⟨Δ, hΔ, ⟨p⟩⟩ := Derives.trans (fun x hx => hder x hx) ⟨L, fun x hx => hx, hp⟩
  have p' : Proof σ (ctxOf (X :: rcl l A))
      [liftBodyX (rclX_suffix l A X) (rclXImg l A X) hX (rclX_cx l A X) Ξ] .bot :=
    Proof.ofSubset (fun x hx => by
      rw [Set.mem_singleton_iff.mp (hΔ x hx)]; exact List.mem_cons_self) p
  haveI : (pullCtx ((ctxOf l).diaIn x) l A).Presented :=
    Ctx.Presented.insertFree inferInstance _ (pullCtxX_fresh l x) _
  have q := Proof.subst p' (retPullS hT σ l A (Ctx.le_boxIn_diaIn _ x) (pullCtxX_fresh l x)
    (.ren (.step x .dia))) (ok_retPullSX hT l A hX)
    (coh_retPullS_of hT l A _ _ _ (ok_retPullSX hT l A hX)) Ctx.NoSlots.slots
  simp only [List.map_cons, List.map_nil, subst_retPull_liftBodyX] at q
  refine hM.1 ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hΞ,
    ⟨Proof.retx_refute hS _ _ Ξ ?_ (Proof.lookup List.mem_cons_self)⟩⟩
  refine Proof.ex_elim l.length _ (pullCtxX_fresh l x)
    (φ := WFF.openFree _ (pullCtxX_fresh l x) Ctx.NoSlots.slots Ξ) (ψ := .bot)
    (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
      (Proof.lookup List.mem_cons_self)) ?_
  exact Proof.ofSubset (fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_self) q

end Seed

/-! ## The witness child, born with the invariants -/

section Birth

variable (hS : ModalSys.BStrong = true) {tp : NodeSt σ} {A : VarType} {y : ℕ}
  (hy : (ctxOf tp.l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) {x : VarSymb}
  {X : VarType} (hX : (ctxOf tp.l).ref x = some (.VTypeDia X))

/-- ⭐The witness child of the atom `◇_x[d ↦ y] Φ` of `tp`. -/
noncomputable def retChildX (Φ : WFF σ (bodyCtxX [.VTypeBox A] tp.l x) 1) : NodeSt σ :=
  ⟨X :: rcl tp.l A, complete (retSeedX hS hy hX tp.M Φ)⟩

variable (hT : ModalSys.T = false) (hM : Theory.IsMCS tp.M)
  {Φ : WFF σ (bodyCtxX [.VTypeBox A] tp.l x) 1}
  (hΦ : WFF.retx hS x ⟨X, hX⟩ (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg tp.l A hy)).2 Φ
    ∈ tp.M)

include hT hM hΦ

theorem retChildX_spec : retSeedX hS hy hX tp.M Φ ⊆ (retChildX hS hy hX Φ).M ∧
    Theory.IsMCS (retChildX hS hy hX Φ).M :=
  complete_spec (retSeedX_consistent hS hy hX hT hM hΦ)

/-- ⭐**The way home at birth**: a witness body true at the child is a returning possibility along
    `x` at the parent — or else the seed has its negation. -/
theorem retChildX_back :
    RetInvX hS (retChildX hS hy hX Φ) tp [.VTypeBox A] (fun _ => y) tp.l Nat.succ x X
      (tp.l.length + 1) := by
  obtain ⟨hsub, hmcs⟩ := retChildX_spec hS hy hX hT hM hΦ
  refine ⟨rclX_suffix tp.l A X, retBackImg tp.l A hy, List.suffix_refl _, rclXImg tp.l A X, hX,
    rclX_cx tp.l A X, fun Θ hΘ => ?_⟩
  rw [WFF.mono_refl]
  by_contra hn
  have h₁ := hsub (Or.inr ⟨Θ, hM.neg_mem_iff.mpr hn, rfl⟩)
  refine hmcs.1 ⟨[_, _], fun x hx => ?_, ⟨Proof.imp_elim
    (φ := liftBodyX (rclX_suffix tp.l A X) (rclXImg tp.l A X) hX (rclX_cx tp.l A X) Θ)
    (Proof.lookup List.mem_cons_self)
    (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁
  · rw [List.mem_singleton.mp hx]; exact hΘ

/-- ⭐**The forward witness arrow at birth**: a witness body true at the parent of its roots'
    necessary object and `x` is the witnessed unit's conjunct read at the child
    (`liftBodyX_unitBodyW`); its negation at the far end would clash with the unit
    (`ret_unitW` with `u := x.dia`, `retx_absurd`), so the seed has `¬¬U`. -/
theorem retChildX_fwd :
    RetInvW hS tp (retChildX hS hy hX Φ) tp.l Nat.succ [.VTypeBox A] (fun _ => y) x X
      (tp.l.length + 1) := by
  obtain ⟨hsub, hmcs⟩ := retChildX_spec hS hy hX hT hM hΦ
  refine ⟨List.suffix_refl _, rclXImg tp.l A X, rclX_suffix tp.l A X, retBackImg tp.l A hy, hX,
    rclX_cx tp.l A X, fun Ψ hΨ => ?_⟩
  refine (congrArg (· ∈ (retChildX hS hy hX Φ).M) (liftBodyX_unitBodyW (rclX_suffix tp.l A X)
    (rclXImg tp.l A X) hX (rclX_cx tp.l A X) hS Ψ)).mp ?_
  have hle := ctxOf_le_of_suffix (List.suffix_refl tp.l)
  have e : WFF.unitBodyW (Γ := ctxOf tp.l) hS (Term.mono hle.boxIn (tupT tp.l).2)
      (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))
      (pack2 [.VTypeBox A] (RShape.wit (.box (bcT tp.l)) X).ty Ψ) =
      WFF.unitBodyW (Γ := ctxOf tp.l) hS (tupT tp.l).2
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))
        (pack2 [.VTypeBox A] (RShape.wit (.box (bcT tp.l)) X).ty Ψ) := by
    rw [Term.mono_refl]
  have hU : WFF.neg (WFF.retx hS x ⟨X, hX⟩
      (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg tp.l A hy)).2
      (WFF.neg (WFF.unitBodyW (Γ := ctxOf tp.l) hS (tupT tp.l).2
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))
        (pack2 [.VTypeBox A] (RShape.wit (.box (bcT tp.l)) X).ty Ψ)))) ∈ tp.M := by
    refine hM.neg_mem_iff.mpr fun hr => hM.1 ⟨[WFF.retx hS x ⟨X, hX⟩
      (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg tp.l A hy)).2
        (WFF.neg (WFF.unitBodyW (Γ := ctxOf tp.l) hS (tupT tp.l).2
          (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))
          (pack2 [.VTypeBox A] (RShape.wit (.box (bcT tp.l)) X).ty Ψ))),
      liftBodyW (List.suffix_refl tp.l) (retBackImg tp.l A hy) hX Ψ], fun x hx => ?_, ⟨?_⟩⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hr
      · rw [List.mem_singleton.mp hx]; exact hΨ
    refine Proof.retx_absurd hS ⟨X, hX⟩ _ _ (ctxOf_fresh (l := tp.l) le_rfl)
      (Proof.conv (by rw [e]) (Proof.ret_unitW hS ⟨X, hX⟩ _ _ (Term.mono hle.boxIn (tupT tp.l).2)
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) _ (Proof.lookup List.mem_cons_self) ?_))
    exact Proof.conv (holeRead_tupImgT_pack2 (retBackImg tp.l A hy)
      (Term.pair (Term.boxtm (Term.mono hle.boxIn (tupT tp.l).2))
        (Term.eta x (.VTypeDia X) (hle.ref hX))) Ψ).symm
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
  have h₁ := hsub (Or.inr ⟨_, hU, rfl⟩)
  exact hmcs.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact h₁,
    ⟨Proof.byContra (Proof.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.lookup List.mem_cons_self))⟩⟩

/-- ⭐**The witness child is born with the invariants**: `RetInvW` out along `x`, `RetInvX` home. -/
theorem RetData.retBirthX : RetData hS tp (retChildX hS hy hX Φ) (some (x, X)) none
    (tp.l.length + 1) 0 tp.l Nat.succ [.VTypeBox A] (fun _ => y) :=
  ⟨retChildX_fwd hS hy hX hT hM hΦ, retChildX_back hS hy hX hT hM hΦ⟩

end Birth

/-! ## The operation -/

namespace NetSt

/-- A returning-possibility obligation along a witness: over a list of a node's variables, the
    type `A` of what comes back, the witness `x`, the alias `y` and the atom's body. -/
abbrev RetOblX (σ : Signature) :=
  Σ l : List VarType, Σ A : VarType, Σ x : VarSymb, ℕ × WFF σ (bodyCtxX [.VTypeBox A] l x) 1

open Classical in
/-- ⭐Give the node `s` the witness child of its atom `◇_x[d ↦ y] Φ`, if it has it. -/
noncomputable def mkRetX (hS : ModalSys.BStrong = true) (N : NetSt σ) (s : Node) :
    RetOblX σ → NetSt σ
  | ⟨l, A, x, y, Φ⟩ =>
      if h : l <:+ (N.st s).l then
        if hy : (ctxOf (N.st s).l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc then
          match hX : (ctxOf (N.st s).l).ref x with
          | some (.VTypeDia X) =>
              if WFF.retx hS x ⟨X, hX⟩ (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg _ A hy)).2
                  (WFF.mono (((ctxOf_le_of_suffix h).diaIn x).insert (.bnd 0) _) Φ) ∈
                  (N.st s).M then
                N.newChild s (some (x, X)) ((N.st s).l.length + 1)
                  (retChildX hS hy hX
                    (WFF.mono (((ctxOf_le_of_suffix h).diaIn x).insert (.bnd 0) _) Φ))
                  Nat.succ [.VTypeBox A] (fun _ => y)
              else N
          | _ => N
        else N
      else N

theorem Ext.mkRetX {hS : ModalSys.BStrong = true} {N : NetSt σ} {s : Node} (hs : N.Live s)
    (o : RetOblX σ) : Ext N (N.mkRetX hS s o) := by
  obtain ⟨l, A, x, y, Φ⟩ := o
  simp only [NetSt.mkRetX]
  split_ifs
  · split
    · split_ifs
      · exact Ext.newChild hs _ _ _ _ _ _
      · exact Ext.refl N
    · exact Ext.refl N
  all_goals exact Ext.refl N

end NetSt

end BArrow

end V12M
