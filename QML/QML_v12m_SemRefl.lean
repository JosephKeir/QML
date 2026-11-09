import QML.QML_v12m_LoopHat
import QML.QML_v12m_SemHere

/-!
# QML v12m — the soundness of U with objects

With 4 and 5, `side a a` is a left unit at `a`'s target, and `a ; side a a = a`.  So at a world an
arrow reaches, reading `□` along that arrow is reading the world itself: the old items are as they
were, and a slot kept along it is the slot.  With `shaped` off that holds at `◇` objects too.

* ⭐`Frame.side_cocycle`, ⭐`Frame.side_self_unit`;
* `Model.keepOf_unit`: a tuple kept along a left unit is the tuple;
* ⭐`Model.sat_fiveRefl`.
-/

namespace V12M

variable [ModalSys]

/-- With 4 and 5, `side` composes: `(side x y) ; (side y z) = side x z`. -/
theorem Frame.side_cocycle {σ : Signature} (F : Frame σ) (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) {w u v t : F.W} (x : F.R w u) (y : F.R w v) (z : F.R w t) :
    F.trans hF (F.side hV x y) (F.side hV y z) = F.side hV x z := by
  have h := F.trans_side hF hV (F.side hV x y) (F.side hV x z)
  rwa [F.side_side hV x y z] at h

/-- ⭐**`side a a` is a left unit**, in every frame with 4 and 5, relational or not, and `a` followed
    by it is `a`.  So at every world an arrow reaches, `□φ̂(k) → φ(k)` holds. -/
theorem Frame.side_self_unit {σ : Signature} (F : Frame σ) (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) {w v t : F.W} (a : F.R w v) (c : F.R v t) :
    F.trans hF (F.side hV a a) c = c := by
  have he := F.side_cocycle hF hV a a a
  have hc := F.trans_side hF hV (F.side hV a a) c
  rw [← hc, ← F.trans_assoc hF, he]

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

/-- A necessary object kept along a left unit is itself. -/
theorem necDup_unit (hF : ModalSys.Four = true) {v : M.frame.W} (e : M.frame.R v v)
    (hu : ∀ {t : M.frame.W} (b : M.frame.R v t), M.frame.trans hF e b = b) {A : VarType}
    (n : M.frame.Nec A v) : M.necEval (M.ops.necDup hF n) ⟨v, ⟨e⟩⟩ = n := by
  refine M.nec_inj ?_
  funext s
  rw [M.necDup_eval hF n ⟨v, ⟨e⟩⟩ s, hu]

/-- A possible object kept along a left unit is itself, with shapes off. -/
theorem posKeep_unit (hF : ModalSys.Four = true) (hN : ModalSys.shaped = false) {v : M.frame.W}
    (e : M.frame.R v v)
    (hu : ∀ {t : M.frame.W} (b : M.frame.R v t), M.frame.trans hF e b = b) {A : VarType}
    (q : M.frame.Pos A v) : M.necEval (M.ops.posKeep hF q) ⟨v, ⟨e⟩⟩ = q := by
  refine M.posFull_inj (Prod.ext ?_ (funext fun h => by simp [hN] at h))
  have key : ∀ (g : ∀ b : M.frame.Acc v, PLift (M.frame.R v b.1)), (∀ b, g b = b.2) →
      ((⟨{b | (⟨b.1, g b⟩ : M.frame.Acc v) ∈ (M.posFull q).1.1},
        fun b => (M.posFull q).1.2 ⟨⟨b.1.1, g b.1⟩, b.2⟩⟩ : M.frame.PosSec A v) =
        (M.posFull q).1) := by
    intro g hg
    obtain rfl : g = fun b => b.2 := funext hg
    rfl
  have h₁ := congrArg Prod.fst (M.posKeep_full hF q ⟨v, ⟨e⟩⟩)
  dsimp only at h₁
  rw [h₁]
  exact key (fun b => ⟨M.frame.trans hF e b.2.down⟩) (fun b => congrArg PLift.up (hu b.2.down))

/-- ⭐**A tuple kept along a left unit is the tuple.** -/
theorem keepOf_unit (hF : ModalSys.Four = true) (hN : ModalSys.shaped = false) {Ω : Ctx}
    {v : M.frame.W} (env : M.Env Ω v) (e : M.frame.R v v)
    (hu : ∀ {t : M.frame.W} (b : M.frame.R v t), M.frame.trans hF e b = b) :
    ∀ (T : VarType) (ht : T.tup = true) (c : VarSymb) (hc : Ω.ref c = some T),
      interp (env.boxPush ⟨v, ⟨e⟩⟩) (Term.keepOf hF T ht c hc) = env.ref c hc
  | .VTypeOne, _, _, _ => rfl
  | .Var, ht, _, _ => by cases ht
  | .VTypeProd A B, ht, c, hc => by
      have hAB : A.tup = true ∧ B.tup = true := by simpa [VarType.tup] using ht
      refine Prod.ext ?_ ?_
      · exact (keepOf_unit hF hN env e hu A hAB.1 _ (Ctx.ref_fst_of hc)).trans
          (Env.ref_fst env hc (Ctx.ref_fst_of hc))
      · exact (keepOf_unit hF hN env e hu B hAB.2 _ (Ctx.ref_snd_of hc)).trans
          (Env.ref_snd env hc (Ctx.ref_snd_of hc))
  | .VTypeBox A, _, c, hc => by
      refine (interp_eta _ _ _).trans ?_
      exact necDup_unit hF e hu (env.ref c hc)
  | .VTypeDia A, _, c, hc => by
      refine (interp_eta _ _ _).trans ?_
      exact posKeep_unit hF hN e hu (env.ref c hc)

/-- A body read at a term of a larger context. -/
theorem sat_singleAt {Λ Ω : Ctx} {T : VarType} {d d' : ℕ} (hle : Λ.Le Ω)
    (hr : Λ.RootFresh (.bnd 0)) (hΛ : (Λ.insert (.bnd 0) T).SlotsFrom d) (hs : Ω.SlotsFrom d')
    (hnp : Λ.NoProjLast) {w : M.frame.W} (env : M.Env Ω w) (env₀ : M.Env Λ w)
    (hag : Env.Agree hle env₀ env) {a : Ann T} (u : Term σ Ω T a)
    (B : WFF σ (Λ.insert (.bnd 0) T) d) (_hO : ModalSys.Opt = false := by opt_off) :
    M.sat env (WFF.subst (Subst.singleIdx (.bnd 0) (.tm u)) (Subst.single (.bnd 0) (.tm u))
        (Subst.ok_single hle rfl) (Subst.coh_single hr hle rfl) hΛ hs B) ↔
      M.sat (env₀.extend (.bnd 0) (interp env u)) B := by
  refine (sat_subst _ _ _ _ _ (hnp.insert _ T) env B).trans (sat_congr_val (fun v U hv => ?_) B)
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    rw [substEnv_val]
    exact (entryVal_congr env
      (show Subst.single (.bnd 0) (.tm u) (.root (.bnd 0)) = .tm u from by slot_rfl) _ rfl).trans
      (Env.extend_root env₀ (.bnd 0) _ hv).symm
  · have hv' : Λ v = some U := by simpa [Ctx.insert, hvr] using hv
    have hl := hnp v U hv'
    rw [substEnv_val]
    exact (entryVal_congr env (show Subst.single (.bnd 0) (.tm u) v = .ren v from if_neg hvr) _
      ((Ctx.ref_nonproj Ω hl).trans (hle v U hv'))).trans
      ((Env.ref_of_nonproj env hl _ _).trans
        ((hag v U hv').symm.trans (Env.extend_ne env₀ _ _ hv hvr hv').symm))

/-- A world's `□` view sits inside its `◇_x` view, with the same values. -/
theorem Env.agree_boxIn_diaIn {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {x : VarSymb}
    {X : VarType} (hx : Γ.ref x = some (.VTypeDia X)) (i : (M.posEval (env.ref x hx)).1) :
    Env.Agree (Ctx.le_boxIn_diaIn Γ x) (env.boxPush i.1) (env.diaPush x hx i) := by
  intro v T hv
  match v with
  | .step u .box => rfl
  | .step u .keep => rfl
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

variable {T : VarType}

/-- ⭐**U with objects, along `□`.** -/
theorem sat_fiveRefl_nec (hF : ModalSys.Four = true) (hV : ModalSys.Five = true)
    (hN : ModalSys.shaped = false) (hT : T.tup = true) {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W}
    (env : M.Env Γ w) (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) :
    M.sat env (WFF.fiveRefl hF hT (.nec : OutLeg Γ) φ) := by
  rintro ⟨v, ⟨a⟩⟩ k hb
  have he := M.frame.trans_side hF hV a a
  have hu : ∀ {t : M.frame.W} (b : M.frame.R v t),
      M.frame.trans hF (M.frame.side hV a a) b = b := fun b =>
    M.frame.side_self_unit hF hV a b
  have hrV := (Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)
  have hrV₂ := (Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).rootFresh (le_refl 0)
  have hle := Ctx.le_insert hrV.root T
  have hag : Env.Agree hle (env.boxPush ⟨v, ⟨a⟩⟩) ((env.boxPush ⟨v, ⟨a⟩⟩).extend (.bnd 0) k) := by
    have := Env.agree_restrict hle ((env.boxPush ⟨v, ⟨a⟩⟩).extend (.bnd 0) k)
    rwa [Env.restrict_extend _ hrV.root k] at this
  have h₁ := (sat_singleAt hle.boxIn hrV₂ ((Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).insert T)
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T).boxIn (Ctx.noProjLast_boxIn _)
    (((env.boxPush ⟨v, ⟨a⟩⟩).extend (.bnd 0) k).boxPush ⟨v, ⟨M.frame.side hV a a⟩⟩)
    ((env.boxPush ⟨v, ⟨a⟩⟩).boxPush ⟨v, ⟨M.frame.side hV a a⟩⟩)
    (Env.boxPush_agree hag _) (Term.keepOf hF T hT (.root (.bnd 0))
      (Ctx.ref_insert_root Γ.boxIn (.bnd 0) T))
    (WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T) φ)).mp
    (hb ⟨v, ⟨M.frame.side hV a a⟩⟩)
  have hkv : interp (((env.boxPush ⟨v, ⟨a⟩⟩).extend (.bnd 0) k).boxPush
      ⟨v, ⟨M.frame.side hV a a⟩⟩) (Term.keepOf (σ := σ) hF T hT (.root (.bnd 0))
        (Ctx.ref_insert_root Γ.boxIn (.bnd 0) T)) = k := by
    rw [keepOf_unit hF hN _ _ hu T hT]
    exact Env.extend_root _ _ _ _
  rw [hkv] at h₁
  have h₂ := (sat_shift ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T)
    ((Env.shiftAgree_twoBox hF env ⟨v, ⟨a⟩⟩ ⟨v, ⟨M.frame.side hV a a⟩⟩).extend hrV k) φ).mp h₁
  have key : ∀ c : M.frame.R w v, c = a →
      M.sat ((env.boxPush ⟨v, ⟨c⟩⟩).extend (.bnd 0) k) φ →
      M.sat ((env.boxPush ⟨v, ⟨a⟩⟩).extend (.bnd 0) k) φ := by
    rintro _ rfl h
    exact h
  exact key _ he h₂

/-- ⭐**U with objects, along `◇_x`**: `side a a` lies in `x.keep`'s extent, `a` being in `x`'s and
    `a ; side a a = a`, with the same content. -/
theorem sat_fiveRefl_pos (hF : ModalSys.Four = true) (hV : ModalSys.Five = true)
    (hN : ModalSys.shaped = false) (hT : T.tup = true) {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W}
    (env : M.Env Γ w) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) :
    M.sat env (WFF.fiveRefl hF hT (.pos x hx : OutLeg Γ) φ) := by
  rintro ⟨X, hr, ⟨⟨v, ⟨a⟩⟩, ham⟩, hneg⟩
  refine hneg fun k hb => ?_
  by_contra hφ
  have he := M.frame.trans_side hF hV a a
  have hu : ∀ {t : M.frame.W} (b : M.frame.R v t),
      M.frame.trans hF (M.frame.side hV a a) b = b := fun b =>
    M.frame.side_self_unit hF hV a b
  have hrk : Γ.boxIn.ref (.step x .keep) = some (.VTypeDia X) :=
    Ctx.ref_keep_of' hF hr VarType.keepable_dia
  have hrU := (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).rootFresh (le_refl 0)
  have hleU := Ctx.le_insert hrU.root T
  have hL := Ctx.le_boxIn_body Γ x T
  have hrk' := hL.ref hrk
  -- The body's environment, and its `□` part.
  have hag₁ : Env.Agree hleU (env.diaPush x hr ⟨⟨v, ⟨a⟩⟩, ham⟩)
      ((env.diaPush x hr ⟨⟨v, ⟨a⟩⟩, ham⟩).extend (.bnd 0) k) := by
    have := Env.agree_restrict hleU ((env.diaPush x hr ⟨⟨v, ⟨a⟩⟩, ham⟩).extend (.bnd 0) k)
    rwa [Env.restrict_extend _ hrU.root k] at this
  have hag₀ : Env.Agree hL (env.boxPush ⟨v, ⟨a⟩⟩)
      ((env.diaPush x hr ⟨⟨v, ⟨a⟩⟩, ham⟩).extend (.bnd 0) k) := fun u U hv =>
    (Env.agree_boxIn_diaIn env hr ⟨⟨v, ⟨a⟩⟩, ham⟩ u U hv).trans (hag₁ u U _)
  -- The own arrow lies in `x.keep`'s extent.
  have hm : (⟨v, ⟨M.frame.trans hF a (M.frame.side hV a a)⟩⟩ : M.frame.Acc w) ∈
      (M.posEval (env.ref x hr)).1 := by
    rw [he]
    exact ham
  have hb' : (⟨v, ⟨M.frame.side hV a a⟩⟩ : M.frame.Acc v) ∈
      (M.posEval ((env.boxPush ⟨v, ⟨a⟩⟩).ref (.step x .keep) hrk)).1 := by
    have H := congrArg Prod.fst (M.posKeep_full hF (env.ref x hr) ⟨v, ⟨a⟩⟩)
    exact (congrArg (fun S : M.frame.PosSec _ _ => (⟨v, ⟨M.frame.side hV a a⟩⟩ : M.frame.Acc v) ∈
      S.1) H).mpr hm
  have hE : (⟨v, ⟨M.frame.side hV a a⟩⟩ : M.frame.Acc v) ∈ (M.posEval
      (((env.diaPush x hr ⟨⟨v, ⟨a⟩⟩, ham⟩).extend (.bnd 0) k).ref (.step x .keep) hrk')).1 := by
    rw [← Env.ref_agree hag₀ (.step x .keep) hrk]
    exact hb'
  refine hb ⟨X, hrk', ⟨⟨v, ⟨M.frame.side hV a a⟩⟩, hE⟩, fun hh => hφ ?_⟩
  have hrD := (Ctx.NoSlots.slots (Γ := Γ.boxIn.diaIn (.step x .keep))).rootFresh (le_refl 0)
  have h₁ := (sat_singleAt (hL.diaIn _) hrD
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn.diaIn (.step x .keep))).insert T)
    (((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert T).diaIn _) (Ctx.noProjLast_diaIn _ _)
    (((env.diaPush x hr ⟨⟨v, ⟨a⟩⟩, ham⟩).extend (.bnd 0) k).diaPush (.step x .keep) hrk'
      ⟨⟨v, ⟨M.frame.side hV a a⟩⟩, hE⟩)
    ((env.boxPush ⟨v, ⟨a⟩⟩).diaPush (.step x .keep) hrk ⟨⟨v, ⟨M.frame.side hV a a⟩⟩, hb'⟩)
    (Env.diaPush_agree hag₀ hrk ⟨⟨v, ⟨M.frame.side hV a a⟩⟩, hb'⟩ hE)
    (Term.keptSlotX (σ := σ) hF hT Γ x)
    (WFF.shift (Ctx.shifts_loopX hF Γ x T) ((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert T) φ)).mp hh
  have hkv : interp (((env.diaPush x hr ⟨⟨v, ⟨a⟩⟩, ham⟩).extend (.bnd 0) k).diaPush (.step x .keep)
      hrk' ⟨⟨v, ⟨M.frame.side hV a a⟩⟩, hE⟩) (Term.keptSlotX (σ := σ) hF hT Γ x) = k := by
    rw [interp_mono (Env.agree_boxIn_diaIn _ hrk' _), keepOf_unit hF hN _ _ hu T hT]
    exact Env.extend_root _ _ _ _
  rw [hkv] at h₁
  have h₂ := (sat_shift ((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert T)
    ((Env.shiftAgree_diaKeep hF env hr ⟨v, ⟨a⟩⟩ ⟨v, ⟨M.frame.side hV a a⟩⟩ hm hrk hb').extend
      hrU k) φ).mp h₁
  have key : ∀ (c : M.frame.R w v) (hc : (⟨v, ⟨c⟩⟩ : M.frame.Acc w) ∈ (M.posEval (env.ref x hr)).1),
      c = a → M.sat ((env.diaPush x hr ⟨⟨v, ⟨c⟩⟩, hc⟩).extend (.bnd 0) k) φ →
      M.sat ((env.diaPush x hr ⟨⟨v, ⟨a⟩⟩, ham⟩).extend (.bnd 0) k) φ := by
    rintro _ _ rfl h
    exact h
  exact key _ hm he h₂

/-- ⭐**U with objects**, along either leg, in every model with 4, 5 and no shapes. -/
theorem sat_fiveRefl (hF : ModalSys.Four = true) (hV : ModalSys.Five = true)
    (hN : ModalSys.shaped = false) (hT : T.tup = true) {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W}
    (env : M.Env Γ w) : (O : OutLeg Γ) → (φ : WFF σ (O.view.insert (.bnd 0) T) 1) →
    M.sat env (WFF.fiveRefl hF hT O φ)
  | .nec, φ => sat_fiveRefl_nec hF hV hN hT env φ
  | .pos _ hx, φ => sat_fiveRefl_pos hF hV hN hT env hx φ

end Model

end V12M
