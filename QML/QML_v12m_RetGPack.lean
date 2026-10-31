import QML.QML_v12m_RetLiftW
import QML.QML_v12m_GView

/-!
# QML v12m — closing a body over the `□` view's tuple, under 4

`BArrow.pack2` with 4 on.  A body over a world's `□` view has parameters, so it is not a hole
formula, and the units only carry hole formulas.  `gpack` sends each item of the `□` view to its
place in the view's tuple (`GArrow.boxItems`, `itemsTm`), so a body becomes a hole formula on the
tuple and its slot, and reading it at the tuple gives the body back (`holeAt_gtup_gpack`).
-/

namespace V12M

variable [ModalSys] {σ : Signature}

open BArrow GArrow

/-- Where the item `v` sits in a tuple of items at `w`. -/
def itemsAt : List (VarSymb × VarType) → VarSymb → VarSymb → VarSymb
  | [], w, _ => w
  | e :: L, w, v => if e.1 = v then .step w .fst else itemsAt L (.step w .snd) v

omit [ModalSys] in
/-- An entry of the list at the item's own address has the item's type. -/
theorem entry_ty {G : VarSymb → Option VarType} {e : VarSymb × VarType} {v : VarSymb}
    {T : VarType} (he : G e.1 = some e.2) (hv : G v = some T) (h : e.1 = v) : e.2 = T := by
  rw [h, hv] at he
  exact (Option.some.inj he).symm

/-- The item is declared where it sits in the tuple. -/
theorem ref_itemsAt {Δ : Ctx} {G : VarSymb → Option VarType} :
    ∀ (L : List (VarSymb × VarType)) (w : VarSymb), Δ.ref w = some (itemsTy L) →
      (∀ e ∈ L, G e.1 = some e.2) → ∀ (v : VarSymb) (T : VarType), (v, T) ∈ L →
      Δ.ref (itemsAt L w v) = some T
  | [], _, _, _, _, _, hm => absurd hm List.not_mem_nil
  | e :: L, w, hw, hG, v, T, hm => by
      unfold itemsAt
      split_ifs with he
      · have hT : e.2 = T := entry_ty (hG e List.mem_cons_self) (hG (v, T) hm) he
        rw [← hT]
        exact Ctx.ref_fst_of hw
      · refine ref_itemsAt L _ (Ctx.ref_snd_of hw)
          (fun e' he' => hG e' (List.mem_cons_of_mem _ he')) v T ?_
        rcases List.mem_cons.mp hm with h | h
        · exact absurd (congrArg Prod.fst h).symm he
        · exact h

/-- A substitution with the tuple at `w` sends the item's place to the item. -/
theorem at_itemsAt {Γ Δ : Ctx} (hle : Γ.Le Δ) (θ : Subst σ Δ) {G : VarSymb → Option VarType} :
    ∀ (L : List (VarSymb × VarType)) (hL : ∀ e ∈ L, Γ.ref e.1 = some e.2) (w : VarSymb),
      θ.at w = .tm (Term.mono hle (itemsTm L hL).2) → (∀ e ∈ L, G e.1 = some e.2) →
      ∀ (v : VarSymb) (T : VarType) (hv : Γ.ref v = some T), (v, T) ∈ L →
      θ.at (itemsAt L w v) = .tm (Term.mono hle (Term.eta v T hv))
  | [], _, _, _, _, _, _, _, hm => absurd hm List.not_mem_nil
  | e :: L, hL, w, hw, hG, v, T, hv, hm => by
      unfold itemsAt
      split_ifs with he
      · have hT : e.2 = T := entry_ty (hG e List.mem_cons_self) (hG (v, T) hm) he
        obtain ⟨e₁, e₂⟩ := e
        obtain rfl : e₁ = v := he
        obtain rfl : e₂ = T := hT
        rw [Subst.at_proj _ _ rfl, hw]
        rfl
      · refine at_itemsAt hle θ L (fun e' he' => hL e' (List.mem_cons_of_mem _ he')) _ ?_
          (fun e' he' => hG e' (List.mem_cons_of_mem _ he')) v T hv ?_
        · rw [Subst.at_proj _ _ rfl, hw]
          rfl
        · rcases List.mem_cons.mp hm with h | h
          · exact absurd (congrArg Prod.fst h).symm he
          · exact h

section Pack

variable (l : List VarType) (U : VarType)

/-- The hole of a closed body: the view's tuple and the body's slot. -/
abbrev gpackCtx : Ctx := Ctx.empty.insert (.bnd 0) (.VTypeProd (itemsTy (boxItems l)) U)

theorem gpackCtx_fst : (gpackCtx l U).ref (.step (.root (.bnd 0)) .fst) =
    some (itemsTy (boxItems l)) :=
  Ctx.ref_fst_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) _)

theorem gpackCtx_snd : (gpackCtx l U).ref (.step (.root (.bnd 0)) .snd) = some U :=
  Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) _)

/-- Each item goes to its place in the tuple. -/
def gpackF (v : VarSymb) : VarSymb := itemsAt (boxItems l) (.step (.root (.bnd 0)) .fst) v

theorem itemOk_gpackF (hF : ModalSys.Four = true) :
    ItemOk (ctxOf l).boxIn (gpackCtx l U) (gpackF l) := fun v T _ hv =>
  ref_itemsAt (boxItems l) _ (gpackCtx_fst l U) (boxItems_spec hF l) v T (mem_boxItems hv)

/-- ⭐The closing substitution: the items to the tuple, the slot to the second component. -/
def gpackS : Subst σ (gpackCtx l U) :=
  (itemS σ (gpackCtx l U) (gpackF l)).set (.bnd 0) (.ren (.step (.root (.bnd 0)) .snd))

/-- Where `gpackS` sends annotation indices. -/
def gpackIdx : VarSymb → VarSymb :=
  Subst.setIdx (itemIdx (gpackF l)) (.bnd 0)
    (.ren (.step (.root (.bnd 0)) .snd) : SubE σ (gpackCtx l U))

theorem ok_gpackS (hF : ModalSys.Four = true) :
    Subst.Ok ((ctxOf l).boxIn.insert (.bnd 0) U) (gpackS (σ := σ) l U) :=
  Subst.ok_set (ok_itemS_kView (k := none) (itemOk_gpackF l U hF)) (gpackCtx_snd l U)

theorem coh_gpackS (hF : ModalSys.Four = true) :
    Subst.Coh (gpackIdx (σ := σ) l U) ((ctxOf l).boxIn.insert (.bnd 0) U)
      (gpackS (σ := σ) l U) :=
  Subst.coh_set (ok_itemS_kView (k := none) (itemOk_gpackF l U hF))
    (coh_itemS_kView (k := none) (itemOk_gpackF l U hF))
    ((Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).rootFresh (le_refl 0)) (gpackCtx_snd l U)

/-- ⭐A body closed into a hole formula over the view's tuple and its slot. -/
def gpack (hF : ModalSys.Four = true) (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) U) 1) :
    WFF σ (gpackCtx l U) 1 :=
  WFF.subst (gpackIdx (σ := σ) l U) (gpackS l U) (ok_gpackS l U hF) (coh_gpackS l U hF)
    ((Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).insert U) (Ctx.slotsFrom_empty.insert _) Φ

end Pack

/-- The `□` view's tuple. -/
abbrev viewTup (hF : ModalSys.Four = true) (l : List VarType) :
    Σ a, Term σ (ctxOf l).boxIn (itemsTy (boxItems l)) a :=
  itemsTm (boxItems l) (boxItems_ref hF l)

/-- ⭐A closed body read at the view's tuple and its slot: the body, weakened. -/
theorem holeAt_gtup_gpack (hF : ModalSys.Four = true) {l : List VarType} {U : VarType} {Δ : Ctx}
    [Δ.NoSlots] (h : (ctxOf l).boxIn.Le Δ) (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) U) 1) :
    WFF.holeAt ((Ctx.NoSlots.slots (Γ := Δ)).insert U)
      (Term.pair (Term.mono (h.trans (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Δ)).root U))
          (viewTup (σ := σ) hF l).2)
        (Term.eta (.root (.bnd 0)) U (Ctx.ref_insert_root Δ (.bnd 0) U)))
      (gpack l U hF Φ) = WFF.mono (h.insert (.bnd 0) U) Φ := by
  have hle := h.trans (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Δ)).root U)
  unfold WFF.holeAt gpack
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ (Subst.ok_idS_le (h.insert (.bnd 0) U))
    (Subst.coh_idS_le (h.insert (.bnd 0) U)) _ _ _ ?_ Φ).trans
    (WFF.subst_ren (h.insert (.bnd 0) U) _ _ _ _ _ (fun v _ _ => Subst.at_idS v) Φ)
  refine Subst.sim_of fun v T hlp hv => ?_
  have h0 := Subst.at_single_root (σ := σ) (Δ := Δ.insert (.bnd 0) U) (.bnd 0)
    (.tm (Term.pair (Term.mono hle (viewTup (σ := σ) hF l).2)
      (Term.eta (.root (.bnd 0)) U (Ctx.ref_insert_root Δ (.bnd 0) U))))
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = U := by simpa [Ctx.insert] using hv.symm
    dsimp only [Subst.comp, gpackS]
    rw [Subst.set_root]
    dsimp only [SubE.comp]
    rw [Subst.at_proj _ _ rfl, h0]
    exact .ren_eta _ _
  · have hv' : (ctxOf l).boxIn v = some T := by simpa [Ctx.insert, hvr] using hv
    obtain ⟨u, s, rfl, -, -⟩ := kView_item (k := none) hv'
    have hs : s.isProj = false := hlp
    have hb : (Subst.single (σ := σ) (Δ := Δ.insert (.bnd 0) U) (.bnd 0)
        (.tm (Term.pair (Term.mono hle (viewTup (σ := σ) hF l).2)
          (Term.eta (.root (.bnd 0)) U (Ctx.ref_insert_root Δ (.bnd 0) U))))).at
          (.step (.root (.bnd 0)) .fst) = .tm (Term.mono hle (viewTup (σ := σ) hF l).2) := by
      rw [Subst.at_proj _ _ rfl, h0]
      rfl
    have hit := (Ctx.ref_nonproj (ctxOf l).boxIn hlp).trans hv'
    dsimp only [Subst.comp, gpackS]
    rw [Subst.set_ne _ _ hvr]
    change SubE.Sim T _ (SubE.comp _ _ _ (if s.isProj then SubE.hide else
      .ren (gpackF l (.step u s))))
    rw [if_neg (by simp [hs])]
    change SubE.Sim T (.ren _) (Subst.at _ (itemsAt (boxItems l) _ _))
    rw [at_itemsAt hle _ (boxItems l) (boxItems_ref hF l) _ hb (boxItems_spec hF l) _ T hit
      (mem_boxItems hv'), Term.mono_eta]
    exact .ren_eta _ _

/-- ⭐A closed body read at the tuple and any object: the body at that object. -/
theorem holeAt_gtup_gpack_at (hF : ModalSys.Four = true) {l : List VarType} {U : VarType} {Δ : Ctx}
    [Δ.NoSlots] (h : (ctxOf l).boxIn.Le Δ) (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) U) 1)
    {u₀ : Ann U} (X : Term σ Δ U u₀) :
    WFF.holeAt Ctx.NoSlots.slots (Term.pair (Term.mono h (viewTup (σ := σ) hF l).2) X)
        (gpack l U hF Φ) =
      WFF.instantiate Ctx.NoSlots.slots X (WFF.mono (h.insert (.bnd 0) U) Φ) := by
  rw [← holeAt_gtup_gpack hF h Φ, ← WFF.instantiate_holeAt_pair (Term.mono h _) _ X,
    Term.mono_mono]

/-! ## Shifting and collapsing a hole read -/

section HoleRead

theorem Ctx.shifts_hole (k : ℕ) (H : VarType) :
    Ctx.Shifts k (Ctx.empty.insert (.bnd 0) H) (Ctx.empty.insert (.bnd 0) H) :=
  Ctx.Shifts.insert (Ctx.Shifts.of_raw fun _ _ _ hv => by cases hv) (Ctx.RootFresh.empty _) H

theorem Ctx.collapses_hole (k : ℕ) (H : VarType) :
    Ctx.Collapses k (Ctx.empty.insert (.bnd 0) H) (Ctx.empty.insert (.bnd 0) H) :=
  Ctx.Collapses.insert (Ctx.Collapses.of_raw fun _ _ _ hv => by cases hv)
    (Ctx.RootFresh.empty _) H

theorem Ctx.shiftCollapseId_hole (m : ℕ) (H : VarType) :
    (Ctx.empty.insert (.bnd 0) H).ShiftCollapseId m :=
  Ctx.ShiftCollapseId.insert (Ctx.ShiftCollapseId.of_raw fun _ _ _ hv => by cases hv) _ H

/-- Shifting a hole read shifts the term and the hole formula. -/
theorem WFF.shift_holeAt {k : ℕ} {Γ Γ' : Ctx} {d : ℕ} (D : Ctx.Shifts k Γ Γ')
    (hs : Γ.SlotsFrom d) (hs' : Γ'.SlotsFrom d) {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) :
    WFF.shift D hs (WFF.holeAt hs t ψ) = WFF.holeAt hs' (Term.shift D t)
      (WFF.shift (Ctx.shifts_hole k A) (Ctx.slotsFrom_empty.insert A) ψ) := by
  unfold WFF.holeAt
  refine WFF.shift_subst (Ctx.shifts_hole k A) D _ _ _ _ _ _ _ _ _ _
    (Subst.shiftCorr_of (Subst.ok_single (e := .tm t) (Ctx.empty_le Γ) rfl) ?_) ψ
  intro v T _ hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    change SubE.Sim T
      (Subst.single (σ := σ) (Δ := Γ') (.bnd 0) (.tm (Term.shift D t)) (.root (.bnd 0)))
      (SubE.shift D (Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm t) (.root (.bnd 0))))
    unfold Subst.single
    rw [if_pos rfl, if_pos rfl]
    exact .refl _
  · change (if v = VarSymb.root (.bnd 0) then _ else Ctx.empty v) = _ at hv
    rw [if_neg hvr] at hv
    cases hv

/-- Collapsing a hole read collapses the term and the hole formula. -/
theorem WFF.collapse_holeAt {k : ℕ} {Γ Γ' : Ctx} {d : ℕ} (D : Ctx.Collapses k Γ Γ')
    (hs : Γ.SlotsFrom d) (hs' : Γ'.SlotsFrom d) {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) :
    WFF.collapse D hs (WFF.holeAt hs t ψ) = WFF.holeAt hs' (Term.collapse D t)
      (WFF.collapse (Ctx.collapses_hole k A) (Ctx.slotsFrom_empty.insert A) ψ) := by
  unfold WFF.holeAt
  refine WFF.collapse_subst (Ctx.collapses_hole k A) D _ _ _ _ _ _ _ _ _ _
    (Subst.corr_of (Subst.ok_single (e := .tm t) (Ctx.empty_le Γ) rfl) ?_) ψ
  intro v T _ hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    change SubE.Sim T
      (Subst.single (σ := σ) (Δ := Γ') (.bnd 0) (.tm (Term.collapse D t)) (.root (.bnd 0)))
      (SubE.collapse D (Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm t) (.root (.bnd 0))))
    unfold Subst.single
    rw [if_pos rfl, if_pos rfl]
    exact .refl _
  · change (if v = VarSymb.root (.bnd 0) then _ else Ctx.empty v) = _ at hv
    rw [if_neg hvr] at hv
    cases hv

/-- A hole read that does not mention the slot, with the slot filled. -/
theorem WFF.instantiate_holeAt_mono {Ω : Ctx} [Ω.NoSlots] {B : VarType} {b₀ : Ann B}
    (b : Term σ Ω B b₀) {H : VarType} {u₀ : Ann H} (u : Term σ Ω H u₀)
    (Θ : WFF σ (Ctx.empty.insert (.bnd 0) H) 1) :
    WFF.instantiate Ctx.NoSlots.slots b (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Ω)).insert B)
      (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Ω)).root B) u) Θ) =
      WFF.holeAt Ctx.NoSlots.slots u Θ := by
  unfold WFF.instantiate WFF.substRoot
  rw [WFF.subst_holeAt]
  exact WFF.holeAt_congr _ (Term.subst_single_mono_sig b u) Θ

end HoleRead

/-! ## Into a kept object's extent -/

section KeepDia

variable {Γ : Ctx} [Γ.NoSlots] {H : VarType} {s₀ : Ann H}

/-- The `□`-view formula that `here_elim` reads, at the kept object. -/
def keepRead (hF : ModalSys.Four = true) (X : VarType) (s : Term σ Γ.boxIn H s₀)
    (Θ : WFF σ (Ctx.empty.insert (.bnd 0) H) 1) : WFF σ (Γ.boxIn.boxIn.insert (.bnd 0) X) 1 :=
  WFF.holeAt ((Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).insert X)
    (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).root X)
      (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) s))
    (WFF.shift (Ctx.shifts_hole 0 H) (Ctx.slotsFrom_empty.insert H) Θ)

/-- Read in the `◇_{x.keep}` view, `keepRead` is the shifted formula, whatever the content. -/
theorem WFF.viewRead_keepRead (hF : ModalSys.Four = true) (x : VarSymb) {X : VarType} {b₀ : Ann X}
    (b : Term σ (Γ.boxIn.diaIn (.step x .keep)) X b₀) (s : Term σ Γ.boxIn H s₀)
    (Θ : WFF σ (Ctx.empty.insert (.bnd 0) H) 1) :
    WFF.viewReadTm b (keepRead hF X s Θ) =
      WFF.shift (Ctx.shifts_diaIn_keep hF Γ x) Ctx.NoSlots.slots (WFF.holeAt Ctx.NoSlots.slots
        (Term.mono (Ctx.le_boxIn_diaIn Γ x) s) Θ) := by
  have L' := Ctx.le_boxIn_diaIn Γ.boxIn (.step x .keep)
  rw [WFF.shift_holeAt _ _ Ctx.NoSlots.slots,
    Term.shift_mono (Ctx.shifts_boxIn_boxIn hF Γ) _ _ L']
  unfold WFF.viewReadTm keepRead
  rw [WFF.mono_holeAt _ _ (Ctx.NoSlots.slots.insert X), Term.mono_mono]
  refine Eq.trans ?_ (WFF.instantiate_holeAt_mono b (Term.mono L' _) _)
  rw [Term.mono_mono]

/-- Read here, `keepRead` is the formula itself, whatever the content. -/
theorem WFF.hereRead_keepRead (hT : ModalSys.T = true) (hF : ModalSys.Four = true) {X : VarType}
    {t₀ : Ann X} (t : Term σ Γ.boxIn X t₀) (s : Term σ Γ.boxIn H s₀)
    (Θ : WFF σ (Ctx.empty.insert (.bnd 0) H) 1) :
    WFF.hereRead hT t (keepRead hF X s Θ) = WFF.holeAt Ctx.NoSlots.slots s Θ := by
  have hr := (Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).root
  have hr' := (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root
  unfold WFF.hereRead keepRead
  rw [WFF.collapse_holeAt _ _ (Ctx.NoSlots.slots.insert X),
    WFF.collapse_shift_same _ _ (Ctx.Le.refl _) (Ctx.shiftCollapseId_hole 0 H), WFF.mono_refl,
    Term.collapse_mono (Ctx.collapses_boxIn_self hT Γ.boxIn) _ _ (Ctx.le_insert hr' X)]
  have e := congrArg (fun p => (⟨_, Term.mono (Ctx.le_insert hr' X) p.2⟩ :
    Σ c, Term σ (Γ.boxIn.insert (.bnd 0) X) H c)) (Term.collapse_shift_boxIn hT hF s)
  rw [WFF.holeAt_congr _ e Θ]
  exact WFF.instantiate_holeAt_mono t s Θ

/-- ⭐**A possibility tied to the kept object is the object's own**:
    `◇(Here (x.keep) t ∧ Θ(s)) ⊢ ◇_x Θ(s)`.  By contradiction: `□_x ¬Θ(s)` is kept by `four_dia`,
    and `Here (x.keep) t` reads the kept formula at the world itself (`here_elim`).  `Θ` is closed
    over `s`, so the shift only moves `s`, and collapsing undoes it. -/
def Proof.dia_here_keep (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    {Δ : List (WFF σ Γ 0)} {x : VarSymb} {X : VarType} (hx : Γ.ref x = some (.VTypeDia X))
    {t₀ : Ann X} (t : Term σ Γ.boxIn X t₀) (s : Term σ Γ.boxIn H s₀)
    (Θ : WFF σ (Ctx.empty.insert (.bnd 0) H) 1)
    (p : Proof σ Γ Δ ((OutLeg.nec : OutLeg Γ).dia (WFF.and (WFF.here hT
      (Term.eta (.step x .keep) (.VTypeDia X) (Ctx.ref_keep_of' hF hx VarType.keepable_dia)) t)
      (WFF.holeAt Ctx.NoSlots.slots s Θ)))) :
    Proof σ Γ Δ (WFF.dia x ⟨X, hx⟩
      (WFF.holeAt Ctx.NoSlots.slots (Term.mono (Ctx.le_boxIn_diaIn Γ x) s) Θ)) := by
  have hk := Ctx.ref_keep_of' hF hx VarType.keepable_dia
  refine Proof.byContra ?_
  have hb := Proof.four_dia hF (Γ := Γ) (Δ := _ :: Δ) ⟨X, hx⟩ (Proof.ofSubset (fun _ hy => by
    rw [List.mem_singleton.mp hy]
    exact List.mem_cons_self) (Proof.boxx_neg_of_not_dia x ⟨X, hx⟩ (WFF.holeAt Ctx.NoSlots.slots
      (Term.mono (Ctx.le_boxIn_diaIn Γ x) s) Θ)))
  have hr : WFF.viewReadTm (Term.eta (σ := σ) (.step (.step x .keep) .dia) X
      (Ctx.ref_diaIn_of hk)) (keepRead hF X s Θ.neg) = _ :=
    WFF.viewRead_keepRead hF x _ s Θ.neg
  have q : Proof σ Γ.boxIn [WFF.boxx (.step x .keep) ⟨X, hk⟩ (WFF.viewReadTm (Term.eta (σ := σ)
      (.step (.step x .keep) .dia) X (Ctx.ref_diaIn_of hk)) (keepRead hF X s Θ.neg))]
      (WFF.and (WFF.here hT (Term.eta (.step x .keep) (.VTypeDia X) hk) t)
        (WFF.holeAt Ctx.NoSlots.slots s Θ)).neg := by
    refine Proof.imp_intro (Proof.imp_elim (Proof.conv (WFF.hereRead_keepRead hT hF t s Θ.neg)
      (Proof.here_elim hT _ ⟨X, hk⟩ t _ _ (Proof.and_elim_l (Proof.lookup List.mem_cons_self))
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))))
      (Proof.and_elim_r (Proof.lookup List.mem_cons_self)))
  exact Proof.imp_elim (Proof.ofSubset (fun _ hy => List.mem_cons_of_mem _ hy) p)
    (Proof.leg_K .nec q (Proof.conv (by rw [hr]; rfl) hb))

end KeepDia

end V12M
