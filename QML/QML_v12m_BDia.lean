import QML.QML_v12m_BChild

/-!
# QML v12m — B's arrow model: arrows into an extent

A world created for `◇_x φ` is reached by a **witness arrow**: the `◇_x` view goes to it, `x.dia`
to a variable `cx` holding the content (`arrowXS`).  Its transfer is for `□_x` (`TransferX`).
Everything the `□` case needs has a `□_x` counterpart here:

* `□_x` distributes (`Proof.boxxK`), and `□` gives `□_x` (`Proof.box_boxx`);
* abstraction in the witness view (`absXS`, `instantiate_tup_absX`, `subst_arrowX_abs`);
* ⭐`realiseX_consistent`: realising the source's next variable along a witness arrow;
* ⭐`childX_consistent`: the existence lemma for `◇_x`.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## Reasoning with `□_x` -/

/-- `□_x` distributes over a derivation in the witness view. -/
def Proof.boxxK {Γ : Ctx} {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    {Δ : List (WFF σ (Γ.diaIn x) 0)} {φ : WFF σ (Γ.diaIn x) 0} (p : Proof σ (Γ.diaIn x) Δ φ) :
    Proof σ Γ (Δ.map (WFF.boxx x hx)) (WFF.boxx x hx φ) :=
  .imp_intro (.dia_bot x hx (Proof.castHyps (by simp) (Proof.K_dia (Δ₁ := []) (Δ₂ := Δ) x hx
    (ψ := φ.neg) (φ := .bot) (.imp_elim (Proof.lookup List.mem_cons_self)
      (Proof.ofSubset (fun y hy => List.mem_cons_of_mem _ (by simpa using hy)) p)))))

/-- What is necessary is `□_x`-necessary. -/
def Proof.box_boxx {Γ : Ctx} {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (χ : WFF σ Γ.boxIn 0) :
    Proof σ Γ [.box χ] (WFF.boxx x hx (WFF.mono (Ctx.le_boxIn_diaIn Γ x) χ)) :=
  .imp_intro (.dia_bot x hx (Proof.castHyps (by simp) (Proof.K_dia (Δ₁ := [χ]) (Δ₂ := []) x hx
    (ψ := (WFF.mono (Ctx.le_boxIn_diaIn Γ x) χ).neg) (φ := .bot)
    (.imp_elim (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ (by simp)))))))

/-- A necessity-like predicate closed under `⊤` and `∧` reduces finite lists to one formula. -/
theorem list_reduce {Γ₀ Δ : Ctx} (P : WFF σ Γ₀ 0 → Prop) (htop : P .top)
    (hand : ∀ {ψ₁ ψ₂}, P ψ₁ → P ψ₂ → P (ψ₁.and ψ₂)) (f : WFF σ Γ₀ 0 → WFF σ Δ 0)
    (hf : ∀ ψ₁ ψ₂, f (ψ₁.and ψ₂) = (f ψ₁).and (f ψ₂)) (S : Set (WFF σ Δ 0)) :
    ∀ L : List (WFF σ Δ 0), (∀ δ ∈ L, δ ∈ S ∨ ∃ ψ, P ψ ∧ δ = f ψ) →
      ∃ ψ, P ψ ∧ ∀ δ ∈ L, Theory.Derives (S ∪ {f ψ}) δ
  | [], _ => ⟨.top, htop, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨ψ₀, hψ₀, hL⟩ := list_reduce P htop hand f hf S L
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      rcases h δ List.mem_cons_self with hS | ⟨ψ₁, hψ₁, rfl⟩
      · refine ⟨ψ₀, hψ₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact Theory.Derives.of_mem (Or.inl hS)
        · exact hL d hd
      · refine ⟨ψ₀.and ψ₁, hand hψ₀ hψ₁, fun d hd => ?_⟩
        have hconj : Theory.Derives (S ∪ {f (ψ₀.and ψ₁)}) ((f ψ₀).and (f ψ₁)) := by
          rw [← hf]
          exact Theory.Derives.of_mem (Or.inr rfl)
        rcases List.mem_cons.mp hd with rfl | hd
        · obtain ⟨Δ', hΔ', p⟩ := hconj
          exact ⟨Δ', hΔ', Provable.and_elim_r p⟩
        · refine Derives.trans (fun x hx => ?_) (hL d hd)
          rcases hx with hx | hx
          · exact Theory.Derives.of_mem (Or.inl hx)
          · rw [Set.mem_singleton_iff.mp hx]
            obtain ⟨Δ', hΔ', p⟩ := hconj
            exact ⟨Δ', hΔ', Provable.and_elim_l p⟩

theorem boxx_and_mem {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)} (hM : Theory.IsMCS M)
    {Γ₀ : Ctx} (hle : Γ₀.Le Γ) {x : VarSymb} (hx : ∃ X, Γ₀.ref x = some (.VTypeDia X))
    {ψ₁ ψ₂ : WFF σ (Γ₀.diaIn x) 0}
    (h₁ : WFF.mono hle (WFF.boxx x hx ψ₁) ∈ M) (h₂ : WFF.mono hle (WFF.boxx x hx ψ₂) ∈ M) :
    WFF.mono hle (WFF.boxx x hx (ψ₁.and ψ₂)) ∈ M := by
  refine hM.closed ⟨[WFF.mono hle (WFF.boxx x hx ψ₁), WFF.mono hle (WFF.boxx x hx ψ₂)],
    fun y hy => ?_, ?_⟩
  · rcases List.mem_cons.mp hy with rfl | hy
    · exact h₁
    · rw [List.mem_singleton.mp hy]; exact h₂
  · exact Provable.monoCtx (Δs := [WFF.boxx x hx ψ₁, WFF.boxx x hx ψ₂]) hle
      ⟨Proof.boxxK hx (Δ := [ψ₁, ψ₂]) (.and_intro (Proof.lookup List.mem_cons_self)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))⟩

theorem boxx_top_mem {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)} (hM : Theory.IsMCS M)
    {Γ₀ : Ctx} (hle : Γ₀.Le Γ) {x : VarSymb} (hx : ∃ X, Γ₀.ref x = some (.VTypeDia X)) :
    WFF.mono hle (WFF.boxx x hx (.top : WFF σ (Γ₀.diaIn x) 0)) ∈ M :=
  hM.closed ⟨[], fun _ h => absurd h List.not_mem_nil,
    Provable.monoCtx (Δs := []) hle ⟨Proof.boxxK hx (Δ := []) .top_intro⟩⟩

/-! ## Abstraction in a witness view -/

/-- Abstracting the variable `c` in the `◇_x` view: `x.dia` stays. -/
def absXS (σ : Signature) (Δ : Ctx) (c : ℕ) (x : VarSymb) : Subst σ Δ := fun v =>
  match v with
  | .step u .box => if u.rt = .free c then .ren (u.reroot (.bnd 0)) else .ren (.step u .box)
  | .step u .dia => if u = x then .ren (.step x .dia) else .hide
  | _ => .hide

/-- The context of an abstracted witness-view formula. -/
abbrev absXCtx (A : VarType) (l : List VarType) (x : VarSymb) : Ctx :=
  ((ctxOf l).diaIn x).insert (.bnd 0) A.bc

theorem absXCtx_slots (A : VarType) (l : List VarType) (x : VarSymb) :
    (absXCtx A l x).SlotsFrom 1 :=
  (Ctx.NoSlots.slots (Γ := (ctxOf l).diaIn x)).insert A.bc

theorem ok_absXS [ModalSys.NoTFour] {A : VarType} {l : List VarType} {x : VarSymb} {X : VarType}
    (hx : (ctxOf l).ref x = some (.VTypeDia X)) :
    Subst.Ok ((ctxOf (A :: l)).diaIn x) (absXS σ (absXCtx A l x) l.length x) := by
  intro v T _ hv
  rcases diaIn_item hv with ⟨u, rfl, hu⟩ | ⟨rfl, hxT⟩
  · change (if u.rt = .free l.length then SubE.ren (u.reroot (.bnd 0))
      else .ren (.step u .box)).OkRef T
    split_ifs with hrt
    · change (absXCtx A l x).ref (u.reroot (.bnd 0)) = some T
      exact ref_reroot_bc (T := .VTypeBox T) hu (by rw [hrt]; exact ctxOf_ref_new A l)
        (Ctx.ref_insert_root _ _ _)
    · change (absXCtx A l x).ref (.step u .box) = some T
      obtain ⟨r, hr⟩ := (reach_ppath hu).2
      rw [Ctx.ref_insert_ne _ (fun h => by
        change u.rt = _ at h
        rw [hr] at h
        cases h)]
      rw [ctxOf_ref_old hrt] at hu
      exact (Ctx.le_boxIn_diaIn _ x).ref (Ctx.ref_boxIn_of ModalSys.NoTFour.keepOnly hu)
  · change (if x = x then SubE.ren (.step x .dia) else .hide).OkRef T
    rw [if_pos rfl]
    obtain ⟨r, hr⟩ := (reach_ppath hx).2
    have hxr : x.rt ≠ .free l.length := by
      obtain ⟨r', e, hlt, -⟩ := ref_rt hx
      rw [e]
      exact fun h => by cases h; omega
    rw [ctxOf_ref_old hxr, hx] at hxT
    cases hxT
    change (absXCtx A l x).ref (.step x .dia) = some _
    rw [Ctx.ref_insert_ne _ (fun h => by
      change x.rt = _ at h
      rw [hr] at h
      cases h)]
    exact Ctx.ref_diaIn_of hx

theorem coh_absXS [ModalSys.NoTFour] {A : VarType} {l : List VarType} {x : VarSymb} {X : VarType}
    (hx : (ctxOf l).ref x = some (.VTypeDia X)) :
    Subst.Coh (absIdx l.length) ((ctxOf (A :: l)).diaIn x)
      (absXS σ (absXCtx A l x) l.length x) := by
  refine Subst.coh_of (ok_absXS hx) ?_
  intro v T _ hv p
  rcases diaIn_item hv with ⟨u, rfl, hu⟩ | ⟨rfl, _⟩
  · change (if u.rt = .free l.length then SubE.ren (u.reroot (.bnd 0))
      else .ren (.step u .box)).idxAlong p = absIdx l.length _
    have hrt' : ((VarSymb.step u .box).ext p).rt = u.rt := VarSymb.ext_rt _ _
    split_ifs with hrt
    · change (u.reroot (.bnd 0)).ext p = _
      rw [absIdx, if_pos (hrt'.trans hrt), erase_box_item (reach_ppath hu).1 p,
        VarSymb.ext_append, VarSymb.reroot_eq]
    · change (VarSymb.step u .box).ext p = _
      rw [absIdx, if_neg (fun h => hrt (hrt'.symm.trans h))]
  · change (if x = x then SubE.ren (.step x .dia) else .hide).idxAlong p = _
    rw [if_pos rfl]
    have hxr : x.rt ≠ .free l.length := by
      obtain ⟨r', e, hlt, -⟩ := ref_rt hx
      rw [e]
      exact fun h => by cases h; omega
    change (VarSymb.step x .dia).ext p = absIdx l.length _
    have hne : ¬ ((VarSymb.step x .dia).ext p).rt = .free l.length := fun h => hxr (by
      rw [VarSymb.ext_rt] at h
      exact h)
    rw [absIdx, if_neg hne]

/-- Weakening the abstracted witness-view context into the new variable's context. -/
theorem absXCtx_le (A : VarType) (l : List VarType) (x : VarSymb) :
    (absXCtx A l x).Le (((ctxOf (A :: l)).diaIn x).insert (.bnd 0) A.bc) :=
  (((ctxOf_le_append [A] l).diaIn x)).insert (.bnd 0) A.bc

/-- ⭐The abstraction of a formula of the new witness view. -/
noncomputable def absX [ModalSys.NoTFour] (A : VarType) (l : List VarType) {x : VarSymb}
    {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X))
    (ψ : WFF σ ((ctxOf (A :: l)).diaIn x) 0) : WFF σ (absXCtx A l x) 1 :=
  WFF.subst (absIdx l.length) (absXS σ (absXCtx A l x) l.length x) (ok_absXS hx) (coh_absXS hx)
    Ctx.NoSlots.slots (absXCtx_slots A l x) ψ

/-- Projecting a weakened tuple entry reaches the weakened tuple of the component. -/
theorem at_single_tup_mono [ModalSys.NoTFour] {A : VarType} {l : List VarType} {Δ : Ctx}
    (h : (ctxOf (A :: l)).boxIn.Le Δ) :
    ∀ {u : VarSymb} {U : VarType} (hu : (ctxOf (A :: l)).ref u = some U),
      u.rt = .free l.length →
      (Subst.single (σ := σ) (Δ := Δ) (.bnd 0)
        (.tm (Term.mono h (tup (.root (.free l.length)) A (ctxOf_ref_new A l))))).at
          (u.reroot (.bnd 0)) = .tm (Term.mono h (tup u U hu))
  | .root r, U, hu, hrt => by
      change VarSymb.rt (.root r) = _ at hrt
      subst hrt
      rw [ctxOf_ref_new] at hu
      cases hu
      change Subst.single (.bnd 0) _ (.root (.bnd 0)) = _
      exact if_pos rfl
  | .step u s, U, hu, hrt => by
      have hp := (reach_ppath hu).1
      have hs : s = .fst ∨ s = .snd := hp s (by simp [VarSymb.path])
      have hproj : s.isProj = true := by rcases hs with rfl | rfl <;> rfl
      have hu' := hu
      simp only [Ctx.ref, if_pos hproj] at hu'
      cases hU : (ctxOf (A :: l)).ref u with
      | none => rw [hU] at hu'; cases hu'
      | some U' =>
          rw [hU] at hu'
          have ih := at_single_tup_mono h hU hrt
          change (Subst.single (.bnd 0) _).at (.step (u.reroot (.bnd 0)) s) = _
          rw [show ∀ (θ : Subst σ Δ) (v : VarSymb),
              θ.at (.step v s) = (θ.at v).proj s from fun θ v => if_pos hproj, ih]
          rcases hs with rfl | rfl
          · cases U' with
            | VTypeProd X Y =>
                cases hu'
                rfl
            | _ => cases hu'
          · cases U' with
            | VTypeProd X Y =>
                cases hu'
                rfl
            | _ => cases hu'

/-- ⭐A formula of the new witness view is its abstraction at the tuple of the new items. -/
theorem instantiate_tup_absX [ModalSys.NoTFour] (A : VarType) (l : List VarType) {x : VarSymb}
    {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X))
    (ψ : WFF σ ((ctxOf (A :: l)).diaIn x) 0) :
    WFF.instantiate Ctx.NoSlots.slots
      (Term.mono (Ctx.le_boxIn_diaIn _ x) (tup (.root (.free l.length)) A (ctxOf_ref_new A l)))
      (WFF.mono (absXCtx_le A l x) (absX A l hx ψ)) = ψ := by
  have hs : (((ctxOf (A :: l)).diaIn x).insert (.bnd 0) A.bc).SlotsFrom 1 :=
    (Ctx.NoSlots.slots (Γ := (ctxOf (A :: l)).diaIn x)).insert A.bc
  unfold WFF.instantiate WFF.substRoot absX
  rw [WFF.subst_mono (absXCtx_le A l x) _ _ _ (absXCtx_slots A l x) hs]
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ Subst.ok_idS Subst.coh_idS _ _ _ ?_ ψ).trans
    (WFF.subst_id _ _ _ ψ)
  refine Subst.sim_of ?_
  intro v T _ hv
  rcases diaIn_item hv with ⟨u, rfl, hu⟩ | ⟨rfl, _⟩
  · change SubE.Sim T (.ren (.step u .box)) ((if u.rt = .free l.length then
      SubE.ren (u.reroot (.bnd 0)) else .ren (.step u .box)).comp _ _ _)
    split_ifs with hrt
    · change SubE.Sim T _ ((Subst.single (.bnd 0) _).at (u.reroot (.bnd 0)))
      rw [at_single_tup_mono _ hu hrt]
      change SubE.Sim T _ (.tm (Term.mono _ (Term.eta (.step u .box) T _)))
      rw [Term.mono_eta]
      exact .ren_eta _ _
    · change SubE.Sim T _ ((Subst.single (.bnd 0) _).at (.step u .box))
      rw [Subst.single_at_ne (by
        change u.rt ≠ _
        obtain ⟨r, hr⟩ := (reach_ppath hu).2
        rw [hr]
        exact fun h => by cases h)]
      exact .refl _
  · change SubE.Sim T (.ren (.step x .dia))
      ((if x = x then SubE.ren (.step x .dia) else .hide).comp _ _ _)
    rw [if_pos rfl]
    change SubE.Sim T _ ((Subst.single (.bnd 0) _).at (.step x .dia))
    rw [Subst.single_at_ne (by
      change x.rt ≠ _
      obtain ⟨r, hr⟩ := (reach_ppath hx).2
      rw [hr]
      exact fun h => by cases h)]
    exact .refl _

/-! ## The extended witness arrow -/

theorem subst_arrowX_abs [ModalSys.NoTFour] {A : VarType} {ls lt : List VarType} {img : ℕ → ℕ}
    (himg : ImgOk ls (ctxOf lt) img) {x : VarSymb} {X : VarType}
    (hx : (ctxOf ls).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : (ctxOf lt).ref (.root (.free cx)) = some X)
    (ψ : WFF σ ((ctxOf (A :: ls)).diaIn x) 0) :
    WFF.subst (arrowXIdx (extImg img ls.length lt.length) x cx)
        (arrowXS σ (ctxOf (A.bc :: lt)) (extImg img ls.length lt.length) x cx)
        (ok_arrowXS (imgOk_ext himg) (by rw [ctxOf_ref_old (by
          obtain ⟨r', e, hlt, -⟩ := ref_rt hx
          rw [e]
          exact fun h => by cases h; omega)]; exact hx)
          ((ctxOf_le_append [A.bc] lt).ref hcx))
        (coh_arrowXS (imgOk_ext himg) (by rw [ctxOf_ref_old (by
          obtain ⟨r', e, hlt, -⟩ := ref_rt hx
          rw [e]
          exact fun h => by cases h; omega)]; exact hx)
          ((ctxOf_le_append [A.bc] lt).ref hcx))
        Ctx.NoSlots.slots Ctx.NoSlots.slots ψ =
      WFF.subst (VarSymb.slotToFree (arrowXIdx img x cx) 0 lt.length)
        ((arrowXS σ (ctxOf lt) img x cx).toFree 0 lt.length A.bc (ctxOf_fresh le_rfl).root)
        (Subst.ok_toFree (ok_arrowXS himg hx hcx) A.bc _)
        (Subst.coh_toFree (ok_arrowXS himg hx hcx) (coh_arrowXS himg hx hcx) Ctx.NoSlots.slots
          A.bc _)
        (absXCtx_slots A ls x) Ctx.NoSlots.slots (absX A ls hx ψ) := by
  refine (WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ ψ).symm
  refine Subst.sim_of ?_
  intro v T _ hv
  rcases diaIn_item hv with ⟨u, rfl, hu⟩ | ⟨rfl, _⟩
  · obtain ⟨hup, r, hr⟩ := reach_ppath hu
    change SubE.Sim T (.ren (u.reroot (imgRoot _ u.rt)))
      ((if u.rt = .free ls.length then SubE.ren (u.reroot (.bnd 0))
        else .ren (.step u .box)).comp _ _ _)
    split_ifs with hrt
    · change SubE.Sim T _ ((Subst.toFree _ 0 lt.length A.bc _).at (u.reroot (.bnd 0)))
      rw [at_toFree_reroot _ _ _ _ u hup, hrt]
      change SubE.Sim T (.ren (u.reroot (.free (if ls.length = ls.length then _ else _)))) _
      rw [if_pos rfl]
      exact .refl _
    · change SubE.Sim T _ ((Subst.toFree _ 0 lt.length A.bc _).at (.step u .box))
      rw [Subst.at_nonproj _ (rfl : (VarSymb.step u .box).lastProj = false)]
      change SubE.Sim T _ (if VarSymb.step u .box = .root (.bnd 0) then _ else _)
      rw [if_neg (fun h => by cases h)]
      change SubE.Sim T _ (.ren (u.reroot (imgRoot img u.rt)))
      rw [hr]
      have hrc : r ≠ ls.length := fun h => hrt (by rw [hr, h])
      change SubE.Sim T (.ren (u.reroot (.free (if r = ls.length then _ else _)))) _
      rw [if_neg hrc]
      exact .refl _
  · change SubE.Sim T (if x = x then SubE.ren (.root (.free cx)) else .hide)
      ((if x = x then SubE.ren (.step x .dia) else .hide).comp _ _ _)
    rw [if_pos rfl, if_pos rfl]
    change SubE.Sim T _ ((Subst.toFree _ 0 lt.length A.bc _).at (.step x .dia))
    rw [Subst.at_nonproj _ (rfl : (VarSymb.step x .dia).lastProj = false)]
    change SubE.Sim T _ (if VarSymb.step x .dia = .root (.bnd 0) then _ else _)
    rw [if_neg (fun h => by cases h)]
    change SubE.Sim T _ (SubE.mono _ (if x = x then SubE.ren (.root (.free cx)) else .hide))
    rw [if_pos rfl]
    exact .refl _

/-! ## Transfer along a witness arrow -/

/-- ⭐The `□_x` transfer of a witness arrow: whatever the source `□_x`-necessitates about its
    variables with images (and `x.dia`), the target says of the images (and of `cx`). -/
def TransferX [ModalSys.NoTFour] {Γ : Ctx} (M : Set (WFF σ Γ 0)) (ls : List VarType)
    (hle : (ctxOf ls).Le Γ) {x : VarSymb} {X : VarType}
    (hx : (ctxOf ls).ref x = some (.VTypeDia X)) {Δ : Ctx} [Δ.NoSlots] (N : Set (WFF σ Δ 0))
    (img : ℕ → ℕ) (himg : ImgOk ls Δ img) (cx : ℕ) (hcx : Δ.ref (.root (.free cx)) = some X) :
    Prop :=
  ∀ ψ : WFF σ ((ctxOf ls).diaIn x) 0, WFF.mono hle (WFF.boxx x ⟨X, hx⟩ ψ) ∈ M →
    WFF.subst (arrowXIdx img x cx) (arrowXS σ Δ img x cx) (ok_arrowXS himg hx hcx)
      (coh_arrowXS himg hx hcx) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈ N

theorem ref_old_of_ref {A : VarType} {ls : List VarType} [ModalSys.NoTFour] {x : VarSymb}
    {X : VarType} (hx : (ctxOf ls).ref x = some (.VTypeDia X)) :
    (ctxOf (A :: ls)).ref x = some (.VTypeDia X) := by
  rw [ctxOf_ref_old (by
    obtain ⟨r', e, hlt, -⟩ := ref_rt hx
    rw [e]
    exact fun h => by cases h; omega)]
  exact hx

/-- The witness arrow extended by the source's next variable. -/
noncomputable abbrev extArrowX [ModalSys.NoTFour] {A : VarType} {ls lt : List VarType} {img : ℕ → ℕ}
    (himg : ImgOk ls (ctxOf lt) img) {x : VarSymb} {X : VarType}
    (hx : (ctxOf ls).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : (ctxOf lt).ref (.root (.free cx)) = some X)
    (ψ : WFF σ ((ctxOf (A :: ls)).diaIn x) 0) : WFF σ (ctxOf (A.bc :: lt)) 0 :=
  WFF.subst (arrowXIdx (extImg img ls.length lt.length) x cx)
    (arrowXS σ (ctxOf (A.bc :: lt)) (extImg img ls.length lt.length) x cx)
    (ok_arrowXS (imgOk_ext himg) (ref_old_of_ref hx) ((ctxOf_le_append [A.bc] lt).ref hcx))
    (coh_arrowXS (imgOk_ext himg) (ref_old_of_ref hx) ((ctxOf_le_append [A.bc] lt).ref hcx))
    Ctx.NoSlots.slots Ctx.NoSlots.slots ψ

theorem realiseX_one [ModalSys.NoTFour] {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)}
    (hM : Theory.IsMCS M) {A : VarType} {ls lt : List VarType}
    (hle : (ctxOf (A :: ls)).Le Γ) {N : Set (WFF σ (ctxOf lt) 0)} (hN : Theory.IsMCS N)
    {img : ℕ → ℕ} (himg : ImgOk ls (ctxOf lt) img) {x : VarSymb} {X : VarType}
    (hx : (ctxOf ls).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : (ctxOf lt).ref (.root (.free cx)) = some X)
    (htr : TransferX M ls ((ctxOf_le_append [A] ls).trans hle) hx N img himg cx hcx)
    {ψ : WFF σ ((ctxOf (A :: ls)).diaIn x) 0}
    (hψ : WFF.mono hle (WFF.boxx x ⟨X, ref_old_of_ref hx⟩ ψ) ∈ M) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [A.bc] lt) '' N ∪
      {extArrowX himg hx hcx ψ}) := by
  have hex : WFF.mono ((ctxOf_le_append [A] ls).trans hle)
      (WFF.boxx x ⟨X, hx⟩ (.ex A.bc (absX A ls hx ψ))) ∈ M := by
    refine hM.closed ⟨[WFF.mono hle (WFF.boxx x ⟨X, ref_old_of_ref hx⟩ ψ)], fun y hy => by
      rw [List.mem_singleton.mp hy]; exact hψ, ?_⟩
    have h := Provable.monoCtx (Δs := [WFF.boxx x ⟨X, ref_old_of_ref hx⟩ ψ]) hle
      ⟨Proof.boxxK ⟨X, ref_old_of_ref hx⟩ (Δ := [ψ]) (Proof.ex_intro A.bc
        (Term.mono (Ctx.le_boxIn_diaIn _ x) (tup (.root (.free ls.length)) A (ctxOf_ref_new A ls)))
        (Proof.conv (instantiate_tup_absX A ls hx ψ).symm (Proof.lookup List.mem_cons_self)))⟩
    rw [← WFF.mono_mono (ctxOf_le_append [A] ls) hle]
    exact h
  have hN' := htr _ hex
  have hsub := subst_arrowX_abs (A := A) himg hx hcx ψ
  rw [← WFF.instantiate_toFree (arrowXS σ (ctxOf lt) img x cx) (ok_arrowXS himg hx hcx)
      (coh_arrowXS himg hx hcx) Ctx.NoSlots.slots Ctx.NoSlots.slots lt.length
      (ctxOf_fresh le_rfl) A.bc Ctx.NoSlots.slots (absX A ls hx ψ),
    WFF.instantiate_eta_openFree _ (ctxOf_fresh le_rfl) Ctx.NoSlots.slots] at hsub
  change _ ∈ N at hN'
  have hc := henkin_consistent hN.1 (Theory.Derives.of_mem hN') (ctxOf_fresh (l := lt) le_rfl)
  rw [show extArrowX himg hx hcx ψ = _ from hsub]
  exact hc

/-- ⭐**Realising the next variable along a witness arrow.** -/
theorem realiseX_consistent [ModalSys.NoTFour] {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)}
    (hM : Theory.IsMCS M) {A : VarType} {ls lt : List VarType}
    (hle : (ctxOf (A :: ls)).Le Γ) {N : Set (WFF σ (ctxOf lt) 0)} (hN : Theory.IsMCS N)
    {img : ℕ → ℕ} (himg : ImgOk ls (ctxOf lt) img) {x : VarSymb} {X : VarType}
    (hx : (ctxOf ls).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : (ctxOf lt).ref (.root (.free cx)) = some X)
    (htr : TransferX M ls ((ctxOf_le_append [A] ls).trans hle) hx N img himg cx hcx) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [A.bc] lt) '' N ∪
      {φ | ∃ ψ, WFF.mono hle (WFF.boxx x ⟨X, ref_old_of_ref hx⟩ ψ) ∈ M ∧
        φ = extArrowX himg hx hcx ψ}) := by
  rintro ⟨L, hL, p⟩
  obtain ⟨ψ, hψ, hder⟩ := list_reduce
    (fun ψ => WFF.mono hle (WFF.boxx x ⟨X, ref_old_of_ref hx⟩ ψ) ∈ M)
    (boxx_top_mem hM hle _) (fun h₁ h₂ => boxx_and_mem hM hle _ h₁ h₂)
    (extArrowX himg hx hcx) (fun _ _ => rfl)
    (WFF.mono (ctxOf_le_append [A.bc] lt) '' N) L (fun δ hδ => (hL δ hδ).imp id id)
  exact realiseX_one hM hle hN himg hx hcx htr hψ (derives_of_derives hder p)

/-- A witness arrow's transfer gives closed transfer. -/
theorem TransferX.closed [ModalSys.NoTFour] {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)}
    (hM : Theory.IsMCS M) {ls : List VarType} {hle : (ctxOf ls).Le Γ} {x : VarSymb} {X : VarType}
    {hx : (ctxOf ls).ref x = some (.VTypeDia X)} {Δ : Ctx} [Δ.NoSlots] {N : Set (WFF σ Δ 0)}
    {img : ℕ → ℕ} {himg : ImgOk ls Δ img} {cx : ℕ} {hcx : Δ.ref (.root (.free cx)) = some X}
    (htr : TransferX M ls hle hx N img himg cx hcx) : CTransfer M N := by
  intro χ hχ
  have hb : WFF.mono hle (WFF.boxx x ⟨X, hx⟩ (χ.closed _)) ∈ M := by
    refine hM.closed ⟨[WFF.box (χ.closed Γ.boxIn)], fun y hy => by
      rw [List.mem_singleton.mp hy]; exact hχ, ?_⟩
    have h := Proof.box_boxx (Γ := Γ) (x := x) ⟨X, hle.ref hx⟩ (χ.closed Γ.boxIn)
    refine ⟨Proof.conv ?_ h⟩
    simp only [WFF.closed, WFF.boxx, WFF.neg, WFF.mono, WFF.mono_mono]
  have h := htr (χ.closed _) hb
  rwa [WFF.closed, WFF.subst_mono_empty _ (Ctx.empty_le _)] at h

/-! ## Creating a witness child -/

/-- The witness child's variables: the world's at the `bc` types, then `x`'s content. -/
theorem childXImg (l : List VarType) (X : VarType) :
    ImgOk l (ctxOf (X :: l.map VarType.bc)) id := fun r hr =>
  (ctxOf_le_append [X] (l.map VarType.bc)).ref (childImg l r hr)

theorem childX_cx (l : List VarType) (X : VarType) :
    (ctxOf (X :: l.map VarType.bc)).ref (.root (.free l.length)) = some X := by
  have := ctxOf_ref_new X (l.map VarType.bc)
  rwa [List.length_map] at this

/-- Pulling back a witness child: its variables to tuples, the content to `x.dia`. -/
def pullXS [ModalSys.NoTFour] (σ : Signature) (l : List VarType) (x : VarSymb) :
    Subst σ ((ctxOf l).diaIn x) :=
  fun v => match v with
  | .root (.free r) =>
      if h : r < l.length then .tm (Term.mono (Ctx.le_boxIn_diaIn _ x)
        (tup (.root (.free r)) (rootTy l r) (by
          rw [Ctx.ref_nonproj _ rfl]; exact ctxOf_root_lt h)))
      else if r = l.length then .ren (.step x .dia) else .hide
  | _ => .hide

/-- Where pulling back a witness child sends annotation indices. -/
def pullXIdx (l : List VarType) (x : VarSymb) (a : VarSymb) : VarSymb :=
  match a.rt with
  | .free r =>
      if r < l.length then (tupAnn (.root (.free r)) (rootTy l r)).idxAt a.path
      else if r = l.length then (VarSymb.step x .dia).ext a.path else a
  | .bnd _ => a

theorem pullX_tm [ModalSys.NoTFour] {l : List VarType} (x : VarSymb) {r : ℕ} (h : r < l.length) :
    pullXS σ l x (.root (.free r)) = .tm (Term.mono (Ctx.le_boxIn_diaIn _ x)
      (tup (.root (.free r)) (rootTy l r) (by
        rw [Ctx.ref_nonproj _ rfl]; exact ctxOf_root_lt h))) :=
  dif_pos h

theorem pullX_cx [ModalSys.NoTFour] (l : List VarType) (x : VarSymb) :
    pullXS σ l x (.root (.free l.length)) = .ren (.step x .dia) := by
  change (if h : l.length < l.length then _ else if l.length = l.length then _ else _) = _
  rw [dif_neg (lt_irrefl _), if_pos rfl]

theorem ok_pullXS [ModalSys.NoTFour] (l : List VarType) {x : VarSymb} {X : VarType}
    (hx : (ctxOf l).ref x = some (.VTypeDia X)) :
    Subst.Ok (ctxOf (X :: l.map VarType.bc)) (pullXS σ l x) := by
  intro v T _ hv
  obtain ⟨r, rfl⟩ := ctxOf_decl hv
  by_cases hr : r < l.length
  · rw [ctxOf_root_lt (by simp; omega), rootTy_old (by simpa using hr),
      rootTy_map_bc l r hr] at hv
    cases hv
    rw [pullX_tm x hr]
    rfl
  · have hrl : r = l.length := by
      by_contra hne
      rw [(ctxOf_fresh (l := X :: l.map VarType.bc) (by simp; omega)) _ rfl] at hv
      cases hv
    subst hrl
    rw [pullX_cx]
    have hT := hv
    rw [ctxOf_root_lt (by simp), show l.length = (l.map VarType.bc).length by simp,
      rootTy_new] at hT
    cases hT
    exact Ctx.ref_diaIn_of hx

theorem coh_pullXS [ModalSys.NoTFour] (l : List VarType) {x : VarSymb} {X : VarType}
    (hx : (ctxOf l).ref x = some (.VTypeDia X)) :
    Subst.Coh (pullXIdx l x) (ctxOf (X :: l.map VarType.bc)) (pullXS σ l x) := by
  refine Subst.coh_of (ok_pullXS l hx) ?_
  intro v T _ hv p
  obtain ⟨r, rfl⟩ := ctxOf_decl hv
  have e : ((VarSymb.root (.free r)).ext p).rt = .free r := VarSymb.ext_rt _ _
  by_cases hr : r < l.length
  · rw [pullX_tm x hr]
    change (tupAnn (.root (.free r)) (rootTy l r)).idxAt p = pullXIdx l x _
    rw [pullXIdx, e]
    simp only [if_pos hr]
    rw [VarSymb.ext_path]
    rfl
  · have hrl : r = l.length := by
      by_contra hne
      rw [(ctxOf_fresh (l := X :: l.map VarType.bc) (by simp; omega)) _ rfl] at hv
      cases hv
    subst hrl
    rw [pullX_cx]
    change (VarSymb.step x .dia).ext p = pullXIdx l x _
    rw [pullXIdx, e]
    simp only [lt_irrefl, if_false]
    rw [VarSymb.ext_path]
    rfl

theorem at_pullX_tup [ModalSys.NoTFour] {l : List VarType} (x : VarSymb) :
    ∀ {u : VarSymb} {U : VarType} (hu : (ctxOf l).ref u = some U),
      (pullXS σ l x).at u = .tm (Term.mono (Ctx.le_boxIn_diaIn _ x) (tup u U hu))
  | .root (.free r'), U, hu => by
      obtain ⟨r₀, e, hr', -⟩ := ref_rt hu
      cases e
      have hU := hu
      rw [Ctx.ref_nonproj _ rfl, ctxOf_root_lt hr'] at hU
      cases hU
      exact pullX_tm x hr'
  | .root (.bnd _), _, hu => by
      obtain ⟨r₀, e, -⟩ := ref_rt hu
      cases e
  | .step u s, U, hu => by
      have hp := (reach_ppath hu).1
      have hs : s = .fst ∨ s = .snd := hp s (by simp [VarSymb.path])
      have hproj : s.isProj = true := by rcases hs with rfl | rfl <;> rfl
      have hu' := hu
      simp only [Ctx.ref, if_pos hproj] at hu'
      cases hU : (ctxOf l).ref u with
      | none => rw [hU] at hu'; cases hu'
      | some U' =>
          rw [hU] at hu'
          have ih := at_pullX_tup x hU
          rw [show (pullXS σ l x).at (.step u s) = ((pullXS σ l x).at u).proj s from
            if_pos hproj, ih]
          rcases hs with rfl | rfl
          · cases U' with
            | VTypeProd X Y =>
                cases hu'
                rfl
            | _ => cases hu'
          · cases U' with
            | VTypeProd X Y =>
                cases hu'
                rfl
            | _ => cases hu'

/-- ⭐Pulling back undoes the witness child's arrow. -/
theorem subst_pullX_arrowX [ModalSys.NoTFour] (l : List VarType) {x : VarSymb} {X : VarType}
    (hx : (ctxOf l).ref x = some (.VTypeDia X)) (χ : WFF σ ((ctxOf l).diaIn x) 0) :
    WFF.subst (pullXIdx l x) (pullXS σ l x) (ok_pullXS l hx) (coh_pullXS l hx) Ctx.NoSlots.slots
      Ctx.NoSlots.slots (WFF.subst (arrowXIdx id x l.length)
        (arrowXS σ (ctxOf (X :: l.map VarType.bc)) id x l.length)
        (ok_arrowXS (childXImg l X) hx (childX_cx l X))
        (coh_arrowXS (childXImg l X) hx (childX_cx l X)) Ctx.NoSlots.slots Ctx.NoSlots.slots
        χ) = χ := by
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ Subst.ok_idS Subst.coh_idS _ _ _ ?_ χ).trans
    (WFF.subst_id _ _ _ χ)
  refine Subst.sim_of ?_
  intro v T _ hv
  rcases diaIn_item hv with ⟨u, rfl, hu⟩ | ⟨rfl, _⟩
  · obtain ⟨-, r, hr⟩ := reach_ppath hu
    change SubE.Sim T (.ren (.step u .box)) ((pullXS σ l x).at (u.reroot (imgRoot id u.rt)))
    have e : u.reroot (imgRoot id u.rt) = u := by
      rw [hr]
      change u.reroot (.free r) = u
      rw [← hr]
      exact reroot_rt_self u
    rw [e, at_pullX_tup x hu]
    change SubE.Sim T _ (.tm (Term.mono _ (Term.eta (.step u .box) T _)))
    rw [Term.mono_eta]
    exact .ren_eta _ _
  · change SubE.Sim T (.ren (.step x .dia))
      ((if x = x then SubE.ren (.root (.free l.length)) else .hide).comp _ _ _)
    rw [if_pos rfl]
    change SubE.Sim T _ (pullXS σ l x (.root (.free l.length)))
    rw [pullX_cx]
    exact .refl _

/-- The arrow into a new witness child, applied to a formula of the witness view. -/
noncomputable abbrev childXArrow [ModalSys.NoTFour] (l : List VarType) {x : VarSymb} {X : VarType}
    (hx : (ctxOf l).ref x = some (.VTypeDia X)) (χ : WFF σ ((ctxOf l).diaIn x) 0) :
    WFF σ (ctxOf (X :: l.map VarType.bc)) 0 :=
  WFF.subst (arrowXIdx id x l.length) (arrowXS σ (ctxOf (X :: l.map VarType.bc)) id x l.length)
    (ok_arrowXS (childXImg l X) hx (childX_cx l X))
    (coh_arrowXS (childXImg l X) hx (childX_cx l X)) Ctx.NoSlots.slots Ctx.NoSlots.slots χ

/-- ⭐**The existence lemma for `◇_x`.**  If `◇_x φ` holds, the `□_x`-necessities sent along the
    witness child's arrow are consistent with the image of `φ`. -/
theorem childX_consistent [ModalSys.NoTFour] {l : List VarType} {M : Set (WFF σ (ctxOf l) 0)}
    (hM : Theory.IsMCS M) {x : VarSymb} {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X))
    {φ : WFF σ ((ctxOf l).diaIn x) 0} (hφ : WFF.dia x ⟨X, hx⟩ φ ∈ M) :
    Theory.Consistent ({childXArrow l hx φ} ∪
      {χ | ∃ ψ, WFF.mono (Ctx.Le.refl _) (WFF.boxx x ⟨X, hx⟩ ψ) ∈ M ∧
        χ = childXArrow l hx ψ}) := by
  rintro ⟨L, hL, p⟩
  obtain ⟨ψ, hψ, hder⟩ := list_reduce
    (fun ψ => WFF.mono (Ctx.Le.refl _) (WFF.boxx x ⟨X, hx⟩ ψ) ∈ M)
    (boxx_top_mem hM _ _) (fun h₁ h₂ => boxx_and_mem hM _ _ h₁ h₂)
    (childXArrow l hx) (fun _ _ => rfl) {childXArrow l hx φ} L (fun δ hδ => hL δ hδ)
  obtain ⟨Δ, hΔ, ⟨q⟩⟩ := derives_of_derives hder p
  have q' : Proof σ (ctxOf (X :: l.map VarType.bc)) [childXArrow l hx φ, childXArrow l hx ψ]
      .bot :=
    Proof.ofSubset (fun y hy => by
      rcases hΔ y hy with hy | hy
      · rw [Set.mem_singleton_iff.mp hy]; exact List.mem_cons_self
      · rw [Set.mem_singleton_iff.mp hy]; exact List.mem_cons_of_mem _ List.mem_cons_self) q
  have q'' := Proof.subst q' (pullXS σ l x) (ok_pullXS l hx) (coh_pullXS l hx) Ctx.NoSlots.slots
  have e : [childXArrow l hx φ, childXArrow l hx ψ].map (WFF.subst (pullXIdx l x) (pullXS σ l x)
      (ok_pullXS l hx) (coh_pullXS l hx) Ctx.NoSlots.slots Ctx.NoSlots.slots) = [φ, ψ] := by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    exact ⟨subst_pullX_arrowX l hx φ, subst_pullX_arrowX l hx ψ⟩
  replace q'' := Proof.castHyps e q''
  rw [WFF.mono_refl] at hψ
  apply hM.1
  refine ⟨[WFF.dia x ⟨X, hx⟩ φ, WFF.boxx x ⟨X, hx⟩ ψ], fun y hy => ?_,
    ⟨.dia_bot x ⟨X, hx⟩ (Proof.castHyps (by simp) (Proof.K_dia (Δ₁ := []) (Δ₂ := [ψ]) x ⟨X, hx⟩
      (ψ := φ) (φ := .bot) (Proof.castHyps (by simp) q'')))⟩⟩
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hφ
  · rw [List.mem_singleton.mp hy]; exact hψ

end BArrow

end V12M
