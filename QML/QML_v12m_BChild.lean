import QML.QML_v12m_BLocal

/-!
# QML v12m — B's arrow model: creating a child, and weak B's base case

* ⭐`child_consistent`: if `□φ` fails at a world, its necessities, sent to a new world with one
  variable per variable of the world (the identity arrow, `childImg`), are consistent with the
  image of `¬φ`.  The proof pulls a refutation back into the world's `□` view by substituting each
  new variable by the tuple of the corresponding variable's items (`pullS`), which undoes the
  arrow (`subst_pull_arrow`), and applies `K_box`.
* ⭐`closed_back`: weak B's base case — the closed necessities of a successor hold at the world,
  given closed forward transfer (`◇□ψ ⊢ ψ`, contraposed).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## The child's variables -/

omit [ModalSys] in
theorem rootTy_map_bc (l : List VarType) (r : ℕ) (h : r < l.length) :
    rootTy (l.map VarType.bc) r = (rootTy l r).bc := by
  unfold rootTy
  rw [← List.map_reverse, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_eq_getElem (by simpa using h)]
  rfl

/-- The child's variables are the world's, at the `bc` types, under the same names. -/
theorem childImg (l : List VarType) : ImgOk l (ctxOf (l.map VarType.bc)) id := by
  intro r hr
  change (ctxOf (l.map VarType.bc)).ref (.root (.free r)) = _
  rw [Ctx.ref_nonproj _ rfl, ctxOf_root_lt (by simpa using hr), rootTy_map_bc l r hr]

/-! ## Pulling back -/

/-- Each variable of the child goes back to the tuple of the corresponding variable's items. -/
def pullS [ModalSys.NoTFour] (σ : Signature) (l : List VarType) : Subst σ (ctxOf l).boxIn :=
  fun v => match v with
  | .root (.free r) =>
      if h : r < l.length then .tm (tup (.root (.free r)) (rootTy l r) (by
        rw [Ctx.ref_nonproj _ rfl]; exact ctxOf_root_lt h)) else .hide
  | _ => .hide

/-- Where pulling back sends annotation indices: along the tuple's annotation. -/
def pullIdx (l : List VarType) (a : VarSymb) : VarSymb :=
  match a.rt with
  | .free r => if r < l.length then (tupAnn (.root (.free r)) (rootTy l r)).idxAt a.path else a
  | .bnd _ => a

theorem pull_tm [ModalSys.NoTFour] {l : List VarType} {r : ℕ} (h : r < l.length) :
    pullS σ l (.root (.free r)) = .tm (tup (.root (.free r)) (rootTy l r) (by
      rw [Ctx.ref_nonproj _ rfl]; exact ctxOf_root_lt h)) :=
  dif_pos h

theorem ok_pullS [ModalSys.NoTFour] (l : List VarType) :
    Subst.Ok (ctxOf (l.map VarType.bc)) (pullS σ l) := by
  intro v T _ hv
  obtain ⟨r, rfl⟩ := ctxOf_decl hv
  have hr : r < l.length := by
    by_contra hge
    rw [(ctxOf_fresh (l := l.map VarType.bc) (by simpa using Nat.le_of_not_lt hge)) _ rfl] at hv
    cases hv
  rw [ctxOf_root_lt (by simpa using hr), rootTy_map_bc l r hr] at hv
  cases hv
  rw [pull_tm hr]
  rfl

theorem coh_pullS [ModalSys.NoTFour] (l : List VarType) :
    Subst.Coh (pullIdx l) (ctxOf (l.map VarType.bc)) (pullS σ l) := by
  refine Subst.coh_of (ok_pullS l) ?_
  intro v T _ hv p
  obtain ⟨r, rfl⟩ := ctxOf_decl hv
  have hr : r < l.length := by
    by_contra hge
    rw [(ctxOf_fresh (l := l.map VarType.bc) (by simpa using Nat.le_of_not_lt hge)) _ rfl] at hv
    cases hv
  rw [pull_tm hr]
  have e : ((VarSymb.root (.free r)).ext p).rt = .free r := VarSymb.ext_rt _ _
  change (tupAnn (.root (.free r)) (rootTy l r)).idxAt p = pullIdx l _
  rw [pullIdx, e]
  simp only [if_pos hr]
  rw [VarSymb.ext_path]
  rfl

/-- Pulling back along a projection path reaches the tuple of the component. -/
theorem at_pull_tup [ModalSys.NoTFour] {l : List VarType} :
    ∀ {u : VarSymb} {U : VarType} (hu : (ctxOf l).ref u = some U) (r : ℕ), u.rt = .free r →
      (pullS σ l).at u = .tm (tup u U hu)
  | .root (.free r'), U, hu, r, hrt => by
      obtain ⟨r₀, e, hr', -⟩ := ref_rt hu
      cases e
      have hU := hu
      rw [Ctx.ref_nonproj _ rfl, ctxOf_root_lt hr'] at hU
      cases hU
      exact pull_tm hr'
  | .root (.bnd _), _, hu, _, hrt => by cases hrt
  | .step u s, U, hu, r, hrt => by
      have hp := (reach_ppath hu).1
      have hs : s = .fst ∨ s = .snd := hp s (by simp [VarSymb.path])
      have hproj : s.isProj = true := by rcases hs with rfl | rfl <;> rfl
      have hu' := hu
      simp only [Ctx.ref, if_pos hproj] at hu'
      cases hU : (ctxOf l).ref u with
      | none => rw [hU] at hu'; cases hu'
      | some U' =>
          rw [hU] at hu'
          have ih := at_pull_tup hU r hrt
          rw [show (pullS σ l).at (.step u s) = ((pullS σ l).at u).proj s from if_pos hproj, ih]
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

omit [ModalSys] in
theorem reroot_rt_self : ∀ u : VarSymb, u.reroot u.rt = u
  | .root _ => rfl
  | .step u s => by
      change VarSymb.step (u.reroot u.rt) s = _
      rw [reroot_rt_self u]

/-- ⭐Pulling back undoes the child's arrow. -/
theorem subst_pull_arrow [ModalSys.NoTFour] (l : List VarType) (χ : WFF σ (ctxOf l).boxIn 0) :
    WFF.subst (pullIdx l) (pullS σ l) (ok_pullS l) (coh_pullS l) Ctx.NoSlots.slots
      Ctx.NoSlots.slots (WFF.subst (arrowIdx id) (arrowS σ (ctxOf (l.map VarType.bc)) id)
        (ok_arrowS (childImg l)) (coh_arrowS (childImg l)) Ctx.NoSlots.slots Ctx.NoSlots.slots
        χ) = χ := by
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ Subst.ok_idS Subst.coh_idS _ _ _ ?_ χ).trans
    (WFF.subst_id _ _ _ χ)
  refine Subst.sim_of ?_
  intro v T _ hv
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  obtain ⟨-, r, hr⟩ := reach_ppath hu
  change SubE.Sim T (.ren (.step u .box)) ((pullS σ l).at (u.reroot (imgRoot id u.rt)))
  have e : u.reroot (imgRoot id u.rt) = u := by
    rw [hr]
    change u.reroot (.free r) = u
    rw [← hr]
    exact reroot_rt_self u
  rw [e, at_pull_tup hu r hr]
  exact .ren_eta _ _

/-! ## Creating a child -/

/-- The arrow into a new child, applied to a formula of the `□` view. -/
abbrev childArrow [ModalSys.NoTFour] (l : List VarType) (χ : WFF σ (ctxOf l).boxIn 0) :
    WFF σ (ctxOf (l.map VarType.bc)) 0 :=
  WFF.subst (arrowIdx id) (arrowS σ (ctxOf (l.map VarType.bc)) id) (ok_arrowS (childImg l))
    (coh_arrowS (childImg l)) Ctx.NoSlots.slots Ctx.NoSlots.slots χ

/-- ⭐**The existence lemma for a child.**  If `□φ` fails, the necessities sent along the child's
    arrow are consistent with the image of `¬φ`. -/
theorem child_consistent [ModalSys.NoTFour] {l : List VarType} {M : Set (WFF σ (ctxOf l) 0)}
    (hM : Theory.IsMCS M) {φ : WFF σ (ctxOf l).boxIn 0} (hφ : .box φ ∉ M) :
    Theory.Consistent ({(childArrow l φ).neg} ∪
      {χ | ∃ ψ, WFF.mono (Ctx.Le.refl _) (.box ψ) ∈ M ∧ χ = childArrow l ψ}) := by
  rintro ⟨L, hL, p⟩
  obtain ⟨ψ, hψ, hder⟩ := box_list hM (Ctx.Le.refl _) (childArrow l) (fun _ _ => rfl)
    {(childArrow l φ).neg} L (fun δ hδ => hL δ hδ)
  obtain ⟨Δ, hΔ, ⟨q⟩⟩ := derives_of_derives hder p
  -- A proof of `ψ' ⊢ φ'` in the child, pulled back to the `□` view.
  have q' : Proof σ (ctxOf (l.map VarType.bc)) [childArrow l ψ] (childArrow l φ) :=
    Proof.byContra (Proof.ofSubset (fun x hx => by
      rcases hΔ x hx with hx | hx
      · rw [Set.mem_singleton_iff.mp hx]; exact List.mem_cons_self
      · rw [Set.mem_singleton_iff.mp hx]; exact List.mem_cons_of_mem _ List.mem_cons_self) q)
  have q'' := Proof.subst q' (pullS σ l) (ok_pullS l) (coh_pullS l) Ctx.NoSlots.slots
  simp only [List.map_cons, List.map_nil, subst_pull_arrow] at q''
  apply hφ
  refine hM.closed ⟨[.box ψ], fun x hx => ?_, ⟨Proof.K_box (Δ := [ψ]) q''⟩⟩
  rw [List.mem_singleton.mp hx]
  rwa [WFF.mono_refl] at hψ

/-! ## Weak B's base case -/

/-- The empty context has an empty view. -/
theorem boxIn_empty (v : VarSymb) : Ctx.empty.boxIn v = none := by
  have hn : ∀ u, Ctx.empty.ref u = none :=
    fun u => Ctx.ref_none_of_rootFresh (fun _ _ => rfl) u rfl
  match v with
  | .step u .box =>
      change (if ModalSys.keepOnly then none else
        (match Ctx.empty.ref u with | some (.VTypeBox A) => some A | _ => none)) = none
      rw [hn u]
      split_ifs <;> rfl
  | .step u .keep =>
      change (if ModalSys.Four then
        (match Ctx.empty.ref u with | some (.VTypeBox A) => some (VarType.VTypeBox A) | _ => none)
        else none) = (none : Option VarType)
      rw [hn u]
      split_ifs <;> rfl
  | .root _ => rfl
  | .step _ .fst => rfl
  | .step _ .snd => rfl
  | .step _ .dia => rfl
  | .step _ .here => rfl

theorem boxIn_empty_le : Ctx.empty.boxIn.Le Ctx.empty := fun v T h => by
  rw [boxIn_empty v] at h
  cases h

/-- A formula of the empty context's view is closed. -/
theorem eq_closed_boxIn_empty (ψ : WFF σ Ctx.empty.boxIn 0) :
    ψ = (WFF.mono boxIn_empty_le ψ).closed _ := by
  rw [WFF.closed, WFF.mono_mono, WFF.mono_refl]

/-- ⭐Closed necessity transfer: the closed necessities of `M` hold in `N`. -/
def CTransfer {Γ Δ : Ctx} (M : Set (WFF σ Γ 0)) (N : Set (WFF σ Δ 0)) : Prop :=
  ∀ χ : WFF σ Ctx.empty 0, WFF.box (χ.closed Γ.boxIn) ∈ M → χ.closed Δ ∈ N

theorem closed_neg_box (Γ : Ctx) (ψ : WFF σ Ctx.empty 0) :
    (WFF.box (Γ := Ctx.empty) (ψ.closed _)).neg.closed Γ = (WFF.box (ψ.closed Γ.boxIn)).neg := by
  simp only [WFF.closed, WFF.neg, WFF.mono, WFF.mono_mono]

/-- ⭐**Weak B's base case.**  Closed necessity transfer from `M` to `N` gives it back from `N` to
    `M`, when `M` is closed under weak B: if `□ψ` holds in `N` but `ψ` fails in `M`, then `□¬□ψ`
    holds in `M` (`B_dia`, contraposed), so `¬□ψ` holds in `N`. -/
theorem closed_back (hB : ModalSys.B = true) {Γ Δ : Ctx} [Γ.Presented] [Δ.Presented]
    {M : Set (WFF σ Γ 0)} (hM : Theory.IsMCS M) {N : Set (WFF σ Δ 0)} (hN : Theory.IsMCS N)
    (hfwd : CTransfer M N) : CTransfer N M := by
  intro ψ hψ
  refine hM.closed ⟨[WFF.diaBox (ψ.closed _)], fun x hx => ?_,
    ⟨Proof.B_dia hB ψ (Proof.lookup List.mem_cons_self)⟩⟩
  rw [List.mem_singleton.mp hx]
  by_contra hnot
  have h1 : WFF.box ((WFF.box (Γ := Γ.boxIn) (ψ.closed _)).neg) ∈ M :=
    hM.closed ⟨[(WFF.diaBox (ψ.closed Γ.boxIn.boxIn)).neg],
      fun x hx => by rw [List.mem_singleton.mp hx]; exact hM.neg_mem_iff.mpr hnot,
      ⟨Proof.byContra (.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
        (Proof.lookup List.mem_cons_self))⟩⟩
  rw [← closed_neg_box] at h1
  have h2 := hfwd _ h1
  rw [closed_neg_box] at h2
  exact hN.neg_mem_iff.mp h2 hψ

/-- An arrow's transfer gives closed transfer. -/
theorem Transfer.closed [ModalSys.NoTFour] {Γ : Ctx} {M : Set (WFF σ Γ 0)} {ls : List VarType}
    {hle : (ctxOf ls).Le Γ} {Δ : Ctx} [Δ.NoSlots] {N : Set (WFF σ Δ 0)} {img : ℕ → ℕ}
    {himg : ImgOk ls Δ img} (htr : Transfer M ls hle N img himg) : CTransfer M N := by
  intro χ hχ
  have h := htr (χ.closed _) (by
    change WFF.box (WFF.mono hle.boxIn (WFF.mono _ χ)) ∈ M
    rw [WFF.mono_mono]
    exact hχ)
  rwa [WFF.closed, WFF.subst_mono_empty _ (Ctx.empty_le _)] at h

/-- Closed transfer gives the transfer of an arrow with nothing yet given an image. -/
theorem Transfer.of_closed [ModalSys.NoTFour] {Γ : Ctx} {M : Set (WFF σ Γ 0)}
    {hle : (ctxOf []).Le Γ} {Δ : Ctx} [Δ.NoSlots] {N : Set (WFF σ Δ 0)} {img : ℕ → ℕ}
    (himg : ImgOk [] Δ img) (h : CTransfer M N) : Transfer M [] hle N img himg := by
  intro ψ hψ
  rw [eq_closed_boxIn_empty ψ] at hψ ⊢
  rw [WFF.closed, WFF.subst_mono_empty _ (Ctx.empty_le _)]
  refine h _ ?_
  change WFF.box (WFF.mono hle.boxIn (WFF.mono _ _)) ∈ M at hψ
  rwa [WFF.mono_mono] at hψ

end BArrow

end V12M
