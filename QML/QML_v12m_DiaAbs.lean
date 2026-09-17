import QML.QML_v12m_SubstId
import QML.QML_v12m_Proof

/-!
# QML v12m — abstracting the content of a `◇` view (strong T)

`WFF.viewRead` reads a `□`-view formula with a hole inside `◇_c`, sending the hole to the witness
content `c.dia`.  The canonical model needs the other direction: given an arbitrary formula of the
view `Γ.diaIn c`, recover the hole formula it came from.  That is a renaming — the address `c.dia`
goes to the slot `bnd 0`, every `u.box` and `u.keep` stays — so, unlike realisation
(`QML_v12m_Realise`), it is a substitution: no level changes, so the address map `ι` is a function
of the address, and `Subst.Coh` holds.  **So strong T's canonical model needs no `Term.realise`
recursion**: realisation is abstraction followed by `hereRead`.

Everything is stated at any context `Γ` that declares `c : ◇A` as a root and writes nothing else
at that root (`hcA`, `hfr`), because the contexts of a world are not in `insert` form.

* `Ctx.ref_insert_dia`, `Ctx.boxIn_insert_dia_le`: declaring a `◇`-typed root adds only that root;
  `Ctx.ref_none_of_dia_root`: nothing else is reachable below it.
* `Subst.diaAbs`: the renaming; `WFF.diaAbs`, `Term.diaAbs`: the operations.
* `WFF.viewReadAt`: `WFF.viewRead` at such a context.
* ⭐`WFF.viewReadAt_diaAbs`: the round trip — every formula of the view is read from its
  abstraction.
* ⭐`WFF.realiseAt`, `Term.realiseAt`: what a formula or term of the `◇_c` view says here, when the
  witness is realised by `t₀`.
-/

namespace V12M

variable [ModalSys]

/-! ## Declaring a `◇`-typed root -/

namespace Ctx

/-- A `◇`-typed root has no reachable addresses below it: an address of the extended context is
    either that root or one of the old ones. -/
theorem ref_insert_dia {Γ : Ctx} {c : ℕ} (_hc : Γ.RootFresh (.free c)) (A : VarType) :
    ∀ {u : VarSymb} {T : VarType}, (Γ.insert (.free c) (.VTypeDia A)).ref u = some T →
      (u = .root (.free c) ∧ T = .VTypeDia A) ∨ Γ.ref u = some T := by
  intro u
  induction u with
  | root r =>
      intro T h
      by_cases hr : r = .free c
      · subst hr
        exact Or.inl ⟨rfl,
          (Option.some.inj ((Ctx.ref_insert_root Γ (.free c) (.VTypeDia A)).symm.trans h)).symm⟩
      · refine Or.inr ?_
        rwa [Ctx.ref_insert_ne (Γ := Γ) (.VTypeDia A) (v := .root r) hr] at h
  | step u s ih =>
      intro T h
      have hstep : (Γ.insert (.free c) (.VTypeDia A)) (.step u s) = Γ (.step u s) := by
        change (if (VarSymb.step u s) = .root (.free c) then some (.VTypeDia A)
          else Γ (.step u s)) = _
        rw [if_neg (fun he => by cases he)]
      by_cases hs : s.isProj = true
      · rw [Ctx.ref_step_proj _ _ hs] at h
        cases hU : (Γ.insert (.free c) (.VTypeDia A)).ref u with
        | none => rw [hU] at h; cases h
        | some U =>
            rw [hU] at h
            rcases ih hU with ⟨rfl, rfl⟩ | hu
            · exfalso
              cases s with
              | fst => nomatch h
              | snd => nomatch h
              | here => nomatch h
              | box => exact absurd hs (by decide)
              | dia => exact absurd hs (by decide)
              | keep => exact absurd hs (by decide)
            · refine Or.inr ?_
              rw [Ctx.ref_step_proj _ _ hs, hu]
              exact h
      · refine Or.inr ?_
        rw [Ctx.ref_step_nonproj _ _ hs] at h ⊢
        rwa [hstep] at h

/-- Declaring a `◇`-typed root adds nothing to the `□` view. -/
theorem boxIn_insert_dia_le {Γ : Ctx} {c : ℕ} (hc : Γ.RootFresh (.free c)) (A : VarType) :
    ((Γ.insert (.free c) (.VTypeDia A)).boxIn).Le Γ.boxIn := by
  intro v T hv
  match v with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hv
      rcases Ctx.ref_insert_dia hc A hu with ⟨rfl, hT⟩ | hu'
      · cases hT
      · exact Ctx.boxIn_box_of hk hu'
  | .step u .keep =>
      obtain ⟨hF, hu, B, rfl⟩ := Ctx.boxIn_keep hv
      rcases Ctx.ref_insert_dia hc A hu with ⟨rfl, hT⟩ | hu'
      · cases hT
      · exact Ctx.boxIn_keep_of hF hu'
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

/-- Where `c` is a declared `◇`-typed root and nothing else is written at that root, no other
    address rooted at `c` is reachable. -/
theorem ref_none_of_dia_root {Γ : Ctx} {c : ℕ} {A : VarType}
    (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none) :
    ∀ {u : VarSymb}, u.rt = .free c → u ≠ .root (.free c) → Γ.ref u = none
  | .root r, hrt, hne => absurd (congrArg VarSymb.root (show r = .free c from hrt)) hne
  | .step u s, hrt, _ => by
      by_cases hs : s.isProj = true
      · rw [Ctx.ref_step_proj _ _ hs]
        by_cases hu : u = .root (.free c)
        · subst hu
          rw [hcA]
          cases s with
          | fst => rfl
          | snd => rfl
          | here => rfl
          | box => exact absurd hs (by decide)
          | dia => exact absurd hs (by decide)
          | keep => exact absurd hs (by decide)
        · rw [ref_none_of_dia_root hcA hfr (u := u) hrt hu]
          rfl
      · rw [Ctx.ref_step_nonproj _ _ hs]
        exact hfr _ hrt (fun he => by cases he)

end Ctx

/-! ## The abstraction -/

namespace Subst

variable {σ : Signature}

/-- The content of the `◇_c` view goes to the hole; everything else stays. -/
def diaAbs (σ : Signature) (Δ : Ctx) (c : ℕ) : Subst σ Δ := fun v =>
  match v with
  | .step u .dia => if u = .root (.free c) then .ren (.root (.bnd 0)) else .hide
  | .step u .box => .ren (.step u .box)
  | .step u .keep => .ren (.step u .keep)
  | _ => .hide

/-- The address map of `diaAbs`: the witness content becomes the slot. -/
def diaAbsIdx (c : ℕ) : VarSymb → VarSymb
  | .root r => .root r
  | .step v s =>
      if v = .root (.free c) ∧ s = .dia then .root (.bnd 0) else .step (diaAbsIdx c v) s

omit [ModalSys] in
/-- Away from the witness content the map is applied at the head of the address. -/
theorem diaAbsIdx_ext_of {c : ℕ} : ∀ (p : List Step) {v : VarSymb}, v ≠ .root (.free c) →
    diaAbsIdx c (v.ext p) = (diaAbsIdx c v).ext p
  | [], _, _ => rfl
  | s :: p, v, h => by
      change diaAbsIdx c ((VarSymb.step v s).ext p) = _
      rw [diaAbsIdx_ext_of p (v := .step v s) (fun he => by cases he)]
      change (if v = .root (.free c) ∧ s = .dia then _ else
        VarSymb.step (diaAbsIdx c v) s).ext p = _
      rw [if_neg (fun hcon => h hcon.1)]
      rfl

omit [ModalSys] in
theorem diaAbsIdx_dia (c : ℕ) (p : List Step) :
    diaAbsIdx c ((VarSymb.step (.root (.free c)) .dia).ext p) = (VarSymb.root (.bnd 0)).ext p := by
  rw [diaAbsIdx_ext_of p (fun he => by cases he)]
  change (if (VarSymb.root (.free c)) = .root (.free c) ∧ Step.dia = .dia then _
    else VarSymb.step _ _).ext p = _
  rw [if_pos ⟨rfl, rfl⟩]

omit [ModalSys] in
/-- An address rooted elsewhere is untouched. -/
theorem diaAbsIdx_of_rt_ne {c : ℕ} : ∀ {i : VarSymb}, i.rt ≠ .free c → diaAbsIdx c i = i
  | .root _, _ => rfl
  | .step v s, h => by
      have hrt : v.rt ≠ .free c := h
      have hv : v ≠ .root (.free c) := by
        intro he
        rw [he] at hrt
        exact hrt rfl
      change (if v = .root (.free c) ∧ s = .dia then _ else VarSymb.step (diaAbsIdx c v) s) = _
      rw [if_neg (fun hcon => hv hcon.1), diaAbsIdx_of_rt_ne (i := v) hrt]

variable {Γ : Ctx} {c : ℕ} {A : VarType}

/-- The view of a declared `◇`-typed root: its entries are the witness content and the `□` view. -/
theorem diaIn_cases (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none) :
    ∀ {v : VarSymb} {T : VarType}, (Γ.diaIn (.root (.free c))) v = some T →
      (v = .step (.root (.free c)) .dia ∧ T = A) ∨
        (v.rt ≠ .free c ∧ Γ.boxIn v = some T ∧ (∀ Δ : Ctx, diaAbs σ Δ c v = .ren v) ∧
          ∀ r : Root, v ≠ .root r) := by
  intro v T hv
  match v with
  | .step u .dia =>
      have hu : u = .root (.free c) := by
        change (if u = .root (.free c) then
          (match Γ.ref (.root (.free c)) with
            | some (.VTypeDia X) => some X | _ => none) else none) = some T at hv
        split_ifs at hv with h
        exact h
      subst hu
      refine Or.inl ⟨rfl, ?_⟩
      change (if (VarSymb.root (.free c)) = .root (.free c) then
        (match Γ.ref (.root (.free c)) with
          | some (.VTypeDia X) => some X | _ => none) else none) = some T at hv
      rw [if_pos rfl, hcA] at hv
      exact (Option.some.inj hv).symm
  | .step u .box =>
      have hv' : Γ.boxIn (.step u .box) = some T := hv
      obtain ⟨_, hu⟩ := Ctx.boxIn_box hv'
      refine Or.inr ⟨?_, hv', fun _ => rfl, fun _ => by nofun⟩
      intro hrt
      by_cases hu0 : u = .root (.free c)
      · rw [hu0, hcA] at hu
        cases hu
      · rw [Ctx.ref_none_of_dia_root hcA hfr (u := u) hrt hu0] at hu
        cases hu
  | .step u .keep =>
      have hv' : Γ.boxIn (.step u .keep) = some T := hv
      obtain ⟨_, hu, _, rfl⟩ := Ctx.boxIn_keep hv'
      refine Or.inr ⟨?_, hv', fun _ => rfl, fun _ => by nofun⟩
      intro hrt
      by_cases hu0 : u = .root (.free c)
      · rw [hu0, hcA] at hu
        cases hu
      · rw [Ctx.ref_none_of_dia_root hcA hfr (u := u) hrt hu0] at hu
        cases hu
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

theorem ok_diaAbs (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    (h₀ : Γ.boxIn (.root (.bnd 0)) = none) :
    Ok (Γ.diaIn (.root (.free c)))
      (diaAbs σ (Γ.boxIn.insert (.bnd 0) A) c) := by
  intro v T hlp hv
  rcases diaIn_cases hcA hfr hv with ⟨rfl, rfl⟩ | ⟨_, hb, hen, _⟩
  · change (if (VarSymb.root (.free c)) = .root (.free c) then SubE.ren (.root (.bnd 0))
      else .hide).OkRef T
    rw [if_pos rfl]
    exact Ctx.ref_insert_root _ (.bnd 0) T
  · rw [hen (Γ.boxIn.insert (.bnd 0) A)]
    change (Γ.boxIn.insert (.bnd 0) A).ref v = some T
    exact (Ctx.ref_nonproj _ hlp).trans (Ctx.le_insert h₀ A v T hb)

theorem coh_diaAbs (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    (h₀ : Γ.boxIn (.root (.bnd 0)) = none) :
    Coh (diaAbsIdx c) (Γ.diaIn (.root (.free c)))
      (diaAbs σ (Γ.boxIn.insert (.bnd 0) A) c) := by
  refine coh_of (ok_diaAbs hcA hfr h₀) ?_
  intro v T _ hv p
  rcases diaIn_cases hcA hfr hv with ⟨rfl, rfl⟩ | ⟨hrt, _, hen, _⟩
  · change (if (VarSymb.root (.free c)) = .root (.free c) then SubE.ren (.root (.bnd 0))
      else .hide).idxAlong p = _
    rw [if_pos rfl, diaAbsIdx_dia c p]
    rfl
  · have hrt' : (v.ext p).rt ≠ .free c := by
      rw [VarSymb.ext_rt]
      exact hrt
    rw [diaAbsIdx_of_rt_ne hrt', hen (Γ.boxIn.insert (.bnd 0) A)]
    rfl

end Subst

/-! ## Abstracting a formula of the view -/

/-- ⭐The hole formula a formula of the `◇_c` view is read from. -/
def WFF.diaAbs {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (c : ℕ) {A : VarType}
    (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    (χ : WFF σ (Γ.diaIn (.root (.free c))) 0) :
    WFF σ (Γ.boxIn.insert (.bnd 0) A) 1 :=
  WFF.subst (Subst.diaAbsIdx c) (Subst.diaAbs σ (Γ.boxIn.insert (.bnd 0) A) c)
    (Subst.ok_diaAbs hcA hfr ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).root))
    (Subst.coh_diaAbs hcA hfr ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).root))
    Ctx.NoSlots.slots ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A) χ

/-- ⭐The same abstraction on a term of the view. -/
def Term.diaAbs {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (c : ℕ) {A : VarType}
    (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    {T : VarType} {b : Ann T} (t : Term σ (Γ.diaIn (.root (.free c))) T b) :
    Term σ (Γ.boxIn.insert (.bnd 0) A) T (b.mapIdx (Subst.diaAbsIdx c)) :=
  Term.subst (Subst.diaAbsIdx c) (Subst.diaAbs σ (Γ.boxIn.insert (.bnd 0) A) c)
    (Subst.ok_diaAbs hcA hfr ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).root))
    (Subst.coh_diaAbs hcA hfr ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).root)) t

/-- ⭐A term of a `□` view with a hole, read here with `t₀` in the hole: the term counterpart of
    `WFF.hereRead`. -/
def Term.hereRead {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true) {A : VarType}
    {a₀ : Ann A} (t₀ : Term σ Γ A a₀) {T : VarType} {b : Ann T}
    (s : Term σ (Γ.boxIn.insert (.bnd 0) A) T b) :
    Term σ Γ T ((b.collapse 0).mapIdx (Subst.singleIdx (.bnd 0) (.tm t₀))) :=
  Term.subst (Subst.singleIdx (.bnd 0) (.tm t₀)) (Subst.single (.bnd 0) (.tm t₀))
    (Subst.ok_single (Ctx.Le.refl Γ) rfl)
    (Subst.coh_single (Ctx.NoSlots.slots.rootFresh (le_refl 0)) (Ctx.Le.refl Γ) rfl)
    (Term.collapse ((Ctx.collapses_boxIn_self hT Γ).insert
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) A) s)

/-- ⭐The realisation of a view term: what it denotes at the world where the witness is realised
    by `t₀`.  Abstraction followed by `Term.hereRead`, so it needs no new recursion. -/
def Term.realiseAt {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true) (c : ℕ)
    {A : VarType} (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    {a₀ : Ann A} (t₀ : Term σ Γ A a₀) {T : VarType} {b : Ann T}
    (t : Term σ (Γ.diaIn (.root (.free c))) T b) :
    Term σ Γ T
      (((b.mapIdx (Subst.diaAbsIdx c)).collapse 0).mapIdx
        (Subst.singleIdx (.bnd 0) (.tm t₀))) :=
  Term.hereRead hT t₀ (Term.diaAbs c hcA hfr t)

/-- ⭐The realisation of a view formula. -/
def WFF.realiseAt {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true) (c : ℕ)
    {A : VarType} (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    {a₀ : Ann A} (t₀ : Term σ Γ A a₀)
    (χ : WFF σ (Γ.diaIn (.root (.free c))) 0) :
    WFF σ Γ 0 :=
  WFF.hereRead hT t₀ (WFF.diaAbs c hcA hfr χ)

/-! ## Weakening -/

/-- Abstraction commutes with weakening. -/
theorem Term.mono_diaAbs {σ : Signature} {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] {c : ℕ}
    {A : VarType} (h : Γ.Le Γ')
    (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hcA' : Γ'.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    (hfr' : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ' v = none)
    {T : VarType} {b : Ann T} (t : Term σ (Γ.diaIn (.root (.free c))) T b) :
    Term.mono (h.boxIn.insert (.bnd 0) A) (Term.diaAbs c hcA hfr t) =
      Term.diaAbs c hcA' hfr' (Term.mono (h.diaIn (.root (.free c))) t) := by
  unfold Term.diaAbs
  rw [Term.mono_subst, Term.subst_mono]
  refine eq_of_heq (Sigma.mk.inj (Term.subst_congr _ _ _ _ _ _ ?_ t)).2
  refine Subst.sim_of ?_
  intro v U _ _
  match v with
  | .step u .dia =>
      change SubE.Sim U (SubE.mono _ (if u = .root (.free c) then SubE.ren (.root (.bnd 0))
        else .hide)) (if u = .root (.free c) then SubE.ren (.root (.bnd 0)) else .hide)
      by_cases hu : u = .root (.free c)
      · simp only [if_pos hu]
        exact .refl _
      · simp only [if_neg hu]
        exact .refl _
  | .step _ .box => exact .refl _
  | .step _ .keep => exact .refl _
  | .root _ => exact .refl _
  | .step _ .fst => exact .refl _
  | .step _ .snd => exact .refl _
  | .step _ .here => exact .refl _

/-- Reading a hole term here commutes with weakening. -/
theorem Term.mono_hereRead {σ : Signature} {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots]
    (hT : ModalSys.T = true) (h : Γ.Le Γ') {A : VarType} {a₀ : Ann A} (t₀ : Term σ Γ A a₀)
    {T : VarType} {b : Ann T} (s : Term σ (Γ.boxIn.insert (.bnd 0) A) T b) :
    Term.mono h (Term.hereRead hT t₀ s) =
      Term.hereRead hT (Term.mono h t₀) (Term.mono (h.boxIn.insert (.bnd 0) A) s) := by
  unfold Term.hereRead
  rw [Term.mono_subst,
    Term.collapse_mono ((Ctx.collapses_boxIn_self hT Γ).insert
        ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) A)
      ((Ctx.collapses_boxIn_self hT Γ').insert
        ((Ctx.NoSlots.slots (Γ := Γ'.boxIn)).rootFresh (le_refl 0)) A)
      (h.boxIn.insert (.bnd 0) A) (h.insert (.bnd 0) A) s, Term.subst_mono]
  refine eq_of_heq (Sigma.mk.inj (Term.subst_congr _ _ _ _ _ _ ?_ _)).2
  refine Subst.sim_of ?_
  intro v U _ _
  by_cases hv : v = .root (.bnd 0)
  · subst hv
    change SubE.Sim U (SubE.mono h (.tm t₀)) (if (VarSymb.root (Root.bnd 0)) = .root (.bnd 0)
      then SubE.tm (Term.mono h t₀) else .ren _)
    rw [if_pos rfl]
    exact .refl _
  · change SubE.Sim U (SubE.mono h (if v = .root (.bnd 0) then .tm t₀ else .ren v))
      (if v = .root (.bnd 0) then SubE.tm (Term.mono h t₀) else .ren v)
    simp only [if_neg hv]
    exact .refl _

/-- Realisation commutes with weakening. -/
theorem Term.mono_realiseAt {σ : Signature} {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots]
    (hT : ModalSys.T = true) (h : Γ.Le Γ') {c : ℕ} {A : VarType}
    (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hcA' : Γ'.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    (hfr' : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ' v = none)
    {a₀ : Ann A} (t₀ : Term σ Γ A a₀) {T : VarType} {b : Ann T}
    (t : Term σ (Γ.diaIn (.root (.free c))) T b) :
    Term.mono h (Term.realiseAt hT c hcA hfr t₀ t) =
      Term.realiseAt hT c hcA' hfr' (Term.mono h t₀) (Term.mono (h.diaIn (.root (.free c))) t) := by
  unfold Term.realiseAt
  rw [Term.mono_hereRead hT h t₀ (Term.diaAbs c hcA hfr t),
    Term.mono_diaAbs h hcA hcA' hfr hfr' t]

/-- ⭐A hole formula read inside `◇_c`, at any context where `c` is a declared `◇`-typed root.
    `WFF.viewRead` is the case of a context that has just declared it. -/
def WFF.viewReadAt {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (c : ℕ) {A : VarType}
    (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) : WFF σ (Γ.diaIn (.root (.free c))) 0 :=
  WFF.renameRoot (.bnd 0) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0))
    (Ctx.le_boxIn_diaIn Γ (.root (.free c))) (.step (.root (.free c)) .dia)
    (Ctx.ref_diaIn_of hcA) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A) Ctx.NoSlots.slots ψ

/-- Abstracting and then reading back is the identity substitution. -/
theorem Subst.sim_diaAbs_viewRead {σ : Signature} {Γ : Ctx} {c : ℕ} {A : VarType}
    (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    {ι₂ : VarSymb → VarSymb}
    (hθ₂ : Subst.Ok (Γ.boxIn.insert (.bnd 0) A)
      (Subst.single (σ := σ) (Δ := Γ.diaIn (.root (.free c)))
        (.bnd 0) (.ren (.step (.root (.free c)) .dia))))
    (hc₂ : Subst.Coh ι₂ (Γ.boxIn.insert (.bnd 0) A)
      (Subst.single (σ := σ) (Δ := Γ.diaIn (.root (.free c)))
        (.bnd 0) (.ren (.step (.root (.free c)) .dia)))) :
    Subst.Sim (Γ.diaIn (.root (.free c)))
      (Subst.idS σ (Γ.diaIn (.root (.free c))))
      ((Subst.diaAbs σ (Γ.boxIn.insert (.bnd 0) A) c).comp
        (Subst.single (.bnd 0) (.ren (.step (.root (.free c)) .dia))) hθ₂ hc₂) := by
  refine Subst.sim_of ?_
  intro v T hlp hv
  rcases Subst.diaIn_cases hcA hfr hv with ⟨rfl, _⟩ | ⟨_, _, hen, hroot⟩
  · change SubE.Sim T (.ren (.step (.root (.free c)) .dia))
      ((if (VarSymb.root (.free c)) = .root (.free c) then SubE.ren (.root (.bnd 0))
        else .hide).comp _ hθ₂ hc₂)
    rw [if_pos rfl]
    change SubE.Sim T (.ren (.step (.root (.free c)) .dia))
      (if (VarSymb.root (Root.bnd 0)) = .root (.bnd 0) then
        SubE.ren (.step (.root (.free c)) .dia) else .ren (.root (.bnd 0)))
    rw [if_pos rfl]
    exact .refl _
  · change SubE.Sim T (.ren v) ((Subst.diaAbs σ (Γ.boxIn.insert (.bnd 0) A) c v).comp _ hθ₂ hc₂)
    rw [hen (Γ.boxIn.insert (.bnd 0) A)]
    change SubE.Sim T (.ren v)
      ((Subst.single (.bnd 0) (.ren (.step (.root (.free c)) .dia))).at v)
    rw [Subst.at_nonproj _ hlp,
      show (Subst.single (σ := σ)
        (Δ := Γ.diaIn (.root (.free c))) (.bnd 0)
        (.ren (.step (.root (.free c)) .dia))) v = .ren v from if_neg (hroot (.bnd 0))]
    exact .refl _

/-- ⭐The round trip: every formula of the `◇_c` view is read from its abstraction. -/
theorem WFF.viewReadAt_diaAbs {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (c : ℕ) {A : VarType}
    (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    (χ : WFF σ (Γ.diaIn (.root (.free c))) 0) :
    WFF.viewReadAt c hcA (WFF.diaAbs c hcA hfr χ) = χ := by
  have h₀ : Γ.boxIn (.root (.bnd 0)) = none := (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root
  refine (WFF.subst_comp _ _ (Subst.idS σ _) (Subst.ok_diaAbs hcA hfr h₀)
    (Subst.coh_diaAbs hcA hfr h₀) _ _
    Subst.ok_idS Subst.coh_idS Ctx.NoSlots.slots ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A)
    Ctx.NoSlots.slots (Subst.sim_diaAbs_viewRead hcA hfr _ _) χ).trans ?_
  exact WFF.subst_id Subst.ok_idS Subst.coh_idS Ctx.NoSlots.slots χ

end V12M
