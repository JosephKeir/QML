import QML.QML_v12m_Leibniz

/-!
# QML v12m — renaming one view onto another

The canonical model's extent has to be closed under the equality of `◇`-types (§2d): a child world
is tagged by the witness whose view its language is, so a child tagged `y` lies in `x`'s extent when
the theory identifies `x` and `y`, and then a body written in the `x`-view has to be read in the
`y`-view.  That reading is a **renaming of the content address**, `x.dia ↦ y.dia`, and it fits the
existing substitution framework:

* ⭐`VarSymb.reView x y`: the address map, replacing the prefix `x.dia` by `y.dia`.  It commutes with
  extension below the prefix (`reView_ext_dia`) and is the identity elsewhere (`reView_eq_self`).
* ⭐`Subst.viewRen`: the substitution itself, every entry a renaming.  Its `Ok` and `Coh` hold
  provided nothing under the symbol `x.dia` is declared in the outer context (`hcl`) — otherwise the
  view's content address and a `□`-component of the outer context would be the same symbol, and no
  address map could serve both.

`Term.subst` and `WFF.subst` along it are then the renaming of a view term and a view formula, with
their laws and semantics coming from the general substitution lemmas.
-/

namespace V12M

variable [ModalSys]

/-! ## The address map -/

/-- ⭐The prefix `x.dia` becomes `y.dia`. -/
def VarSymb.reView (x y : VarSymb) : VarSymb → VarSymb
  | .root r => .root r
  | .step v s => if v = x ∧ s = Step.dia then .step y .dia else .step (VarSymb.reView x y v) s

namespace VarSymb

variable {x y : VarSymb}

omit [ModalSys] in
theorem reView_step_of_ne {v : VarSymb} {s : Step} (h : ¬(v = x ∧ s = Step.dia)) :
    reView x y (.step v s) = .step (reView x y v) s :=
  if_neg h

omit [ModalSys] in
theorem reView_dia : reView x y (.step x .dia) = .step y .dia := if_pos ⟨rfl, rfl⟩

omit [ModalSys] in
theorem ext_append : ∀ (v : VarSymb) (p : List Step) (s : Step),
    v.ext (p ++ [s]) = .step (v.ext p) s
  | _, [], _ => rfl
  | v, s' :: p, s => ext_append (.step v s') p s

omit [ModalSys] in
theorem path_ext : ∀ (v : VarSymb) (p : List Step), (v.ext p).path = v.path ++ p
  | _, [] => (List.append_nil _).symm
  | v, s :: p => by
      change (VarSymb.ext (.step v s) p).path = _
      rw [path_ext (.step v s) p]
      change v.path ++ [s] ++ p = _
      rw [List.append_assoc]
      rfl

omit [ModalSys] in
/-- Below the prefix the map is extension. -/
theorem reView_ext_of_long : ∀ (p : List Step) {v : VarSymb},
    x.path.length < v.path.length → reView x y (v.ext p) = (reView x y v).ext p
  | [], _, _ => rfl
  | s :: p, v, hv => by
      have hstep : x.path.length < (VarSymb.step v s).path.length := by
        change x.path.length < (v.path ++ [s]).length
        rw [List.length_append]
        omega
      have hne : ¬(v = x ∧ s = Step.dia) := fun h => by
        rw [h.1] at hv
        omega
      change reView x y ((VarSymb.step v s).ext p) = _
      rw [reView_ext_of_long p hstep, reView_step_of_ne hne]
      rfl

omit [ModalSys] in
/-- ⭐The map on the view's own addresses. -/
theorem reView_ext_dia (p : List Step) :
    reView x y ((VarSymb.step x .dia).ext p) = (VarSymb.step y .dia).ext p := by
  have hlen : x.path.length < (VarSymb.step x .dia).path.length := by
    change x.path.length < (x.path ++ [Step.dia]).length
    simp
  rw [reView_ext_of_long p hlen, reView_dia]

omit [ModalSys] in
/-- ⭐Elsewhere the map does nothing. -/
theorem reView_eq_self {v : VarSymb} (h : ∀ p, v ≠ (VarSymb.step x .dia).ext p) :
    reView x y v = v := by
  induction v with
  | root r => rfl
  | step v s ih =>
      have hne : ¬(v = x ∧ s = Step.dia) := fun hc => h [] (by obtain ⟨rfl, rfl⟩ := hc; rfl)
      rw [reView_step_of_ne hne, ih (fun p hp => h (p ++ [s]) (by rw [ext_append, ← hp]))]

end VarSymb

/-! ## The substitution -/

/-- The view's content address is not a symbol the outer context declares below or above: no
    box-visible address of the view has `x.dia` as a prefix, and none is a prefix of it.  Otherwise
    one symbol would have to be both the view's content and a `□`-component, and no address map
    could serve both.  Every context of the canonical model is clean in this sense. -/
def Ctx.ViewClean (Γ : Ctx) (x : VarSymb) : Prop :=
  ∀ (v : VarSymb) (T : VarType), v.lastProj = false → Γ.boxIn v = some T →
    ∀ p q : List Step, v.ext p ≠ (VarSymb.step x .dia).ext q

theorem Ctx.diaIn_of_ne_dia {Γ : Ctx} {y : VarSymb} :
    ∀ {v : VarSymb}, (∀ u, v ≠ .step u .dia) → Γ.diaIn y v = Γ.boxIn v
  | .root _, _ => rfl
  | .step _ .fst, _ => rfl
  | .step _ .snd, _ => rfl
  | .step _ .box, _ => rfl
  | .step _ .here, _ => rfl
  | .step _ .keep, _ => rfl
  | .step u .dia, h => absurd rfl (h u)

namespace Subst

variable {σ : Signature}

/-- ⭐The view renaming: the content address moves, every other entry stays where it is. -/
def viewRen (σ : Signature) (Γ : Ctx) (x y : VarSymb) : Subst σ (Γ.diaIn y) := fun v =>
  match v with
  | .step u .dia => if u = x then .ren (.step y .dia) else .hide
  | v => .ren v

theorem viewRen_dia {Γ : Ctx} {x y : VarSymb} :
    viewRen σ Γ x y (.step x .dia) = .ren (.step y .dia) := if_pos rfl

theorem viewRen_of_ne_dia {Γ : Ctx} {x y : VarSymb} :
    ∀ {v : VarSymb}, (∀ u, v ≠ .step u .dia) → viewRen σ Γ x y v = .ren v
  | .root _, _ => rfl
  | .step _ .fst, _ => rfl
  | .step _ .snd, _ => rfl
  | .step _ .box, _ => rfl
  | .step _ .here, _ => rfl
  | .step _ .keep, _ => rfl
  | .step u .dia, h => absurd rfl (h u)

/-- ⭐The entries fit: the content address has the content type at both ends, and every other
    visible address is a `□`-component, which the view does not touch. -/
theorem ok_viewRen {Γ : Ctx} {x y : VarSymb} {A : VarType}
    (hx : Γ.ref x = some (.VTypeDia A)) (hy : Γ.ref y = some (.VTypeDia A)) :
    Ok (Γ.diaIn x) (viewRen σ Γ x y) := by
  intro v T hlp hv
  by_cases hd : ∃ u, v = .step u .dia
  · obtain ⟨u, rfl⟩ := hd
    change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
      else none) = some T at hv
    split_ifs at hv with hux
    · subst hux
      rw [hx] at hv
      cases hv
      rw [viewRen_dia]
      exact Ctx.ref_diaIn_of hy
  · have hne : ∀ u, v ≠ .step u .dia := fun u h => hd ⟨u, h⟩
    rw [Ctx.diaIn_of_ne_dia hne] at hv
    change (viewRen σ Γ x y v).OkRef T
    rw [viewRen_of_ne_dia hne]
    change (Γ.diaIn y).ref v = some T
    rw [Ctx.ref_nonproj _ hlp, Ctx.diaIn_of_ne_dia hne]
    exact hv

/-- ⭐The annotations follow the address map. -/
theorem coh_viewRen {Γ : Ctx} {x y : VarSymb} {A : VarType}
    (hx : Γ.ref x = some (.VTypeDia A)) (hy : Γ.ref y = some (.VTypeDia A))
    (hcl : Ctx.ViewClean Γ x) :
    Coh (VarSymb.reView x y) (Γ.diaIn x) (viewRen σ Γ x y) := by
  refine coh_of (ok_viewRen hx hy) ?_
  intro v T hlp hv p
  by_cases hd : ∃ u, v = .step u .dia
  · obtain ⟨u, rfl⟩ := hd
    change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
      else none) = some T at hv
    split_ifs at hv with hux
    · subst hux
      rw [viewRen_dia]
      exact (VarSymb.reView_ext_dia p).symm
  · have hne : ∀ u, v ≠ .step u .dia := fun u h => hd ⟨u, h⟩
    rw [Ctx.diaIn_of_ne_dia hne] at hv
    rw [viewRen_of_ne_dia hne]
    exact (VarSymb.reView_eq_self (fun q => hcl v T hlp hv p q)).symm

end Subst


/-! ## Renaming a view term and a view formula -/

/-- ⭐A term of the `x`-view, read in the `y`-view. -/
def Term.reView {σ : Signature} {Γ : Ctx} {x y : VarSymb} {A : VarType}
    (hx : Γ.ref x = some (.VTypeDia A)) (hy : Γ.ref y = some (.VTypeDia A))
    (hcl : Ctx.ViewClean Γ x) {T : VarType} {a : Ann T} (t : Term σ (Γ.diaIn x) T a) :
    Term σ (Γ.diaIn y) T (a.mapIdx (VarSymb.reView x y)) :=
  Term.subst (VarSymb.reView x y) (Subst.viewRen σ Γ x y) (Subst.ok_viewRen hx hy)
    (Subst.coh_viewRen hx hy hcl) t

/-- ⭐A formula of the `x`-view, read in the `y`-view. -/
def WFF.reView {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {x y : VarSymb} {A : VarType}
    (hx : Γ.ref x = some (.VTypeDia A)) (hy : Γ.ref y = some (.VTypeDia A))
    (hcl : Ctx.ViewClean Γ x) (φ : WFF σ (Γ.diaIn x) 0) : WFF σ (Γ.diaIn y) 0 :=
  WFF.subst (VarSymb.reView x y) (Subst.viewRen σ Γ x y) (Subst.ok_viewRen hx hy)
    (Subst.coh_viewRen hx hy hcl) (Ctx.NoSlots.slots.diaIn x) (Ctx.NoSlots.slots.diaIn y) φ

omit [ModalSys] in
/-- The address map of a view renamed onto itself is the identity. -/
theorem VarSymb.reView_self {x : VarSymb} : ∀ v : VarSymb, VarSymb.reView x x v = v
  | .root _ => rfl
  | .step v s => by
      by_cases hc : v = x ∧ s = Step.dia
      · obtain ⟨rfl, rfl⟩ := hc
        exact VarSymb.reView_dia
      · rw [VarSymb.reView_step_of_ne hc, VarSymb.reView_self v]

omit [ModalSys] in
theorem VarSymb.reView_self_eq {x : VarSymb} : VarSymb.reView x x = id :=
  funext VarSymb.reView_self

/-- Every visible address of the view is its own entry when the view is renamed onto itself. -/
theorem Subst.at_viewRen_self {σ : Signature} {Γ : Ctx} {x : VarSymb} :
    ∀ {v : VarSymb} {T : VarType}, (Γ.diaIn x).ref v = some T →
      (Subst.viewRen σ Γ x x).at v = .ren v
  | .root _, _, _ => rfl
  | .step v s, T, hv => by
      change (if s.isProj then ((Subst.viewRen σ Γ x x).at v).proj s
        else Subst.viewRen σ Γ x x (.step v s)) = _
      by_cases hs : s.isProj = true
      · rw [if_pos hs, Ctx.ref_step_proj _ _ hs] at *
        obtain ⟨U, hU, -⟩ := Option.bind_eq_some_iff.mp hv
        rw [Subst.at_viewRen_self hU]
        rfl
      · rw [if_neg hs]
        match s with
        | .fst => exact absurd rfl hs
        | .snd => exact absurd rfl hs
        | .here => exact absurd rfl hs
        | .box => rfl
        | .keep => rfl
        | .dia =>
            rw [Ctx.ref_nonproj _ (rfl : (VarSymb.step v .dia).lastProj = false)] at hv
            change (if v = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
              else none) = some T at hv
            split_ifs at hv with hvx
            · subst hvx
              exact Subst.viewRen_dia

/-- ⭐Renaming a view onto itself changes nothing. -/
theorem Term.reView_self {σ : Signature} {Γ : Ctx} {x : VarSymb} {A : VarType}
    (hx : Γ.ref x = some (.VTypeDia A)) (hcl : Ctx.ViewClean Γ x) {T : VarType} {a : Ann T}
    (t : Term σ (Γ.diaIn x) T a) :
    (⟨_, Term.reView hx hx hcl t⟩ : Σ b, Term σ (Γ.diaIn x) T b) = ⟨a, t⟩ :=
  (Term.subst_ren (Ctx.Le.refl _) _ _ _ (fun _ _ hv => Subst.at_viewRen_self hv) t).trans
    (congrArg (Sigma.mk _) (Term.mono_refl _ t))

end V12M
