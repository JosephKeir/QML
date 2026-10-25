import QML.QML_v12m_GView
import QML.QML_v12m_SubstShift
import QML.QML_v12m_ViewFresh

/-!
# QML v12m — the growing tree: keeping a pulled-back view along a view tuple's edge

The syntactic core of strong 4's `◇`-lift with view tuples (`docs/v12-modal-extensions.md` §3 4,
D-H1).  A root `x` of the parent is lifted to `z`'s view tuple `◇_z ⟨η(z.dia), items⟩`; a term `u`
of `z`'s view, pulled back to `x`'s view (`pullS`), kept along the edge, is `u` again:

* `Subst.atShift`: a substitution read at the addresses shifted at `0`, with `Ok`, `Coh` (one level
  step per declared address) and `PreShift`;
* `SubE.projs`, `Subst.at_ext_ppath`: entries along projection paths; `projs_itemsTm`: the `k`-th
  item of an items tuple;
* ⭐`subst_shift_pullS`: substituting the edge's entries into the shifted pull-back of `u` is `u`
  (`Term.subst_shift`, `Term.subst_comp` with the composite `∼` the identity, `subst_idS_mono`).
-/

namespace V12M

variable [ModalSys]

open BArrow

/-! ## A substitution at shifted addresses -/

namespace Subst

variable {σ : Signature} {Δ : Ctx}

/-- `Ψ` read at the addresses shifted at `0`. -/
def atShift (Ψ : Subst σ Δ) : Subst σ Δ := fun v => Ψ.at (v.shift 0)

theorem at_atShift (Ψ : Subst σ Δ) : ∀ v : VarSymb, (atShift Ψ).at v = Ψ.at (v.shift 0)
  | .root _ => rfl
  | .step v s => by
      by_cases hs : s.isProj = true
      · change (if s.isProj then ((atShift Ψ).at v).proj s else _) = _
        rw [if_pos hs, at_atShift Ψ v, VarSymb.shift_proj hs]
        change _ = (if s.isProj then (Ψ.at (v.shift 0)).proj s else _)
        rw [if_pos hs]
      · rw [at_nonproj _ (show (VarSymb.step v s).lastProj = false from
          Bool.eq_false_iff.mpr hs)]
        rfl

theorem ok_atShift {Γ Γ' : Ctx} (C : Ctx.Shifts 0 Γ Γ') {Ψ : Subst σ Δ} (hΨ : Ok Γ' Ψ) :
    Ok Γ (atShift Ψ) :=
  fun v T hlp hv => okRef_at hΨ (C v T ((Ctx.ref_nonproj Γ hlp).trans hv))

theorem coh_atShift {Γ Γ' : Ctx} (C : Ctx.Shifts 0 Γ Γ') {Ψ : Subst σ Δ} (hΨ : Ok Γ' Ψ)
    {ι : VarSymb → VarSymb} (hc : Coh ι Γ' Ψ)
    (hlv : ∀ v T, v.lastProj = false → Γ v = some T → Step.levels v.path = 1) :
    Coh (fun y => ι (y.shift (Step.levels y.path - 1))) Γ (atShift Ψ) := by
  refine coh_of (ok_atShift C hΨ) fun v T hlp hv p => ?_
  change (Ψ.at (v.shift 0)).idxAlong p = _
  rw [hc _ _ (C v T ((Ctx.ref_nonproj Γ hlp).trans hv)) p, VarSymb.ext_path, Step.levels_append,
    hlv v T hlp hv, show 1 + Step.levels p - 1 = 0 + Step.levels p by omega, VarSymb.shift_ext]

theorem preShift_atShift (Γ : Ctx) (Ψ : Subst σ Δ) : PreShift 0 Γ Ψ (atShift Ψ) :=
  fun v _ _ => by
    rw [at_atShift]
    exact .refl _

end Subst

/-! ## Entries along projection paths -/

namespace SubE

variable {σ : Signature} {Δ : Ctx}

/-- An entry read along a path of projections. -/
def projs : SubE σ Δ → List Step → SubE σ Δ
  | e, [] => e
  | e, s :: q => projs (e.proj s) q

end SubE

theorem Subst.at_ext_ppath {σ : Signature} {Δ : Ctx} (θ : Subst σ Δ) :
    ∀ (w : VarSymb) (q : List Step), PPath q → θ.at (w.ext q) = (θ.at w).projs q
  | _, [], _ => rfl
  | w, s :: q, hq => by
      change θ.at ((VarSymb.step w s).ext q) = _
      rw [Subst.at_ext_ppath θ (.step w s) q (fun s' h => hq s' (List.mem_cons_of_mem _ h))]
      change ((if s.isProj then (θ.at w).proj s else θ _)).projs q = _
      rw [if_pos (hq s List.mem_cons_self)]
      rfl

omit [ModalSys] in
theorem levels_ppath : ∀ {p : List Step}, PPath p → Step.levels p = 0
  | [], _ => rfl
  | s :: p, h => by
      change (if s.isProj then 0 else 1) + Step.levels p = 0
      rw [if_pos (h s List.mem_cons_self),
        levels_ppath (fun s' hs => h s' (List.mem_cons_of_mem _ hs))]

omit [ModalSys] in
theorem shift_ext_ppath (w : VarSymb) {q : List Step} (hq : PPath q) :
    (w.ext q).shift 0 = (w.shift 0).ext q := by
  have := VarSymb.shift_ext w q 0
  rwa [levels_ppath hq] at this

/-! ## The items of a tuple -/

theorem mono_itemsTm {σ : Signature} {Γ Γ' : Ctx} (h : Γ.Le Γ') :
    ∀ (L : List (VarSymb × VarType)) (hL : ∀ e ∈ L, Γ.ref e.1 = some e.2)
      (hL' : ∀ e ∈ L, Γ'.ref e.1 = some e.2),
      (⟨_, Term.mono h (itemsTm (σ := σ) L hL).2⟩ : Σ a, Term σ Γ' (itemsTy L) a) =
        itemsTm (σ := σ) L hL'
  | [], _, _ => rfl
  | _ :: L, _, hL' =>
      sig_pair (congrArg (Sigma.mk _) (Term.mono_eta h _ _ _))
        (mono_itemsTm h L _ (fun e' he' => hL' e' (List.mem_cons_of_mem _ he')))

theorem projs_itemsTm {σ : Signature} {Γ : Ctx} :
    ∀ (L : List (VarSymb × VarType)) (hL : ∀ e ∈ L, Γ.ref e.1 = some e.2) (k : ℕ)
      (hk : k < L.length),
      (SubE.tm (itemsTm (σ := σ) L hL).2).projs (itemPath k) =
        .tm (Term.eta L[k].1 L[k].2 (hL _ (List.getElem_mem hk)))
  | _ :: _, _, 0, _ => rfl
  | _ :: L, hL, k + 1, hk => projs_itemsTm L _ k (by simpa using hk)

/-! ## Keeping a pulled-back view along the edge -/

variable {σ : Signature}

/-- Every declared address of a world language's `◇` view has one level step. -/
theorem levels_diaIn_ctxOf {l : List VarType} {x : VarSymb}
    {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X)) :
    ∀ v T, v.lastProj = false → (ctxOf l).diaIn x v = some T → Step.levels v.path = 1 := by
  intro v T _ hv
  have one : ∀ (u : VarSymb) (s : Step), PPath u.path → s.isProj = false →
      Step.levels (VarSymb.step u s).path = 1 := fun u s hu hs => by
    change Step.levels (u.path ++ [s]) = 1
    rw [Step.levels_append, levels_ppath hu]
    simp [Step.levels, hs]
  match v, hv with
  | .step u .dia, hv =>
      change (if u = x then _ else none) = some T at hv
      split_ifs at hv with h
      subst h
      exact one u .dia (reach_ppath hx).1 rfl
  | .step u .keep, hv => exact one u .keep (reach_ppath (Ctx.boxIn_keep hv).2.1).1 rfl
  | .step u .box, hv => exact one u .box (reach_ppath (Ctx.boxIn_box hv).2).1 rfl
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .here, hv => cases hv

theorem SubE.tm_of_sig {Δ : Ctx} {T : VarType} {a b : Ann T} {s : Term σ Δ T a}
    {t : Term σ Δ T b} (h : (⟨a, s⟩ : Σ c, Term σ Δ T c) = ⟨b, t⟩) :
    (SubE.tm s : SubE σ Δ) = SubE.tm t := by
  cases h
  rfl

theorem SubE.sim_ren_eta' {Δ : Ctx} {v w : VarSymb} {T U : VarType} (h : Δ.ref w = some U)
    (hv : w = v) (hT : U = T) : SubE.Sim T (.ren v) (SubE.tm (σ := σ) (Term.eta w U h)) := by
  subst hv hT
  exact .ren_eta _ _

/-- The declared addresses of a `◇` view other than its content are the `□` view's. -/
theorem diaIn_boxIn_of_ne {Γ : Ctx} {z v : VarSymb} {T : VarType} (hv : Γ.diaIn z v = some T)
    (hvz : v ≠ .step z .dia) : Γ.boxIn v = some T := by
  match v, hv with
  | .step u .dia, hv =>
      change (if u = z then _ else none) = some T at hv
      split_ifs at hv with h
      · exact absurd (congrArg (VarSymb.step · Step.dia) h) hvz
  | .root _, hv => exact hv
  | .step _ .fst, hv => exact hv
  | .step _ .snd, hv => exact hv
  | .step _ .box, hv => exact hv
  | .step _ .keep, hv => exact hv
  | .step _ .here, hv => exact hv

/-- The edge's entry at the content of a root lifted to a view tuple: the tuple's body. -/
theorem at_keep_dia_viewTuple (hF : ModalSys.Four = true) {l : List VarType} {Δ : Ctx}
    (hle : (ctxOf l).Le Δ) {z x : VarSymb} {Z : VarType}
    (hz : (ctxOf l).ref z = some (.VTypeDia Z)) (E : Subst σ Δ)
    (hent : E.at (.step x .keep) =
      .tm (Term.mono hle (GArrow.viewTuple (σ := σ) hF l z Z hz).2.2.2)) :
    (E.dia (.step x .keep) z).at (.step (.step x .keep) .dia) =
      .tm (.pair (Term.eta (.step z .dia) Z (Ctx.ref_diaIn_of (hle.ref hz)))
        (itemsTm (σ := σ) (boxItems l) fun e he =>
          (hle.diaIn z).ref ((Ctx.le_boxIn_diaIn _ z).ref (boxItems_ref hF l e he))).2) := by
  rw [Subst.at_nonproj _ rfl]
  change (if VarSymb.step x .keep = VarSymb.step x .keep then
    (E.at (.step x .keep)).diaBody z else .hide) = _
  rw [if_pos rfl, hent]
  change (SubE.tm (Term.diatm z _ (Term.mono (hle.diaIn z) _))).diaBody z = _
  rw [SubE.diaBody_diatm]
  refine SubE.tm_of_sig ?_
  change (⟨_, Term.pair (Term.mono (hle.diaIn z) (Term.eta _ _ _))
    (Term.mono (hle.diaIn z) (Term.mono _ (itemsTm _ _).2))⟩ : Σ b, Term σ _ _ b) = _
  rw [Term.mono_eta, Term.mono_mono]
  exact sig_pair rfl (mono_itemsTm _ _ _ _)

/-- ⭐**Keeping a pulled-back view term along a view tuple's edge gives it back.**  The edge's entry
    for the lifted root's kept item is the view tuple; read at the shifted pull-back, the edge sends
    `z.dia` and each item of the `□` view to its η-expansion, so the composite is the identity up to
    η. -/
theorem subst_shift_pullS (hF : ModalSys.Four = true) {l l' : List VarType} {Δ : Ctx}
    (hle : (ctxOf l).Le Δ) {z x : VarSymb} {Z : VarType}
    (hz : (ctxOf l).ref z = some (.VTypeDia Z))
    (hx : (ctxOf l').ref x = some (.VTypeDia (.VTypeProd Z (itemsTy (boxItems l)))))
    {ι : VarSymb → VarSymb} (E : Subst σ Δ) (hE : Subst.Ok (ctxOf l').boxIn E)
    (hcE : Subst.Coh ι (ctxOf l').boxIn E)
    (hent : E.at (.step x .keep) =
      .tm (Term.mono hle (GArrow.viewTuple (σ := σ) hF l z Z hz).2.2.2))
    {A : VarType} {a : Ann A} (u : Term σ ((ctxOf l).diaIn z) A a) :
    (⟨_, Term.subst ι E hE hcE (Term.diatm (.step x .keep) (Ctx.exists_keep_dia hF ⟨_, hx⟩)
        (Term.shift (Ctx.shifts_diaIn_keep hF (ctxOf l') x)
          (Term.subst (pullIdx l z x) (pullS l z x) (ok_pullS hF hz hx) (coh_pullS hF hz hx)
            u)))⟩ : Σ b, Term σ Δ (.VTypeDia A) b) =
      ⟨_, Term.mono hle (Term.diatm z ⟨Z, hz⟩ u)⟩ := by
  have hxk : (ctxOf l').boxIn.ref (.step x .keep) =
      some (.VTypeDia (.VTypeProd Z (itemsTy (boxItems l)))) :=
    Ctx.ref_keep_of' hF hx VarType.keepable_dia
  have hwz : ι (.step x .keep) = z := by
    have := hcE _ _ hxk []
    rw [hent] at this
    exact this.symm
  have C := Ctx.shifts_diaIn_keep hF (ctxOf l') x
  have hlv := levels_diaIn_ctxOf hx
  have key : ∀ (y : VarSymb) (_hy : y = z) (P : ∃ Y, Δ.ref y = some (.VTypeDia Y))
      (p : Subst.Ok ((ctxOf l').boxIn.diaIn (.step x .keep)) (E.dia (.step x .keep) y))
      (q : Subst.Coh ι ((ctxOf l').boxIn.diaIn (.step x .keep)) (E.dia (.step x .keep) y)),
      (⟨_, Term.diatm y P (Term.subst ι (E.dia (.step x .keep) y) p q
          (Term.shift (Ctx.shifts_diaIn_keep hF (ctxOf l') x)
            (Term.subst (pullIdx l z x) (pullS l z x) (ok_pullS hF hz hx)
              (coh_pullS hF hz hx) u)))⟩ : Σ b, Term σ Δ (.VTypeDia A) b) =
        ⟨_, Term.mono hle (Term.diatm z ⟨Z, hz⟩ u)⟩ := by
    intro y hy P p q
    cases hy
    refine sig_diatm ?_
    have okA := Subst.ok_atShift C p
    have cohA := Subst.coh_atShift C p q hlv
    have hsim : Subst.Sim ((ctxOf l).diaIn z) (Subst.idS σ (Δ.diaIn z))
        ((pullS l z x).comp (Subst.atShift (E.dia (.step x .keep) z)) okA cohA) := by
      refine Subst.sim_of fun v T _ hv => ?_
      change SubE.Sim T (.ren v) ((pullS l z x v).comp _ okA cohA)
      by_cases hvz : v = .step z .dia
      · subst hvz
        rw [pullS_dia]
        change SubE.Sim T (.ren _) ((Subst.atShift (E.dia (.step x .keep) z)).at _)
        rw [Subst.at_atShift,
          show (x.ext [.dia, .fst]).shift 0 = (VarSymb.step (.step x .keep) .dia).ext [.fst] from
            rfl,
          Subst.at_ext_ppath _ _ _ (fun s hs => by rw [List.mem_singleton.mp hs]; rfl),
          at_keep_dia_viewTuple hF hle hz E hent]
        have hZ : Z = T := by
          change (if z = z then (match (ctxOf l).ref z with
            | some (.VTypeDia X) => some X | _ => none) else none) = some T at hv
          rw [if_pos rfl, hz] at hv
          exact Option.some.inj hv
        exact SubE.sim_ren_eta' _ rfl hZ
      · have hb := diaIn_boxIn_of_ne hv hvz
        have hm := mem_boxItems hb
        have hany : (boxItems l).any (·.1 == v) = true :=
          List.any_eq_true.mpr ⟨_, hm, by simp⟩
        have hlt := findIdx_lt_boxItems hm
        rw [pullS_item hvz hany]
        change SubE.Sim T (.ren _) ((Subst.atShift (E.dia (.step x .keep) z)).at _)
        have hq : PPath (.snd :: itemPath ((boxItems l).findIdx (·.1 == v))) :=
          fun s hs => (List.mem_cons.mp hs).elim (fun e => e ▸ rfl) (itemPath_ppath _ s)
        rw [Subst.at_atShift,
          show x.ext (.dia :: .snd :: itemPath ((boxItems l).findIdx (·.1 == v))) =
            (VarSymb.step x .dia).ext (.snd :: itemPath ((boxItems l).findIdx (·.1 == v)))
            from rfl,
          shift_ext_ppath _ hq, show (VarSymb.step x .dia).shift 0 =
            VarSymb.step (.step x .keep) .dia from rfl,
          Subst.at_ext_ppath _ _ _ hq, at_keep_dia_viewTuple hF hle hz E hent]
        change SubE.Sim T (.ren v) ((SubE.tm (itemsTm (σ := σ) (boxItems l) _).2).projs
          (itemPath _))
        rw [projs_itemsTm _ _ _ hlt]
        refine SubE.sim_ren_eta' _ (getElem_findIdx_boxItems hm) ?_
        have e := boxItems_spec hF l _ (List.getElem_mem hlt)
        rw [getElem_findIdx_boxItems hm, hb] at e
        exact (Option.some.inj e).symm
    exact (Term.subst_shift C _ p q _ okA cohA (Subst.preShift_atShift _ _) _).trans
      ((Term.subst_comp_sig (pullS l z x) _ (Subst.idS σ (Δ.diaIn z)) (ok_pullS hF hz hx)
        (coh_pullS hF hz hx) okA cohA (Subst.ok_idS_le (hle.diaIn z))
        (Subst.coh_idS_le (hle.diaIn z)) hsim u).trans
        (Term.subst_idS_mono (hle.diaIn z) _ _ u))
  exact key _ hwz _ _ _

/-! ## Keeping a pulled-back `□` view along a `□` view tuple's edge -/

/-- Every declared address of a world language's `□` view has one level step. -/
theorem levels_boxIn_ctxOf {l : List VarType} :
    ∀ v T, v.lastProj = false → (ctxOf l).boxIn v = some T → Step.levels v.path = 1 := by
  intro v T _ hv
  have one : ∀ (u : VarSymb) (s : Step), PPath u.path → s.isProj = false →
      Step.levels (VarSymb.step u s).path = 1 := fun u s hu hs => by
    change Step.levels (u.path ++ [s]) = 1
    rw [Step.levels_append, levels_ppath hu]
    simp [Step.levels, hs]
  match v, hv with
  | .step u .keep, hv => exact one u .keep (reach_ppath (Ctx.boxIn_keep hv).2.1).1 rfl
  | .step u .box, hv => exact one u .box (reach_ppath (Ctx.boxIn_box hv).2).1 rfl
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .dia, hv => cases hv
  | .step _ .here, hv => cases hv

/-- The edge's entry at the shifted contents of a root lifted to the `□` view tuple: the tuple. -/
theorem at_inner_boxTuple (hF : ModalSys.Four = true) {l : List VarType} {Δ : Ctx}
    (hle : (ctxOf l).Le Δ) {r : VarSymb} (E : Subst σ Δ)
    (hent : E.at (.step r .keep) = .tm (Term.mono hle (GArrow.boxTuple (σ := σ) hF l).2.2.2)) :
    E.box.at (r.inner.shift 0) =
      .tm (itemsTm (σ := σ) (boxItems l) fun e he => hle.boxIn.ref (boxItems_ref hF l e he)).2 := by
  cases hk : ModalSys.keepOnly with
  | true =>
      obtain ⟨hT, -⟩ := ModalSys.keepOnly_flags hk
      rw [VarSymb.inner_keepOnly hk]
      change E.box.at (.step (.step (.step r .keep) .keep) .here) = _
      rw [Subst.at_proj _ _ rfl, Subst.at_nonproj _ rfl]
      change (E.at (.step r .keep)).keepE.proj .here = _
      rw [hent]
      change (SubE.tm (Term.boxtm (Term.mono hle.boxIn _))).keepE.proj .here = _
      rw [SubE.keepE_tm _ hF, SubE.proj_boxtm_here _ hT]
      refine SubE.tm_of_sig ?_
      refine (Term.collapse_shift_same (Ctx.shifts_boxIn_boxIn hF Δ)
        (Ctx.collapses_boxIn_self hT Δ.boxIn) (Ctx.Le.refl _)
        (Ctx.shiftCollapseId_keepOnly hk Δ) _).trans ?_
      rw [Term.mono_refl]
      exact mono_itemsTm _ _ _ _
  | false =>
      rw [VarSymb.inner_box hk, Subst.at_nonproj _ rfl]
      change (E.at (.step r .keep)).unbox = _
      rw [hent]
      exact SubE.tm_of_sig (mono_itemsTm _ _ _ _)

/-- ⭐**Keeping a pulled-back `□`-view term along a `□` view tuple's edge gives it back.** -/
theorem subst_shift_pullBox (hF : ModalSys.Four = true) {l l' : List VarType} {Δ : Ctx}
    (hle : (ctxOf l).Le Δ) {r : VarSymb}
    (hr : (ctxOf l').ref r = some (.VTypeBox (itemsTy (boxItems l))))
    {ι : VarSymb → VarSymb} (E : Subst σ Δ) (hE : Subst.Ok (ctxOf l').boxIn E)
    (hcE : Subst.Coh ι (ctxOf l').boxIn E)
    (hent : E.at (.step r .keep) = .tm (Term.mono hle (GArrow.boxTuple (σ := σ) hF l).2.2.2))
    {A : VarType} {a : Ann A} (b : Term σ (ctxOf l).boxIn A a) :
    (⟨_, Term.subst ι E.box (Subst.ok_box hE) (Subst.coh_box hE hcE)
        (Term.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf l'))
          (Term.subst (pullBoxIdx l r) (pullBoxS l r) (ok_pullBoxS hF hr) (coh_pullBoxS hF hr)
            b))⟩ : Σ c, Term σ Δ.boxIn A c) =
      ⟨_, Term.mono hle.boxIn b⟩ := by
  have C := Ctx.shifts_boxIn_boxIn hF (ctxOf l')
  have okA := Subst.ok_atShift C (Subst.ok_box hE)
  have cohA := Subst.coh_atShift C (Subst.ok_box hE) (Subst.coh_box hE hcE) levels_boxIn_ctxOf
  have hsim : Subst.Sim (ctxOf l).boxIn (Subst.idS σ Δ.boxIn)
      ((pullBoxS l r).comp (Subst.atShift E.box) okA cohA) := by
    refine Subst.sim_of fun v T _ hb => ?_
    change SubE.Sim T (.ren v) ((pullBoxS l r v).comp _ okA cohA)
    have hm := mem_boxItems hb
    have hany : (boxItems l).any (·.1 == v) = true := List.any_eq_true.mpr ⟨_, hm, by simp⟩
    have hlt := findIdx_lt_boxItems hm
    rw [pullBoxS_item hany]
    change SubE.Sim T (.ren _) ((Subst.atShift E.box).at _)
    rw [Subst.at_atShift, shift_ext_ppath _ (itemPath_ppath _), Subst.at_ext_ppath _ _ _
      (itemPath_ppath _), at_inner_boxTuple hF hle E hent, projs_itemsTm _ _ _ hlt]
    refine SubE.sim_ren_eta' _ (getElem_findIdx_boxItems hm) ?_
    have e := boxItems_spec hF l _ (List.getElem_mem hlt)
    rw [getElem_findIdx_boxItems hm, hb] at e
    exact (Option.some.inj e).symm
  exact (Term.subst_shift C _ _ _ _ okA cohA (Subst.preShift_atShift _ _) _).trans
    ((Term.subst_comp_sig (pullBoxS l r) _ (Subst.idS σ Δ.boxIn) (ok_pullBoxS hF hr)
      (coh_pullBoxS hF hr) okA cohA (Subst.ok_idS_le hle.boxIn)
      (Subst.coh_idS_le hle.boxIn) hsim b).trans
      (Term.subst_idS_mono hle.boxIn _ _ b))

/-! ## Keeping a pulled-back view along the edges of a lifted address and the `□` view tuple -/

/-- Inside the kept view of a lifted possible root, the edge's entry at the shifted contents of
    the root lifted to the `□` view tuple: the tuple. -/
theorem at_inner_boxTuple_dia (hF : ModalSys.Four = true) {l : List VarType} {Δ : Ctx}
    (hle : (ctxOf l).Le Δ) {r : VarSymb} (E : Subst σ Δ) (x z : VarSymb)
    (hent : E.at (.step r .keep) = .tm (Term.mono hle (GArrow.boxTuple (σ := σ) hF l).2.2.2)) :
    (E.dia (.step x .keep) z).at (r.inner.shift 0) =
      .tm (itemsTm (σ := σ) (boxItems l) fun e he =>
        ((hle.boxIn).trans (Ctx.le_boxIn_diaIn Δ z)).ref (boxItems_ref hF l e he)).2 := by
  cases hk : ModalSys.keepOnly with
  | true =>
      obtain ⟨hT, -⟩ := ModalSys.keepOnly_flags hk
      rw [VarSymb.inner_keepOnly hk]
      change (E.dia (.step x .keep) z).at (.step (.step (.step r .keep) .keep) .here) = _
      rw [Subst.at_proj _ _ rfl, Subst.at_nonproj _ rfl]
      change ((E.at (.step r .keep)).keepE.mono (Ctx.le_boxIn_diaIn Δ z)).proj .here = _
      rw [hent]
      change ((SubE.tm (Term.boxtm (Term.mono hle.boxIn _))).keepE.mono
        (Ctx.le_boxIn_diaIn Δ z)).proj .here = _
      rw [SubE.keepE_tm _ hF]
      change (SubE.tm (Term.boxtm (Term.mono (Ctx.le_boxIn_diaIn Δ z).boxIn
        (Term.shift (Ctx.shifts_boxIn_boxIn hF Δ) _)))).proj .here = _
      rw [SubE.proj_boxtm_here _ hT,
        Term.collapse_mono (Ctx.collapses_boxIn_self hT Δ.boxIn)
          (Ctx.collapses_boxIn_self hT (Δ.diaIn z)) _ (Ctx.le_boxIn_diaIn Δ z)]
      refine SubE.tm_of_sig ?_
      have e := Term.collapse_shift_same (Ctx.shifts_boxIn_boxIn hF Δ)
        (Ctx.collapses_boxIn_self hT Δ.boxIn) (Ctx.Le.refl _)
        (Ctx.shiftCollapseId_keepOnly hk Δ)
        (Term.mono hle.boxIn (itemsTm (σ := σ) (boxItems l) (boxItems_ref hF l)).2)
      rw [Term.mono_refl] at e
      refine (congrArg (fun p : Σ b, Term σ Δ.boxIn (itemsTy (boxItems l)) b =>
        (⟨_, Term.mono (Ctx.le_boxIn_diaIn Δ z) p.2⟩ :
          Σ b, Term σ (Δ.diaIn z) (itemsTy (boxItems l)) b)) e).trans ?_
      rw [Term.mono_mono]
      exact mono_itemsTm _ _ _ _
  | false =>
      rw [VarSymb.inner_box hk]
      change (E.dia (.step x .keep) z).at (.step (.step r .keep) .box) = _
      rw [Subst.at_nonproj _ rfl]
      change ((E.at (.step r .keep)).unbox.mono (Ctx.le_boxIn_diaIn Δ z)) = _
      rw [hent]
      change SubE.tm (Term.mono (Ctx.le_boxIn_diaIn Δ z) (Term.mono hle.boxIn _)) = _
      rw [Term.mono_mono]
      exact SubE.tm_of_sig (mono_itemsTm _ _ _ _)

/-- ⭐**Keeping a pulled-back view term along the lift edges gives it back** (D-H3): with `x`
    lifted to `η(z)` and `r` to the `□` view tuple, the kept view's substitution sends `x.dia`
    (shifted, `x.keep.dia`) to `η(z.dia)` and each component of `r`'s contents to the item's
    η-expansion, so the composite with the pull-back is the identity up to η. -/
theorem subst_shift_pullD (hF : ModalSys.Four = true) {l l' : List VarType} {Δ : Ctx}
    (hle : (ctxOf l).Le Δ) {z x r : VarSymb} {Z : VarType}
    (hz : (ctxOf l).ref z = some (.VTypeDia Z)) (hx : (ctxOf l').ref x = some (.VTypeDia Z))
    (hr : (ctxOf l').ref r = some (.VTypeBox (itemsTy (boxItems l))))
    {ι : VarSymb → VarSymb} (E : Subst σ Δ) (hE : Subst.Ok (ctxOf l').boxIn E)
    (hcE : Subst.Coh ι (ctxOf l').boxIn E)
    (hentx : E.at (.step x .keep) = .tm (Term.mono hle (GArrow.etaTerm (σ := σ) l z Z hz).2.2.2))
    (hentr : E.at (.step r .keep) =
      .tm (Term.mono hle (GArrow.boxTuple (σ := σ) hF l).2.2.2))
    {A : VarType} {a : Ann A} (u : Term σ ((ctxOf l).diaIn z) A a) :
    (⟨_, Term.subst ι E hE hcE (Term.diatm (.step x .keep) (Ctx.exists_keep_dia hF ⟨_, hx⟩)
        (Term.shift (Ctx.shifts_diaIn_keep hF (ctxOf l') x)
          (Term.subst (pullDIdx l z x r) (pullD l z x r) (ok_pullD hF hz hx hr)
            (coh_pullD hF hz hx hr) u)))⟩ : Σ b, Term σ Δ (.VTypeDia A) b) =
      ⟨_, Term.mono hle (Term.diatm z ⟨Z, hz⟩ u)⟩ := by
  have hxk : (ctxOf l').boxIn.ref (.step x .keep) = some (.VTypeDia Z) :=
    Ctx.ref_keep_of' hF hx VarType.keepable_dia
  have hwz : ι (.step x .keep) = z := by
    have := hcE _ _ hxk []
    rw [hentx] at this
    exact this.symm
  have C := Ctx.shifts_diaIn_keep hF (ctxOf l') x
  have hlv := levels_diaIn_ctxOf hx
  have key : ∀ (y : VarSymb) (_hy : y = z) (P : ∃ Y, Δ.ref y = some (.VTypeDia Y))
      (p : Subst.Ok ((ctxOf l').boxIn.diaIn (.step x .keep)) (E.dia (.step x .keep) y))
      (q : Subst.Coh ι ((ctxOf l').boxIn.diaIn (.step x .keep)) (E.dia (.step x .keep) y)),
      (⟨_, Term.diatm y P (Term.subst ι (E.dia (.step x .keep) y) p q
          (Term.shift (Ctx.shifts_diaIn_keep hF (ctxOf l') x)
            (Term.subst (pullDIdx l z x r) (pullD l z x r) (ok_pullD hF hz hx hr)
              (coh_pullD hF hz hx hr) u)))⟩ : Σ b, Term σ Δ (.VTypeDia A) b) =
        ⟨_, Term.mono hle (Term.diatm z ⟨Z, hz⟩ u)⟩ := by
    intro y hy P p q
    cases hy
    refine sig_diatm ?_
    have okA := Subst.ok_atShift C p
    have cohA := Subst.coh_atShift C p q hlv
    have hsim : Subst.Sim ((ctxOf l).diaIn z) (Subst.idS σ (Δ.diaIn z))
        ((pullD l z x r).comp (Subst.atShift (E.dia (.step x .keep) z)) okA cohA) := by
      refine Subst.sim_of fun v T _ hv => ?_
      change SubE.Sim T (.ren v) ((pullD l z x r v).comp _ okA cohA)
      by_cases hvz : v = .step z .dia
      · subst hvz
        rw [pullD_dia]
        change SubE.Sim T (.ren _) ((Subst.atShift (E.dia (.step x .keep) z)).at _)
        rw [Subst.at_atShift,
          show (VarSymb.step x .dia).shift 0 = VarSymb.step (.step x .keep) .dia from rfl,
          Subst.at_nonproj _ rfl]
        change SubE.Sim T (.ren _) (if VarSymb.step x .keep = VarSymb.step x .keep then
          (E.at (.step x .keep)).diaBody z else .hide)
        rw [if_pos rfl, hentx]
        change SubE.Sim T (.ren _) ((SubE.tm (Term.diatm z _
          (Term.mono (hle.diaIn z) (Term.eta (.step z .dia) Z (Ctx.ref_diaIn_of hz))))).diaBody z)
        rw [SubE.diaBody_diatm, Term.mono_eta]
        have hZ : Z = T := by
          change (if z = z then (match (ctxOf l).ref z with
            | some (.VTypeDia X) => some X | _ => none) else none) = some T at hv
          rw [if_pos rfl, hz] at hv
          exact Option.some.inj hv
        exact SubE.sim_ren_eta' _ rfl hZ
      · have hb := diaIn_boxIn_of_ne hv hvz
        have hm := mem_boxItems hb
        have hany : (boxItems l).any (·.1 == v) = true :=
          List.any_eq_true.mpr ⟨_, hm, by simp⟩
        have hlt := findIdx_lt_boxItems hm
        rw [pullD_item hvz hany]
        change SubE.Sim T (.ren _) ((Subst.atShift (E.dia (.step x .keep) z)).at _)
        rw [Subst.at_atShift, shift_ext_ppath _ (itemPath_ppath _),
          Subst.at_ext_ppath _ _ _ (itemPath_ppath _),
          at_inner_boxTuple_dia hF hle E x z hentr, projs_itemsTm _ _ _ hlt]
        refine SubE.sim_ren_eta' _ (getElem_findIdx_boxItems hm) ?_
        have e := boxItems_spec hF l _ (List.getElem_mem hlt)
        rw [getElem_findIdx_boxItems hm, hb] at e
        exact (Option.some.inj e).symm
    exact (Term.subst_shift C _ p q _ okA cohA (Subst.preShift_atShift _ _) _).trans
      ((Term.subst_comp_sig (pullD l z x r) _ (Subst.idS σ (Δ.diaIn z)) (ok_pullD hF hz hx hr)
        (coh_pullD hF hz hx hr) okA cohA (Subst.ok_idS_le (hle.diaIn z))
        (Subst.coh_idS_le (hle.diaIn z)) hsim u).trans
        (Term.subst_idS_mono (hle.diaIn z) _ _ u))
  exact key _ hwz _ _ _

end V12M
