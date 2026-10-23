import QML.QML_v12m_GItems
import QML.QML_v12m_BAbs

/-!
# QML v12m — the growing tree: abstracting a variable's items under 4

`BArrow`'s abstraction (`QML_v12m_BAbs.lean`) made for 4, over item maps.  Realising a new
variable `c : A` of the source along an arrow needs two identities between formulas of the
source's `□` view (with `c` the newest variable, `l.length`):

* ⭐`instantiate_gtup_gabs`: a formula `ψ` is its **abstraction** (`gabs`: `c`'s items go to the
  components of the slot `bnd 0 : A.gc`, where `gPath` says, every other item stays) instantiated
  at the **tuple** of `c`'s items (`gtup`).  So `□ψ` gives `□∃y. ψ̃(y)`, a formula about the older
  variables only.
* ⭐`subst_gext_gabs`: an arrow's item map `f` extended by the fresh realisation `c ↦ z`
  (`gextF`) sends `ψ` to the abstraction sent by `f` and opened at `z` — the Henkin instance the
  target realises.

Both the abstraction and the extension are item maps, so their substitutions are well formed and
coherent by `GArrow.coh_itemS`.  The extension takes any item map `f`, so it serves the growing
tree's arrows, whose lifted roots go to existing addresses.

Everything is stated for an edge's view `Ctx.kView k`: the `□` view (`k = none`), or the `◇_x`
view of a child made for `◇_x` (`k = some x`, `x` older than `c`: `KOld`).  An item map already
sends `x.dia` where the edge says, and the abstraction leaves it alone, so one proof serves both
kinds of edge (B needs a second copy, `QML_v12m_BDia.lean`).  The tuple is a term of the `□` view,
weakened into the edge's view (`at_gPath_gtupB`).
-/

namespace V12M

variable [ModalSys]

namespace Ctx

/-- The view's entry at a level step depends only on the address before it. -/
theorem boxIn_step_congr {Γ Γ' : Ctx} {u : VarSymb} (h : Γ.ref u = Γ'.ref u) (s : Step) :
    Γ.boxIn (.step u s) = Γ'.boxIn (.step u s) := by
  cases s <;> simp only [Ctx.boxIn, h]

theorem diaIn_step_congr {Γ Γ' : Ctx} {u : VarSymb} (h : Γ.ref u = Γ'.ref u) (x : VarSymb)
    (s : Step) : Γ.diaIn x (.step u s) = Γ'.diaIn x (.step u s) := by
  cases s with
  | dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = (if u = x then (match Γ'.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none)
      by_cases hux : u = x
      · subst hux
        rw [if_pos rfl, if_pos rfl, h]
      · rw [if_neg hux, if_neg hux]
  | box => exact boxIn_step_congr h .box
  | keep => exact boxIn_step_congr h .keep
  | fst => exact boxIn_step_congr h .fst
  | snd => exact boxIn_step_congr h .snd
  | here => exact boxIn_step_congr h .here

/-- ⭐The view an edge translates: the `□` view, or for a child made for `◇_x` the `◇_x` view
    (B's edge kinds). -/
def kView (Γ : Ctx) : Option VarSymb → Ctx
  | none => Γ.boxIn
  | some x => Γ.diaIn x

instance {Γ : Ctx} [Γ.NoSlots] {k : Option VarSymb} : (Γ.kView k).NoSlots := by
  cases k <;> (unfold kView; infer_instance)

theorem le_boxIn_kView (Γ : Ctx) : ∀ k : Option VarSymb, Γ.boxIn.Le (Γ.kView k)
  | none => Le.refl _
  | some x => le_boxIn_diaIn Γ x

theorem Le.kView {Γ Γ' : Ctx} (h : Γ.Le Γ') : ∀ k : Option VarSymb, (Γ.kView k).Le (Γ'.kView k)
  | none => h.boxIn
  | some x => h.diaIn x

theorem kView_step_congr {Γ Γ' : Ctx} {u : VarSymb} (h : Γ.ref u = Γ'.ref u) :
    ∀ (k : Option VarSymb) (s : Step), Γ.kView k (.step u s) = Γ'.kView k (.step u s)
  | none, s => boxIn_step_congr h s
  | some x, s => diaIn_step_congr h x s

end Ctx

namespace GArrow

open BArrow

variable {σ : Signature}

/-! ## Item images -/

/-- Item images are projection paths. -/
theorem ppath_gPath : ∀ (R : VarType) (q : List Step) (s : Step), PPath (gPath R q s)
  | .VTypeProd A _, .fst :: q, s => fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · exact ppath_gPath A q s t ht
  | .VTypeProd _ B, .snd :: q, s => fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · exact ppath_gPath B q s t ht
  | .VTypeBox A, .here :: q, s => fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · exact ppath_gPath A q s t ht
  | .VTypeBox _, [], .box => fun t ht => by rw [List.mem_singleton.mp ht]; rfl
  | .VTypeBox _, [], .keep => fun t ht => by
      change t ∈ cond ModalSys.keepOnly [.fst] [.snd] at ht
      revert ht
      cases ModalSys.keepOnly <;> intro ht <;> (rw [List.mem_singleton.mp ht]; rfl)
  | .VTypeBox _, [], .fst | .VTypeBox _, [], .snd | .VTypeBox _, [], .dia
  | .VTypeBox _, [], .here => fun _ ht => by cases ht
  | .VTypeProd _ _, [], _ | .VTypeProd _ _, .box :: _, _ | .VTypeProd _ _, .dia :: _, _
  | .VTypeProd _ _, .keep :: _, _ | .VTypeProd _ _, .here :: _, _ => fun _ ht => by cases ht
  | .VTypeBox _, .fst :: _, _ | .VTypeBox _, .snd :: _, _ | .VTypeBox _, .box :: _, _
  | .VTypeBox _, .dia :: _, _ | .VTypeBox _, .keep :: _, _ => fun _ ht => by cases ht
  | .VTypeDia _, _, _ | .Var, _, _ | .VTypeOne, _, _ => fun _ ht => by cases ht

/-! ## The tuple of a variable's items -/

/-- The annotation of `gtupB`. -/
def gtupAnnB : VarSymb → (R : VarType) → (b : Bool) → Ann (R.gcB b)
  | _, .Var, _ => .one
  | _, .VTypeOne, _ => .one
  | u, .VTypeProd A B, b => .prod (gtupAnnB (.step u .fst) A b) (gtupAnnB (.step u .snd) B b)
  | u, .VTypeBox A, true =>
      .prod (Ann.eta (.step u .keep) (.VTypeBox A)) (gtupAnnB (.step u .here) A true)
  | u, .VTypeBox A, false =>
      .prod (Ann.eta (.step u .box) A) (Ann.eta (.step u .keep) (.VTypeBox A))
  | u, .VTypeDia A, _ => Ann.eta (.step u .keep) (.VTypeDia A)

/-- The items of `u : R` under 4 as one term of the `□` view, for a value `b` of
    `ModalSys.keepOnly`: a `□A` component contributes its contents and its kept object (under
    T + 4 the kept object and the items of its value here), a `◇A` component its kept object. -/
def gtupB (hF : ModalSys.Four = true) {Γ : Ctx} : (u : VarSymb) → (R : VarType) → (b : Bool) →
    ModalSys.keepOnly = b → Γ.ref u = some R → Term σ Γ.boxIn (R.gcB b) (gtupAnnB u R b)
  | _, .Var, _, _, _ => .unit
  | _, .VTypeOne, _, _, _ => .unit
  | u, .VTypeProd A B, b, hb, h =>
      .pair (gtupB hF (.step u .fst) A b hb (Ctx.ref_fst_of h))
        (gtupB hF (.step u .snd) B b hb (Ctx.ref_snd_of h))
  | u, .VTypeBox A, true, hb, h =>
      .pair (Term.eta (.step u .keep) (.VTypeBox A) (Ctx.ref_keep_of' hF h rfl))
        (gtupB hF (.step u .here) A true hb (Ctx.ref_here_of (ModalSys.keepOnly_flags hb).1 h))
  | u, .VTypeBox A, false, hb, h =>
      .pair (Term.eta (.step u .box) A (Ctx.ref_boxIn_of hb h))
        (Term.eta (.step u .keep) (.VTypeBox A) (Ctx.ref_keep_of' hF h rfl))
  | u, .VTypeDia A, _, _, h => Term.eta (.step u .keep) (.VTypeDia A) (Ctx.ref_keep_of' hF h rfl)

/-- ⭐The items of `u : R` under 4, as one term of the `□` view of type `R.gc`. -/
abbrev gtup (hF : ModalSys.Four = true) {Γ : Ctx} (u : VarSymb) (R : VarType)
    (h : Γ.ref u = some R) : Term σ Γ.boxIn R.gc (gtupAnnB u R ModalSys.keepOnly) :=
  gtupB hF u R ModalSys.keepOnly rfl h

/-- ⭐An entry holding the tuple of `u : U` (weakened into a larger context), read where `gPath`
    sends the item `v.s` of `v = u.q`, is the item itself. -/
theorem at_gPath_gtupB (hF : ModalSys.Four = true) {Γ Δ : Ctx} (hle : Γ.boxIn.Le Δ)
    (θ : Subst σ Δ) (b : Bool) (hb : ModalSys.keepOnly = b) {s : Step} (hs : s.isProj = false)
    {T : VarType} :
    ∀ (U : VarType) (q : List Step) {U' : VarType} (u w : VarSymb) (hu : Γ.ref u = some U),
      PPath q → U.walk q = some U' → θ.at w = .tm (Term.mono hle (gtupB hF u U b hb hu)) →
      ∀ (v : VarSymb), v = u.ext q → ∀ (hit : Γ.boxIn.ref (.step v s) = some T),
        θ.at (w.ext (gPath U q s)) = .tm (Term.mono hle (Term.eta (.step v s) T hit))
  | U, [], U', u, w, hu, _, _, hw, v, hv, hit => by
      subst v
      change Γ.boxIn.ref (.step u s) = some T at hit
      rw [Ctx.ref_nonproj _ (show (VarSymb.step u s).lastProj = false from hs)] at hit
      cases s with
      | box =>
          obtain ⟨hk, hu'⟩ := Ctx.boxIn_box hit
          rw [hu] at hu'
          cases hu'
          obtain rfl : b = false := hb.symm.trans hk
          change θ.at (.step w .fst) = _
          rw [Subst.at_proj _ _ rfl, hw]
          rfl
      | keep =>
          obtain ⟨-, hu', hk⟩ := Ctx.boxIn_keep hit
          rw [hu] at hu'
          cases hu'
          cases T with
          | VTypeBox A =>
              cases b with
              | false =>
                  change θ.at (w.ext (cond ModalSys.keepOnly [.fst] [.snd])) = _
                  rw [hb]
                  change θ.at (.step w .snd) = _
                  rw [Subst.at_proj _ _ rfl, hw]
                  rfl
              | true =>
                  change θ.at (w.ext (cond ModalSys.keepOnly [.fst] [.snd])) = _
                  rw [hb]
                  change θ.at (.step w .fst) = _
                  rw [Subst.at_proj _ _ rfl, hw]
                  rfl
          | VTypeDia A =>
              cases b <;> exact hw
          | _ => cases hk
      | dia => cases hit
      | _ => cases hs
  | U, t :: q, U', u, w, hu, hp, hq, hw, v, hv, hit => by
      have hq' : PPath q := fun s' hs' => hp s' (by simp [hs'])
      cases t with
      | fst =>
          cases U with
          | VTypeProd X Y =>
              have hw' : θ.at (.step w .fst) = .tm (Term.mono hle (gtupB hF (.step u .fst) X b hb
                  (Ctx.ref_fst_of hu))) := by
                rw [Subst.at_proj _ _ rfl, hw]
                rfl
              exact at_gPath_gtupB hF hle θ b hb hs X q _ _ _ hq' hq hw' v hv hit
          | _ => cases hq
      | snd =>
          cases U with
          | VTypeProd X Y =>
              have hw' : θ.at (.step w .snd) = .tm (Term.mono hle (gtupB hF (.step u .snd) Y b hb
                  (Ctx.ref_snd_of hu))) := by
                rw [Subst.at_proj _ _ rfl, hw]
                rfl
              exact at_gPath_gtupB hF hle θ b hb hs Y q _ _ _ hq' hq hw' v hv hit
          | _ => cases hq
      | here =>
          cases U with
          | VTypeBox X =>
              have hT : ModalSys.T = true := by
                cases hT : ModalSys.T
                · simp [VarType.walk, VarType.step, hT] at hq
                · rfl
              have hk : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
              obtain rfl : b = true := hb.symm.trans hk
              have hq'' : X.walk q = some U' := by
                simpa [VarType.walk, VarType.step, hT] using hq
              have hw' : θ.at (.step w .snd) = .tm (Term.mono hle (gtupB hF (.step u .here) X
                  true hb (Ctx.ref_here_of hT hu))) := by
                rw [Subst.at_proj _ _ rfl, hw]
                rfl
              exact at_gPath_gtupB hF hle θ true hb hs X q _ _ _ hq' hq'' hw' v hv hit
          | _ => cases hq
      | box => exact absurd (hp .box (by simp)) (by decide)
      | dia => exact absurd (hp .dia (by simp)) (by decide)
      | keep => exact absurd (hp .keep (by simp)) (by decide)

/-! ## The views of an edge -/

/-- An item of a view is a reachable address followed by a level step. -/
theorem kView_item {l : List VarType} {k : Option VarSymb} {v : VarSymb} {T : VarType}
    (h : (ctxOf l).kView k v = some T) :
    ∃ u s, v = .step u s ∧ PPath u.path ∧ ∃ U, (ctxOf l).ref u = some U := by
  cases k with
  | none => exact boxIn_item h
  | some x => exact diaIn_item h

theorem ok_itemS_kView {l : List VarType} {k : Option VarSymb} {Δ : Ctx}
    {f : VarSymb → VarSymb} (hf : ItemOk ((ctxOf l).kView k) Δ f) :
    Subst.Ok ((ctxOf l).kView k) (itemS σ Δ f) :=
  ok_itemS hf fun _ _ _ hT => by
    obtain ⟨u, s, e, -, -⟩ := kView_item hT
    exact ⟨u, s, e⟩

theorem coh_itemS_kView {l : List VarType} {k : Option VarSymb} {Δ : Ctx}
    {f : VarSymb → VarSymb} (hf : ItemOk ((ctxOf l).kView k) Δ f) :
    Subst.Coh (itemIdx f) ((ctxOf l).kView k) (itemS σ Δ f) :=
  coh_itemS hf fun _ _ _ hT => by
    obtain ⟨u, s, e, hu, _⟩ := kView_item hT
    exact ⟨u, s, e, hu⟩

/-- The witness of an edge's view, if any, is not the variable `c`. -/
def KOld (k : Option VarSymb) (c : ℕ) : Prop := ∀ x, k = some x → x.rt ≠ .free c

omit [ModalSys] in
theorem kOld_none (c : ℕ) : KOld none c := fun _ h => by cases h

/-- A declared witness is older than the next variable. -/
theorem kOld_some {l : List VarType} {x : VarSymb} {X : VarType}
    (hx : (ctxOf l).ref x = some X) : KOld (some x) l.length := by
  intro x' e
  cases e
  obtain ⟨r, hr, hlt, -⟩ := ref_rt hx
  rw [hr]
  exact fun h => by cases h; omega

/-- An item of the new variable in an edge's view is an item of its `□` view. -/
theorem kView_boxIn {L : List VarType} {k : Option VarSymb} {c : ℕ} (hk : KOld k c)
    {u : VarSymb} (hrt : u.rt = .free c) {s : Step} {T : VarType}
    (h : (ctxOf L).kView k (.step u s) = some T) : (ctxOf L).boxIn (.step u s) = some T := by
  cases k with
  | none => exact h
  | some x =>
      cases s with
      | dia =>
          change (if u = x then _ else none) = some T at h
          rw [if_neg (fun e => hk x rfl (by rw [← e]; exact hrt))] at h
          cases h
      | box => exact h
      | keep => exact h
      | fst => exact h
      | snd => exact h
      | here => exact h

/-- An item of an older variable is in the older view. -/
theorem kView_old {A : VarType} {l : List VarType} {u : VarSymb} (h : u.rt ≠ .free l.length)
    (k : Option VarSymb) (s : Step) :
    (ctxOf (A :: l)).kView k (.step u s) = (ctxOf l).kView k (.step u s) :=
  Ctx.kView_step_congr (ctxOf_ref_old h) k s

/-! ## Abstraction -/

/-- The item map of abstracting the variable `c : A`: its items go where `gPath` sends them in
    the slot `bnd 0`, the others (`x.dia` included) stay. -/
def gabsF (A : VarType) (c : ℕ) (v : VarSymb) : VarSymb :=
  match v with
  | .step u s => if u.rt = .free c then (VarSymb.root (.bnd 0)).ext (gPath A u.path s) else v
  | .root _ => v

theorem gabsF_new {A : VarType} {c : ℕ} {u : VarSymb} (h : u.rt = .free c) (s : Step) :
    gabsF A c (.step u s) = (VarSymb.root (.bnd 0)).ext (gPath A u.path s) :=
  if_pos h

theorem gabsF_old {A : VarType} {c : ℕ} {u : VarSymb} (h : ¬ u.rt = .free c) (s : Step) :
    gabsF A c (.step u s) = .step u s :=
  if_neg h

/-- The context of the abstracted formula: the older variables' view and the slot. -/
abbrev gabsCtx (k : Option VarSymb) (A : VarType) (l : List VarType) : Ctx :=
  ((ctxOf l).kView k).insert (.bnd 0) A.gc

theorem gabsCtx_slots (k : Option VarSymb) (A : VarType) (l : List VarType) :
    (gabsCtx k A l).SlotsFrom 1 :=
  (Ctx.NoSlots.slots (Γ := (ctxOf l).kView k)).insert A.gc

theorem itemOk_gabsF (hF : ModalSys.Four = true) {k : Option VarSymb} (A : VarType)
    (l : List VarType) (hk : KOld k l.length) :
    ItemOk ((ctxOf (A :: l)).kView k) (gabsCtx k A l) (gabsF A l.length) := by
  intro v T hl hv
  obtain ⟨u, s, rfl, -, U, hU⟩ := kView_item hv
  by_cases hrt : u.rt = .free l.length
  · rw [gabsF_new hrt]
    have h := ref_gItem hF (kView_boxIn hk hrt hv) hrt (Δ := gabsCtx k A l) (z := .bnd 0)
      (by rw [rootTy_new]; exact Ctx.ref_insert_root _ _ _)
    rwa [rootTy_new] at h
  · obtain ⟨r, hr⟩ := (reach_ppath hU).2
    rw [gabsF_old hrt, Ctx.ref_insert_ne _ (fun h => by
      change u.rt = _ at h
      rw [hr] at h
      cases h), Ctx.ref_nonproj _ hl]
    rw [kView_old hrt] at hv
    exact hv

/-- Weakening the abstracted context into the new variable's context. -/
theorem gabsCtx_le (k : Option VarSymb) (A : VarType) (l : List VarType) :
    (gabsCtx k A l).Le (((ctxOf (A :: l)).kView k).insert (.bnd 0) A.gc) :=
  ((ctxOf_le_append [A] l).kView k).insert (.bnd 0) A.gc

/-- ⭐The abstraction of a formula of the new variable's view (`□`, or `◇_x` for an older `x`),
    under 4. -/
def gabs (hF : ModalSys.Four = true) (k : Option VarSymb) (A : VarType) (l : List VarType)
    (hk : KOld k l.length) (ψ : WFF σ ((ctxOf (A :: l)).kView k) 0) : WFF σ (gabsCtx k A l) 1 :=
  WFF.subst (itemIdx (gabsF A l.length)) (itemS σ (gabsCtx k A l) (gabsF A l.length))
    (ok_itemS_kView (itemOk_gabsF hF A l hk)) (coh_itemS_kView (itemOk_gabsF hF A l hk))
    Ctx.NoSlots.slots (gabsCtx_slots k A l) ψ

/-! ## Instantiating the abstraction at the tuple -/

/-- ⭐A formula of the new variable's view is its abstraction instantiated at the tuple of the
    new variable's items. -/
theorem instantiate_gtup_gabs (hF : ModalSys.Four = true) (k : Option VarSymb) (A : VarType)
    (l : List VarType) (hk : KOld k l.length) (ψ : WFF σ ((ctxOf (A :: l)).kView k) 0) :
    WFF.instantiate Ctx.NoSlots.slots
      (Term.mono (Ctx.le_boxIn_kView _ k)
        (gtup hF (.root (.free l.length)) A (ctxOf_ref_new A l)))
      (WFF.mono (gabsCtx_le k A l) (gabs hF k A l hk ψ)) = ψ := by
  have hs : (((ctxOf (A :: l)).kView k).insert (.bnd 0) A.gc).SlotsFrom 1 :=
    (Ctx.NoSlots.slots (Γ := (ctxOf (A :: l)).kView k)).insert A.gc
  unfold WFF.instantiate WFF.substRoot gabs
  rw [WFF.subst_mono (gabsCtx_le k A l) _ _ _ (gabsCtx_slots k A l) hs]
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ Subst.ok_idS Subst.coh_idS _ _ _ ?_ ψ).trans
    (WFF.subst_id _ _ _ ψ)
  refine Subst.sim_of ?_
  intro v T hl hv
  obtain ⟨u, s, rfl, hup, U, hU⟩ := kView_item hv
  have hs' : s.isProj = false := hl
  change SubE.Sim T (.ren (.step u s))
    ((if s.isProj then SubE.hide else .ren (gabsF A l.length (.step u s))).comp _ _ _)
  rw [if_neg (by simp [hs'])]
  by_cases hrt : u.rt = .free l.length
  · rw [gabsF_new hrt]
    change SubE.Sim T _ ((Subst.single (.bnd 0) _).at
      ((VarSymb.root (.bnd 0)).ext (gPath A u.path s)))
    have hwalk : A.walk u.path = some U := by
      have e := Ctx.ref_ext_ppath (ctxOf (A :: l)) u.path (.root u.rt) hup
      rw [← VarSymb.eq_root_ext u, hU, hrt, ctxOf_ref_new] at e
      exact e.symm
    have hit : (ctxOf (A :: l)).boxIn.ref (.step u s) = some T := by
      rw [Ctx.ref_nonproj _ hl]
      exact kView_boxIn hk hrt hv
    rw [at_gPath_gtupB hF (Ctx.le_boxIn_kView _ k) _ ModalSys.keepOnly rfl hs' A u.path
      (.root (.free l.length)) (.root (.bnd 0)) (ctxOf_ref_new A l) hup hwalk
      (by change Subst.single (.bnd 0) _ (.root (.bnd 0)) = _; exact if_pos rfl) u
      (by rw [← hrt]; exact VarSymb.eq_root_ext u) hit, Term.mono_eta]
    exact .ren_eta _ _
  · rw [gabsF_old hrt]
    change SubE.Sim T _ ((Subst.single (.bnd 0) _).at (.step u s))
    rw [Subst.single_at_ne (by
      change u.rt ≠ _
      obtain ⟨r, hr⟩ := (reach_ppath hU).2
      rw [hr]
      exact fun h => by cases h)]
    exact .refl _

/-! ## Entries: an edge's map, with terms for lifted items -/

/-- A term over a list of variables. -/
abbrev LTerm (σ : Signature) := Σ (l : List VarType) (T : VarType) (a : Ann T), Term σ (ctxOf l) T a

/-- ⭐An **entry** of an edge's map: an address, or a term — a lifted root's kept item goes to the
    term lifted (docs §3 4, paper pass, D5 (a)). -/
abbrev LEnt (σ : Signature) := VarSymb ⊕ LTerm σ

open Classical in
/-- An entry as a substitution entry into `Δ`: a term is weakened into `Δ`, when it lies in it. -/
noncomputable def entOf (Δ : Ctx) : LEnt σ → SubE σ Δ
  | .inl w => .ren w
  | .inr ⟨l, _, _, t⟩ => if h : (ctxOf l).Le Δ then .tm (Term.mono h t) else .hide

/-- ⭐The renaming of an edge given by an entry map `g`. -/
noncomputable def eS (σ : Signature) (Δ : Ctx) (g : VarSymb → LEnt σ) : Subst σ Δ := fun v =>
  match v with
  | .step u s => if s.isProj then .hide else entOf Δ (g (.step u s))
  | .root _ => .hide

/-- Where an entry sends annotation indices below it. -/
def entIdx : LEnt σ → List Step → VarSymb
  | .inl w, k => w.ext k
  | .inr ⟨_, _, a, _⟩, k => a.idxAt k

/-- Where an entry map sends annotation indices: the item before the first level step by its
    entry, the rest kept. -/
def eIdx (g : VarSymb → LEnt σ) (a : VarSymb) : VarSymb :=
  match splitLevel a.path with
  | some (q, s, k) => entIdx (g (.step ((VarSymb.root a.rt).ext q) s)) k
  | none => a

/-- The entries are at the items' types. -/
def EntOk (Γ Δ : Ctx) (g : VarSymb → LEnt σ) : Prop :=
  ∀ v T, v.lastProj = false → Γ v = some T → (entOf Δ (g v)).OkRef T

/-- A renaming as an entry map. -/
def ofRen (f : VarSymb → VarSymb) : VarSymb → LEnt σ := fun v => .inl (f v)

theorem entOk_ofRen {Γ Δ : Ctx} {f : VarSymb → VarSymb} (hf : ItemOk Γ Δ f) :
    EntOk Γ Δ (ofRen (σ := σ) f) := hf

theorem eS_item {Δ : Ctx} (g : VarSymb → LEnt σ) {u : VarSymb} {s : Step}
    (hs : s.isProj = false) : eS σ Δ g (.step u s) = entOf Δ (g (.step u s)) := by
  change (if s.isProj then SubE.hide else _) = _
  rw [if_neg (by simp [hs])]

open Classical in
theorem idxAlong_entOf {Δ : Ctx} {e : LEnt σ} {T : VarType} (h : (entOf Δ e).OkRef T)
    (p : List Step) : (entOf Δ e).idxAlong p = entIdx e p := by
  match e, h with
  | .inl w, _ => rfl
  | .inr ⟨l, _, a, t⟩, h =>
      change (if h : (ctxOf l).Le Δ then SubE.tm (Term.mono h t) else .hide).OkRef T at h
      change (if h : (ctxOf l).Le Δ then SubE.tm (Term.mono h t) else .hide).idxAlong p = _
      split_ifs with hl
      · rfl
      · rw [dif_neg hl] at h
        exact h.elim

open Classical in
/-- An entry into a context stays one into a larger context. -/
theorem entOf_mono {Δ Δ' : Ctx} (h : Δ.Le Δ') {e : LEnt σ} {T : VarType}
    (he : (entOf Δ e).OkRef T) : (entOf Δ e).mono h = entOf Δ' e := by
  match e, he with
  | .inl w, _ => rfl
  | .inr ⟨l, _, a, t⟩, he =>
      change (if h : (ctxOf l).Le Δ then SubE.tm (Term.mono h t) else .hide).OkRef T at he
      change SubE.mono h (if h : (ctxOf l).Le Δ then SubE.tm (Term.mono h t) else .hide) =
        (if h : (ctxOf l).Le Δ' then SubE.tm (Term.mono h t) else .hide)
      by_cases hl : (ctxOf l).Le Δ
      · rw [dif_pos hl, dif_pos (hl.trans h)]
        change SubE.tm (Term.mono h (Term.mono hl t)) = _
        rw [Term.mono_mono]
      · rw [dif_neg hl] at he
        exact he.elim

theorem okRef_entOf_mono {Δ Δ' : Ctx} (h : Δ.Le Δ') {e : LEnt σ} {T : VarType}
    (he : (entOf Δ e).OkRef T) : (entOf Δ' e).OkRef T := by
  rw [← entOf_mono h he]
  match entOf Δ e, he with
  | .ren w, he => exact h.ref he
  | .tm _, he => exact he

theorem EntOk.le {Γ Δ Δ' : Ctx} {g : VarSymb → LEnt σ} (hg : EntOk Γ Δ g) (hle : Δ.Le Δ') :
    EntOk Γ Δ' g := fun v T hl hv => okRef_entOf_mono hle (hg v T hl hv)

theorem ok_eS_kView {l : List VarType} {k : Option VarSymb} {Δ : Ctx}
    {g : VarSymb → LEnt σ} (hg : EntOk ((ctxOf l).kView k) Δ g) :
    Subst.Ok ((ctxOf l).kView k) (eS σ Δ g) := by
  intro v T hl hT
  obtain ⟨u, s, rfl, -, -⟩ := kView_item hT
  rw [eS_item g hl]
  exact hg _ T hl hT

/-- The index map of an entry map at an item `u.s`, followed by `p`, for `u` a projection path. -/
theorem eIdx_item (g : VarSymb → LEnt σ) {u : VarSymb} (hu : PPath u.path) {s : Step}
    (hs : s.isProj = false) (p : List Step) :
    eIdx g ((VarSymb.step u s).ext p) = entIdx (g (.step u s)) p := by
  unfold eIdx
  rw [VarSymb.ext_path, VarSymb.ext_rt]
  rw [show (VarSymb.step u s).path ++ p = u.path ++ s :: p by
    change (u.path ++ [s]) ++ p = _
    simp, splitLevel_ppath hu hs p]
  change entIdx (g (.step ((VarSymb.root u.rt).ext u.path) s)) p = _
  rw [← VarSymb.eq_root_ext u]

theorem coh_eS_kView {l : List VarType} {k : Option VarSymb} {Δ : Ctx}
    {g : VarSymb → LEnt σ} (hg : EntOk ((ctxOf l).kView k) Δ g) :
    Subst.Coh (eIdx g) ((ctxOf l).kView k) (eS σ Δ g) := by
  refine Subst.coh_of (ok_eS_kView hg) ?_
  intro v T hl hT p
  obtain ⟨u, s, rfl, hu, -⟩ := kView_item hT
  rw [eS_item g hl, idxAlong_entOf (hg _ T hl hT) p, eIdx_item g hu hl p]

/-- A growing target keeps an edge's substitution, up to agreement on the view. -/
theorem sim_eS_mono {l : List VarType} {k : Option VarSymb} {Δ Δ' : Ctx} (h : Δ.Le Δ')
    {g : VarSymb → LEnt σ} (hg : EntOk ((ctxOf l).kView k) Δ g) :
    Subst.Sim ((ctxOf l).kView k) ((eS σ Δ g).mono h) (eS σ Δ' g) :=
  Subst.sim_of fun v T hl hv => by
    obtain ⟨u, s, rfl, -, -⟩ := kView_item hv
    change SubE.Sim T (SubE.mono h (eS σ Δ g (.step u s))) _
    rw [eS_item g hl, eS_item g hl, entOf_mono h (hg _ T hl hv)]
    exact .refl _

/-- Entry maps agreeing on a view give agreeing substitutions. -/
theorem sim_eS_congr {l : List VarType} {k : Option VarSymb} {Δ : Ctx}
    {g g' : VarSymb → LEnt σ}
    (hag : ∀ v T, v.lastProj = false → (ctxOf l).kView k v = some T → g' v = g v) :
    Subst.Sim ((ctxOf l).kView k) (eS σ Δ g) (eS σ Δ g') :=
  Subst.sim_of fun v T hl hv => by
    obtain ⟨u, s, rfl, -, -⟩ := kView_item hv
    rw [eS_item g hl, eS_item g' hl, hag _ T hl hv]
    exact .refl _

/-! ## An arrow extended by a fresh realisation is the old one opened at it -/

/-- An entry map extended by the fresh realisation of `c : A` at the variable `z`. -/
def gextF (f : VarSymb → LEnt σ) (A : VarType) (c z : ℕ) (v : VarSymb) : LEnt σ :=
  match v with
  | .step u s =>
      if u.rt = .free c then .inl ((VarSymb.root (.free z)).ext (gPath A u.path s)) else f v
  | .root _ => f v

theorem gextF_new {f : VarSymb → LEnt σ} {A : VarType} {c z : ℕ} {u : VarSymb}
    (h : u.rt = .free c) (s : Step) :
    gextF f A c z (.step u s) = .inl ((VarSymb.root (.free z)).ext (gPath A u.path s)) :=
  if_pos h

theorem gextF_old {f : VarSymb → LEnt σ} {A : VarType} {c z : ℕ} {u : VarSymb}
    (h : ¬ u.rt = .free c) (s : Step) : gextF f A c z (.step u s) = f (.step u s) :=
  if_neg h

/-- ⭐The extended entry map types the new view. -/
theorem itemOk_gextF (hF : ModalSys.Four = true) {k : Option VarSymb} {A : VarType}
    {ls lt : List VarType} (hk : KOld k ls.length) {f : VarSymb → LEnt σ}
    (hf : EntOk ((ctxOf ls).kView k) (ctxOf lt) f) :
    EntOk ((ctxOf (A :: ls)).kView k) (ctxOf (A.gc :: lt)) (gextF f A ls.length lt.length) := by
  intro v T hl hv
  obtain ⟨u, s, rfl, -, U, hU⟩ := kView_item hv
  by_cases hrt : u.rt = .free ls.length
  · rw [gextF_new hrt]
    have h := ref_gItem hF (kView_boxIn hk hrt hv) hrt (Δ := ctxOf (A.gc :: lt))
      (z := .free lt.length) (by rw [rootTy_new]; exact ctxOf_ref_new A.gc lt)
    rwa [rootTy_new] at h
  · rw [gextF_old hrt]
    rw [kView_old hrt] at hv
    exact okRef_entOf_mono (ctxOf_le_append [A.gc] lt) (hf _ T hl hv)

/-- ⭐The entry map extended by the new variable's fresh realisation is the old map applied to
    the abstraction, with the slot sent to the new variable — along either kind of edge. -/
theorem subst_gext_gabs (hF : ModalSys.Four = true) {k : Option VarSymb} {A : VarType}
    {ls lt : List VarType} (hk : KOld k ls.length) {f : VarSymb → LEnt σ}
    (hf : EntOk ((ctxOf ls).kView k) (ctxOf lt) f)
    (ψ : WFF σ ((ctxOf (A :: ls)).kView k) 0) :
    WFF.subst (eIdx (gextF f A ls.length lt.length))
        (eS σ (ctxOf (A.gc :: lt)) (gextF f A ls.length lt.length))
        (ok_eS_kView (itemOk_gextF hF hk hf)) (coh_eS_kView (itemOk_gextF hF hk hf))
        Ctx.NoSlots.slots Ctx.NoSlots.slots ψ =
      WFF.subst (VarSymb.slotToFree (eIdx f) 0 lt.length)
        ((eS σ (ctxOf lt) f).toFree 0 lt.length A.gc (ctxOf_fresh le_rfl).root)
        (Subst.ok_toFree (ok_eS_kView hf) A.gc _)
        (Subst.coh_toFree (ok_eS_kView hf) (coh_eS_kView hf) Ctx.NoSlots.slots A.gc _)
        (gabsCtx_slots k A ls) Ctx.NoSlots.slots (gabs hF k A ls hk ψ) := by
  refine (WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ ψ).symm
  refine Subst.sim_of ?_
  intro v T hl hv
  obtain ⟨u, s, rfl, -, U, hU⟩ := kView_item hv
  have hs' : s.isProj = false := hl
  rw [eS_item _ hs']
  change SubE.Sim T _
    ((if s.isProj then SubE.hide else .ren (gabsF A ls.length (.step u s))).comp _ _ _)
  rw [if_neg (by simp [hs'])]
  by_cases hrt : u.rt = .free ls.length
  · rw [gextF_new hrt, gabsF_new hrt]
    change SubE.Sim T _ ((Subst.toFree _ 0 lt.length A.gc _).at
      ((VarSymb.root (.bnd 0)).ext (gPath A u.path s)))
    have hat := at_toFree_reroot (eS σ (ctxOf lt) f) lt.length A.gc
      (ctxOf_fresh le_rfl).root ((VarSymb.root (.bnd 0)).ext (gPath A u.path s))
      (by rw [VarSymb.ext_path]; exact ppath_gPath A u.path s)
    rw [VarSymb.reroot_eq, VarSymb.reroot_eq, VarSymb.ext_path,
      show (VarSymb.root (.bnd 0)).path = [] from rfl, List.nil_append] at hat
    rw [hat]
    exact .refl _
  · rw [gextF_old hrt, gabsF_old hrt]
    change SubE.Sim T _ ((Subst.toFree _ 0 lt.length A.gc _).at (.step u s))
    rw [Subst.at_nonproj _ hl]
    change SubE.Sim T _ (if VarSymb.step u s = .root (.bnd 0) then _ else _)
    rw [if_neg (fun h => by cases h)]
    change SubE.Sim T _ (SubE.mono _ (eS σ (ctxOf lt) f (.step u s)))
    rw [kView_old hrt] at hv
    rw [eS_item _ hs', entOf_mono _ (hf _ T hl hv)]
    exact .refl _

end GArrow

end V12M
