import QML.QML_v12m_GLoop
import QML.QML_v12m_GFwd

/-!
# QML v12m — the root's loop: extending the transfer

The root's self-edge (`docs/v12-modal-extensions.md`, "KB5 and KDB5: the step in Lean") commits the
root's next variable `c : A`: its kept items go to `c`'s own components, and its `□` items to a
fresh root of the type of their contents (`gloopF`).

`gpairS` abstracts `c`'s items into one slot, the kept part first.  Splitting that slot,
`Proof.loop_tup` reflects the kept part, and the transfer on the older variables does the rest.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature}

/-! ## The parts of a variable -/

/-- The contents of a variable's `□` components, with T off. -/
abbrev VarType.lc (A : VarType) : VarType := VarType.bcB false A

/-- The type of a variable's items: its kept part and its contents. -/
abbrev VarType.pc (A : VarType) : VarType := .VTypeProd (VarType.kc A) (VarType.lc A)

theorem walk_kc (hT : ModalSys.T = false) :
    ∀ (A : VarType) (q : List Step) {U : VarType}, PPath q → A.walk q = some U →
      U.keepable = true → (VarType.kc A).walk q = some U
  | A, [], U, _, h, hk => by
      cases h
      cases A <;> first | rfl | cases hk
  | .VTypeProd X _, .fst :: q, _, hp, h, hk =>
      walk_kc hT X q (fun s hs => hp s (List.mem_cons_of_mem _ hs)) h hk
  | .VTypeProd _ Y, .snd :: q, _, hp, h, hk =>
      walk_kc hT Y q (fun s hs => hp s (List.mem_cons_of_mem _ hs)) h hk
  | .VTypeBox _, .here :: _, _, _, h, _ => by simp [VarType.walk, VarType.step, hT] at h
  | .VTypeBox _, .box :: _, _, hp, _, _ => absurd (hp .box (by simp)) (by decide)
  | .VTypeDia _, .dia :: _, _, hp, _, _ => absurd (hp .dia (by simp)) (by decide)
  | .VTypeProd _ _, .box :: _, _, _, h, _ | .VTypeProd _ _, .dia :: _, _, _, h, _
  | .VTypeProd _ _, .keep :: _, _, _, h, _ | .VTypeProd _ _, .here :: _, _, _, h, _
  | .VTypeBox _, .fst :: _, _, _, h, _ | .VTypeBox _, .snd :: _, _, _, h, _
  | .VTypeBox _, .dia :: _, _, _, h, _ | .VTypeBox _, .keep :: _, _, _, h, _
  | .VTypeDia _, .fst :: _, _, _, h, _ | .VTypeDia _, .snd :: _, _, _, h, _
  | .VTypeDia _, .box :: _, _, _, h, _ | .VTypeDia _, .keep :: _, _, _, h, _
  | .VTypeDia _, .here :: _, _, _, h, _ | .Var, _ :: _, _, _, h, _
  | .VTypeOne, _ :: _, _, _, h, _ => by simp [VarType.walk, VarType.step] at h

theorem walk_lc (hT : ModalSys.T = false) :
    ∀ (A : VarType) (q : List Step) {B : VarType}, PPath q → A.walk q = some (.VTypeBox B) →
      (VarType.lc A).walk q = some B
  | A, [], _, _, h => by
      cases h
      rfl
  | .VTypeProd X _, .fst :: q, _, hp, h =>
      walk_lc hT X q (fun s hs => hp s (List.mem_cons_of_mem _ hs)) h
  | .VTypeProd _ Y, .snd :: q, _, hp, h =>
      walk_lc hT Y q (fun s hs => hp s (List.mem_cons_of_mem _ hs)) h
  | .VTypeBox _, .here :: _, _, _, h => by simp [VarType.walk, VarType.step, hT] at h
  | .VTypeBox _, .box :: _, _, hp, _ => absurd (hp .box (by simp)) (by decide)
  | .VTypeDia _, .dia :: _, _, hp, _ => absurd (hp .dia (by simp)) (by decide)
  | .VTypeProd _ _, .box :: _, _, _, h | .VTypeProd _ _, .dia :: _, _, _, h
  | .VTypeProd _ _, .keep :: _, _, _, h | .VTypeProd _ _, .here :: _, _, _, h
  | .VTypeBox _, .fst :: _, _, _, h | .VTypeBox _, .snd :: _, _, _, h
  | .VTypeBox _, .dia :: _, _, _, h | .VTypeBox _, .keep :: _, _, _, h
  | .VTypeDia _, .fst :: _, _, _, h | .VTypeDia _, .snd :: _, _, _, h
  | .VTypeDia _, .box :: _, _, _, h | .VTypeDia _, .keep :: _, _, _, h
  | .VTypeDia _, .here :: _, _, _, h | .Var, _ :: _, _, _, h
  | .VTypeOne, _ :: _, _, _, h => by simp [VarType.walk, VarType.step] at h

/-- The annotation of `kcTup`. -/
def kcAnn (g : VarSymb → VarSymb) : VarSymb → (A : VarType) → Ann (VarType.kc A)
  | _, .Var => .one
  | _, .VTypeOne => .one
  | u, .VTypeProd X Y => .prod (kcAnn g (.step u .fst) X) (kcAnn g (.step u .snd) Y)
  | u, .VTypeBox B => Ann.eta (g u) (.VTypeBox B)
  | u, .VTypeDia B => Ann.eta (g u) (.VTypeDia B)

/-- ⭐The keepable components of `u : A`, each sent along `g`: the objects themselves, or kept. -/
def kcTup {Γ Ω : Ctx} (g : VarSymb → VarSymb)
    (hg : ∀ p U, Γ.ref p = some U → U.keepable = true → Ω.ref (g p) = some U) :
    (A : VarType) → (u : VarSymb) → Γ.ref u = some A → Term σ Ω (VarType.kc A) (kcAnn g u A)
  | .Var, _, _ => .unit
  | .VTypeOne, _, _ => .unit
  | .VTypeProd X Y, u, h =>
      .pair (kcTup g hg X (.step u .fst) (Ctx.ref_fst_of h))
        (kcTup g hg Y (.step u .snd) (Ctx.ref_snd_of h))
  | .VTypeBox B, u, h => Term.eta (g u) (.VTypeBox B) (hg u _ h rfl)
  | .VTypeDia B, u, h => Term.eta (g u) (.VTypeDia B) (hg u _ h rfl)

/-- The annotation of `lcTm`. -/
def lcAnn : VarSymb → (A : VarType) → Ann (VarType.lc A)
  | _, .Var => .one
  | _, .VTypeOne => .one
  | _, .VTypeDia _ => .one
  | u, .VTypeProd X Y => .prod (lcAnn (.step u .fst) X) (lcAnn (.step u .snd) Y)
  | u, .VTypeBox B => Ann.eta (.step u .box) B

/-- ⭐The contents of `u : A`'s `□` components, as a term of the `□` view. -/
def lcTm {Γ : Ctx} (hk : ModalSys.keepOnly = false) :
    (A : VarType) → (u : VarSymb) → Γ.ref u = some A →
      Term σ Γ.boxIn (VarType.lc A) (lcAnn u A)
  | .Var, _, _ => .unit
  | .VTypeOne, _, _ => .unit
  | .VTypeDia _, _, _ => .unit
  | .VTypeProd X Y, u, h =>
      .pair (lcTm hk X (.step u .fst) (Ctx.ref_fst_of h))
        (lcTm hk Y (.step u .snd) (Ctx.ref_snd_of h))
  | .VTypeBox B, u, h => Term.eta (.step u .box) B (Ctx.ref_boxIn_of hk h)

/-! ## Reading a tuple along a path -/

theorem SubE.projs_ren {Δ : Ctx} : ∀ (q : List Step) (w : VarSymb),
    (SubE.ren w : SubE σ Δ).projs q = .ren (w.ext q)
  | [], _ => rfl
  | _ :: q, w => SubE.projs_ren q (.step w _)

theorem SubE.Sim.projs {Δ : Ctx} : ∀ {U T : VarType} {e e' : SubE σ Δ}, SubE.Sim U e e' →
    ∀ (q : List Step), PPath q → U.walk q = some T → SubE.Sim T (e.projs q) (e'.projs q)
  | _, _, _, _, h, [], _, hw => by
      cases hw
      exact h
  | U, T, _, _, h, s :: q, hp, hw => by
      cases hs : U.step s with
      | none => simp [VarType.walk, hs] at hw
      | some U' =>
          have hw' : U'.walk q = some T := by simpa [VarType.walk, hs] using hw
          exact SubE.Sim.projs (h.proj_step (hp s (by simp)) hs) q
            (fun s' hs' => hp s' (List.mem_cons_of_mem _ hs')) hw'

theorem projs_kcTup {Γ Ω : Ctx} (hT : ModalSys.T = false) (g : VarSymb → VarSymb)
    (hg : ∀ p U, Γ.ref p = some U → U.keepable = true → Ω.ref (g p) = some U) :
    ∀ (q : List Step) (A : VarType) (u : VarSymb) (h : Γ.ref u = some A) {U : VarType},
      PPath q → A.walk q = some U → U.keepable = true →
      ∀ hr : Ω.ref (g (u.ext q)) = some U,
        (SubE.tm (kcTup (σ := σ) g hg A u h)).projs q = .tm (Term.eta (g (u.ext q)) U hr)
  | [], A, u, h, U, _, hw, hk, hr => by
      cases hw
      cases A with
      | VTypeBox B => rfl
      | VTypeDia B => rfl
      | Var => cases hk
      | VTypeOne => cases hk
      | VTypeProd X Y => cases hk
  | s :: q, A, u, h, U, hp, hw, hk, hr => by
      have hp' : PPath q := fun s' hs' => hp s' (List.mem_cons_of_mem _ hs')
      cases s with
      | fst =>
          cases A with
          | VTypeProd X Y =>
              exact projs_kcTup hT g hg q X (.step u .fst) (Ctx.ref_fst_of h) hp' hw hk hr
          | _ => simp [VarType.walk, VarType.step] at hw
      | snd =>
          cases A with
          | VTypeProd X Y =>
              exact projs_kcTup hT g hg q Y (.step u .snd) (Ctx.ref_snd_of h) hp' hw hk hr
          | _ => simp [VarType.walk, VarType.step] at hw
      | here => cases A <;> simp [VarType.walk, VarType.step, hT] at hw
      | box => exact absurd (hp .box (by simp)) (by decide)
      | dia => exact absurd (hp .dia (by simp)) (by decide)
      | keep => exact absurd (hp .keep (by simp)) (by decide)

theorem projs_lcTm {Γ : Ctx} (hT : ModalSys.T = false) (hb : ModalSys.keepOnly = false) :
    ∀ (q : List Step) (A : VarType) (u : VarSymb) (h : Γ.ref u = some A) {B : VarType},
      PPath q → A.walk q = some (.VTypeBox B) →
      ∀ hr : Γ.boxIn.ref (.step (u.ext q) .box) = some B,
        (SubE.tm (lcTm (σ := σ) hb A u h)).projs q = .tm (Term.eta (.step (u.ext q) .box) B hr)
  | [], A, u, h, B, _, hw, hr => by
      cases hw
      rfl
  | s :: q, A, u, h, B, hp, hw, hr => by
      have hp' : PPath q := fun s' hs' => hp s' (List.mem_cons_of_mem _ hs')
      cases s with
      | fst =>
          cases A with
          | VTypeProd X Y =>
              exact projs_lcTm hT hb q X (.step u .fst) (Ctx.ref_fst_of h) hp' hw hr
          | _ => simp [VarType.walk, VarType.step] at hw
      | snd =>
          cases A with
          | VTypeProd X Y =>
              exact projs_lcTm hT hb q Y (.step u .snd) (Ctx.ref_snd_of h) hp' hw hr
          | _ => simp [VarType.walk, VarType.step] at hw
      | here => cases A <;> simp [VarType.walk, VarType.step, hT] at hw
      | box => exact absurd (hp .box (by simp)) (by decide)
      | dia => exact absurd (hp .dia (by simp)) (by decide)
      | keep => exact absurd (hp .keep (by simp)) (by decide)

/-! ## The abstraction -/

/-- The item map of abstracting the variable `c`: its kept items and its `□` items go to the two
    sides of the slot, at their own paths. -/
def gpairF (c : ℕ) (v : VarSymb) : VarSymb :=
  match v with
  | .step u .box =>
      if u.rt = .free c then (VarSymb.step (.root (.bnd 0)) .snd).ext u.path else v
  | .step u .keep =>
      if u.rt = .free c then (VarSymb.step (.root (.bnd 0)) .fst).ext u.path else v
  | _ => v

/-- The entries of the root's self-edge, extended by `c : A` with `□` contents in the root `z`:
    its kept items are its own components. -/
def gloopF (f : VarSymb → LEnt σ) (c z : ℕ) (v : VarSymb) : LEnt σ :=
  match v with
  | .step u .box => if u.rt = .free c then .inl ((VarSymb.root (.free z)).ext u.path) else f v
  | .step u .keep => if u.rt = .free c then .inl u else f v
  | _ => f v

/-- The context of the abstracted formula. -/
abbrev gpairCtx (A : VarType) (l : List VarType) : Ctx :=
  ((ctxOf l).kView none).insert (.bnd 0) (VarType.pc A)

omit [ModalSys] in
theorem gpairF_old {c : ℕ} {u : VarSymb} (h : ¬ u.rt = .free c) :
    ∀ s : Step, gpairF c (.step u s) = .step u s
  | .box => if_neg h
  | .keep => if_neg h
  | .fst => rfl
  | .snd => rfl
  | .dia => rfl
  | .here => rfl

omit [ModalSys] in
theorem gpairF_box {c : ℕ} {u : VarSymb} (h : u.rt = .free c) :
    gpairF c (.step u .box) = (VarSymb.step (.root (.bnd 0)) .snd).ext u.path := if_pos h

omit [ModalSys] in
theorem gpairF_keep {c : ℕ} {u : VarSymb} (h : u.rt = .free c) :
    gpairF c (.step u .keep) = (VarSymb.step (.root (.bnd 0)) .fst).ext u.path := if_pos h

theorem gloopF_old {f : VarSymb → LEnt σ} {c z : ℕ} {u : VarSymb} (h : ¬ u.rt = .free c) :
    ∀ s : Step, gloopF f c z (.step u s) = f (.step u s)
  | .box => if_neg h
  | .keep => if_neg h
  | .fst => rfl
  | .snd => rfl
  | .dia => rfl
  | .here => rfl

theorem gloopF_box {f : VarSymb → LEnt σ} {c z : ℕ} {u : VarSymb} (h : u.rt = .free c) :
    gloopF f c z (.step u .box) = .inl ((VarSymb.root (.free z)).ext u.path) := if_pos h

theorem gloopF_keep {f : VarSymb → LEnt σ} {c z : ℕ} {u : VarSymb} (h : u.rt = .free c) :
    gloopF f c z (.step u .keep) = .inl u := if_pos h

/-- The type a new variable's address reaches, from its root. -/
theorem walk_of_new {A : VarType} {l : List VarType} {u : VarSymb} {U : VarType}
    (hup : PPath u.path) (hU : (ctxOf (A :: l)).ref u = some U) (hrt : u.rt = .free l.length) :
    A.walk u.path = some U := by
  have e := Ctx.ref_ext_ppath (ctxOf (A :: l)) u.path (.root u.rt) hup
  rw [← VarSymb.eq_root_ext u, hU, hrt, ctxOf_ref_new] at e
  exact e.symm

omit [ModalSys] in
/-- The new variable's address, from its root. -/
theorem ext_of_new {c : ℕ} {u : VarSymb} (hrt : u.rt = .free c) :
    (VarSymb.root (.free c)).ext u.path = u := by
  rw [← hrt]
  exact (VarSymb.eq_root_ext u).symm

theorem itemOk_gpairF (hT : ModalSys.T = false) (A : VarType) (l : List VarType) :
    ItemOk ((ctxOf (A :: l)).kView none) (gpairCtx A l) (gpairF l.length) := by
  intro v T hl hv
  obtain ⟨u, s, rfl, hup, U, hU⟩ := kView_item hv
  by_cases hrt : u.rt = .free l.length
  · have hwalk := walk_of_new hup hU hrt
    have hr := Ctx.ref_insert_root ((ctxOf l).kView none) (.bnd 0) (VarType.pc A)
    have hv' : (ctxOf (A :: l)).boxIn (.step u s) = some T := hv
    cases s with
    | box =>
        obtain ⟨-, hu⟩ := Ctx.boxIn_box hv'
        rw [hU] at hu
        cases hu
        rw [gpairF_box hrt, Ctx.ref_ext_ppath _ _ _ hup, Ctx.ref_snd_of hr]
        exact walk_lc hT A _ hup hwalk
    | keep =>
        obtain ⟨-, hu, hk⟩ := Ctx.boxIn_keep hv'
        rw [hU] at hu
        cases hu
        rw [gpairF_keep hrt, Ctx.ref_ext_ppath _ _ _ hup, Ctx.ref_fst_of hr]
        exact walk_kc hT A _ hup hwalk hk
    | dia => cases hv'
    | fst => cases hl
    | snd => cases hl
    | here => cases hl
  · obtain ⟨r, hr⟩ := (reach_ppath hU).2
    rw [gpairF_old hrt, Ctx.ref_insert_ne _ (fun h => by
      change u.rt = _ at h
      rw [hr] at h
      cases h), Ctx.ref_nonproj _ hl]
    rw [kView_old hrt] at hv
    exact hv

/-- The extended entries type the new view. -/
theorem entOk_gloopF (hT : ModalSys.T = false) {A : VarType} {cl l : List VarType}
    (hle : (ctxOf (A :: cl)).Le (ctxOf l)) {f : VarSymb → LEnt σ}
    (hf : EntOk ((ctxOf cl).kView none) (ctxOf l) f) :
    EntOk ((ctxOf (A :: cl)).kView none) (ctxOf (VarType.lc A :: l))
      (gloopF f cl.length l.length) := by
  intro v T hl hv
  obtain ⟨u, s, rfl, hup, U, hU⟩ := kView_item hv
  by_cases hrt : u.rt = .free cl.length
  · have hwalk := walk_of_new hup hU hrt
    have hv' : (ctxOf (A :: cl)).boxIn (.step u s) = some T := hv
    cases s with
    | box =>
        obtain ⟨-, hu⟩ := Ctx.boxIn_box hv'
        rw [hU] at hu
        cases hu
        rw [gloopF_box hrt]
        change (ctxOf (VarType.lc A :: l)).ref _ = _
        rw [Ctx.ref_ext_ppath _ _ _ hup, ctxOf_ref_new]
        exact walk_lc hT A _ hup hwalk
    | keep =>
        obtain ⟨-, hu, hk⟩ := Ctx.boxIn_keep hv'
        rw [hU] at hu
        cases hu
        rw [gloopF_keep hrt]
        exact (ctxOf_le_append [VarType.lc A] l).ref (hle.ref hU)
    | dia => cases hv'
    | fst => cases hl
    | snd => cases hl
    | here => cases hl
  · rw [gloopF_old hrt]
    rw [kView_old hrt] at hv
    exact okRef_entOf_mono (ctxOf_le_append [VarType.lc A] l) (hf _ T hl hv)

/-- ⭐The abstraction of a formula of the new variable's `□` view: `c`'s items in one slot. -/
def gpairAbs (hT : ModalSys.T = false) (A : VarType) (l : List VarType)
    (ψ : WFF σ ((ctxOf (A :: l)).kView none) 0) : WFF σ (gpairCtx A l) 1 :=
  WFF.subst (itemIdx (gpairF l.length)) (itemS σ (gpairCtx A l) (gpairF l.length))
    (ok_itemS_kView (itemOk_gpairF hT A l)) (coh_itemS_kView (itemOk_gpairF hT A l))
    Ctx.NoSlots.slots ((Ctx.NoSlots.slots (Γ := (ctxOf l).kView none)).insert _) ψ

theorem SubE.Sim.ren_eta_of {Δ : Ctx} {U : VarType} {w w' : VarSymb} (e : w' = w)
    (h : Δ.ref w' = some U) : SubE.Sim U (.ren w) (.tm (Term.eta (σ := σ) w' U h)) := by
  subst e
  exact .ren_eta _ _

theorem SubE.Sim.eta_ren_of {Δ : Ctx} {U : VarType} {w w' : VarSymb} (e : w' = w)
    (h : Δ.ref w' = some U) : SubE.Sim U (.tm (Term.eta (σ := σ) w' U h)) (.ren w) := by
  subst e
  exact .eta_ren _ _

/-- The new variable's kept part, in its `□` view. -/
abbrev keptTup (hF : ModalSys.Four = true) (A : VarType) (l : List VarType) :
    Term σ (ctxOf (A :: l)).boxIn (VarType.kc A)
      (kcAnn (fun p => .step p .keep) (.root (.free l.length)) A) :=
  kcTup (fun p => .step p .keep) (fun _ _ h hk => Ctx.ref_keep_of' hF h hk) A
    (.root (.free l.length)) (ctxOf_ref_new A l)

/-- ⭐A formula of the new variable's view is its abstraction read at the variable's own items. -/
theorem instantiate_gpairAbs (hF : ModalSys.Four = true) (hT : ModalSys.T = false)
    (hb : ModalSys.keepOnly = false) (A : VarType) (l : List VarType)
    (ψ : WFF σ ((ctxOf (A :: l)).kView none) 0) :
    WFF.instantiate Ctx.NoSlots.slots
      (Term.pair (keptTup (σ := σ) hF A l) (lcTm hb A _ (ctxOf_ref_new A l)))
      (WFF.mono ((ctxOf_le_append [A] l).boxIn.insert (.bnd 0) _) (gpairAbs hT A l ψ)) = ψ := by
  have hs : (((ctxOf (A :: l)).kView none).insert (.bnd 0) (VarType.pc A)).SlotsFrom 1 :=
    (Ctx.NoSlots.slots (Γ := (ctxOf (A :: l)).kView none)).insert _
  unfold WFF.instantiate WFF.substRoot gpairAbs
  rw [WFF.subst_mono ((ctxOf_le_append [A] l).boxIn.insert (.bnd 0) _) _ _ _
    ((Ctx.NoSlots.slots (Γ := (ctxOf l).kView none)).insert _) hs]
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ Subst.ok_idS Subst.coh_idS _ _ _ ?_ ψ).trans
    (WFF.subst_id _ _ _ ψ)
  refine Subst.sim_of ?_
  intro v T hl hv
  obtain ⟨u, s, rfl, hup, U, hU⟩ := kView_item hv
  have hs' : s.isProj = false := hl
  change SubE.Sim T (.ren (.step u s))
    ((if s.isProj then SubE.hide else .ren (gpairF l.length (.step u s))).comp _ _ _)
  rw [if_neg (by simp [hs'])]
  by_cases hrt : u.rt = .free l.length
  · have hwalk := walk_of_new hup hU hrt
    have hv' : (ctxOf (A :: l)).boxIn (.step u s) = some T := hv
    cases s with
    | box =>
        obtain ⟨-, hu⟩ := Ctx.boxIn_box hv'
        rw [hU] at hu
        cases hu
        rw [gpairF_box hrt]
        change SubE.Sim _ _ ((Subst.single (.bnd 0) _).at _)
        rw [Subst.at_ext_ppath _ _ _ hup, Subst.at_proj _ _ rfl, Subst.at_single_root]
        change SubE.Sim _ _ ((SubE.tm (lcTm hb A _ (ctxOf_ref_new A l))).projs _)
        have hr : (ctxOf (A :: l)).boxIn.ref (.step ((VarSymb.root (.free l.length)).ext u.path)
            .box) = some T := by
          rw [ext_of_new hrt, Ctx.ref_nonproj _ hl]
          exact hv'
        rw [projs_lcTm hT hb _ _ _ _ hup hwalk hr]
        exact SubE.Sim.ren_eta_of (by rw [ext_of_new hrt]) hr
    | keep =>
        obtain ⟨-, hu, hk⟩ := Ctx.boxIn_keep hv'
        rw [hU] at hu
        cases hu
        rw [gpairF_keep hrt]
        change SubE.Sim _ _ ((Subst.single (.bnd 0) _).at _)
        rw [Subst.at_ext_ppath _ _ _ hup, Subst.at_proj _ _ rfl, Subst.at_single_root]
        change SubE.Sim _ _ ((SubE.tm (keptTup hF A l)).projs _)
        have hr : (ctxOf (A :: l)).boxIn.ref (.step ((VarSymb.root (.free l.length)).ext u.path)
            .keep) = some T := by
          rw [ext_of_new hrt, Ctx.ref_nonproj _ hl]
          exact hv'
        rw [projs_kcTup hT _ _ _ _ _ _ hup hwalk hk hr]
        exact SubE.Sim.ren_eta_of (by rw [ext_of_new hrt]) hr
    | dia => cases hv'
    | fst => cases hl
    | snd => cases hl
    | here => cases hl
  · rw [gpairF_old hrt]
    change SubE.Sim T _ ((Subst.single (.bnd 0) _).at (.step u s))
    rw [Subst.single_at_ne (by
      change u.rt ≠ _
      obtain ⟨r, hr⟩ := (reach_ppath hU).2
      rw [hr]
      exact fun h => by cases h)]
    exact .refl _

/-! ## Reading through the transfer -/

theorem SubE.mono_refl' {Δ : Ctx} (h : Δ.Le Δ) : ∀ e : SubE σ Δ, e.mono h = e
  | .hide => rfl
  | .ren _ => rfl
  | .tm s => congrArg SubE.tm (Term.mono_refl h s)

theorem SubE.Sim.symm' {Δ : Ctx} {U : VarType} {e e' : SubE σ Δ} (h : SubE.Sim U e e') :
    SubE.Sim U e' e := by
  cases h with
  | refl => exact .refl _
  | eta_ren w h => exact .ren_eta w h
  | ren_eta w h => exact .eta_ren w h

theorem mono_kcTup {Γ Ω Ω' : Ctx} (h : Ω.Le Ω') (g : VarSymb → VarSymb)
    (hg : ∀ p U, Γ.ref p = some U → U.keepable = true → Ω.ref (g p) = some U)
    (hg' : ∀ p U, Γ.ref p = some U → U.keepable = true → Ω'.ref (g p) = some U) :
    ∀ (A : VarType) (u : VarSymb) (hu : Γ.ref u = some A),
      Term.mono h (kcTup (σ := σ) g hg A u hu) = kcTup g hg' A u hu
  | .Var, _, _ => rfl
  | .VTypeOne, _, _ => rfl
  | .VTypeProd X Y, u, hu => by
      change Term.pair (Term.mono h (kcTup g hg X _ _)) (Term.mono h (kcTup g hg Y _ _)) = _
      rw [mono_kcTup h g hg hg' X, mono_kcTup h g hg hg' Y]
      rfl
  | .VTypeBox _, _, _ => Term.mono_eta _ _ _ _
  | .VTypeDia _, _, _ => Term.mono_eta _ _ _ _

/-- ⭐Under a substitution sending `w` to `u`'s keepable components, `w` kept is those components
    kept. -/
theorem read_kcTup (hF : ModalSys.Four = true) {Γ Ω V : Ctx} {ι : VarSymb → VarSymb}
    (θ : Subst σ Ω) (hθ : Subst.Ok V θ) (hc : Subst.Coh ι V θ)
    (hg : ∀ p U, Γ.ref p = some U → U.keepable = true → Ω.ref (id p) = some U)
    (hg' : ∀ p U, Γ.ref p = some U → U.keepable = true → Ω.boxIn.ref (.step p .keep) = some U) :
    ∀ (A : VarType) (u : VarSymb) (hu : Γ.ref u = some A) (w : VarSymb)
      (h : V.ref w = some (VarType.kc A)), θ.at w = .tm (kcTup id hg A u hu) →
      (⟨_, Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc)
        (Term.keepOf hF (VarType.kc A) (VarType.tup_kc A) w h)⟩ :
          Σ b, Term σ Ω.boxIn (VarType.kc A) b) =
        ⟨_, kcTup (fun p => .step p .keep) hg' A u hu⟩
  | .Var, _, _, _, _, _ => rfl
  | .VTypeOne, _, _, _, _, _ => rfl
  | .VTypeProd X Y, u, hu, w, h, hw => by
      refine sig_pair (read_kcTup hF θ hθ hc hg hg' X _ _ _ _ ?_)
        (read_kcTup hF θ hθ hc hg hg' Y _ _ _ _ ?_)
      · rw [Subst.at_proj _ _ rfl, hw]
        rfl
      · rw [Subst.at_proj _ _ rfl, hw]
        rfl
  | .VTypeBox B, u, hu, w, h, hw => by
      refine Term.subst_eta_tm _ _ _ _ _ _ _ ?_
      rw [Subst.box_at_keep, hw]
      exact SubE.keepE_eta_of hF (hg u _ hu rfl) rfl
  | .VTypeDia B, u, hu, w, h, hw => by
      refine Term.subst_eta_tm _ _ _ _ _ _ _ ?_
      rw [Subst.box_at_keep, hw]
      exact SubE.keepE_eta_of hF (hg u _ hu rfl) rfl

section Reads

variable {V Δ : Ctx} [V.NoSlots] [Δ.NoSlots] {X Y T : VarType}

/-- A substitution's entry, weakened past a slot and filled, is the entry. -/
theorem comp_single_mono {Δ' : Ctx} [Δ'.NoSlots] (h : Δ.Le Δ') {b₀ : Ann Y} (b : Term σ Δ' Y b₀)
    {I : VarSymb → VarSymb} (hok : Subst.Ok (Δ.insert (.bnd 0) Y)
      (Subst.single (σ := σ) (.bnd 0) (.tm b)))
    (hco : Subst.Coh I (Δ.insert (.bnd 0) Y) (Subst.single (σ := σ) (.bnd 0) (.tm b)))
    {U : VarType} : ∀ e : SubE σ Δ, e.OkRef U →
      SubE.Sim U (e.mono h) (SubE.comp _ hok hco (e.mono (body_le Y)))
  | .hide, he => he.elim
  | .ren w, he => by
      have hfr := (Ctx.NoSlots.slots (Γ := Δ)).rootFresh (le_refl 0)
      change SubE.Sim U (.ren w) (Subst.at _ w)
      rw [Subst.single_at_ne (Ctx.ref_rt_ne hfr he)]
      exact .refl _
  | .tm s, _ => by
      have hfr := (Ctx.NoSlots.slots (Γ := Δ)).rootFresh (le_refl 0)
      refine SubE.Sim.of_sig ?_ U
      refine Eq.symm ?_
      rw [Term.subst_mono]
      exact Term.subst_ren h _ _ _ (fun v _ hv => Subst.single_at_ne (Ctx.ref_rt_ne hfr hv)) s

/-- ⭐Filling a slot under a substitution sets the slot in it. -/
theorem WFF.instantiate_subst_under {ι : VarSymb → VarSymb} (θ : Subst σ Δ)
    (hθ : Subst.Ok V θ) (hc : Subst.Coh ι V θ) {t₀ : Ann T} (t : Term σ Δ T t₀)
    (B : WFF σ (V.insert (.bnd 0) T) 1) :
    WFF.instantiate Ctx.NoSlots.slots t
      (WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.under 0 0 T (Ctx.NoSlots.slots (Γ := Δ)).root)
        (Subst.ok_under hθ T _) (Subst.coh_under hθ hc Ctx.NoSlots.slots T _)
        ((Ctx.NoSlots.slots (Γ := V)).insert T) ((Ctx.NoSlots.slots (Γ := Δ)).insert T) B) =
      WFF.subst (Subst.setIdx ι (.bnd 0) (.tm t)) (θ.set (.bnd 0) (.tm t))
        (Subst.ok_set hθ rfl) (Subst.coh_set hθ hc
          ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) rfl)
        ((Ctx.NoSlots.slots (Γ := V)).insert T) Ctx.NoSlots.slots B := by
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ B
  refine Subst.sim_of ?_
  intro v U hl hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    rw [Subst.set_root]
    change SubE.Sim U _ (SubE.comp _ _ _ (Subst.under _ _ _ _ _ (.root (.bnd 0))))
    unfold Subst.under
    rw [if_pos rfl]
    change SubE.Sim U _ (Subst.at _ _)
    rw [Subst.at_single_root]
    exact .refl _
  · have hv' : V v = some U := by
      have := hv
      simpa [Ctx.insert, hvr] using this
    rw [Subst.set_ne _ _ hvr]
    change SubE.Sim U _ (SubE.comp _ _ _ (Subst.under _ _ _ _ _ v))
    unfold Subst.under
    rw [if_neg hvr]
    have e := comp_single_mono (Ctx.Le.refl Δ) t (Subst.ok_single (Ctx.Le.refl Δ) rfl)
      (Subst.coh_single ((Ctx.NoSlots.slots (Γ := Δ)).rootFresh (le_refl 0)) (Ctx.Le.refl Δ) rfl)
      (θ v) (hθ v U hl hv')
    rwa [SubE.mono_refl'] at e

/-- ⭐A substitution through a split slot's first component. -/
theorem WFF.subst_ex_slotPair {ι : VarSymb → VarSymb} (θ : Subst σ Δ) (hθ : Subst.Ok V θ)
    (hc : Subst.Coh ι V θ) (ρ : WFF σ (V.insert (.bnd 0) (.VTypeProd X Y)) 1) {a₀ : Ann X}
    (t : Term σ Δ X a₀) :
    WFF.subst (Subst.setIdx ι (.bnd 0) (.tm t)) (θ.set (.bnd 0) (.tm t))
        (Subst.ok_set hθ rfl) (Subst.coh_set hθ hc
          ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) rfl)
        ((Ctx.NoSlots.slots (Γ := V)).insert X) Ctx.NoSlots.slots (.ex Y (WFF.slotPair ρ)) =
      .ex Y (WFF.subst (Subst.setIdx ι (.bnd 0) (.tm (slotTm t Y)))
        ((θ.mono (body_le Y)).set (.bnd 0) (.tm (slotTm t Y)))
        (Subst.ok_set (Subst.ok_mono hθ _) rfl) (Subst.coh_set (Subst.ok_mono hθ _)
          (Subst.coh_mono hc _) ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) rfl)
        ((Ctx.NoSlots.slots (Γ := V)).insert _) ((Ctx.NoSlots.slots (Γ := Δ)).insert Y) ρ) := by
  refine congrArg (WFF.ex Y) (WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ ρ)
  refine Subst.sim_of ?_
  intro v U hl hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    change SubE.Sim _ ((θ.mono (body_le Y)).set (.bnd 0) (.tm (slotTm t Y)) (.root (.bnd 0)))
      (SubE.comp _ _ _ ((Subst.idS σ _).set (.bnd 0) (.tm (twoPair V X Y)) (.root (.bnd 0))))
    rw [Subst.set_root, Subst.set_root]
    change SubE.Sim _ _ (.tm (Term.pair (Term.subst _ _ _ _ (Term.eta (.root (.bnd 0)) X two_ref))
      (Term.subst _ _ _ _ (Term.eta (.root (.bnd 1)) Y (Ctx.ref_insert_root _ _ Y)))))
    refine SubE.Sim.of_sig (sig_pair (Term.subst_eta_tm _ _ _ _ _ _ (Term.mono (body_le Y) t) ?_)
      (Term.subst_eta_renAt _ _ _ _ _ _ _ (Ctx.ref_insert_root Δ (.bnd 0) Y) ?_)).symm _
    · change Subst.under _ _ _ _ _ (VarSymb.root (.bnd 0)) = _
      unfold Subst.under
      rw [if_neg (by simp), Subst.set_root]
      rfl
    · change Subst.under _ _ _ _ _ (VarSymb.root (.bnd 1)) = _
      unfold Subst.under
      exact if_pos rfl
  · have hv' : V.ref v = some U := by
      have := hv
      rw [Ctx.ref_nonproj _ hl]
      simpa [Ctx.insert, hvr] using this
    have hne : v ≠ .root (.bnd 1) := fun e => Ctx.ref_rt_ne
      ((Ctx.NoSlots.slots (Γ := V)).rootFresh (Nat.zero_le 1)) hv' (by rw [e]; rfl)
    change SubE.Sim U ((θ.mono (body_le Y)).set (.bnd 0) (.tm (slotTm t Y)) v)
      (SubE.comp _ _ _ ((Subst.idS σ _).set (.bnd 0) (.tm (twoPair V X Y)) v))
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    change SubE.Sim U _ (Subst.at _ v)
    rw [Subst.at_nonproj _ hl]
    change SubE.Sim U _ (if v = .root (.bnd 1) then _ else SubE.mono _ (θ.set (.bnd 0) (.tm t) v))
    rw [if_neg hne, Subst.set_ne _ _ hvr]
    exact .refl _

/-- ⭐Filling the second component, under a substitution. -/
theorem WFF.instantiate_mono_pairSet {Δ' : Ctx} [Δ'.NoSlots] (h : Δ.Le Δ')
    {ι : VarSymb → VarSymb} (θ : Subst σ Δ) (hθ : Subst.Ok V θ) (hc : Subst.Coh ι V θ)
    {a₀ : Ann X} (a : Term σ Δ X a₀) (ρ : WFF σ (V.insert (.bnd 0) (.VTypeProd X Y)) 1)
    {b₀ : Ann Y} (b : Term σ Δ' Y b₀) :
    WFF.instantiate Ctx.NoSlots.slots b (WFF.mono (h.insert (.bnd 0) Y)
      (WFF.subst (Subst.setIdx ι (.bnd 0) (.tm (slotTm a Y)))
        ((θ.mono (body_le Y)).set (.bnd 0) (.tm (slotTm a Y)))
        (Subst.ok_set (Subst.ok_mono hθ _) rfl) (Subst.coh_set (Subst.ok_mono hθ _)
          (Subst.coh_mono hc _) ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) rfl)
        ((Ctx.NoSlots.slots (Γ := V)).insert _) ((Ctx.NoSlots.slots (Γ := Δ)).insert Y) ρ)) =
      WFF.subst (Subst.setIdx ι (.bnd 0) (.tm (Term.pair (Term.mono h a) b)))
        ((θ.mono h).set (.bnd 0) (.tm (Term.pair (Term.mono h a) b)))
        (Subst.ok_set (Subst.ok_mono hθ _) rfl) (Subst.coh_set (Subst.ok_mono hθ _)
          (Subst.coh_mono hc _) ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) rfl)
        ((Ctx.NoSlots.slots (Γ := V)).insert _) Ctx.NoSlots.slots ρ := by
  have hfr := (Ctx.NoSlots.slots (Γ := Δ)).rootFresh (le_refl 0)
  refine (WFF.subst_mono _ _ _ _ _ _ _ _).trans (WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ ρ)
  refine Subst.sim_of ?_
  intro v U hl hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    change SubE.Sim _ ((θ.mono h).set (.bnd 0) (.tm (Term.pair (Term.mono h a) b)) (.root (.bnd 0)))
      (SubE.comp _ _ _ ((θ.mono (body_le Y)).set (.bnd 0) (.tm (slotTm a Y)) (.root (.bnd 0))))
    rw [Subst.set_root, Subst.set_root]
    change SubE.Sim _ _ (.tm (Term.pair (Term.subst _ _ _ _ (Term.mono (body_le Y) a))
      (Term.subst _ _ _ _ (Term.eta (.root (.bnd 0)) Y (Ctx.ref_insert_root Δ (.bnd 0) Y)))))
    refine SubE.Sim.of_sig (sig_pair ?_
      (Term.subst_eta_tm _ _ _ _ _ _ b (Subst.at_single_root _ _))).symm _
    rw [Term.subst_mono]
    exact Term.subst_ren h _ _ _ (fun v _ hv => Subst.single_at_ne (Ctx.ref_rt_ne hfr hv)) a
  · have hv' : V v = some U := by
      have := hv
      simpa [Ctx.insert, hvr] using this
    change SubE.Sim U ((θ.mono h).set (.bnd 0) (.tm (Term.pair (Term.mono h a) b)) v)
      (SubE.comp _ _ _ ((θ.mono (body_le Y)).set (.bnd 0) (.tm (slotTm a Y)) v))
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    exact comp_single_mono h b _ _ (θ v) (hθ v U hl hv')

end Reads

/-- ⭐**The hat under a substitution**: when `θ` undoes the shift on the old items and reads the
    slot kept as `k`, `θ` of the hat is `φ` itself, with the slot at `k`. -/
theorem WFF.subst_loopHat {Γ Γ₁ : Ctx} [Γ.NoSlots] [Γ₁.NoSlots] (hF : ModalSys.Four = true)
    {T : VarType} (hT : T.tup = true) {ι : VarSymb → VarSymb} (θ : Subst σ Γ₁)
    (hθ : Subst.Ok (Γ.boxIn.insert (.bnd 0) T) θ) (hc : Subst.Coh ι (Γ.boxIn.insert (.bnd 0) T) θ)
    (hle : Γ.boxIn.Le Γ₁.boxIn) {k₀ : Ann T} (k : Term σ Γ₁.boxIn T k₀)
    (hk : (⟨_, Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc)
      (Term.keepOf hF T hT (.root (.bnd 0)) (Ctx.ref_insert_root Γ.boxIn (.bnd 0) T))⟩ :
        Σ b, Term σ Γ₁.boxIn T b) = ⟨_, k⟩)
    (hfix : ∀ v U, v.lastProj = false → Γ.boxIn v = some U →
      SubE.Sim U (θ.box.at (v.shift 0)) (.ren v))
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) :
    WFF.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc)
        ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T).boxIn Ctx.NoSlots.slots
        (WFF.loopHat hF hT φ) =
      WFF.instantiate Ctx.NoSlots.slots k (WFF.mono (hle.insert (.bnd 0) T) φ) := by
  have hL : Γ.boxIn.boxIn.Le (Γ.boxIn.insert (.bnd 0) T).boxIn :=
    (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root T).boxIn
  have hfr₁ := (Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)
  have hfr₂ := (Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).rootFresh (le_refl 0)
  have hO : Subst.Ok Γ.boxIn.boxIn θ.box := (Subst.ok_box hθ).restrict hL
  have hC : Subst.Coh ι Γ.boxIn.boxIn θ.box := (Subst.coh_box hθ hc).restrict hL
  have hΨ := Subst.ok_set (r := .bnd 0) (T := T) (e := .tm k) hO rfl
  have hcΨ := Subst.coh_set (r := .bnd 0) (T := T) (e := .tm k) hO hC hfr₂ rfl
  have hΨ' : Subst.Ok (Γ.boxIn.insert (.bnd 0) T) (Subst.single (σ := σ) (.bnd 0) (.tm k)) :=
    Subst.ok_single hle rfl
  have hcΨ' : Subst.Coh (Subst.singleIdx (.bnd 0) (.tm k)) (Γ.boxIn.insert (.bnd 0) T)
      (Subst.single (σ := σ) (.bnd 0) (.tm k)) := Subst.coh_single hfr₁ hle rfl
  refine (WFF.subst_comp _ _ _ _ _ _ _ hΨ hcΨ _ _ _ ?_ _).trans
    ((WFF.subst_shift (Ctx.shifts_loop hF Γ T) _ _ _ hΨ hcΨ _ hΨ' hcΨ' _ ?_ φ).trans
      (WFF.subst_mono _ _ _ _ _ _ _ _).symm)
  · refine Subst.sim_of ?_
    intro v U hl hv
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      change SubE.Sim _ (θ.box.set (.bnd 0) (.tm k) (.root (.bnd 0)))
        (SubE.comp _ _ _ (Subst.single (.bnd 0) (.tm _) (.root (.bnd 0))))
      rw [Subst.set_root, show Subst.single (σ := σ) (Δ := (Γ.boxIn.insert (.bnd 0) T).boxIn)
        (.bnd 0) (.tm (Term.keepOf hF T hT (.root (.bnd 0))
          (Ctx.ref_insert_root Γ.boxIn (.bnd 0) T))) (.root (.bnd 0)) = _ from if_pos rfl]
      exact SubE.Sim.of_sig hk.symm _
    · change SubE.Sim U (θ.box.set (.bnd 0) (.tm k) v)
        (SubE.comp _ _ _ (Subst.single (.bnd 0) (.tm _) v))
      rw [Subst.set_ne _ _ hvr, show Subst.single (σ := σ) (Δ := (Γ.boxIn.insert (.bnd 0) T).boxIn)
        (.bnd 0) (.tm (Term.keepOf hF T hT (.root (.bnd 0))
          (Ctx.ref_insert_root Γ.boxIn (.bnd 0) T))) v = .ren v from if_neg hvr]
      change SubE.Sim U _ (Subst.at _ v)
      rw [Subst.at_nonproj _ hl]
      exact .refl _
  · refine Subst.preShift_of fun v U hl hv => ?_
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      change SubE.Sim U (Subst.at _ (.root (.bnd 0)))
        (Subst.single (.bnd 0) (.tm k) (.root (.bnd 0)))
      rw [show Subst.single (σ := σ) (.bnd 0) (.tm k) (.root (.bnd 0)) = .tm k from if_pos rfl]
      change SubE.Sim U (θ.box.set (.bnd 0) (.tm k) (.root (.bnd 0))) _
      rw [Subst.set_root]
      exact .refl _
    · have hv' : Γ.boxIn v = some U := by
        have := hv
        simpa [Ctx.insert, hvr] using this
      rw [show Subst.single (σ := σ) (.bnd 0) (.tm k) v = .ren v from if_neg hvr]
      have h := hfix v U hl hv'
      match v, hl with
      | .root _, _ => cases hv'
      | .step u s, hl =>
          have hs : s.isProj = false := hl
          have hs₂ : (VarSymb.step (.step u .keep) s).lastProj = false := hs
          rw [VarSymb.shift_level_zero hs] at h ⊢
          rw [Subst.at_nonproj _ hs₂, Subst.set_ne _ _ (fun e => by cases e)]
          rwa [Subst.at_nonproj _ hs₂] at h

/-- The entries fix the kept items: `u.keep ↦ u`. -/
def KeepFix (cl : List VarType) (f : VarSymb → LEnt σ) : Prop :=
  ∀ v U, (ctxOf cl).boxIn (.step v .keep) = some U → f (.step v .keep) = .inl v

/-- A variable's keepable components, as objects. -/
abbrev objTup {A : VarType} {cl : List VarType} {Ω : Ctx} (hle : (ctxOf (A :: cl)).Le Ω) :
    Term σ Ω (VarType.kc A) (kcAnn id (.root (.free cl.length)) A) :=
  kcTup id (fun _ _ h _ => hle.ref h) A (.root (.free cl.length)) (ctxOf_ref_new A cl)

/-- The term the extended entries read `gpairAbs`'s slot at. -/
abbrev gloopTm {A : VarType} {cl l : List VarType} (hle : (ctxOf (A :: cl)).Le (ctxOf l)) :
    Term σ (ctxOf (VarType.lc A :: l)) (VarType.pc A)
      (.prod (kcAnn id (.root (.free cl.length)) A) (Ann.eta (.root (.free l.length)) _)) :=
  .pair (Term.mono (ctxOf_le_append [VarType.lc A] l) (objTup hle))
    (Term.eta (.root (.free l.length)) (VarType.lc A) (ctxOf_ref_new _ l))

/-- The extended entries applied to a formula. -/
noncomputable abbrev gloopArrow (hT : ModalSys.T = false) {A : VarType} {cl l : List VarType}
    (hle : (ctxOf (A :: cl)).Le (ctxOf l)) {f : VarSymb → LEnt σ}
    (hf : EntOk ((ctxOf cl).kView none) (ctxOf l) f)
    (ψ : WFF σ ((ctxOf (A :: cl)).kView none) 0) : WFF σ (ctxOf (VarType.lc A :: l)) 0 :=
  WFF.subst (eIdx (gloopF f cl.length l.length))
    (eS σ (ctxOf (VarType.lc A :: l)) (gloopF f cl.length l.length))
    (ok_eS_kView (entOk_gloopF hT hle hf)) (coh_eS_kView (entOk_gloopF hT hle hf))
    Ctx.NoSlots.slots Ctx.NoSlots.slots ψ

/-- ⭐The extended entries are the old ones on the abstraction, with the slot read at the
    variable's kept part and the fresh root. -/
theorem gloopArrow_eq (hT : ModalSys.T = false) {A : VarType} {cl l : List VarType}
    (hle : (ctxOf (A :: cl)).Le (ctxOf l)) {f : VarSymb → LEnt σ}
    (hf : EntOk ((ctxOf cl).kView none) (ctxOf l) f)
    (ψ : WFF σ ((ctxOf (A :: cl)).kView none) 0) :
    gloopArrow hT hle hf ψ =
      WFF.subst (Subst.setIdx (eIdx f) (.bnd 0) (.tm (gloopTm hle)))
        (((eS σ (ctxOf l) f).mono (ctxOf_le_append [VarType.lc A] l)).set (.bnd 0)
          (.tm (gloopTm hle)))
        (Subst.ok_set (Subst.ok_mono (ok_eS_kView hf) _) rfl)
        (Subst.coh_set (Subst.ok_mono (ok_eS_kView hf) _) (Subst.coh_mono (coh_eS_kView hf) _)
          ((Ctx.NoSlots.slots (Γ := (ctxOf cl).kView none)).rootFresh (le_refl 0)) rfl)
        ((Ctx.NoSlots.slots (Γ := (ctxOf cl).kView none)).insert _) Ctx.NoSlots.slots
        (gpairAbs hT A cl ψ) := by
  refine (WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ ψ).symm
  refine Subst.sim_of ?_
  intro v T hl hv
  obtain ⟨u, s, rfl, hup, U, hU⟩ := kView_item hv
  have hs' : s.isProj = false := hl
  rw [eS_item _ hs']
  change SubE.Sim T _ ((if s.isProj then SubE.hide else
    .ren (gpairF cl.length (.step u s))).comp _ _ _)
  rw [if_neg (by simp [hs'])]
  by_cases hrt : u.rt = .free cl.length
  · have hwalk := walk_of_new hup hU hrt
    have hv' : (ctxOf (A :: cl)).boxIn (.step u s) = some T := hv
    cases s with
    | box =>
        obtain ⟨-, hu⟩ := Ctx.boxIn_box hv'
        rw [hU] at hu
        cases hu
        rw [gloopF_box hrt, gpairF_box hrt]
        change SubE.Sim _ (.ren _) (Subst.at _ _)
        rw [Subst.at_ext_ppath _ _ _ hup, Subst.at_proj _ _ rfl]
        change SubE.Sim _ _ (SubE.projs (SubE.proj
          (((eS σ (ctxOf l) f).mono _).set (.bnd 0) (.tm (gloopTm hle)) (.root (.bnd 0))) .snd) _)
        rw [Subst.set_root]
        have h := SubE.Sim.projs (SubE.Sim.eta_ren (σ := σ) (.root (.free l.length))
          (ctxOf_ref_new (VarType.lc A) l)) u.path hup (walk_lc hT A _ hup hwalk)
        rw [SubE.projs_ren] at h
        exact SubE.Sim.symm' h
    | keep =>
        obtain ⟨-, hu, hk⟩ := Ctx.boxIn_keep hv'
        rw [hU] at hu
        cases hu
        rw [gloopF_keep hrt, gpairF_keep hrt]
        change SubE.Sim _ (.ren _) (Subst.at _ _)
        rw [Subst.at_ext_ppath _ _ _ hup, Subst.at_proj _ _ rfl]
        change SubE.Sim _ _ (SubE.projs (SubE.proj
          (((eS σ (ctxOf l) f).mono _).set (.bnd 0) (.tm (gloopTm hle)) (.root (.bnd 0))) .fst) _)
        rw [Subst.set_root]
        change SubE.Sim _ _ ((SubE.tm (Term.mono _ (objTup hle))).projs _)
        rw [mono_kcTup _ id _ (fun _ _ h _ =>
          (ctxOf_le_append [VarType.lc A] l).ref (hle.ref h))]
        have hr : (ctxOf (VarType.lc A :: l)).ref
            (id ((VarSymb.root (.free cl.length)).ext u.path)) = some T := by
          change (ctxOf (VarType.lc A :: l)).ref ((VarSymb.root (.free cl.length)).ext u.path) = _
          rw [ext_of_new hrt]
          exact (ctxOf_le_append [VarType.lc A] l).ref (hle.ref hU)
        rw [projs_kcTup hT _ _ _ _ _ _ hup hwalk hk hr]
        exact SubE.Sim.ren_eta_of (ext_of_new hrt) hr
    | dia => cases hv'
    | fst => cases hl
    | snd => cases hl
    | here => cases hl
  · rw [gloopF_old hrt, gpairF_old hrt]
    rw [kView_old hrt] at hv
    change SubE.Sim T _ (Subst.at _ (.step u s))
    rw [Subst.at_nonproj _ hl, Subst.set_ne _ _ (fun e => by cases e)]
    change SubE.Sim T _ (SubE.mono _ (eS σ (ctxOf l) f (.step u s)))
    rw [eS_item _ hs', entOf_mono _ (hf _ T hl hv)]
    exact .refl _

/-- What `Proof.loop_tup` reflects for `ψ`: its `□` contents existentially closed. -/
def gloopBody (hT : ModalSys.T = false) (A : VarType) (cl : List VarType)
    (ψ : WFF σ ((ctxOf (A :: cl)).kView none) 0) :
    WFF σ ((ctxOf cl).boxIn.insert (.bnd 0) (VarType.kc A)) 1 :=
  .ex (VarType.lc A) (WFF.slotPair (gpairAbs hT A cl ψ))

/-- `ψ` gives the body at the variable's kept part. -/
def gloop_kept (hF : ModalSys.Four = true) (hT : ModalSys.T = false)
    (hb : ModalSys.keepOnly = false) (A : VarType) (cl : List VarType)
    (ψ : WFF σ ((ctxOf (A :: cl)).kView none) 0) :
    Proof σ (ctxOf (A :: cl)).boxIn [ψ] (WFF.instantiate Ctx.NoSlots.slots (keptTup hF A cl)
      (WFF.mono ((ctxOf_le_append [A] cl).boxIn.insert (.bnd 0) _) (gloopBody hT A cl ψ))) := by
  refine Proof.conv (WFF.instantiate_ex_slotPair (ctxOf_le_append [A] cl).boxIn _ _).symm
    (Proof.ex_intro _ (lcTm hb A _ (ctxOf_ref_new A cl)) ?_)
  have e := WFF.instantiate_bodyRepl_pair (Ctx.Le.refl _) (keptTup (σ := σ) hF A cl)
    (WFF.mono ((ctxOf_le_append [A] cl).boxIn.insert (.bnd 0) _) (gpairAbs hT A cl ψ))
    (lcTm hb A _ (ctxOf_ref_new A cl))
  rw [WFF.mono_refl, WFF.mono_refl, Term.mono_refl, instantiate_gpairAbs hF hT hb A cl ψ] at e
  rw [e]
  exact Proof.lookup List.mem_cons_self

/-- `θ`, sending kept items to themselves, undoes the shift on a `□` view. -/
theorem box_shift_ren (hF : ModalSys.Four = true) (hb : ModalSys.keepOnly = false)
    {cl : List VarType} {Δ : Ctx} {θ : Subst σ Δ}
    (he : ∀ u W, (ctxOf cl).boxIn (.step u .keep) = some W → θ.at (.step u .keep) = .ren u)
    {v : VarSymb} {U : VarType} (hl : v.lastProj = false) (hv : (ctxOf cl).boxIn v = some U) :
    SubE.Sim U (θ.box.at (v.shift 0)) (.ren v) := by
  obtain ⟨u, s, rfl, -, W, hW⟩ := kView_item (k := none) hv
  cases s with
  | box =>
      obtain ⟨-, hu⟩ := Ctx.boxIn_box hv
      have hk := Ctx.boxIn_keep_of' hF hu rfl
      rw [VarSymb.shift_level_zero rfl, Subst.at_nonproj _ rfl]
      change SubE.Sim U (SubE.unbox (Subst.at _ _)) _
      rw [he _ _ hk]
      change SubE.Sim U (.ren (VarSymb.inner u)) _
      rw [show VarSymb.inner u = .step u .box by simp [VarSymb.inner, hb]]
      exact .refl _
  | keep =>
      rw [VarSymb.shift_level_zero rfl, Subst.box_at_keep, he _ _ hv]
      exact .refl _
  | dia => cases hv
  | fst => cases hl
  | snd => cases hl
  | here => cases hl

/-- Entries fixing kept items, with a slot set, undo the shift. -/
theorem keepFix_shift (hF : ModalSys.Four = true) (hb : ModalSys.keepOnly = false)
    {cl : List VarType} {Δ : Ctx} {f : VarSymb → LEnt σ} (hkf : KeepFix cl f)
    {e : SubE σ Δ} {v : VarSymb} {U : VarType} (hl : v.lastProj = false)
    (hv : (ctxOf cl).boxIn v = some U) :
    SubE.Sim U (((eS σ Δ f).set (.bnd 0) e).box.at (v.shift 0)) (.ren v) :=
  box_shift_ren hF hb (fun u W h => by
    rw [Subst.at_nonproj _ rfl, Subst.set_ne _ _ (fun e => by cases e), eS_item _ rfl,
      hkf u W h]
    rfl) hl hv

/-- ⭐**One necessity about the root's next variable is consistent with the root**: `◇¬` of the
    hat is refuted (`Proof.loop_tup`), so the transfer reflects `□ψ` at the variable's kept part,
    and the Henkin witness of its contents is the fresh root. -/
theorem gloop_one (hF : ModalSys.Four = true) (hV : ModalSys.Five = true)
    (hS : ModalSys.FourStrong = true) (hW : ModalSys.FourStrongW = true)
    (hT : ModalSys.T = false) {A : VarType} {cl l : List VarType}
    {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.IsMCS M) (hle : (ctxOf (A :: cl)).Le (ctxOf l))
    {f : VarSymb → LEnt σ} (hf : EntOk ((ctxOf cl).kView none) (ctxOf l) f)
    (hkf : KeepFix cl f)
    (htr : GTransfer M cl ((ctxOf_le_append [A] cl).trans hle) none (kDecl_none _) M f hf)
    {ψ : WFF σ ((ctxOf (A :: cl)).kView none) 0} (hψ : WFF.mono hle (.box ψ) ∈ M) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [VarType.lc A] l) '' M ∪
      {gloopArrow hT hle hf ψ}) := by
  have hb : ModalSys.keepOnly = false := by simp [ModalSys.keepOnly, hT]
  have hle₀ : (ctxOf cl).Le (ctxOf l) := (ctxOf_le_append [A] cl).trans hle
  have hTt := VarType.tup_kc A
  have hfrV := (Ctx.NoSlots.slots (Γ := (ctxOf cl).boxIn)).rootFresh (le_refl 0)
  have hO : Subst.Ok (ctxOf cl).boxIn (eS σ (ctxOf l) f) := ok_eS_kView hf
  have hC : Subst.Coh (eIdx f) (ctxOf cl).boxIn (eS σ (ctxOf l) f) := coh_eS_kView hf
  have hg' : ∀ p U, (ctxOf (A :: cl)).ref p = some U → U.keepable = true →
      (ctxOf l).boxIn.ref (.step p .keep) = some U :=
    fun _ _ h hk => Ctx.ref_keep_of' hF (hle.ref h) hk
  -- The step, through the transfer, at the variable's objects.
  have hE : WFF.mono hle₀ (.box (.all _ (.imp (.box (WFF.loopHat hF hTt (gloopBody hT A cl ψ)))
      (gloopBody hT A cl ψ)))) ∈ M := hM.closed ⟨[], (fun _ hx => by cases hx),
    Provable.monoCtx (Δs := []) hle₀ ⟨Proof.loop_tup hF hV hS hW hTt _⟩⟩
  have him := htr _ hE
  have eI := WFF.instantiate_subst_under (V := (ctxOf cl).boxIn) _ hO hC (objTup (σ := σ) hle)
    (.imp (.box (WFF.loopHat hF hTt (gloopBody hT A cl ψ))) (gloopBody hT A cl ψ))
  have h₂ := hM.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact him,
    ⟨Proof.conv eI (Proof.all_elim _ (objTup hle) (Proof.lookup List.mem_cons_self))⟩⟩
  -- Its hat is the body at the variable's kept part.
  have hθ₁ := Subst.ok_set (r := .bnd 0) (T := VarType.kc A) (e := .tm (objTup (σ := σ) hle)) hO rfl
  have hc₁ := Subst.coh_set (r := .bnd 0) (T := VarType.kc A) (e := .tm (objTup (σ := σ) hle))
    hO hC hfrV rfl
  have hk := read_kcTup hF _ hθ₁ hc₁ (fun _ _ h _ => hle.ref h) hg' A
    (.root (.free cl.length)) (ctxOf_ref_new A cl) (.root (.bnd 0))
    (Ctx.ref_insert_root (ctxOf cl).boxIn (.bnd 0) _) (Subst.set_root _ _ _)
  have ehat := WFF.subst_loopHat hF hTt _ hθ₁ hc₁ hle₀.boxIn _ hk
    (fun _ _ hl hv => keepFix_shift hF hb hkf hl hv) (gloopBody hT A cl ψ)
  have hbox : .box (WFF.instantiate Ctx.NoSlots.slots
      (kcTup (σ := σ) (fun p => .step p .keep) hg' A (.root (.free cl.length)) (ctxOf_ref_new A cl))
      (WFF.mono (hle₀.boxIn.insert (.bnd 0) _) (gloopBody hT A cl ψ))) ∈ M := by
    have hm := hM.closed ⟨[WFF.mono hle (.box ψ)], fun x hx => by
        rw [List.mem_singleton.mp hx]; exact hψ,
      Provable.monoCtx (Δs := [.box ψ]) hle ⟨Proof.K_box (gloop_kept hF hT hb A cl ψ)⟩⟩
    have e := WFF.mono_instantiate hle.boxIn Ctx.NoSlots.slots Ctx.NoSlots.slots
      (keptTup (σ := σ) hF A cl)
      (WFF.mono ((ctxOf_le_append [A] cl).boxIn.insert (.bnd 0) _) (gloopBody hT A cl ψ))
    rw [WFF.mono_mono, mono_kcTup _ _ _ hg'] at e
    exact (congrArg WFF.box e) ▸ hm
  have hex : WFF.subst _ _ _ _ _ _ (gloopBody hT A cl ψ) ∈ M :=
    hM.closed ⟨[_, _], fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h₂
        · rw [List.mem_singleton.mp hx]
          exact hbox,
      ⟨Proof.imp_elim (φ := .box _) (Proof.conv (congrArg (fun z => WFF.imp (.box z) _) ehat)
        (Proof.lookup List.mem_cons_self))
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩
  -- The Henkin witness of the contents is the fresh root.
  have hu := ctxOf_fresh (l := l) le_rfl
  have hex' := (WFF.subst_ex_slotPair (V := (ctxOf cl).boxIn) _ hO hC (gpairAbs hT A cl ψ)
    (objTup hle)) ▸ hex
  have hcons := henkin_consistent hM.1 (Theory.Derives.of_mem hex') hu
  have e₂ := (WFF.instantiate_eta_openFree l.length hu Ctx.NoSlots.slots Ctx.NoSlots.slots
    _).symm.trans ((WFF.instantiate_mono_pairSet (V := (ctxOf cl).boxIn)
      (ctxOf_le_append [VarType.lc A] l) (eS σ (ctxOf l) f) hO hC (objTup hle)
      (gpairAbs hT A cl ψ) _).trans (gloopArrow_eq hT hle hf ψ).symm)
  rw [← e₂]
  exact hcons

/-- ⭐**Committing the root's next variable.**  Everything the root necessitates about its
    variables up to the next one is consistent with the root, the next one's `□` contents going to
    a fresh variable. -/
theorem gloop_consistent (hF : ModalSys.Four = true) (hV : ModalSys.Five = true)
    (hS : ModalSys.FourStrong = true) (hW : ModalSys.FourStrongW = true)
    (hT : ModalSys.T = false) {A : VarType} {cl l : List VarType}
    {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.IsMCS M) (hle : (ctxOf (A :: cl)).Le (ctxOf l))
    {f : VarSymb → LEnt σ} (hf : EntOk ((ctxOf cl).kView none) (ctxOf l) f)
    (hkf : KeepFix cl f)
    (htr : GTransfer M cl ((ctxOf_le_append [A] cl).trans hle) none (kDecl_none _) M f hf) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [VarType.lc A] l) '' M ∪
      {φ | ∃ ψ, WFF.mono hle (.box ψ) ∈ M ∧ φ = gloopArrow hT hle hf ψ}) := by
  rintro ⟨L, hL, p⟩
  obtain ⟨ψ, hψ, hder⟩ := list_reduce (fun ψ => WFF.mono hle (.box ψ) ∈ M)
    (box_top_mem hM hle) (fun h₁ h₂ => box_and_mem hM hle h₁ h₂)
    (gloopArrow hT hle hf) (fun _ _ => rfl)
    (WFF.mono (ctxOf_le_append [VarType.lc A] l) '' M) L (fun δ hδ => (hL δ hδ).imp id id)
  exact gloop_one hF hV hS hW hT hM hle hf hkf htr hψ (derives_of_derives hder p)

/-! ## The step at the root -/

/-- ⭐The root's self-edge: a transfer of the theory into itself, fixing kept items. -/
def LoopData (t : NodeSt σ) (cl : List VarType) (f : VarSymb → LEnt σ) : Prop :=
  FwdData t t none cl f ∧ KeepFix cl f

/-- What committing the next variable `A` puts into the root. -/
noncomputable def gloopSet (t : NodeSt σ) (cl : List VarType) (f : VarSymb → LEnt σ)
    (A : VarType) : Set (WFF σ (ctxOf (VarType.lc A :: t.l)) 0) :=
  {φ | ∃ (hT : ModalSys.T = false) (hle : (ctxOf (A :: cl)).Le (ctxOf t.l))
    (hf : EntOk ((ctxOf cl).kView none) (ctxOf t.l) f)
    (ψ : WFF σ ((ctxOf (A :: cl)).kView none) 0),
    WFF.mono hle (.box ψ) ∈ t.M ∧ φ = gloopArrow hT hle hf ψ}

/-- The root grown by committing its next variable. -/
noncomputable def gloopStep (t : NodeSt σ) (cl : List VarType) (f : VarSymb → LEnt σ) :
    NodeSt σ :=
  ⟨VarType.lc (nextTy t.l cl) :: t.l,
    complete (WFF.mono (ctxOf_le_append [VarType.lc (nextTy t.l cl)] t.l) '' t.M ∪
      gloopSet t cl f (nextTy t.l cl))⟩

/-- The extended entries add no term. -/
theorem gloopF_inr {f : VarSymb → LEnt σ} {c z : ℕ} {v : VarSymb} {e : LTerm σ}
    (h : gloopF f c z v = .inr e) : f v = .inr e := by
  match v, h with
  | .root _, h => exact h
  | .step u s, h =>
      by_cases hrt : u.rt = .free c
      · cases s with
        | box =>
            rw [gloopF_box hrt] at h
            cases h
        | keep =>
            rw [gloopF_keep hrt] at h
            cases h
        | dia => exact h
        | fst => exact h
        | snd => exact h
        | here => exact h
      · rwa [gloopF_old hrt] at h

theorem keepFix_gloopF {A : VarType} {cl : List VarType} {f : VarSymb → LEnt σ}
    (hkf : KeepFix cl f) (z : ℕ) : KeepFix (A :: cl) (gloopF f cl.length z) := by
  intro v U hv
  by_cases hrt : v.rt = .free cl.length
  · exact gloopF_keep hrt
  · rw [gloopF_old hrt]
    exact hkf v U ((kView_old hrt none .keep).symm.trans hv)

/-- ⭐One step along the root's self-edge. -/
theorem gloopStep_ok (hF : ModalSys.Four = true) (hV : ModalSys.Five = true)
    (hS : ModalSys.FourStrong = true) (hW : ModalSys.FourStrongW = true)
    (hT : ModalSys.T = false) {t : NodeSt σ} {cl : List VarType} {f : VarSymb → LEnt σ}
    (hs : Theory.IsMCS t.M) (hd : LoopData t cl f) (hlt : cl.length < t.l.length) :
    Theory.IsMCS (gloopStep t cl f).M ∧ Grows t (gloopStep t cl f) ∧
      LoopData (gloopStep t cl f) (nextTy t.l cl :: cl) (gloopF f cl.length t.l.length) := by
  obtain ⟨⟨hsuf, _, hf, htr⟩, hkf⟩ := hd
  have hsuf' := suffix_next hsuf hlt
  have hle := ctxOf_le_of_suffix hsuf'
  have hcons := gloop_consistent hF hV hS hW hT hs hle hf hkf htr
  have hsub : WFF.mono (ctxOf_le_append [VarType.lc (nextTy t.l cl)] t.l) '' t.M ∪
      gloopSet t cl f (nextTy t.l cl) ⊆
        WFF.mono (ctxOf_le_append [VarType.lc (nextTy t.l cl)] t.l) '' t.M ∪
          {φ | ∃ ψ, WFF.mono hle (.box ψ) ∈ t.M ∧ φ = gloopArrow hT hle hf ψ} := by
    rintro φ (h | ⟨_, _, _, ψ, h₁, h₂⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ψ, h₁, h₂⟩
  obtain ⟨hS', hmcs⟩ := complete_spec (hcons.mono hsub)
  have hg : Grows t (gloopStep t cl f) := ⟨⟨[_], rfl⟩, fun φ hφ => hS' (Or.inl ⟨φ, hφ, rfl⟩)⟩
  have hfd : FwdData t (gloopStep t cl f) none (nextTy t.l cl :: cl)
      (gloopF f cl.length t.l.length) :=
    ⟨hsuf', kDecl_none _, entOk_gloopF hT hle hf, fun ψ hψ =>
      hS' (Or.inr ⟨hT, hle, hf, ψ, hψ, rfl⟩)⟩
  exact ⟨hmcs, hg, hfd.grow_src hs hmcs hg, keepFix_gloopF hkf _⟩

/-- ⭐**The base**: with nothing committed the self-edge is closed T (`Proof.closed_T`). -/
theorem loopData_nil (hB : ModalSys.B = true) (hF : ModalSys.Four = true) {t : NodeSt σ}
    (hs : Theory.IsMCS t.M) (hne : (WFF.box (Γ := ctxOf t.l) .bot).neg ∈ t.M)
    (f : VarSymb → LEnt σ) : LoopData t [] f := by
  have hf : EntOk ((ctxOf []).kView none) (ctxOf t.l) f := fun v T _ hv => by
    rw [show (ctxOf []).kView none v = none from boxIn_empty v] at hv
    cases hv
  refine ⟨⟨List.nil_suffix, kDecl_none _, hf, fun ψ hψ => ?_⟩, fun v U hv => ?_⟩
  · have hψ' : WFF.mono (ctxOf_le_of_suffix List.nil_suffix) (.box ψ) ∈ t.M := hψ
    rw [eq_closed_boxIn_empty ψ] at hψ' ⊢
    rw [WFF.closed, WFF.subst_mono_empty _ (Ctx.empty_le _)]
    change WFF.box (WFF.mono _ (WFF.mono _ _)) ∈ t.M at hψ'
    rw [WFF.mono_mono] at hψ'
    exact hs.closed ⟨[_, _], fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hne
        · rw [List.mem_singleton.mp hx]
          exact hψ',
      ⟨Proof.closed_T hB hF _ (Proof.lookup List.mem_cons_self)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩
  · rw [show (ctxOf []).boxIn (.step v .keep) = none from boxIn_empty _] at hv
    cases hv

end GArrow

end V12M
