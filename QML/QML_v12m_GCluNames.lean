import QML.QML_v12m_GLimit

/-!
# QML v12m — 5 on the growing tree: names are unique

Names by origin (`docs/v12-modal-extensions.md` §3 5, (N1)): under 5 every object of a child
has exactly one origin, so the cluster model can share its modal carriers with `keep` the
identity.  This file proves the invariant behind it: along every edge, a child's address is
named by at most one committed kept parent item.

Naming is by an address (`.inl z`) or by its η-term (`.inr η z`).  η-expansion is injective
exactly at the types with a base or a possible part (`VarType.etaInj`); at the others (built from
`𝟙`, `×` and `□`) every world has one object, so names need not be unique there.

* `NamesE`, `KeepInj`, `GNetSt.NamesInj`;
* `VarType.etaInj`, `eta_inj`, `gPath_keep_inj`, `names_ref`.
-/

namespace V12M

/-- The types at which η-expansion is injective: those with a base or a possible part. -/
def VarType.etaInj : VarType → Bool
  | .Var => true
  | .VTypeOne => false
  | .VTypeProd A B => A.etaInj || B.etaInj
  | .VTypeBox A => A.etaInj
  | .VTypeDia _ => true

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature}

/-- An entry **names** `z`: it is `z`, or `z`'s η-term. -/
def NamesE (e : LEnt σ) (z : VarSymb) : Prop :=
  e = .inl z ∨ ∃ (L : List VarType) (T : VarType) (hz : (ctxOf L).ref z = some T),
    e = .inr ⟨L, T, _, Term.eta z T hz⟩

/-- An edge names a child address, at an η-faithful type, by at most one committed kept parent
    item. -/
def KeepInj (cl : List VarType) (k : Option VarSymb) (f : VarSymb → LEnt σ) : Prop :=
  ∀ v v' U U' z, (ctxOf cl).kView k (.step v .keep) = some U →
    (ctxOf cl).kView k (.step v' .keep) = some U' → U.etaInj = true → U'.etaInj = true →
    NamesE (f (.step v .keep)) z → NamesE (f (.step v' .keep)) z → v = v'

/-- ⭐**Names are unique** along every edge of a network. -/
def GNetSt.NamesInj (N : GNetSt σ) : Prop :=
  ∀ c p, N.Live (c :: p) → KeepInj (N.fcl (c :: p)) (N.kind (c :: p)) (N.fmap (c :: p))

/-! ## Injectivity of the naming maps -/

theorem VarSymb.inner_inj_box {w w' : VarSymb} (hk : ModalSys.keepOnly = false)
    (h : w.inner = w'.inner) : w = w' := by
  rw [VarSymb.inner_box hk, VarSymb.inner_box hk] at h
  exact (VarSymb.step.inj h).1

theorem sig_pair_inj {Γ : Ctx} {A B : VarType} {a a' : Ann A} {b b' : Ann B}
    {s : Term σ Γ A a} {s' : Term σ Γ A a'} {t : Term σ Γ B b} {t' : Term σ Γ B b'}
    (h : (⟨_, Term.pair s t⟩ : Σ c, Term σ Γ (.VTypeProd A B) c) = ⟨_, Term.pair s' t'⟩) :
    (⟨_, s⟩ : Σ c, Term σ Γ A c) = ⟨_, s'⟩ ∧ (⟨_, t⟩ : Σ c, Term σ Γ B c) = ⟨_, t'⟩ := by
  cases h
  exact ⟨rfl, rfl⟩

theorem sig_boxtm_inj {Γ : Ctx} {A : VarType} {a a' : Ann A}
    {s : Term σ Γ.boxIn A a} {s' : Term σ Γ.boxIn A a'}
    (h : (⟨_, Term.boxtm s⟩ : Σ c, Term σ Γ (.VTypeBox A) c) = ⟨_, Term.boxtm s'⟩) :
    (⟨_, s⟩ : Σ c, Term σ Γ.boxIn A c) = ⟨_, s'⟩ := by
  cases h
  rfl

/-- ⭐η-expansion is injective at an η-faithful type. -/
theorem eta_inj (hk : ModalSys.keepOnly = false) :
    ∀ {Γ : Ctx} (T : VarType), T.etaInj = true → ∀ {w w' : VarSymb}
      (h : Γ.ref w = some T) (h' : Γ.ref w' = some T),
      (⟨_, Term.eta (σ := σ) w T h⟩ : Σ a, Term σ Γ T a) = ⟨_, Term.eta w' T h'⟩ → w = w'
  | _, .Var, _, _, _, _, _, e => by
      have := eq_of_heq (Sigma.mk.inj e).2
      injection this
  | _, .VTypeOne, hT, _, _, _, _, _ => by cases hT
  | Γ, .VTypeProd A B, hT, w, w', h, h', e => by
      have e' : (⟨_, Term.pair (Term.eta (σ := σ) (.step w .fst) A (Ctx.ref_fst_of h))
            (Term.eta (.step w .snd) B (Ctx.ref_snd_of h))⟩ : Σ c, Term σ Γ (.VTypeProd A B) c) =
          ⟨_, Term.pair (Term.eta (.step w' .fst) A (Ctx.ref_fst_of h'))
            (Term.eta (.step w' .snd) B (Ctx.ref_snd_of h'))⟩ := e
      obtain ⟨e₁, e₂⟩ := sig_pair_inj e'
      simp only [VarType.etaInj, Bool.or_eq_true] at hT
      rcases hT with hA | hB
      · exact (VarSymb.step.inj (eta_inj hk A hA _ _ e₁)).1
      · exact (VarSymb.step.inj (eta_inj hk B hB _ _ e₂)).1
  | Γ, .VTypeBox A, hT, w, w', h, h', e => by
      have e' : (⟨_, Term.boxtm (Term.eta (σ := σ) w.inner A (Ctx.ref_inner h))⟩ :
          Σ c, Term σ Γ (.VTypeBox A) c) =
          ⟨_, Term.boxtm (Term.eta w'.inner A (Ctx.ref_inner h'))⟩ := e
      exact VarSymb.inner_inj_box hk (eta_inj hk A hT _ _ (sig_boxtm_inj e'))
  | _, .VTypeDia A, _, w, w', h, h', e => by
      have := (Sigma.mk.inj e).1
      injection this

/-- With T off, a keepable type has no projections. -/
theorem step_proj_keepable (hT : ModalSys.T = false) {U : VarType} (hU : U.keepable = true)
    {s : Step} (hs : s.isProj = true) : U.step s = none := by
  cases U <;> cases s <;> simp_all [VarType.step, VarType.keepable, Step.isProj]

theorem walk_cons_some {U A : VarType} {s : Step} {q : List Step}
    (h : U.walk (s :: q) = some A) : ∃ U₁, U.step s = some U₁ ∧ U₁.walk q = some A := by
  simp only [VarType.walk] at h
  cases h₁ : U.step s with
  | none => rw [h₁] at h; cases h
  | some U₁ => rw [h₁] at h; exact ⟨U₁, rfl, h⟩

/-- ⭐**Kept items' paths are told apart by `gPath`** (T off): two projection paths to keepable
    types with one kept image are one path. -/
theorem gPath_keep_inj (hT : ModalSys.T = false) :
    ∀ (U : VarType) (p p' : List Step), PPath p → PPath p' → ∀ {A A' : VarType},
      U.walk p = some A → U.walk p' = some A' → A.keepable = true → A'.keepable = true →
      gPath U p .keep = gPath U p' .keep → p = p'
  | _, [], [], _, _, _, _, _, _, _, _, _ => rfl
  | U, [], s :: q, _, hp', A, A', hw, hw', hA, _, _ => by
      obtain rfl : U = A := Option.some.inj hw
      obtain ⟨U₁, h₁, -⟩ := walk_cons_some hw'
      rw [step_proj_keepable hT hA (hp' s List.mem_cons_self)] at h₁
      cases h₁
  | U, s :: q, [], hp, _, A, A', hw, hw', _, hA', _ => by
      obtain rfl : U = A' := Option.some.inj hw'
      obtain ⟨U₁, h₁, -⟩ := walk_cons_some hw
      rw [step_proj_keepable hT hA' (hp s List.mem_cons_self)] at h₁
      cases h₁
  | U, s :: q, s' :: q', hp, hp', A, A', hw, hw', hA, hA', e => by
      obtain ⟨U₁, h₁, hq⟩ := walk_cons_some hw
      obtain ⟨U₂, h₂, hq'⟩ := walk_cons_some hw'
      have hpq : PPath q := fun x hx => hp x (List.mem_cons_of_mem _ hx)
      have hpq' : PPath q' := fun x hx => hp' x (List.mem_cons_of_mem _ hx)
      cases U with
      | VTypeProd B C =>
          cases s <;> cases s' <;> simp only [VarType.step] at h₁ h₂
          all_goals first
            | (cases h₁; done)
            | (cases h₂; done)
            | (cases h₁; cases h₂; simp only [gPath, List.cons.injEq] at e
               first
                 | exact absurd e.1 (by decide)
                 | rw [gPath_keep_inj hT _ q q' hpq hpq' hq hq' hA hA' e.2])
      | VTypeBox B =>
          cases s <;> simp only [VarType.step] at h₁
          all_goals first
            | (cases h₁; done)
            | (simp [hT] at h₁; done)
            | exact absurd (hp _ List.mem_cons_self) (by decide)
      | VTypeDia B =>
          cases s <;> simp only [VarType.step] at h₁
          all_goals first
            | (cases h₁; done)
            | exact absurd (hp _ List.mem_cons_self) (by decide)
      | Var => cases s <;> simp [VarType.step] at h₁
      | VTypeOne => cases s <;> simp [VarType.step] at h₁

/-- What an entry names, it declares, at the entry's type. -/
theorem names_ref {Δ : Ctx} {e : LEnt σ} {U : VarType} (he : (entOf Δ e).OkRef U) {z : VarSymb}
    (hn : NamesE e z) : Δ.ref z = some U := by
  rcases hn with rfl | ⟨L, T, hz, rfl⟩
  · exact he
  · have hL : (ctxOf L).Le Δ := by
      by_contra hn
      rw [show entOf Δ (.inr ⟨L, T, _, Term.eta z T hz⟩) = .hide from dif_neg hn] at he
      exact he
    rw [show entOf Δ (.inr ⟨L, T, _, Term.eta z T hz⟩) = .tm (Term.mono hL (Term.eta z T hz))
      from dif_pos hL] at he
    cases he
    exact hL.ref hz

theorem namesE_inl {w z : VarSymb} : NamesE (σ := σ) (.inl w) z ↔ w = z := by
  constructor
  · rintro (h | ⟨_, _, _, h⟩)
    · exact Sum.inl.inj h
    · cases h
  · rintro rfl
    exact Or.inl rfl

omit [ModalSys] in
theorem root_ext_inj {r r' : Root} {g g' : List Step}
    (h : (VarSymb.root r).ext g = (VarSymb.root r').ext g') : r = r' ∧ g = g' := by
  have h₁ := congrArg VarSymb.rt h
  have h₂ := congrArg VarSymb.path h
  rw [VarSymb.ext_rt, VarSymb.ext_rt] at h₁
  rw [VarSymb.ext_path, VarSymb.ext_path] at h₂
  exact ⟨h₁, by simpa [VarSymb.path] using h₂⟩

/-- A kept item's address: a declared root and a projection path walking to its keepable type. -/
theorem keep_item_root {l : List VarType} {u : VarSymb} {U : VarType}
    (h : (ctxOf l).boxIn (.step u .keep) = some U) :
    ∃ r, u = (VarSymb.root (.free r)).ext u.path ∧ PPath u.path ∧
      (rootTy l r).walk u.path = some U ∧ U.keepable = true := by
  obtain ⟨-, hu, hk⟩ := Ctx.boxIn_keep h
  obtain ⟨hpp, -⟩ := reach_ppath hu
  obtain ⟨r, hr, -, hroot⟩ := ref_rt hu
  have he : u = (VarSymb.root (.free r)).ext u.path := by
    rw [← hr]
    exact VarSymb.eq_root_ext u
  refine ⟨r, he, hpp, ?_, hk⟩
  have := Ctx.ref_ext_ppath (ctxOf l) u.path (.root u.rt) hpp
  rw [← VarSymb.eq_root_ext u, hu, hroot] at this
  simpa using this.symm

/-- ⭐**A child's naming map is injective on kept items** (T off): `gImg` keeps the root and moves
    the path by `gPath`. -/
theorem keepInj_gchild (hT : ModalSys.T = false) (l : List VarType) (kd : Option VarSymb) :
    KeepInj l kd (ofRen (σ := σ) (gchildMap l kd)) := by
  intro v v' U U' z hv hv' _ _ hn hn'
  have hb := kView_boxIn' hv (by rintro ⟨_, _, _, h⟩; cases h)
  have hb' := kView_boxIn' hv' (by rintro ⟨_, _, _, h⟩; cases h)
  rw [ofRen, namesE_inl] at hn hn'
  have hg : ∀ u : VarSymb, gchildMap l kd (.step u .keep) = gImg l id (.step u .keep) := by
    intro u
    cases kd with
    | none => rfl
    | some x =>
        change (if VarSymb.step u .keep = .step x .dia then _ else _) = _
        rw [if_neg (by simp)]
  rw [hg] at hn hn'
  obtain ⟨r, hr, hp, hw, hk⟩ := keep_item_root hb
  obtain ⟨r', hr', hp', hw', hk'⟩ := keep_item_root hb'
  have e := hn.trans hn'.symm
  rw [hr, hr'] at e
  simp only [gImg, VarSymb.ext_rt, VarSymb.rt, VarSymb.ext_path, VarSymb.path,
    List.nil_append, id] at e
  obtain ⟨er, eg⟩ := root_ext_inj e
  cases er
  rw [hr, hr', gPath_keep_inj hT _ _ _ hp hp' hw hw' hk hk' eg]

namespace GNetSt

variable {N : GNetSt σ}

theorem NamesInj.setSt (hI : N.NamesInj) (s : Node) (t : NodeSt σ) : (N.setSt s t).NamesInj :=
  fun c p hk => hI c p ((live_setSt N s t _).mp hk)

theorem NamesInj.setFwd (hI : N.NamesInj) {k : Node} {cl : List VarType}
    {f : VarSymb → LEnt σ} (hk : KeepInj cl (N.kind k) f) : (N.setFwd k cl f).NamesInj := by
  intro c p hl
  rw [live_setFwd] at hl
  by_cases he : (c :: p : Node) = k
  · subst he
    simp only [GNetSt.setFwd, Function.update_self]
    exact hk
  · simp only [GNetSt.setFwd, Function.update_of_ne he]
    exact hI c p hl

theorem NamesInj.henk (hI : N.NamesInj) (s : Node)
    (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : (N.henk s o).NamesInj := by
  obtain ⟨l, φ⟩ := o
  simp only [GNetSt.henk]
  split_ifs
  · split
    · split_ifs
      · exact hI.setSt _ _
      · exact hI
    · split_ifs
      · exact hI.setSt _ _
      · exact hI
    · exact hI
  · exact hI

theorem NamesInj.newChild (hI : N.NamesInj) {s : Node} (hs : N.Live s) (kd : Option VarSymb)
    (t : NodeSt σ) {f : VarSymb → LEnt σ} (hk : KeepInj (N.st s).l kd f) :
    (N.newChild s kd t f).NamesInj := by
  have hks : (N.nch s :: s : Node) ≠ s := NetSt.ne_parent _ s
  intro c p hl
  rcases (live_newChild hs kd t f _).mp hl with hl | he
  · have hne : (c :: p : Node) ≠ N.nch s :: s := fun h => not_live_new s (h ▸ hl)
    change KeepInj (Function.update N.fcl _ (N.st s).l (c :: p))
      (Function.update N.kind _ kd (c :: p)) (Function.update N.fmap _ f (c :: p))
    simp only [Function.update_of_ne hne]
    exact hI c p hl
  · rw [he]
    change KeepInj (Function.update N.fcl _ (N.st s).l _) (Function.update N.kind _ kd _)
      (Function.update N.fmap _ f _)
    simp only [Function.update_self]
    exact hk

theorem NamesInj.mkChild (hT : ModalSys.T = false) (hF : ModalSys.Four = true)
    (hI : N.NamesInj) {s : Node} (hs : N.Live s)
    (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : (N.mkChild hF s o).NamesInj := by
  obtain ⟨l, φ⟩ := o
  simp only [GNetSt.mkChild]
  split_ifs
  · split
    · split_ifs
      · exact hI
      · exact hI.newChild hs _ _ (keepInj_gchild hT _ _)
    · split_ifs
      · split
        · exact hI.newChild hs _ _ (keepInj_gchild hT _ _)
        · exact hI
      · exact hI
    · exact hI
  · exact hI

end GNetSt

/-- ⭐**Realising forward keeps names unique** (T off): the new variable's kept items go to
    distinct addresses under the child's fresh variable, which no older entry names. -/
theorem keepInj_gextF (hT : ModalSys.T = false) {cl : List VarType} {k : Option VarSymb}
    {f : VarSymb → LEnt σ} {tl : List VarType} (hkd : KOld k cl.length)
    (hf : EntOk ((ctxOf cl).kView k) (ctxOf tl) f) (hold : KeepInj cl k f) (A : VarType) :
    KeepInj (A :: cl) k (gextF f A cl.length tl.length) := by
  intro v v' U U' z hv hv' hU hU' hn hn'
  have fresh : ∀ {w : VarSymb} {W : VarType} {g : List Step},
      (ctxOf cl).kView k (.step w .keep) = some W → w.rt ≠ .free cl.length →
      NamesE (f (.step w .keep)) ((VarSymb.root (.free tl.length)).ext g) → False := by
    intro w W g hw _ hnw
    obtain ⟨r, hr, hlt, -⟩ := ref_rt (names_ref (hf _ _ rfl hw) hnw)
    rw [VarSymb.ext_rt] at hr
    cases hr
    omega
  by_cases h₁ : v.rt = .free cl.length <;> by_cases h₂ : v'.rt = .free cl.length
  · rw [gextF_new h₁, namesE_inl] at hn
    rw [gextF_new h₂, namesE_inl] at hn'
    obtain ⟨r, hr, hp, hw, hk⟩ := keep_item_root (kView_boxIn hkd h₁ hv)
    obtain ⟨r', hr', hp', hw', hk'⟩ := keep_item_root (kView_boxIn hkd h₂ hv')
    have hrr : r = cl.length := by
      have := congrArg VarSymb.rt hr
      rw [VarSymb.ext_rt, h₁] at this
      exact (Root.free.inj this).symm
    have hrr' : r' = cl.length := by
      have := congrArg VarSymb.rt hr'
      rw [VarSymb.ext_rt, h₂] at this
      exact (Root.free.inj this).symm
    subst hrr hrr'
    rw [rootTy_new] at hw hw'
    obtain ⟨-, eg⟩ := root_ext_inj (hn.trans hn'.symm)
    rw [hr, hr', gPath_keep_inj hT A _ _ hp hp' hw hw' hk hk' eg]
  · rw [gextF_new h₁, namesE_inl] at hn
    rw [gextF_old h₂] at hn'
    rw [kView_old h₂] at hv'
    exact (fresh hv' h₂ (hn ▸ hn')).elim
  · rw [gextF_old h₁] at hn
    rw [gextF_new h₂, namesE_inl] at hn'
    rw [kView_old h₁] at hv
    exact (fresh hv h₁ (hn' ▸ hn)).elim
  · rw [gextF_old h₁] at hn
    rw [gextF_old h₂] at hn'
    rw [kView_old h₁] at hv
    rw [kView_old h₂] at hv'
    exact hold v v' U U' z hv hv' hU hU' hn hn'

namespace GNetSt

variable {N : GNetSt σ}

theorem NamesInj.realF (hT : ModalSys.T = false) (hF : ModalSys.Four = true) (hN : N.Good)
    (hI : N.NamesInj) {k : Node} (hk : N.Live k) : (N.realF hF k).NamesInj := by
  match k with
  | [] => exact hI
  | c :: p =>
      simp only [GNetSt.realF]
      split_ifs
      · obtain ⟨_, hkd, hf, _⟩ := hN.fwd c p hk
        exact (hI.setSt _ _).setFwd
          (keepInj_gextF hT (kOld_of_kDecl hkd) hf (hI c p hk) _)
      · exact hI

theorem NamesInj.iterate_realF (hT : ModalSys.T = false) (hF : ModalSys.Four = true) (k : Node) :
    ∀ (j : ℕ) {N : GNetSt σ}, N.Good → N.Live k → N.NamesInj →
      ((fun N' => N'.realF hF k)^[j] N).NamesInj
  | 0, _, _, _, hI => hI
  | j + 1, _, hN, hk, hI => by
      rw [Function.iterate_succ_apply]
      exact NamesInj.iterate_realF hT hF k j (hN.realF hF hk)
        ((live_of_nch (nch_realF hF _ k) k).mpr hk) (hI.realF hT hF hN hk)

theorem NamesInj.catchUp (hT : ModalSys.T = false) (hF : ModalSys.Four = true) (hN : N.Good)
    (hI : N.NamesInj) {k : Node} (hk : N.Live k) : (N.catchUp hF k).NamesInj := by
  match k with
  | [] => exact hI
  | c :: p => exact NamesInj.iterate_realF hT hF (c :: p) _ hN hk hI

end GNetSt

/-- The new root of a lift is its only new kept item: a liftable type has no projections (T
    off). -/
theorem lift_item_root (hT : ModalSys.T = false) {cl : List VarType} {k : Option VarSymb}
    {T : VarType} (hkd : KOld k cl.length) (hl : T.liftable = true) {v : VarSymb} {U : VarType}
    (h₁ : v.rt = .free cl.length) (hv : (ctxOf (T :: cl)).kView k (.step v .keep) = some U) :
    v = .root (.free cl.length) ∧ U = T := by
  obtain ⟨r, hr, hp, hw, hk⟩ := keep_item_root (kView_boxIn hkd h₁ hv)
  have hrr : r = cl.length := by
    have := congrArg VarSymb.rt hr
    rw [VarSymb.ext_rt, h₁] at this
    exact (Root.free.inj this).symm
  subst hrr
  rw [rootTy_new] at hw
  cases hpath : v.path with
  | nil =>
      rw [hpath] at hr hw
      exact ⟨hr, (Option.some.inj hw).symm⟩
  | cons s q =>
      rw [hpath] at hw hp
      obtain ⟨U₁, h₁', -⟩ := walk_cons_some hw
      rw [step_proj_keepable hT (VarType.keepable_of_liftable hl) (hp s List.mem_cons_self)]
        at h₁'
      cases h₁'

/-- ⭐**A guarded lift keeps names unique** (T off): the new root's kept item names only the
    lifted address, which no committed item named. -/
theorem keepInj_gliftG (hT : ModalSys.T = false) (hk : ModalSys.keepOnly = false)
    {cl : List VarType} {k : Option VarSymb} {f : VarSymb → LEnt σ} (hold : KeepInj cl k f)
    (hkd : KOld k cl.length) {T : VarType} (hl : T.liftable = true) {L : List VarType}
    {z : VarSymb} (hz : (ctxOf L).ref z = some T)
    (hfresh : ¬ ∃ v U, (ctxOf cl).kView k (.step v .keep) = some U ∧
      NamesE (f (.step v .keep)) z) (ρ : Root) :
    KeepInj (T :: cl) k (gliftG f T cl.length (.inr ⟨L, T, _, Term.eta (σ := σ) z T hz⟩) ρ) := by
  have hκ : ∀ w, NamesE (σ := σ) (.inr ⟨L, T, _, Term.eta z T hz⟩) w → T.etaInj = true →
      w = z := by
    rintro w (he | ⟨L', T', hw, he⟩) hTe
    · cases he
    · have h1 := Sigma.mk.inj (Sum.inr.inj he)
      obtain ⟨rfl, h2⟩ := h1
      obtain ⟨rfl, h4⟩ := Sigma.mk.inj (eq_of_heq h2)
      exact (eta_inj hk T hTe hz hw (eq_of_heq h4)).symm
  intro v v' U U' w hv hv' hU hU' hn hn'
  by_cases h₁ : v.rt = .free cl.length <;> by_cases h₂ : v'.rt = .free cl.length
  · rw [(lift_item_root hT hkd hl h₁ hv).1, (lift_item_root hT hkd hl h₂ hv').1]
  · obtain ⟨rfl, rfl⟩ := lift_item_root hT hkd hl h₁ hv
    rw [gliftG_keep] at hn
    rw [gliftG_old h₂] at hn'
    rw [kView_old h₂] at hv'
    obtain rfl := hκ w hn hU
    exact (hfresh ⟨v', U', hv', hn'⟩).elim
  · obtain ⟨rfl, rfl⟩ := lift_item_root hT hkd hl h₂ hv'
    rw [gliftG_keep] at hn'
    rw [gliftG_old h₁] at hn
    rw [kView_old h₁] at hv
    obtain rfl := hκ w hn' hU'
    exact (hfresh ⟨v, U, hv, hn⟩).elim
  · rw [gliftG_old h₁] at hn
    rw [gliftG_old h₂] at hn'
    rw [kView_old h₁] at hv
    rw [kView_old h₂] at hv'
    exact hold v v' U U' w hv hv' hU hU' hn hn'

namespace GNetSt

variable {N : GNetSt σ}

theorem NamesInj.lift (hV : ModalSys.Five = true) (hT : ModalSys.T = false)
    (hF : ModalSys.Four = true) (hN : N.Good) (hI : N.NamesInj) {k : Node} (hk : N.Live k)
    (o : LTerm σ) : (N.lift hF k o).NamesInj := by
  have hko : ModalSys.keepOnly = false := by simp [ModalSys.keepOnly, hT]
  match k, o with
  | [], _ => exact hI
  | c :: p, ⟨l, T, a, t⟩ =>
      simp only [GNetSt.lift]
      split_ifs with hcl h hl hv
      · obtain ⟨z, T', hz, he, hnk⟩ := hv.2 hV
        obtain ⟨-, h2⟩ := Sigma.mk.inj he
        obtain ⟨rfl, h3⟩ := Sigma.mk.inj (eq_of_heq h2)
        obtain ⟨rfl, h4⟩ := Sigma.mk.inj (eq_of_heq h3)
        have hz' : (ctxOf l).ref z = some T := hz
        have ht : t = Term.eta z T hz' := eq_of_heq h4
        clear h4 h3 h2 he hz
        subst ht
        obtain ⟨_, hkd, _, _⟩ := hN.fwd c p hk
        rw [hcl] at hkd
        have hold := hI c p hk
        rw [hcl] at hold
        refine ((hI.setSt _ _).setSt _ _).setFwd ?_
        change KeepInj (T :: (N.st p).l) (N.kind (c :: p)) (gliftG (N.fmap (c :: p)) T
          (N.st p).l.length (.inr ⟨(N.st (c :: p)).l, T, _,
            Term.mono (ctxOf_le_of_suffix h) (Term.eta z T hz')⟩)
          (.free (N.st (c :: p)).l.length))
        rw [Term.mono_eta]
        refine keepInj_gliftG hT hko hold (kOld_of_kDecl hkd) hl _ ?_ _
        rintro ⟨v, U, hv', hn⟩
        exact hnk ⟨v, U, hcl ▸ hv', hn⟩
      all_goals exact hI

end GNetSt

namespace GNetSt

variable {N : GNetSt σ}

theorem NamesInj.applyOp (hV : ModalSys.Five = true) (hT : ModalSys.T = false)
    (hF : ModalSys.Four = true) (hN : N.Good) (hI : N.NamesInj) (o : GOp σ) :
    (N.applyOp hF o).NamesInj := by
  rcases o with ⟨s, o⟩ | ⟨s, o⟩ | k | ⟨k, n⟩
  · simp only [GNetSt.applyOp]
    split_ifs
    · exact hI.henk s o
    · exact hI
  · simp only [GNetSt.applyOp]
    split_ifs with hs
    · exact hI.mkChild hT hF hs o
    · exact hI
  · simp only [GNetSt.applyOp]
    split_ifs with hk
    · exact hI.realF hT hF hN hk
    · exact hI
  · simp only [GNetSt.applyOp]
    split_ifs with hk
    · obtain ⟨hN', hk', -⟩ := hN.catchUp hF hk
      exact (hI.catchUp hT hF hN hk).lift hV hT hF hN' hk' n
    · exact hI

theorem namesInj_init {l₀ : List VarType} (M₀ : Set (WFF σ (ctxOf l₀) 0)) :
    (init M₀).NamesInj := fun _ _ hk => nomatch init_live hk

end GNetSt

/-- ⭐**Names are unique along every edge of every network of the chain** (under 5, T off). -/
theorem namesInj_gnet [Countable σ.FuncSyms] [Countable σ.RelSyms] (hV : ModalSys.Five = true)
    (hT : ModalSys.T = false) (hF : ModalSys.Four = true) {l₀ : List VarType}
    {M₀ : Set (WFF σ (ctxOf l₀) 0)} (hM₀ : Theory.IsMCS M₀) : ∀ n, (gnet hF M₀ n).NamesInj
  | 0 => GNetSt.namesInj_init M₀
  | n + 1 =>
      (namesInj_gnet hV hT hF hM₀ n).applyOp hV hT hF (good_gnet hF hM₀ n) (gsched n)

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-- ⭐**Names are unique in the limit** (`docs/v12-modal-extensions.md` §3 5, (N1)): two kept
    items of a parent that name one address of the child, at an η-faithful type, are one item. -/
theorem names_unique (hV : ModalSys.Five = true) (hT : ModalSys.T = false)
    (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) {i i' : ℕ} {v v' z : VarSymb}
    {U U' : VarType} (hv : (ctxOf (glat s i)).ref v = some U) (hkp : U.keepable = true)
    (hv' : (ctxOf (glat s i')).ref v' = some U') (hkp' : U'.keepable = true)
    (hU : U.etaInj = true) (hU' : U'.etaInj = true)
    (hn : NamesE (fmapL hF M₀ t.1 (.step v .keep)) z)
    (hn' : NamesE (fmapL hF M₀ t.1 (.step v' .keep)) z) : v = v' := by
  obtain ⟨c, hc⟩ := h
  set i₀ := max i i'
  have hsuf : ∀ {j : ℕ}, j ≤ i₀ → glat s j <:+ glat s i₀ := fun hj =>
    gnet_lang_suffix hF hM₀ (by omega) (live_gbirth hF hM₀ s.2 (Nat.le_add_right _ _))
  have hv₀ := (ctxOf_le_of_suffix (hsuf (le_max_left i i'))).ref hv
  have hv₀' := (ctxOf_le_of_suffix (hsuf (le_max_right i i'))).ref hv'
  have hkv : (ctxOf (glat s i₀)).kView (lkd t) (.step v .keep) = some U :=
    (Ctx.le_boxIn_kView _ _) _ _ (Ctx.boxIn_keep_of' hF hv₀ hkp)
  have hkv' : (ctxOf (glat s i₀)).kView (lkd t) (.step v' .keep) = some U' :=
    (Ctx.le_boxIn_kView _ _) _ _ (Ctx.boxIn_keep_of' hF hv₀' hkp')
  obtain ⟨hfcl, hag, -⟩ := gfwd_at hM₀ hc i₀
  have hlive : (gnet hF M₀ (grnd s t i₀)).Live (c :: s.1) :=
    hc ▸ live_gbirth hF hM₀ t.2 (Nat.le_add_right _ _)
  have hkind : (gnet hF M₀ (grnd s t i₀)).kind (c :: s.1) = lkd t :=
    hc ▸ kind_at hM₀ t (Nat.le_add_right _ _)
  have hinj := namesInj_gnet hV hT hF hM₀ (grnd s t i₀) c s.1 hlive
  rw [hkind, ← hc] at hinj
  rw [← hag _ _ hkv] at hn
  rw [← hag _ _ hkv'] at hn'
  exact hinj v v' U U' z (((ctxOf_le_of_suffix hfcl).kView _) _ _ hkv)
    (((ctxOf_le_of_suffix hfcl).kView _) _ _ hkv') hU hU' hn hn'

end GArrow

end V12M
