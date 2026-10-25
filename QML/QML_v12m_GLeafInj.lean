import QML.QML_v12m_GLeaf
import QML.QML_v12m_GCanonDom

/-!
# QML v12m — the growing tree: labels are injective

The second half of the leaf calculus (`docs/v12-modal-extensions.md` §3 4, "The leaf calculus,
revised plan"), under T.  In a pushed canonical environment
(`Pushed`) the `◇` addresses are of two kinds:
* *root-level* (and level-free) ones, labelled by a root and a path spelling the address
  (`Pushed.rootSh`, `cEnv_dia_generic`);
* *keep-first* ones `u.keep.rest`, labelled by families.  These are compared along a **late
  edge**, a child born after the stage (`glate`), whose entries are all images.  Wrapped into a
  term of the `□` view (`Wr.wrap`), an address's label is a term's shape; read along the edge it
  is the shape of the term's translation (`unT_termShp`, `comp_pull`, `termShp_subst`), whose
  annotation records the address's image.

* `Wr`, `Wr.wrap`, `pushAlong`: wrapping a term of a chain of views into the `□` view;
* `KF`, `KLe`, ⭐`Pushed.kpart`: the keep-first part of a pushed environment is a chain of views
  from the `□` view.
-/

namespace V12M

variable [ModalSys]

/-! ## Wrapping terms into the `□` view -/

/-- ⭐A chain of views entered from the `□` view of `Γ`. -/
inductive Wr (Γ : Ctx) : Ctx → Type
  | nil : Wr Γ Γ.boxIn
  | box {Δ : Ctx} : Wr Γ Δ → Wr Γ Δ.boxIn
  | dia {Δ : Ctx} : Wr Γ Δ → (x : VarSymb) → (X : VarType) → Δ.ref x = some (.VTypeDia X) →
      Wr Γ (Δ.diaIn x)

namespace Wr

variable {Γ : Ctx}

/-- The views entered after the `□` view. -/
def len : {Δ : Ctx} → Wr Γ Δ → ℕ
  | _, .nil => 0
  | _, .box w => w.len + 1
  | _, .dia w _ _ _ => w.len + 1

/-- The type of a wrapped term. -/
def ty : {Δ : Ctx} → Wr Γ Δ → VarType → VarType
  | _, .nil, A => A
  | _, .box w, A => w.ty (.VTypeBox A)
  | _, .dia w _ _ _, A => w.ty (.VTypeDia A)

/-- The annotation of a wrapped term. -/
def ann : {Δ : Ctx} → (w : Wr Γ Δ) → {A : VarType} → Ann A → Ann (w.ty A)
  | _, .nil, _, a => a
  | _, .box w, _, a => w.ann (.box a)
  | _, .dia w x _ _, _, a => w.ann (.dia x a)

/-- ⭐A term of the chain's last view, wrapped into a term of the `□` view. -/
def wrap {σ : Signature} : {Δ : Ctx} → (w : Wr Γ Δ) → {A : VarType} → {a : Ann A} →
    Term σ Δ A a → Term σ Γ.boxIn (w.ty A) (w.ann a)
  | _, .nil, _, _, u => u
  | _, .box w, _, _, u => w.wrap (.boxtm u)
  | _, .dia w x _ hx, _, _, u => w.wrap (.diatm x ⟨_, hx⟩ u)

/-- Wrapping keeps annotations apart. -/
theorem mapIdx_ann_inj (ι : VarSymb → VarSymb) : ∀ {Δ : Ctx} (w : Wr Γ Δ) {A : VarType}
    {a a' : Ann A}, (w.ann a).mapIdx ι = (w.ann a').mapIdx ι → a.mapIdx ι = a'.mapIdx ι
  | _, .nil, _, _, _, h => h
  | _, .box w, _, a, a', h => by
      have h' := mapIdx_ann_inj ι w (a := .box a) (a' := .box a') h
      change Ann.box (a.mapIdx ι) = Ann.box (a'.mapIdx ι) at h'
      injection h'
  | _, .dia w x _ _, _, a, a', h => by
      have h' := mapIdx_ann_inj ι w (a := .dia x a) (a' := .dia x a') h
      change Ann.dia (ι x) (a.mapIdx ι) = Ann.dia (ι x) (a'.mapIdx ι) at h'
      injection h'

end Wr

/-- An environment pushed along a chain of views from its `□` view. -/
def Model.ShEnv.pushAlong {σ : Signature} {F : Arrows σ} {Root : F.W → Type u}
    [Arrows.RootKeep F Root] {Γ : Ctx} {w₀ : F.W} (ρ : Model.ShEnv F Root Γ w₀) :
    {Δ : Ctx} → Wr Γ Δ → Model.ShEnv F Root Δ w₀
  | _, .nil => ρ.boxPush 0
  | _, .box w => (ρ.pushAlong w).boxPush (w.len + 1)
  | _, .dia w x _ hx => (ρ.pushAlong w).diaPush (w.len + 1) x hx

/-- ⭐**A wrapped term's shape depends only on the shape in the hole.** -/
theorem Model.termShp_wrap_congr {σ : Signature} {F : Arrows σ} {Root : F.W → Type u}
    [Arrows.RootKeep F Root] {Γ : Ctx} {w₀ : F.W} (ρ : Model.ShEnv F Root Γ w₀) :
    ∀ {Δ : Ctx} (w : Wr Γ Δ) {A : VarType} {a a' : Ann A} (u : Term σ Δ A a)
      (u' : Term σ Δ A a'),
      Model.termShp (ρ.pushAlong w) (w.len + 1) u =
          Model.termShp (ρ.pushAlong w) (w.len + 1) u' →
        Model.termShp (ρ.boxPush 0) 1 (w.wrap u) = Model.termShp (ρ.boxPush 0) 1 (w.wrap u')
  | _, .nil, _, _, _, _, _, h => h
  | _, .box w, _, _, _, u, u', h => by
      refine Model.termShp_wrap_congr ρ w (.boxtm u) (.boxtm u') ?_
      change Shp.box (Model.termShp ((ρ.pushAlong w).boxPush (w.len + 1)) (w.len + 1 + 1) u) =
        Shp.box (Model.termShp ((ρ.pushAlong w).boxPush (w.len + 1)) (w.len + 1 + 1) u')
      exact congrArg _ h
  | _, .dia w x _ hx, _, _, _, u, u', h => by
      refine Model.termShp_wrap_congr ρ w (.diatm x ⟨_, hx⟩ u) (.diatm x ⟨_, hx⟩ u') ?_
      rw [Model.termShp_diatm _ _ hx, Model.termShp_diatm _ _ hx]
      exact congrArg _ h

/-! ## Modal depth -/

/-- The modal depth of a term: the nesting of its `□` and `◇` formers. -/
def Term.mdepth {σ : Signature} : {Γ : Ctx} → {T : VarType} → {a : Ann T} → Term σ Γ T a → ℕ
  | _, _, _, .var _ _ => 0
  | _, _, _, .func _ => 0
  | _, _, _, .unit => 0
  | _, _, _, .pair s t => max s.mdepth t.mdepth
  | _, _, _, .boxtm t => t.mdepth + 1
  | _, _, _, .diatm _ _ t => t.mdepth + 1

theorem Term.mdepth_var {σ : Signature} {Γ : Ctx} {a : Ann .Var} :
    ∀ t : Term σ Γ .Var a, t.mdepth = 0
  | .var _ _ => rfl
  | .func _ => rfl

theorem Term.mdepth_toVar {σ : Signature} {Δ : Ctx} (e : SubE σ Δ) (h : e.OkRef .Var) :
    (e.toVar h).mdepth = 0 :=
  Term.mdepth_var _

/-- Substitution keeps the modal depth. -/
theorem Term.mdepth_subst {σ : Signature} (ι : VarSymb → VarSymb) :
    ∀ {Γ Δ : Ctx} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {T : VarType}
      {a : Ann T} (t : Term σ Γ T a), (Term.subst ι θ hθ hc t).mdepth = t.mdepth
  | _, _, θ, hθ, _, _, _, .var _ hv => Term.mdepth_var _
  | _, _, _, _, _, _, _, .func _ => rfl
  | _, _, _, _, _, _, _, .unit => rfl
  | _, _, θ, hθ, hc, _, _, .pair s t => by
      change max _ _ = max _ _
      rw [Term.mdepth_subst ι θ hθ hc s, Term.mdepth_subst ι θ hθ hc t]
  | _, _, θ, hθ, hc, _, _, .boxtm t => by
      change _ + 1 = _ + 1
      rw [Term.mdepth_subst ι θ.box _ _ t]
  | _, _, θ, hθ, hc, _, _, .diatm x hx t => by
      change _ + 1 = _ + 1
      rw [Term.mdepth_subst ι _ _ _ t]

theorem Wr.mdepth_wrap {σ : Signature} {Γ : Ctx} : ∀ {Δ : Ctx} (w : Wr Γ Δ) {A : VarType}
    {a : Ann A} (u : Term σ Δ A a), (w.wrap u).mdepth = w.len + u.mdepth
  | _, .nil, _, _, _ => (Nat.zero_add _).symm
  | _, .box w, _, _, u => by
      change (w.wrap (.boxtm u)).mdepth = w.len + 1 + u.mdepth
      rw [Wr.mdepth_wrap w (.boxtm u)]
      change w.len + (u.mdepth + 1) = w.len + 1 + u.mdepth
      omega
  | _, .dia w x _ hx, _, _, u => by
      change (w.wrap (.diatm x ⟨_, hx⟩ u)).mdepth = w.len + 1 + u.mdepth
      rw [Wr.mdepth_wrap w (.diatm x ⟨_, hx⟩ u)]
      change w.len + (u.mdepth + 1) = w.len + 1 + u.mdepth
      omega

/-! ## Keep-first addresses -/

omit [ModalSys] in
theorem ppath_of_levels_zero : ∀ {p : List Step}, Step.levels p = 0 → PPath p
  | [], _ => fun _ h => by cases h
  | s :: p, h => by
      change (if s.isProj then 0 else 1) + Step.levels p = 0 at h
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · by_contra hs
        rw [if_neg hs] at h
        omega
      · exact ppath_of_levels_zero (by split_ifs at h <;> omega) t ht

/-- ⭐An address whose first level step is a `keep`. -/
def KF (y : VarSymb) : Prop :=
  ∃ (u : VarSymb) (rest : List Step), PPath u.path ∧ y = (VarSymb.step u .keep).ext rest

omit [ModalSys] in
theorem KF.step {y : VarSymb} (h : KF y) (st : Step) : KF (.step y st) := by
  obtain ⟨u, rest, hu, rfl⟩ := h
  exact ⟨u, rest ++ [st], hu, (ext_append_step _ _ _).symm⟩

omit [ModalSys] in
/-- Cutting a keep-first address at its last step. -/
theorem KF.of_step {v : VarSymb} {st : Step} (h : KF (.step v st)) :
    (PPath v.path ∧ st = .keep) ∨ KF v := by
  obtain ⟨u, rest, hu, he⟩ := h
  rcases List.eq_nil_or_concat rest with rfl | ⟨r', b, rfl⟩
  · injection he with h₁ h₂
    subst h₁ h₂
    exact Or.inl ⟨hu, rfl⟩
  · rw [List.concat_eq_append, ext_append_step] at he
    injection he with h₁ h₂
    exact Or.inr ⟨u, r', hu, h₁⟩

omit [ModalSys] in
theorem not_KF_root (r : Root) : ¬ KF (.root r) := by
  rintro ⟨u, rest, -, he⟩
  rcases List.eq_nil_or_concat rest with rfl | ⟨r', b, rfl⟩
  · cases he
  · rw [List.concat_eq_append, ext_append_step] at he
    cases he

omit [ModalSys] in
theorem not_KF_of_ppath {y : VarSymb} (hy : PPath y.path) : ¬ KF y := by
  rintro ⟨u, rest, -, rfl⟩
  rw [VarSymb.ext_path] at hy
  exact absurd (hy .keep (List.mem_append_left _ (by simp [VarSymb.path]))) (by decide)

omit [ModalSys] in
/-- A `◇`-content is keep-first exactly when its witness is. -/
theorem KF.of_dia {x : VarSymb} (h : KF (.step x .dia)) : KF x := by
  rcases KF.of_step h with ⟨-, h'⟩ | h'
  · cases h'
  · exact h'

/-- `Δ'` declares every keep-first address `Δ` reaches, with its type. -/
def KLe (Δ' Δ : Ctx) : Prop :=
  ∀ y T, KF y → Δ.ref y = some T → Δ'.ref y = some T

theorem KLe.refl (Δ : Ctx) : KLe Δ Δ := fun _ _ _ h => h

theorem KLe.trans {Δ'' Δ' Δ : Ctx} (h₁ : KLe Δ'' Δ') (h₂ : KLe Δ' Δ) : KLe Δ'' Δ :=
  fun y T hy h => h₁ y T hy (h₂ y T hy h)

/-- It suffices to check the declared keep-first addresses. -/
theorem KLe.of_decl {Δ' Δ : Ctx}
    (h : ∀ y T, KF y → y.lastProj = false → Δ y = some T → Δ'.ref y = some T) : KLe Δ' Δ
  | .root r, _, hy, _ => absurd hy (not_KF_root r)
  | .step v st, T, hy, hr => by
      by_cases hs : st.isProj = true
      · rw [Ctx.ref_step_proj Δ v hs] at hr
        rw [Ctx.ref_step_proj Δ' v hs]
        rcases KF.of_step hy with ⟨-, rfl⟩ | hv
        · cases hs
        cases hU : Δ.ref v with
        | none => rw [hU] at hr; cases hr
        | some U =>
            rw [hU] at hr
            rw [KLe.of_decl h v U hv hU]
            exact hr
      · exact h _ T hy (Bool.eq_false_iff.mpr hs)
          (by rwa [Ctx.ref_step_nonproj Δ v hs] at hr)


/-- The `◇` view declares only its witness's content. -/
theorem Ctx.diaIn_dia_inv {Δ : Ctx} {x u : VarSymb} {T : VarType}
    (h : (Δ.diaIn x) (.step u .dia) = some T) : u = x ∧ Δ.ref x = some (.VTypeDia T) := by
  change (if u = x then (match Δ.ref x with | some (.VTypeDia X) => some X | _ => none)
    else none) = some T at h
  split_ifs at h with hux
  refine ⟨hux, ?_⟩
  split at h
  · rename_i X hX
    cases h
    exact hX
  · cases h

/-- Entering `□` keeps the keep-first part, when every address has a level step. -/
theorem KLe.boxIn {Δ' Δ : Ctx} (h : KLe Δ' Δ)
    (hlv : ∀ v T, Δ.ref v = some T → ¬ PPath v.path) : KLe Δ'.boxIn Δ.boxIn :=
  KLe.of_decl fun y T hy _ hd => by
    match y, hd with
    | .step u .keep, hd =>
        obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep hd
        rcases KF.of_step hy with ⟨hpp, -⟩ | hu'
        · exact absurd hpp (hlv u T hu)
        · exact Ctx.ref_keep_of' hF (h u T hu' hu) hk
    | .step u .box, hd =>
        obtain ⟨hk, hu⟩ := Ctx.boxIn_box hd
        rcases KF.of_step hy with ⟨-, hb⟩ | hu'
        · cases hb
        · exact (Ctx.ref_nonproj _ rfl).trans (Ctx.boxIn_box_of hk (h u _ hu' hu))
    | .root _, hd => cases hd
    | .step _ .fst, hd => cases hd
    | .step _ .snd, hd => cases hd
    | .step _ .dia, hd => cases hd
    | .step _ .here, hd => cases hd

/-- The keep-first part of a `◇` view of a witness that is not keep-first is in the `□` view. -/
theorem KLe.boxIn_diaIn (Δ : Ctx) {x : VarSymb} (hx : ¬ KF x) : KLe Δ.boxIn (Δ.diaIn x) :=
  KLe.of_decl fun y T hy _ hd => by
    match y, hd with
    | .step u .dia, hd =>
        obtain ⟨rfl, -⟩ := Ctx.diaIn_dia_inv hd
        exact absurd (KF.of_dia hy) hx
    | .step u .keep, hd => exact (Ctx.ref_nonproj _ rfl).trans hd
    | .step u .box, hd => exact (Ctx.ref_nonproj _ rfl).trans hd
    | .root _, hd => cases hd
    | .step _ .fst, hd => cases hd
    | .step _ .snd, hd => cases hd
    | .step _ .here, hd => cases hd

/-- Entering `◇_x` keeps the keep-first part, when every address has a level step. -/
theorem KLe.diaIn {Δ' Δ : Ctx} (h : KLe Δ' Δ)
    (hlv : ∀ v T, Δ.ref v = some T → ¬ PPath v.path) (x : VarSymb) :
    KLe (Δ'.diaIn x) (Δ.diaIn x) :=
  KLe.of_decl fun y T hy _ hd => by
    match y, hd with
    | .step u .dia, hd =>
        obtain ⟨rfl, hx⟩ := Ctx.diaIn_dia_inv hd
        exact Ctx.ref_diaIn_of (h u _ (KF.of_dia hy) hx)
    | .step u .keep, hd =>
        exact (Ctx.le_boxIn_diaIn Δ' u).ref
          (KLe.boxIn h hlv _ T hy ((Ctx.ref_nonproj _ rfl).trans hd)) |>.trans rfl
    | .step u .box, hd =>
        exact (Ctx.le_boxIn_diaIn Δ' x).ref
          (KLe.boxIn h hlv _ T hy ((Ctx.ref_nonproj _ rfl).trans hd))
    | .root _, hd => cases hd
    | .step _ .fst, hd => cases hd
    | .step _ .snd, hd => cases hd
    | .step _ .here, hd => cases hd

theorem Model.ShEnv.Agree.trans {σ : Signature} {F : Arrows σ} {Root : F.W → Type u}
    {Γ₁ Γ₂ Γ₃ : Ctx} {h₁ : Γ₁.Le Γ₂} {h₂ : Γ₂.Le Γ₃} {w : F.W}
    {ρ₁ : Model.ShEnv F Root Γ₁ w} {ρ₂ : Model.ShEnv F Root Γ₂ w} {ρ₃ : Model.ShEnv F Root Γ₃ w}
    (a₁ : Model.ShEnv.Agree h₁ ρ₁ ρ₂) (a₂ : Model.ShEnv.Agree h₂ ρ₂ ρ₃) :
    Model.ShEnv.Agree (h₁.trans h₂) ρ₁ ρ₃ :=
  fun v T hv => (a₁ v T hv).trans (a₂ v T _)

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

theorem Pushed.not_ppath {s : GW hF M₀} {i : ℕ} {Δ : Ctx} {ρ : GEnv hF M₀ Δ s} {j : ℕ}
    (hP : Pushed hF M₀ s i Δ ρ (j + 1)) : ∀ v T, Δ.ref v = some T → ¬ PPath v.path :=
  fun v _ hv hp => by
    have := hP.levels v hv
    rw [levels_ppath hp] at this
    cases this

/-- ⭐**The keep-first part of a pushed environment is a chain of views from the `□` view**: the
    canonical environment pushed along it agrees with the pushed one, and declares every
    keep-first address. -/
theorem Pushed.kpart {s : GW hF M₀} {i : ℕ} {Δ : Ctx} {ρ : GEnv hF M₀ Δ s} {j : ℕ}
    (hP : Pushed hF M₀ s i Δ ρ (j + 1)) :
    ∃ (Δ' : Ctx) (w : Wr (ctxOf (glat s i)) Δ') (hle : Δ'.Le Δ), w.len = j ∧
      Model.ShEnv.Agree hle ((famEnv cEnv (ctxOf (glat s i)) s).pushAlong w) ρ ∧ KLe Δ' Δ := by
  generalize hn : j + 1 = n at hP
  induction hP generalizing j with
  | base => cases hn
  | @box Δ ρ j₀ hP ih =>
      obtain rfl : j₀ = j := by omega
      cases j₀ with
      | zero =>
          cases hP with
          | base => exact ⟨_, .nil, Ctx.Le.refl _, rfl, fun _ _ _ => rfl, KLe.refl _⟩
      | succ j' =>
          obtain ⟨Δ', w, hle, hlen, hag, hk⟩ := ih rfl
          subst hlen
          exact ⟨_, .box w, hle.boxIn, rfl, Model.ShEnv.boxPush_agree hag _,
            KLe.boxIn hk hP.not_ppath⟩
  | @dia Δ ρ j₀ x X hx hP ih =>
      obtain rfl : j₀ = j := by omega
      cases j₀ with
      | zero =>
          cases hP with
          | base =>
              refine ⟨_, .nil, Ctx.le_boxIn_diaIn _ x, rfl,
                Model.ShEnv.box_dia_agree _ 0 hx, KLe.boxIn_diaIn _ (not_KF_of_ppath ?_)⟩
              exact ppath_of_levels_zero ((Pushed.base (i := i)).levels x hx)
      | succ j' =>
          obtain ⟨Δ', w, hle, hlen, hag, hk⟩ := ih rfl
          subst hlen
          by_cases hKF : KF x
          · have hx' := hk x _ hKF hx
            exact ⟨_, .dia w x X hx', hle.diaIn x, rfl,
              Model.ShEnv.diaPush_agree hag _ hx', KLe.diaIn hk hP.not_ppath x⟩
          · exact ⟨_, .box w, hle.boxIn.trans (Ctx.le_boxIn_diaIn Δ x), rfl,
              (Model.ShEnv.boxPush_agree hag _).trans (Model.ShEnv.box_dia_agree ρ _ hx),
              (KLe.boxIn hk hP.not_ppath).trans (KLe.boxIn_diaIn Δ hKF)⟩


/-! ## The two kinds of addresses -/

/-- Reachable addresses have a property closed under projections when the declared ones do. -/
theorem ref_induct {Δ : Ctx} {P : VarSymb → Prop}
    (hd : ∀ v T, v.lastProj = false → Δ v = some T → P v)
    (hp : ∀ v st, st.isProj = true → P v → P (.step v st)) :
    ∀ (y : VarSymb) {T : VarType}, Δ.ref y = some T → P y
  | .root r, T, hy => hd _ T rfl hy
  | .step v st, T, hy => by
      by_cases hs : st.isProj = true
      · rw [Ctx.ref_step_proj _ v hs] at hy
        cases hU : Δ.ref v with
        | none => rw [hU] at hy; cases hy
        | some U => exact hp v st hs (ref_induct hd hp v hU)
      · exact hd _ T (Bool.eq_false_iff.mpr hs) (by rwa [Ctx.ref_step_nonproj _ v hs] at hy)

/-- Under T + 4 no reachable address of a pushed context has a `box` step. -/
theorem Pushed.nobox (hko : ModalSys.keepOnly = true) {s : GW hF M₀} {i : ℕ} {Δ : Ctx}
    {ρ : GEnv hF M₀ Δ s} {j : ℕ} (hP : Pushed hF M₀ s i Δ ρ j) :
    ∀ (y : VarSymb) {T : VarType}, Δ.ref y = some T → Step.box ∉ y.path := by
  have hp : ∀ (v : VarSymb) (st : Step), st.isProj = true → Step.box ∉ v.path →
      Step.box ∉ (VarSymb.step v st).path := fun v st hs hv h => by
    change Step.box ∈ v.path ++ [st] at h
    rcases List.mem_append.mp h with h | h
    · exact hv h
    · rw [← List.mem_singleton.mp h] at hs
      cases hs
  induction hP with
  | base =>
      refine ref_induct (fun v T _ hv => ?_) hp
      obtain ⟨r, rfl⟩ := ctxOf_decl hv
      exact List.not_mem_nil
  | @box Δ ρ j hP ih =>
      refine ref_induct (fun v T _ hv => ?_) hp
      match v, hv with
      | .step u .keep, hv =>
          intro h
          change Step.box ∈ u.path ++ [.keep] at h
          rcases List.mem_append.mp h with h | h
          · exact ih u (Ctx.boxIn_keep hv).2.1 h
          · cases List.mem_singleton.mp h
      | .step u .box, hv =>
          rw [(Ctx.boxIn_box hv).1] at hko
          cases hko
      | .root _, hv => cases hv
      | .step _ .fst, hv => cases hv
      | .step _ .snd, hv => cases hv
      | .step _ .dia, hv => cases hv
      | .step _ .here, hv => cases hv
  | @dia Δ ρ j x X hx hP ih =>
      refine ref_induct (fun v T _ hv => ?_) hp
      match v, hv with
      | .step u .dia, hv =>
          obtain ⟨rfl, -⟩ := Ctx.diaIn_dia_inv hv
          intro h
          change Step.box ∈ u.path ++ [.dia] at h
          rcases List.mem_append.mp h with h | h
          · exact ih u hx h
          · cases List.mem_singleton.mp h
      | .step u .keep, hv =>
          intro h
          change Step.box ∈ u.path ++ [.keep] at h
          rcases List.mem_append.mp h with h | h
          · exact ih u (Ctx.boxIn_keep (Γ := Δ) hv).2.1 h
          · cases List.mem_singleton.mp h
      | .step u .box, hv =>
          rw [(Ctx.boxIn_box (Γ := Δ) hv).1] at hko
          cases hko
      | .root _, hv => cases hv
      | .step _ .fst, hv => cases hv
      | .step _ .snd, hv => cases hv
      | .step _ .here, hv => cases hv

omit [ModalSys] in
/-- An address without `box` steps is level-free, root-level, or keep-first. -/
theorem addr_cases : ∀ (y : VarSymb), Step.box ∉ y.path →
    PPath y.path ∨ (∃ (pre : VarSymb) (q : List Step), PPath pre.path ∧
      y = pre.ext (.dia :: q)) ∨ KF y
  | .root _, _ => Or.inl fun _ h => by cases h
  | .step v st, hb => by
      have hb' : Step.box ∉ v.path := fun h => hb (List.mem_append_left _ h)
      rcases addr_cases v hb' with hv | ⟨pre, q, hpre, rfl⟩ | hv
      · by_cases hs : st.isProj = true
        · refine Or.inl fun t ht => ?_
          rcases List.mem_append.mp ht with ht | ht
          · exact hv t ht
          · rw [List.mem_singleton.mp ht]
            exact hs
        · cases st with
          | dia => exact Or.inr (Or.inl ⟨v, [], hv, rfl⟩)
          | keep => exact Or.inr (Or.inr ⟨v, [], hv, rfl⟩)
          | box => exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) hb
          | _ => cases hs rfl
      · exact Or.inr (Or.inl ⟨pre, q ++ [st], hpre, by
          rw [show Step.dia :: (q ++ [st]) = (Step.dia :: q) ++ [st] from rfl,
            ext_append_step]⟩)
      · exact Or.inr (Or.inr (hv.step st))

/-- Pushing the canonical environment along a chain of views from the `□` view keeps it
    well-formed, with a `□` level first. -/
theorem pushAlong_wf {s : GW hF M₀} {Γ : Ctx} (ρ : GEnv hF M₀ Γ s) (hρ : ρ.WF []) :
    ∀ {Δ : Ctx} (w : Wr Γ Δ), ∃ lw' : List Bool, lw'.length = w.len ∧
      (ρ.pushAlong w).WF (true :: lw')
  | _, .nil => ⟨[], rfl, Model.ShEnv.wf_boxPush' hρ rfl⟩
  | _, .box w => by
      obtain ⟨lw', hl, hw⟩ := pushAlong_wf ρ hρ w
      exact ⟨lw' ++ [true], by simp [hl, Wr.len], Model.ShEnv.wf_boxPush' hw (by simp [hl])⟩
  | _, .dia w _ _ hx => by
      obtain ⟨lw', hl, hw⟩ := pushAlong_wf ρ hρ w
      exact ⟨lw' ++ [false], by simp [hl, Wr.len], Model.ShEnv.wf_diaPush' hw (by simp [hl]) hx⟩

theorem isFam_label_of_wf {s : GW hF M₀} (lw : List Bool) {X : VarType}
    (S : GShape hF M₀ s (.VTypeDia X))
    (h : Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) (true :: lw) S) :
    IsFam S.label := by
  have h' := allL_isFam_of_wf lw S h
  match S, h' with
  | .dia _ _, h' => exact h'.1

/-- ⭐**The labels of a pushed environment**: a root-level address is labelled by its root and its
    path, a keep-first one by a family. -/
theorem Pushed.label_cases (hT : ModalSys.T = true)
    (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {i : ℕ} {Δ : Ctx} {ρ : GEnv hF M₀ Δ s} {j : ℕ}
    (hP : Pushed hF M₀ s i Δ ρ (j + 1)) {y : VarSymb} {X : VarType}
    (h : Δ.ref y = some (.VTypeDia X)) :
    (∃ (pre : VarSymb) (q : List Step), PPath pre.path ∧ y = pre.ext (.dia :: q) ∧
        (ρ.ref (j + 1) y h).label = .root pre (.dia :: q)) ∨
      (KF y ∧ IsFam (ρ.ref (j + 1) y h).label) := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  rcases addr_cases y (hP.nobox hko y h) with hy | ⟨pre, q, hpre, rfl⟩ | hy
  · exact absurd hy (hP.not_ppath y _ h)
  · refine Or.inl ⟨pre, q, hpre, rfl, ?_⟩
    rw [hP.rootSh hT hM₀ pre hpre _ h q rfl]
    rfl
  · refine Or.inr ⟨hy, ?_⟩
    obtain ⟨Δ', w, hle, hlen, hag, hk⟩ := hP.kpart
    have hy' := hk y _ hy h
    obtain ⟨lw', hl, hw⟩ := pushAlong_wf _ (famEnv_wf (fun t v T => cEnv_wf t v T) _ s) w
    have e := Model.ShEnv.ref_agree hag (j + 1) y hy'
    rw [show ρ.ref (j + 1) y h = ρ.ref (j + 1) y (hle.ref hy') from rfl, ← e]
    exact isFam_label_of_wf lw' _ (Model.ShEnv.wf_ref' hw (by simp [hl, hlen]) y hy')


/-! ## Keep-first addresses come from kept items of the base -/

omit [ModalSys] in
/-- Cutting an address below a root's step at its last step. -/
theorem ext_cons_eq_step {pre v : VarSymb} {a st : Step} {q : List Step}
    (h : pre.ext (a :: q) = .step v st) :
    (q = [] ∧ v = pre ∧ st = a) ∨ ∃ q', q = q' ++ [st] ∧ v = pre.ext (a :: q') := by
  rcases List.eq_nil_or_concat q with rfl | ⟨q', b, rfl⟩
  · left
    change VarSymb.step pre a = _ at h
    injection h with h₁ h₂
    exact ⟨rfl, h₁.symm, h₂.symm⟩
  · right
    rw [List.concat_eq_append, ← List.cons_append, ext_append_step] at h
    injection h with h₁ h₂
    subst h₂
    exact ⟨q', List.concat_eq_append .., h₁.symm⟩

/-- A level-free address of a pushed context is one of the base's. -/
theorem Pushed.ref_ppath {s : GW hF M₀} {i : ℕ} {Δ : Ctx} {ρ : GEnv hF M₀ Δ s} {j : ℕ}
    (hP : Pushed hF M₀ s i Δ ρ j) {u : VarSymb} {T : VarType} (h : Δ.ref u = some T)
    (hu : PPath u.path) : (ctxOf (glat s i)).ref u = some T := by
  have hl := hP.levels u h
  rw [levels_ppath hu] at hl
  subst hl
  cases hP
  exact h

/-- ⭐**A keep-first address of a pushed context is below a kept item of the base.** -/
theorem Pushed.kf_prefix {s : GW hF M₀} {i : ℕ} {Δ : Ctx} {ρ : GEnv hF M₀ Δ s} {j : ℕ}
    (hP : Pushed hF M₀ s i Δ ρ j) :
    ∀ (y : VarSymb) {T : VarType}, Δ.ref y = some T → ∀ (u : VarSymb) (rest : List Step),
      PPath u.path → y = (VarSymb.step u .keep).ext rest →
        ∃ U, (ctxOf (glat s i)).ref u = some U ∧ U.keepable = true := by
  have hp : ∀ (v : VarSymb) (st : Step), st.isProj = true →
      (∀ (u : VarSymb) (rest : List Step), PPath u.path → v = (VarSymb.step u .keep).ext rest →
        ∃ U, (ctxOf (glat s i)).ref u = some U ∧ U.keepable = true) →
      ∀ (u : VarSymb) (rest : List Step), PPath u.path →
        VarSymb.step v st = (VarSymb.step u .keep).ext rest →
        ∃ U, (ctxOf (glat s i)).ref u = some U ∧ U.keepable = true := by
    intro v st hs hv u rest hu he
    rcases ext_cons_eq_step (pre := u) he.symm with ⟨-, -, rfl⟩ | ⟨q', -, hv'⟩
    · cases hs
    · exact hv u q' hu hv'
  induction hP with
  | base =>
      refine ref_induct (fun v T _ hv => ?_) hp
      obtain ⟨r, rfl⟩ := ctxOf_decl hv
      intro u rest hu he
      exact absurd ⟨u, rest, hu, he⟩ (not_KF_root _)
  | @box Δ ρ j hP ih =>
      refine ref_induct (fun v T _ hv => ?_) hp
      match v, hv with
      | .step u' .keep, hv =>
          intro u rest hu he
          obtain ⟨-, hu', hk⟩ := Ctx.boxIn_keep hv
          rcases ext_cons_eq_step (pre := u) he.symm with ⟨-, rfl, -⟩ | ⟨q', -, hv'⟩
          · exact ⟨_, hP.ref_ppath hu' hu, hk⟩
          · exact ih u' hu' u q' hu hv'
      | .step u' .box, hv =>
          intro u rest hu he
          rcases ext_cons_eq_step (pre := u) he.symm with ⟨-, -, h⟩ | ⟨q', -, hv'⟩
          · cases h
          · exact ih u' (Ctx.boxIn_step_box hv) u q' hu hv'
      | .root _, hv => cases hv
      | .step _ .fst, hv => cases hv
      | .step _ .snd, hv => cases hv
      | .step _ .dia, hv => cases hv
      | .step _ .here, hv => cases hv
  | @dia Δ ρ j x X hx hP ih =>
      refine ref_induct (fun v T _ hv => ?_) hp
      match v, hv with
      | .step u' .dia, hv =>
          intro u rest hu he
          obtain ⟨rfl, -⟩ := Ctx.diaIn_dia_inv hv
          rcases ext_cons_eq_step (pre := u) he.symm with ⟨-, -, h⟩ | ⟨q', -, hv'⟩
          · cases h
          · exact ih u' hx u q' hu hv'
      | .step u' .keep, hv =>
          intro u rest hu he
          obtain ⟨-, hu', hk⟩ := Ctx.boxIn_keep (Γ := Δ) hv
          rcases ext_cons_eq_step (pre := u) he.symm with ⟨-, rfl, -⟩ | ⟨q', -, hv'⟩
          · exact ⟨_, hP.ref_ppath hu' hu, hk⟩
          · exact ih u' hu' u q' hu hv'
      | .step u' .box, hv =>
          intro u rest hu he
          rcases ext_cons_eq_step (pre := u) he.symm with ⟨-, -, h⟩ | ⟨q', -, hv'⟩
          · cases h
          · exact ih u' (Ctx.boxIn_step_box (Γ := Δ) hv) u q' hu hv'
      | .root _, hv => cases hv
      | .step _ .fst, hv => cases hv
      | .step _ .snd, hv => cases hv
      | .step _ .here, hv => cases hv

/-! ## A late edge -/

/-- ⭐**A late edge**: under T every stage has a child born after it (for `¬□⊥`), whose entries
    for the stage's kept items are all images. -/
theorem glate (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ) :
    ∃ (t : GW hF M₀) (c : ℕ) (_ : t.1 = c :: s.1) (L : List VarType), glat s i <:+ L ∧
      ∀ v T, (ctxOf (glat s i)).kView none v = some T →
        fmapL hF M₀ t.1 v = .inl (gchildMap L none v) := by
  have hψ : WFF.box (.bot : WFF σ ((ctxOf (glat s i)).kView none) 0) ∉
      ((gnet hF M₀ (gbirth hF M₀ s.2 + i)).st s.1).M := fun h =>
    ((gw hM₀ s).mcs i).bot_not_mem (BWorld.mem_of_provable (Δ := [.box .bot])
      (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact h)
      ⟨Proof.T_box hT (Proof.lookup List.mem_cons_self)⟩)
  obtain ⟨m, _, hsuf, M', hnot, hlive, hst, hkind, hfcl, hfmap, hmem⟩ :=
    child_box hF hM₀ (live_gbirth hF hM₀ s.2 (Nat.le_add_right _ i)) hψ
  let t : GW hF M₀ := ⟨(gnet hF M₀ m).nch s.1 :: s.1, m + 1, hlive⟩
  exact ⟨t, _, rfl, _, hsuf, fun v T hv =>
    (glimit_child_ag hM₀ hsuf (t := t) hlive hkind hfcl hfmap v T hv).symm⟩

/-- ⭐**A term of the `□` view, its shape read along an edge, is its translation's shape** at the
    child (`unT_termShp`, `comp_pull`, `termShp_subst`). -/
theorem edge_shp (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ}
    (hc : t.1 = c :: s.1) (i : ℕ) {A : VarType} {a : Ann A}
    (X : Term σ (ctxOf (glat s i)).boxIn A a) :
    unT (edgeAcc hc) (Model.termShp ((famEnv cEnv (ctxOf (glat s i)) s).boxPush 0) 1 X) =
      Model.termShp (famEnv cEnv (ctxOf (glat t (glstg s t i))) t) 0
        (Term.subst (eIdx (fmapL hF M₀ t.1)) (eS σ _ (fmapL hF M₀ t.1))
          (ok_eS_kView (gentOk_box hM₀ ⟨c, hc⟩ i)) (coh_eS_kView (gentOk_box hM₀ ⟨c, hc⟩ i))
          X) := by
  have hτ : ∀ v T h', (((famEnv cEnv (ctxOf (glat s i)) s).boxPush 0) v T h').AllL IsFam :=
    fun v T h' => allL_isFam_of_wf [] _ (Model.ShEnv.wf_boxPush' (k := 0)
      (famEnv_wf (fun t v T => cEnv_wf t v T) _ s) rfl v T h')
  calc unT (edgeAcc hc) (Model.termShp ((famEnv cEnv (ctxOf (glat s i)) s).boxPush 0) 1 X)
      = Model.termShp (fun v T h => unT (edgeAcc hc)
          (((famEnv cEnv (ctxOf (glat s i)) s).boxPush 0) v T h)) 0 X :=
        unT_termShp _ hτ (edgeAcc hc) 0 X
    _ = Model.termShp (pullP hM₀ [c] s t hc pathOk_cons i
          (famEnv cEnv (ctxOf (glat t (pstg s t [c] hc i))) t)) 0 X := by
        rw [comp_pull hT hM₀ [c] s t hc pathOk_cons i]
    _ = _ := (Model.termShp_subst _ _ _ (Ctx.noProjLast_boxIn _) _ 0 (lw := []) rfl
          (fun _ => famEnv_wf (fun t v T => cEnv_wf t v T) _ t) X).symm


/-! ## The late edge's images are injective -/

/-- Where a kept item lands in its root's image determines the item and what follows. -/
theorem gPath_keep_inj (hT : ModalSys.T = true) (hko : ModalSys.keepOnly = true) :
    ∀ (R : VarType) (q q' : List Step) {U U' : VarType} (rest rest' : List Step),
      PPath q → PPath q' → R.walk q = some U → R.walk q' = some U' → U.keepable = true →
        U'.keepable = true → gPath R q .keep ++ rest = gPath R q' .keep ++ rest' →
          q = q' ∧ rest = rest' := by
  intro R
  induction R with
  | Var | VTypeOne =>
      intro q q' U U' rest rest' hq hq' hw hw' hk hk' h
      exfalso
      rcases q with _ | ⟨st, q⟩
      · simp only [VarType.walk, Option.some.injEq] at hw
        subst hw
        cases hk
      · cases st <;> simp [VarType.walk, VarType.step] at hw
  | VTypeProd A B ihA ihB =>
      intro q q' U U' rest rest' hq hq' hw hw' hk hk' h
      rcases q with _ | ⟨st, q⟩
      · simp only [VarType.walk, Option.some.injEq] at hw
        subst hw
        cases hk
      rcases q' with _ | ⟨st', q'⟩
      · simp only [VarType.walk, Option.some.injEq] at hw'
        subst hw'
        cases hk'
      have hq₁ : PPath q := fun t ht => hq t (List.mem_cons_of_mem _ ht)
      have hq₁' : PPath q' := fun t ht => hq' t (List.mem_cons_of_mem _ ht)
      cases st <;> cases st' <;> simp only [VarType.walk, VarType.step, Option.bind_some,
        Option.bind_none, reduceCtorEq] at hw hw' <;>
        simp only [gPath, List.cons_append, List.cons.injEq] at h <;>
        (try exact absurd h.1 (by decide))
      · obtain ⟨hq, hr⟩ := ihA q q' rest rest' hq₁ hq₁' hw hw' hk hk' h.2
        exact ⟨by rw [hq], hr⟩
      · obtain ⟨hq, hr⟩ := ihB q q' rest rest' hq₁ hq₁' hw hw' hk hk' h.2
        exact ⟨by rw [hq], hr⟩
  | VTypeBox A ih =>
      intro q q' U U' rest rest' hq hq' hw hw' hk hk' h
      rcases q with _ | ⟨st, q⟩ <;> rcases q' with _ | ⟨st', q'⟩
      · simp only [gPath, hko, cond_true, List.cons_append, List.nil_append,
          List.cons.injEq, true_and] at h
        exact ⟨rfl, h⟩
      · cases st' <;> simp [VarType.walk, VarType.step] at hw' <;>
          simp [gPath, hko] at h
        exact absurd (hq' _ List.mem_cons_self) (by decide)
      · cases st <;> simp [VarType.walk, VarType.step] at hw <;>
          simp [gPath, hko] at h
        exact absurd (hq _ List.mem_cons_self) (by decide)
      · have hq₁ : PPath q := fun t ht => hq t (List.mem_cons_of_mem _ ht)
        have hq₁' : PPath q' := fun t ht => hq' t (List.mem_cons_of_mem _ ht)
        cases st <;> cases st' <;> simp only [VarType.walk, VarType.step, hT,
          ↓reduceIte, Option.bind_some, Option.bind_none, reduceCtorEq] at hw hw' <;>
          (try exact absurd (hq _ List.mem_cons_self) (by decide)) <;>
          (try exact absurd (hq' _ List.mem_cons_self) (by decide))
        simp only [gPath, List.cons_append, List.cons.injEq, true_and] at h
        obtain ⟨hq, hr⟩ := ih q q' rest rest' hq₁ hq₁' hw hw' hk hk' h
        exact ⟨by rw [hq], hr⟩
  | VTypeDia A _ =>
      intro q q' U U' rest rest' hq hq' hw hw' hk hk' h
      rcases q with _ | ⟨st, q⟩
      · rcases q' with _ | ⟨st', q'⟩
        · exact ⟨rfl, by simpa [gPath] using h⟩
        · exfalso
          cases st' <;> simp [VarType.walk, VarType.step] at hw'
          exact absurd (hq' _ List.mem_cons_self) (by decide)
      · exfalso
        cases st <;> simp [VarType.walk, VarType.step] at hw
        exact absurd (hq _ List.mem_cons_self) (by decide)

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- ⭐**Along an edge whose entries are images, the index map is injective on keep-first
    addresses** below the base's kept items. -/
theorem late_inj (hT : ModalSys.T = true) (hF : ModalSys.Four = true) {l L : List VarType}
    (hsuf : l <:+ L) {g : VarSymb → LEnt σ}
    (hg : ∀ v T, (ctxOf l).kView none v = some T → g v = .inl (gchildMap L none v))
    {u u' : VarSymb} {rest rest' : List Step} {U U' : VarType}
    (hu : (ctxOf l).ref u = some U) (hk : U.keepable = true)
    (hu' : (ctxOf l).ref u' = some U') (hk' : U'.keepable = true)
    (h : eIdx g ((VarSymb.step u .keep).ext rest) = eIdx g ((VarSymb.step u' .keep).ext rest')) :
    (VarSymb.step u .keep).ext rest = (VarSymb.step u' .keep).ext rest' := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  obtain ⟨hpu, -⟩ := reach_ppath hu
  obtain ⟨hpu', -⟩ := reach_ppath hu'
  obtain ⟨r, hr, hlt, hR⟩ := ref_rt hu
  obtain ⟨r', hr', hlt', hR'⟩ := ref_rt hu'
  rw [eIdx_item g hpu rfl rest, eIdx_item g hpu' rfl rest',
    hg (.step u .keep) U (Ctx.boxIn_keep_of' hF hu hk),
    hg (.step u' .keep) U' (Ctx.boxIn_keep_of' hF hu' hk')] at h
  change (gImg L id (.step u .keep)).ext rest = (gImg L id (.step u' .keep)).ext rest' at h
  rw [gImg_item L id hr, gImg_item L id hr', ext_ext, ext_ext] at h
  have hrt := congrArg VarSymb.rt h
  rw [VarSymb.ext_rt, VarSymb.ext_rt] at hrt
  obtain rfl : r = r' := by
    have e : Root.free r = Root.free r' := hrt
    injection e
  have hpa := congrArg VarSymb.path h
  rw [VarSymb.ext_path, VarSymb.ext_path] at hpa
  have hL : rootTy L r = rootTy l r := by
    have e₁ := ctxOf_le_of_suffix hsuf (.root (.free r)) _ (ctxOf_root_lt hlt)
    rw [ctxOf_root_lt (lt_of_lt_of_le hlt hsuf.length_le)] at e₁
    exact Option.some.inj e₁
  have hw : ∀ {v : VarSymb} {V : VarType}, (ctxOf l).ref v = some V → v.rt = .free r →
      (rootTy L r).walk v.path = some V := fun {v V} hv hvr => by
    have e := Ctx.ref_ext_ppath (ctxOf l) v.path (.root v.rt) (reach_ppath hv).1
    rw [← eq_root_ext v, hv, hvr, Ctx.ref_nonproj _ rfl, ctxOf_root_lt hlt, ← hL] at e
    exact e.symm
  obtain ⟨hq, hrest⟩ := gPath_keep_inj hT hko (rootTy L r) u.path u'.path rest rest' hpu hpu'
    (hw hu hr) (hw hu' hr') hk hk' (by simpa using hpa)
  have e₁ := eq_root_ext u
  have e₂ := eq_root_ext u'
  rw [hr, hq] at e₁
  rw [hr'] at e₂
  rw [e₁.trans e₂.symm, hrest]


/-! ## Tags determine annotations -/

variable (hF M₀) in
/-- Labels of possible addresses are injective in every canonical environment pushed `j` views
    in. -/
def LabInjAt (j : ℕ) : Prop :=
  ∀ (s : GW hF M₀) (i : ℕ) (Δ : Ctx) (ρ : GEnv hF M₀ Δ s), Pushed hF M₀ s i Δ ρ j →
    ∀ (y y' : VarSymb) (X X' : VarType) (h : Δ.ref y = some (.VTypeDia X))
      (h' : Δ.ref y' = some (.VTypeDia X')), (ρ.ref j y h).label = (ρ.ref j y' h').label → y = y'

/-- ⭐**Shapes determine annotations** in a pushed canonical environment, for terms whose depth
    with the context's is at most `n`, when labels are injective below `n`. -/
theorem ann_eq_of_termShp_pushed {n : ℕ} (hL : ∀ k < n, LabInjAt hF M₀ k) :
    ∀ {s : GW hF M₀} {i : ℕ} {Δ : Ctx} {ρ : GEnv hF M₀ Δ s} {j : ℕ}, Pushed hF M₀ s i Δ ρ j →
      ∀ {A : VarType} {a a' : Ann A} (t : Term σ Δ A a) (t' : Term σ Δ A a'),
        j + t.mdepth ≤ n → Model.termShp ρ j t = Model.termShp ρ j t' → a = a'
  | _, _, _, _, _, _, _, _, _, .var _ _, .var _ _, _, _ => rfl
  | _, _, _, _, _, _, _, _, _, .var _ _, .func _, _, _ => rfl
  | _, _, _, _, _, _, _, _, _, .func _, .var _ _, _, _ => rfl
  | _, _, _, _, _, _, _, _, _, .func _, .func _, _, _ => rfl
  | _, _, _, _, _, _, _, _, _, .unit, .unit, _, _ => rfl
  | _, _, _, _, j, hP, _, _, _, .pair t₁ t₂, .pair t₁' t₂', hn, h => by
      change Shp.prod _ _ = Shp.prod _ _ at h
      injection h with _ _ h₁ h₂
      change j + max t₁.mdepth t₂.mdepth ≤ n at hn
      rw [ann_eq_of_termShp_pushed hL hP t₁ t₁' (by omega) h₁,
        ann_eq_of_termShp_pushed hL hP t₂ t₂' (by omega) h₂]
  | _, _, _, _, j, hP, _, _, _, .boxtm u, .boxtm u', hn, h => by
      change Shp.box _ = Shp.box _ at h
      injection h with _ h₁
      change j + (u.mdepth + 1) ≤ n at hn
      rw [ann_eq_of_termShp_pushed hL hP.box u u' (by omega) h₁]
  | s, i, Δ, ρ, j, hP, _, _, _, .diatm x hx u, .diatm x' hx' u', hn, h => by
      obtain ⟨X, hr⟩ := id hx
      obtain ⟨X', hr'⟩ := id hx'
      rw [Model.termShp_diatm ρ j hr hx u, Model.termShp_diatm ρ j hr' hx' u'] at h
      injection h with _ hl hb
      change j + (u.mdepth + 1) ≤ n at hn
      obtain rfl := hL j (by omega) s i Δ ρ hP x x' X X' hr hr' hl
      obtain rfl : X = X' := by
        rw [hr] at hr'
        injection hr' with e
        injection e
      rw [ann_eq_of_termShp_pushed hL (hP.dia hr) u u' (by omega) hb]

/-- Level-free labels are injective: every possible address's canonical shape is generic. -/
theorem labInj_zero (hT : ModalSys.T = true)
    (hM₀ : Theory.IsMCS M₀) : LabInjAt hF M₀ 0 := by
  intro s i Δ ρ hP y y' X X' h h' hl
  cases hP
  rw [cEnv_ref hT hM₀ (Ctx.Le.refl _) y h, cEnv_ref hT hM₀ (Ctx.Le.refl _) y' h',
    cEnv_dia_generic hT hM₀ ⟨i, h⟩,
    cEnv_dia_generic hT hM₀ ⟨i, h'⟩] at hl
  have hl' : (Arrows.Leaf.root y [] : GLeaf hF M₀ s) = .root y' [] := hl
  injection hl' with _ h₁

/-- ⭐**Keep-first labels are injective**, given shapes determine annotations at the depth: wrapped
    into terms of the `□` view and read along a late edge, the two addresses' images have equal
    annotations at the child (`edge_shp`), and the late edge's index map is injective
    (`late_inj`). -/
theorem labInj_kf (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {j : ℕ}
    (hL : ∀ k < j + 1, LabInjAt hF M₀ k) {s : GW hF M₀} {i : ℕ} {Δ : Ctx}
    {ρ : GEnv hF M₀ Δ s} (hP : Pushed hF M₀ s i Δ ρ (j + 1)) {y y' : VarSymb} {X X' : VarType}
    (h : Δ.ref y = some (.VTypeDia X)) (h' : Δ.ref y' = some (.VTypeDia X')) (hky : KF y)
    (hky' : KF y') (hl : (ρ.ref (j + 1) y h).label = (ρ.ref (j + 1) y' h').label) : y = y' := by
  obtain ⟨Δ', w, hle, hlen, hag, hk⟩ := hP.kpart
  have hy := hk y _ hky h
  have hy' := hk y' _ hky' h'
  have hl' : (((famEnv cEnv (ctxOf (glat s i)) s).pushAlong w).ref (j + 1) y hy).label =
      (((famEnv cEnv (ctxOf (glat s i)) s).pushAlong w).ref (j + 1) y' hy').label := by
    rw [Model.ShEnv.ref_agree hag (j + 1) y hy, Model.ShEnv.ref_agree hag (j + 1) y' hy']
    exact hl
  have hu : Model.termShp ((famEnv cEnv (ctxOf (glat s i)) s).pushAlong w) (w.len + 1)
      (Term.diatm (σ := σ) y ⟨X, hy⟩ .unit) =
        Model.termShp ((famEnv cEnv (ctxOf (glat s i)) s).pushAlong w) (w.len + 1)
          (Term.diatm (σ := σ) y' ⟨X', hy'⟩ .unit) := by
    rw [Model.termShp_diatm _ _ hy, Model.termShp_diatm _ _ hy', hlen, hl']
    rfl
  have hw := Model.termShp_wrap_congr (famEnv cEnv (ctxOf (glat s i)) s) w _ _ hu
  obtain ⟨t, c, hc, L, hsuf, hg⟩ := glate hT hM₀ s i
  have he := congrArg (unT (edgeAcc hc)) hw
  rw [edge_shp hT hM₀ hc i, edge_shp hT hM₀ hc i] at he
  have ha := ann_eq_of_termShp_pushed (n := j + 1) hL (Pushed.base (s := t) (i := glstg s t i))
    _ _ (by
      rw [Term.mdepth_subst, Wr.mdepth_wrap, hlen]
      change 0 + (j + (0 + 1)) ≤ j + 1
      omega) he
  have ha' := Wr.mapIdx_ann_inj _ w ha
  change Ann.dia (eIdx _ y) .one = Ann.dia (eIdx _ y') .one at ha'
  injection ha' with _ hι
  obtain ⟨u₀, rest, hu₀, rfl⟩ := hky
  obtain ⟨u₀', rest', hu₀', rfl⟩ := hky'
  obtain ⟨U, hU, hkU⟩ := hP.kf_prefix _ h u₀ rest hu₀ rfl
  obtain ⟨U', hU', hkU'⟩ := hP.kf_prefix _ h' u₀' rest' hu₀' rfl
  exact late_inj hT hF hsuf hg hU hkU hU' hkU' hι

/-- ⭐⭐**Labels are injective** in every pushed canonical environment, by induction on the depth:
    root-level labels spell their addresses, keep-first ones are families told apart along a late
    edge by the shallower case (`labInj_kf`). -/
theorem labInj (hT : ModalSys.T = true)
    (hM₀ : Theory.IsMCS M₀) : ∀ j, LabInjAt hF M₀ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero => exact labInj_zero hT hM₀
    | succ j =>
      intro s i Δ ρ hP y y' X X' h h' hl
      rcases hP.label_cases hT hM₀ h with ⟨pre, q, -, rfl, hy⟩ | ⟨hky, hfy⟩ <;>
        rcases hP.label_cases hT hM₀ h' with ⟨pre', q', -, rfl, hy'⟩ | ⟨hky', hfy'⟩
      · rw [hy, hy'] at hl
        injection hl with _ h₁ h₂
        subst h₁
        injection h₂ with _ h₃
        rw [h₃]
      · rw [← hl, hy] at hfy'
        exact hfy'.elim
      · rw [hl, hy'] at hfy
        exact hfy.elim
      · exact labInj_kf hT hM₀ ih hP h h' hky hky' hl

/-- ⭐⭐**Canonical shapes determine annotations**: two terms of a stage's language with the same
    canonical shape have the same annotation. -/
theorem ann_eq_of_termShp (hT : ModalSys.T = true)
    (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {i : ℕ} {A : VarType} {a a' : Ann A}
    (t : Term σ (ctxOf (glat s i)) A a) (t' : Term σ (ctxOf (glat s i)) A a')
    (h : Model.termShp (famEnv cEnv (ctxOf (glat s i)) s) 0 t =
      Model.termShp (famEnv cEnv (ctxOf (glat s i)) s) 0 t') : a = a' :=
  ann_eq_of_termShp_pushed (n := t.mdepth) (fun k _ => labInj hT hM₀ k) Pushed.base t t'
    (Nat.zero_add _).le h

/-- ⭐⭐**Tags determine annotations**: under T, two terms with one denotation have one
    annotation. -/
theorem ann_eq_of_grden (hT : ModalSys.T = true)
    (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {i : ℕ} {A : VarType} {a a' : Ann A}
    (t : Term σ (ctxOf (glat s i)) A a) (t' : Term σ (ctxOf (glat s i)) A a')
    (h : grden hM₀ s i (Ctx.Le.refl _) t = grden hM₀ s i (Ctx.Le.refl _) t') : a = a' :=
  ann_eq_of_termShp hT hM₀ t t' (by
    rw [← grawShape_grden (hM₀ := hM₀) hT s i (Ctx.Le.refl _) t,
      ← grawShape_grden (hM₀ := hM₀) hT s i (Ctx.Le.refl _) t', h])

end GArrow

end V12M
