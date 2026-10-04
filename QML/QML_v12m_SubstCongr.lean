import QML.QML_v12m_Subst

/-!
# QML v12m — substitution depends only on its entries, up to η

`Term.eta w T` is the η-expansion of an address `w : T` (`pair`, `boxtm`, `diatm` down to base
addresses).  An entry `ren w` and the term entry `tm (eta w T)` substitute identically
(`SubE.Sim`).  Main result: substituting with two substitutions whose entries agree up to η at
every visible address gives the same result, whatever their annotation maps (`WFF.subst_congr`).

Under T, the `here` component of an η-expanded necessary address is the η-expansion of its `here`
address (`Term.collapse_eta`), so η-agreement survives the `here` projection.
-/

namespace V12M

/-! ## η-expansion -/

variable [ModalSys]

def Ann.eta : VarSymb → (T : VarType) → Ann T
  | _, .Var => .var
  | _, .VTypeOne => .one
  | w, .VTypeProd A B => .prod (Ann.eta (.step w .fst) A) (Ann.eta (.step w .snd) B)
  | w, .VTypeBox A => .box (Ann.eta w.inner A)
  | w, .VTypeDia A => .dia w (Ann.eta (.step w .dia) A)

namespace Ctx

theorem ref_fst_of {Γ : Ctx} {w : VarSymb} {A B : VarType}
    (h : Γ.ref w = some (.VTypeProd A B)) : Γ.ref (.step w .fst) = some A := by
  rw [Ctx.ref_step_proj _ _ rfl, h]
  rfl

theorem ref_snd_of {Γ : Ctx} {w : VarSymb} {A B : VarType}
    (h : Γ.ref w = some (.VTypeProd A B)) : Γ.ref (.step w .snd) = some B := by
  rw [Ctx.ref_step_proj _ _ rfl, h]
  rfl

theorem ref_here_of {Γ : Ctx} (hT : ModalSys.T = true) {w : VarSymb} {A : VarType}
    (h : Γ.ref w = some (.VTypeBox A)) : Γ.ref (.step w .here) = some A := by
  rw [Ctx.ref_step_proj _ _ rfl, h]
  simp only [Option.bind_some, VarType.step, hT, if_true]

theorem ref_boxIn_of {Γ : Ctx} (hk : ModalSys.keepOnly = false) {w : VarSymb} {A : VarType}
    (h : Γ.ref w = some (.VTypeBox A)) : Γ.boxIn.ref (.step w .box) = some A := by
  rw [Ctx.ref_nonproj _ (rfl : (VarSymb.step w .box).lastProj = false)]
  exact Ctx.boxIn_box_of hk h

end Ctx

/-- ⭐The η-expansion of a reachable address. -/
def Term.eta {σ : Signature} : {Γ : Ctx} → (w : VarSymb) → (T : VarType) →
    Γ.ref w = some T → Term σ Γ T (Ann.eta w T)
  | _, w, .Var, h => .var w h
  | _, _, .VTypeOne, _ => .unit
  | _, w, .VTypeProd A B, h =>
      .pair (Term.eta (.step w .fst) A (Ctx.ref_fst_of h))
        (Term.eta (.step w .snd) B (Ctx.ref_snd_of h))
  | _, w, .VTypeBox A, h => .boxtm (Term.eta w.inner A (Ctx.ref_inner h))
  | _, w, .VTypeDia A, h => .diatm w ⟨A, h⟩ (Term.eta (.step w .dia) A (Ctx.ref_diaIn_of h))

theorem Term.mono_eta {σ : Signature} : ∀ {Γ Γ' : Ctx} (hle : Γ.Le Γ') (w : VarSymb)
    (T : VarType) (h : Γ.ref w = some T),
    Term.mono hle (Term.eta (σ := σ) w T h) = Term.eta w T (hle.ref h)
  | _, _, _, _, .Var, _ => rfl
  | _, _, _, _, .VTypeOne, _ => rfl
  | _, _, hle, w, .VTypeProd A B, h => by
      change Term.pair (Term.mono hle (Term.eta _ A _)) (Term.mono hle (Term.eta _ B _)) = _
      rw [Term.mono_eta hle _ A, Term.mono_eta hle _ B]
      rfl
  | _, _, hle, w, .VTypeBox A, h => by
      change Term.boxtm (Term.mono hle.boxIn (Term.eta _ A _)) = _
      rw [Term.mono_eta hle.boxIn _ A]
      rfl
  | _, _, hle, w, .VTypeDia A, h => by
      change Term.diatm w _ (Term.mono (hle.diaIn w) (Term.eta _ A _)) = _
      rw [Term.mono_eta (hle.diaIn w) _ A]
      rfl

/-! ## Terms packed with their annotations -/

section Sig

variable {σ : Signature}

theorem sig_pair {Γ : Ctx} {A B : VarType} {a a' : Ann A} {b b' : Ann B}
    {s : Term σ Γ A a} {s' : Term σ Γ A a'} {t : Term σ Γ B b} {t' : Term σ Γ B b'}
    (h₁ : (⟨a, s⟩ : Σ c, Term σ Γ A c) = ⟨a', s'⟩)
    (h₂ : (⟨b, t⟩ : Σ c, Term σ Γ B c) = ⟨b', t'⟩) :
    (⟨_, Term.pair s t⟩ : Σ c, Term σ Γ (.VTypeProd A B) c) = ⟨_, Term.pair s' t'⟩ := by
  cases h₁
  cases h₂
  rfl

theorem sig_boxtm {Γ : Ctx} {A : VarType} {a a' : Ann A} {s : Term σ Γ.boxIn A a}
    {s' : Term σ Γ.boxIn A a'} (h : (⟨a, s⟩ : Σ c, Term σ Γ.boxIn A c) = ⟨a', s'⟩) :
    (⟨_, Term.boxtm s⟩ : Σ c, Term σ Γ (.VTypeBox A) c) = ⟨_, Term.boxtm s'⟩ := by
  cases h
  rfl

theorem sig_diatm {Γ : Ctx} {A : VarType} {x : VarSymb}
    {hx hx' : ∃ X, Γ.ref x = some (.VTypeDia X)} {a a' : Ann A} {s : Term σ (Γ.diaIn x) A a}
    {s' : Term σ (Γ.diaIn x) A a'} (h : (⟨a, s⟩ : Σ c, Term σ (Γ.diaIn x) A c) = ⟨a', s'⟩) :
    (⟨_, Term.diatm x hx s⟩ : Σ c, Term σ Γ (.VTypeDia A) c) = ⟨_, Term.diatm x hx' s'⟩ := by
  cases h
  rfl

/-- Substituting into equal terms, annotations included: the outer annotation follows the inner
    one, so the equation has to be moved as a `Sigma` rather than rewritten. -/
theorem sig_subst {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) {T : VarType} {a a' : Ann T} {t : Term σ Γ T a} {t' : Term σ Γ T a'}
    (h : (⟨a, t⟩ : Σ c, Term σ Γ T c) = ⟨a', t'⟩) :
    (⟨_, Term.subst ι θ hθ hc t⟩ : Σ c, Term σ Δ T c) = ⟨_, Term.subst ι θ hθ hc t'⟩ := by
  cases h
  rfl

theorem SubE.tm_eq_of_sig {Δ : Ctx} {T : VarType} {a a' : Ann T} {t : Term σ Δ T a}
    {t' : Term σ Δ T a'} (h : (⟨a, t⟩ : Σ c, Term σ Δ T c) = ⟨a', t'⟩) :
    SubE.tm t = SubE.tm t' := by
  cases h
  rfl

theorem Term.eta_congr {Γ : Ctx} {w w' : VarSymb} (e : w = w') (T : VarType)
    (h : Γ.ref w = some T) (h' : Γ.ref w' = some T) :
    (⟨_, Term.eta (σ := σ) w T h⟩ : Σ b, Term σ Γ T b) = ⟨_, Term.eta w' T h'⟩ := by
  subst e
  rfl

end Sig

/-- Collapsing an η-expansion expands the collapsed address. -/
theorem Term.collapse_eta {σ : Signature} : ∀ {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Collapses k Γ₁ Γ₂)
    (w : VarSymb) (T : VarType) (hw : Γ₁.ref w = some T),
    (⟨_, Term.collapse h (Term.eta (σ := σ) w T hw)⟩ : Σ b, Term σ Γ₂ T b) =
      ⟨_, Term.eta (w.collapse k) T (h w T hw)⟩
  | _, _, _, _, _, .Var, _ => rfl
  | _, _, _, _, _, .VTypeOne, _ => rfl
  | _, _, _, h, w, .VTypeProd A B, hw =>
      sig_pair
        ((Term.collapse_eta h (.step w .fst) A (Ctx.ref_fst_of hw)).trans
          (Term.eta_congr (VarSymb.collapse_proj (s := .fst) rfl) A _ _))
        ((Term.collapse_eta h (.step w .snd) B (Ctx.ref_snd_of hw)).trans
          (Term.eta_congr (VarSymb.collapse_proj (s := .snd) rfl) B _ _))
  | _, _, _, h, w, .VTypeBox A, hw =>
      sig_boxtm ((Term.collapse_eta h.boxIn w.inner A (Ctx.ref_inner hw)).trans
        (Term.eta_congr (VarSymb.inner_collapse_succ w _) A _ _))
  | _, _, _, h, w, .VTypeDia A, hw =>
      sig_diatm ((Term.collapse_eta (h.diaIn w) (.step w .dia) A (Ctx.ref_diaIn_of hw)).trans
        (Term.eta_congr (VarSymb.collapse_level_succ (s := .dia) rfl) A _ _))

/-- Under T, the `here` component of an η-expanded necessary address. -/
theorem SubE.proj_here_eta {σ : Signature} {Δ : Ctx} (hT : ModalSys.T = true) {w : VarSymb}
    {A : VarType} (hw : Δ.ref w = some (.VTypeBox A)) :
    (SubE.tm (Term.eta (σ := σ) w (.VTypeBox A) hw)).proj .here =
      SubE.tm (Term.eta (.step w .here) A (Ctx.ref_here_of hT hw)) := by
  change (SubE.tm (Term.boxtm (Term.eta (σ := σ) w.inner A (Ctx.ref_inner hw)))).proj .here = _
  rw [SubE.proj_boxtm_here _ hT]
  exact SubE.tm_eq_of_sig ((Term.collapse_eta _ _ A _).trans
    (Term.eta_congr (VarSymb.inner_collapse_zero w) A _ _))

/-- Shifting an η-expansion expands the shifted address. -/
theorem Term.shift_eta {σ : Signature} : ∀ {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Shifts k Γ₁ Γ₂)
    (w : VarSymb) (T : VarType) (hw : Γ₁.ref w = some T),
    (⟨_, Term.shift h (Term.eta (σ := σ) w T hw)⟩ : Σ b, Term σ Γ₂ T b) =
      ⟨_, Term.eta (w.shift k) T (h w T hw)⟩
  | _, _, _, _, _, .Var, _ => rfl
  | _, _, _, _, _, .VTypeOne, _ => rfl
  | _, _, _, h, w, .VTypeProd A B, hw =>
      sig_pair
        ((Term.shift_eta h (.step w .fst) A (Ctx.ref_fst_of hw)).trans
          (Term.eta_congr (VarSymb.shift_proj (s := .fst) rfl) A _ _))
        ((Term.shift_eta h (.step w .snd) B (Ctx.ref_snd_of hw)).trans
          (Term.eta_congr (VarSymb.shift_proj (s := .snd) rfl) B _ _))
  | _, _, _, h, w, .VTypeBox A, hw =>
      sig_boxtm ((Term.shift_eta h.boxIn w.inner A (Ctx.ref_inner hw)).trans
        (Term.eta_congr (VarSymb.inner_shift_succ w _) A _ _))
  | _, _, _, h, w, .VTypeDia A, hw =>
      sig_diatm ((Term.shift_eta (h.diaIn w) (.step w .dia) A (Ctx.ref_diaIn_of hw)).trans
        (Term.eta_congr (VarSymb.shift_level_succ (s := .dia) rfl) A _ _))

/-- Under 4, the kept component of an η-expanded necessary address. -/
theorem SubE.keepE_eta {σ : Signature} {Δ : Ctx} (hF : ModalSys.Four = true) {w : VarSymb}
    {A : VarType} (hw : Δ.ref w = some (.VTypeBox A)) :
    (SubE.tm (Term.eta (σ := σ) w (.VTypeBox A) hw)).keepE =
      SubE.tm (Term.eta (.step w .keep) (.VTypeBox A) (Ctx.ref_keep_of hF hw)) := by
  change (SubE.tm (Term.boxtm (Term.eta (σ := σ) w.inner A (Ctx.ref_inner hw)))).keepE = _
  rw [SubE.keepE_tm _ hF]
  exact SubE.tm_eq_of_sig (sig_boxtm ((Term.shift_eta _ _ A _).trans
    (Term.eta_congr (VarSymb.inner_shift_zero w) A _ _)))

/-! ## Entries agreeing up to η -/

namespace SubE

variable {σ : Signature} {Δ : Ctx}

inductive Sim : VarType → SubE σ Δ → SubE σ Δ → Prop
  | refl {T : VarType} (e : SubE σ Δ) : Sim T e e
  | eta_ren {T : VarType} (w : VarSymb) (h : Δ.ref w = some T) :
      Sim T (.tm (Term.eta w T h)) (.ren w)
  | ren_eta {T : VarType} (w : VarSymb) (h : Δ.ref w = some T) :
      Sim T (.ren w) (.tm (Term.eta w T h))

theorem Sim.proj_step {U T : VarType} {s : Step} {e e' : SubE σ Δ} (h : Sim U e e')
    (hs : s.isProj = true) (hst : U.step s = some T) : Sim T (e.proj s) (e'.proj s) := by
  cases s with
  | box => cases hs
  | dia => cases hs
  | keep => cases hs
  | here =>
      cases U <;> try cases hst
      obtain ⟨hT, hAT⟩ := VarType.step_here hst
      subst hAT
      cases h with
      | refl => exact .refl _
      | eta_ren w h =>
          rw [SubE.proj_here_eta hT h]
          exact .eta_ren _ _
      | ren_eta w h =>
          rw [SubE.proj_here_eta hT h]
          exact .ren_eta _ _
  | fst =>
      cases U <;> cases hst
      cases h with
      | refl => exact .refl _
      | eta_ren w h => exact .eta_ren _ (Ctx.ref_fst_of h)
      | ren_eta w h => exact .ren_eta _ (Ctx.ref_fst_of h)
  | snd =>
      cases U <;> cases hst
      cases h with
      | refl => exact .refl _
      | eta_ren w h => exact .eta_ren _ (Ctx.ref_snd_of h)
      | ren_eta w h => exact .ren_eta _ (Ctx.ref_snd_of h)

theorem Sim.unbox {A : VarType} {e e' : SubE σ Δ} (h : Sim (.VTypeBox A) e e') :
    Sim A e.unbox e'.unbox := by
  cases h with
  | refl => exact .refl _
  | eta_ren w h => exact .eta_ren _ (Ctx.ref_inner h)
  | ren_eta w h => exact .ren_eta _ (Ctx.ref_inner h)

theorem Sim.keepE (hF : ModalSys.Four = true) {A : VarType} {e e' : SubE σ Δ}
    (h : Sim (.VTypeBox A) e e') : Sim (.VTypeBox A) e.keepE e'.keepE := by
  cases h with
  | refl => exact .refl _
  | eta_ren w h =>
      rw [SubE.keepE_eta hF h]
      exact .eta_ren _ _
  | ren_eta w h =>
      rw [SubE.keepE_eta hF h]
      exact .ren_eta _ _

theorem Sim.mono {Δ' : Ctx} (hle : Δ.Le Δ') {T : VarType} {e e' : SubE σ Δ} (h : Sim T e e') :
    Sim T (e.mono hle) (e'.mono hle) := by
  cases h with
  | refl => exact .refl _
  | eta_ren w h =>
      change Sim T (.tm (Term.mono hle (Term.eta w T h))) (.ren w)
      rw [Term.mono_eta]
      exact .eta_ren _ _
  | ren_eta w h =>
      change Sim T (.ren w) (.tm (Term.mono hle (Term.eta w T h)))
      rw [Term.mono_eta]
      exact .ren_eta _ _

theorem Sim.idx {X : VarType} {e e' : SubE σ Δ} (h : Sim (.VTypeDia X) e e') :
    e.idxAlong [] = e'.idxAlong [] := by
  cases h <;> rfl

theorem Sim.toVar {e e' : SubE σ Δ} (h : Sim .Var e e') (he : e.OkRef .Var)
    (he' : e'.OkRef .Var) : e.toVar he = e'.toVar he' := by
  cases h <;> rfl

theorem Sim.diaBody {X : VarType} {ιx : VarSymb} {e e' : SubE σ Δ} (h : Sim (.VTypeDia X) e e')
    (hw : e.idxAlong [] = ιx) : Sim X (e.diaBody ιx) (e'.diaBody ιx) := by
  cases h with
  | refl => exact .refl _
  | eta_ren w h =>
      have hw' : w = ιx := hw
      subst hw'
      rw [show (SubE.tm (Term.eta (σ := σ) w (.VTypeDia X) h)).diaBody w =
        SubE.tm (Term.mono (Ctx.Le.refl _) (Term.eta (.step w .dia) X (Ctx.ref_diaIn_of h)))
        from dif_pos rfl, Term.mono_eta]
      exact .eta_ren _ _
  | ren_eta w h =>
      have hw' : w = ιx := hw
      subst hw'
      rw [show (SubE.tm (Term.eta (σ := σ) w (.VTypeDia X) h)).diaBody w =
        SubE.tm (Term.mono (Ctx.Le.refl _) (Term.eta (.step w .dia) X (Ctx.ref_diaIn_of h)))
        from dif_pos rfl, Term.mono_eta]
      exact .ren_eta _ _

end SubE

/-! ## Agreement at every reachable address -/

namespace Subst

variable {σ : Signature} {Δ : Ctx}

/-- Two substitutions agree up to η at every reachable address of `Γ`. -/
def Sim (Γ : Ctx) (θ θ' : Subst σ Δ) : Prop :=
  ∀ v T, Γ.ref v = some T → SubE.Sim T (θ.at v) (θ'.at v)

theorem sim_of {Γ : Ctx} {θ θ' : Subst σ Δ}
    (hvis : ∀ v T, v.lastProj = false → Γ v = some T → SubE.Sim T (θ v) (θ' v)) :
    Sim Γ θ θ' := by
  intro v
  induction v with
  | root r => intro T hv; exact hvis _ _ rfl hv
  | step v s ih =>
      intro T hv
      simp only [Ctx.ref] at hv
      simp only [Subst.at]
      split_ifs at hv ⊢ with hs
      · cases hU : Γ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U =>
            rw [hU] at hv
            exact (ih U hU).proj_step hs hv
      · exact hvis _ _ (show (VarSymb.step v s).lastProj = false from Bool.eq_false_iff.mpr hs) hv

theorem sim_box {Γ : Ctx} {θ θ' : Subst σ Δ} (hs : Sim Γ θ θ') : Sim Γ.boxIn θ.box θ'.box := by
  refine sim_of ?_
  intro v T _ hv
  match v with
  | .step u .box => exact (hs u _ (Ctx.boxIn_step_box hv)).unbox
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep hv
      exact (hs u _ hu).keepE hF
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem sim_dia {Γ : Ctx} {θ θ' : Subst σ Δ} (hs : Sim Γ θ θ') {x ιx : VarSymb}
    (hw : (θ.at x).idxAlong [] = ιx) : Sim (Γ.diaIn x) (θ.dia x ιx) (θ'.dia x ιx) := by
  refine sim_of ?_
  intro v T _ hv
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with hux
      · subst hux
        cases hx : Γ.ref u with
        | none => rw [hx] at hv; cases hv
        | some U =>
            rw [hx] at hv
            cases U <;> try cases hv
            change SubE.Sim _ (if u = u then (θ.at u).diaBody ιx else SubE.hide)
              (if u = u then (θ'.at u).diaBody ιx else SubE.hide)
            rw [if_pos rfl, if_pos rfl]
            exact (hs u _ hx).diaBody hw
  | .step u .box => exact (hs u _ (Ctx.boxIn_step_box (Γ := Γ) hv)).unbox.mono _
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep (Γ := Γ) hv
      exact ((hs u _ hu).keepE hF).mono _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

theorem sim_under {Γ : Ctx} {θ θ' : Subst σ Δ} (hs : Sim Γ θ θ') {d d' : ℕ} (T : VarType)
    (h : Δ (.root (.bnd d')) = none) :
    Sim (Γ.insert (.bnd d) T) (θ.under d d' T h) (θ'.under d d' T h) := by
  refine sim_of ?_
  intro v U hlp hv
  by_cases hvr : v = .root (.bnd d)
  · rw [show θ.under d d' T h v = .ren (.root (.bnd d')) from if_pos hvr,
      show θ'.under d d' T h v = .ren (.root (.bnd d')) from if_pos hvr]
    exact .refl _
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    rw [show θ.under d d' T h v = (θ v).mono (Ctx.le_insert h T) from if_neg hvr,
      show θ'.under d d' T h v = (θ' v).mono (Ctx.le_insert h T) from if_neg hvr]
    have h₁ := hs v U ((Ctx.ref_nonproj Γ hlp).trans hv')
    rw [Subst.at_nonproj θ hlp, Subst.at_nonproj θ' hlp] at h₁
    exact h₁.mono _

end Subst

/-! ## Congruence -/

section Congr

variable {σ : Signature}

/-- Coherent substitutions agreeing up to η pick the same witnesses. -/
theorem Subst.idx_eq {ι ι' : VarSymb → VarSymb} {Γ Δ : Ctx} {θ θ' : Subst σ Δ}
    (hc : Subst.Coh ι Γ θ) (hc' : Subst.Coh ι' Γ θ') (hs : Subst.Sim Γ θ θ') {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) : ι' x = ι x := by
  obtain ⟨X, hX⟩ := hx
  have h₁ : (θ.at x).idxAlong [] = ι x := hc x _ hX []
  have h₂ : (θ'.at x).idxAlong [] = ι' x := hc' x _ hX []
  exact h₂.symm.trans ((hs x _ hX).idx.symm.trans h₁)

mutual
  theorem Func.subst_congr {ι ι' : VarSymb → VarSymb} {Γ Δ : Ctx} (θ θ' : Subst σ Δ)
      (hθ : Subst.Ok Γ θ) (hθ' : Subst.Ok Γ θ') (hc : Subst.Coh ι Γ θ)
      (hc' : Subst.Coh ι' Γ θ') (hs : Subst.Sim Γ θ θ') :
      {n : ℕ} → (f : Func σ Γ n) → Func.subst ι θ hθ hc f = Func.subst ι' θ' hθ' hc' f
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.subst ι θ hθ hc g) (Term.subst ι θ hθ hc t) =
          Func.eval (Func.subst ι' θ' hθ' hc' g) (Term.subst ι' θ' hθ' hc' t)
        rw [Func.subst_congr θ θ' hθ hθ' hc hc' hs g,
          eq_of_heq (Sigma.mk.inj (Term.subst_congr θ θ' hθ hθ' hc hc' hs t)).2]
    termination_by structural _ f => f

  /-- ⭐Stated for `Σ`-packed terms: the annotation maps may differ. -/
  theorem Term.subst_congr {ι ι' : VarSymb → VarSymb} {Γ Δ : Ctx} (θ θ' : Subst σ Δ)
      (hθ : Subst.Ok Γ θ) (hθ' : Subst.Ok Γ θ') (hc : Subst.Coh ι Γ θ)
      (hc' : Subst.Coh ι' Γ θ') (hs : Subst.Sim Γ θ θ') :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ T a) →
      (⟨_, Term.subst ι θ hθ hc t⟩ : Σ b, Term σ Δ T b) = ⟨_, Term.subst ι' θ' hθ' hc' t⟩
    | _, _, .var v hv => congrArg (Sigma.mk _) ((hs v _ hv).toVar _ _)
    | _, _, .func f => by
        change (⟨_, Term.func (Func.subst ι θ hθ hc f)⟩ : Σ b, Term σ Δ .Var b) =
          ⟨_, Term.func (Func.subst ι' θ' hθ' hc' f)⟩
        rw [Func.subst_congr θ θ' hθ hθ' hc hc' hs f]
    | _, _, .unit => rfl
    | _, _, .pair s t =>
        sig_pair (Term.subst_congr θ θ' hθ hθ' hc hc' hs s)
          (Term.subst_congr θ θ' hθ hθ' hc hc' hs t)
    | _, _, .boxtm t =>
        sig_boxtm (Term.subst_congr θ.box θ'.box (Subst.ok_box hθ) (Subst.ok_box hθ')
          (Subst.coh_box hθ hc) (Subst.coh_box hθ' hc') (Subst.sim_box hs) t)
    | _, _, .diatm x hx t => by
        have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
        have key : ∀ (y : VarSymb) (_hy : y = ι x) (P : ∃ Y, Δ.ref y = some (.VTypeDia Y))
            (p : Subst.Ok (Γ.diaIn x) (θ'.dia x y))
            (q : Subst.Coh ι' (Γ.diaIn x) (θ'.dia x y)),
            (⟨_, Term.subst ι θ hθ hc (Term.diatm x hx t)⟩ : Σ b, Term σ Δ _ b) =
              ⟨_, Term.diatm y P (Term.subst ι' (θ'.dia x y) p q t)⟩ := by
          intro y hy P p q
          subst hy
          exact sig_diatm (Term.subst_congr (θ.dia x (ι x)) (θ'.dia x (ι x))
            (Subst.ok_dia hθ hx hw) p (Subst.coh_dia hθ hc hx) q (Subst.sim_dia hs hw) t)
        exact key (ι' x) (Subst.idx_eq hc hc' hs hx) _ _ _
    termination_by structural _ _ t => t
end

theorem Term.subst_congr_var {ι ι' : VarSymb → VarSymb} {Γ Δ : Ctx} (θ θ' : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hθ' : Subst.Ok Γ θ') (hc : Subst.Coh ι Γ θ)
    (hc' : Subst.Coh ι' Γ θ') (hs : Subst.Sim Γ θ θ') (t : Term σ Γ .Var .var) :
    Term.subst ι θ hθ hc t = Term.subst ι' θ' hθ' hc' t :=
  eq_of_heq (Sigma.mk.inj (Term.subst_congr θ θ' hθ hθ' hc hc' hs t)).2

theorem Rel.subst_congr {ι ι' : VarSymb → VarSymb} {Γ Δ : Ctx} (θ θ' : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hθ' : Subst.Ok Γ θ') (hc : Subst.Coh ι Γ θ)
    (hc' : Subst.Coh ι' Γ θ') (hs : Subst.Sim Γ θ θ') :
    {n : ℕ} → (ρ : Rel σ Γ n) → Rel.subst ι θ hθ hc ρ = Rel.subst ι' θ' hθ' hc' ρ
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.subst ι θ hθ hc ρ) (Term.subst ι θ hθ hc t) =
        Rel.eval (Rel.subst ι' θ' hθ' hc' ρ) (Term.subst ι' θ' hθ' hc' t)
      rw [Rel.subst_congr θ θ' hθ hθ' hc hc' hs ρ, Term.subst_congr_var θ θ' hθ hθ' hc hc' hs t]

/-- ⭐Substitution in formulas depends only on the entries up to η, not on the annotation map. -/
theorem WFF.subst_congr : {ι ι' : VarSymb → VarSymb} → {Γ Δ : Ctx} → {d d' : ℕ} →
    (θ θ' : Subst σ Δ) → (hθ : Subst.Ok Γ θ) → (hθ' : Subst.Ok Γ θ') →
    (hc : Subst.Coh ι Γ θ) → (hc' : Subst.Coh ι' Γ θ') → (hΓ : Γ.SlotsFrom d) →
    (hΔ : Δ.SlotsFrom d') → Subst.Sim Γ θ θ' → (φ : WFF σ Γ d) →
    WFF.subst ι θ hθ hc hΓ hΔ φ = WFF.subst ι' θ' hθ' hc' hΓ hΔ φ
  | _, _, _, _, _, _, θ, θ', hθ, hθ', hc, hc', _, _, hs, .atom ρ =>
      congrArg WFF.atom (Rel.subst_congr θ θ' hθ hθ' hc hc' hs ρ)
  | _, _, _, _, _, _, θ, θ', hθ, hθ', hc, hc', _, _, hs, .eq t s =>
      congrArg₂ WFF.eq (Term.subst_congr_var θ θ' hθ hθ' hc hc' hs t)
        (Term.subst_congr_var θ θ' hθ hθ' hc hc' hs s)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, _, _, θ, θ', hθ, hθ', hc, hc', hΓ, hΔ, hs, .and φ ψ =>
      congrArg₂ WFF.and (WFF.subst_congr θ θ' hθ hθ' hc hc' hΓ hΔ hs φ)
        (WFF.subst_congr θ θ' hθ hθ' hc hc' hΓ hΔ hs ψ)
  | _, _, _, _, _, _, θ, θ', hθ, hθ', hc, hc', hΓ, hΔ, hs, .or φ ψ =>
      congrArg₂ WFF.or (WFF.subst_congr θ θ' hθ hθ' hc hc' hΓ hΔ hs φ)
        (WFF.subst_congr θ θ' hθ hθ' hc hc' hΓ hΔ hs ψ)
  | _, _, _, _, _, _, θ, θ', hθ, hθ', hc, hc', hΓ, hΔ, hs, .imp φ ψ =>
      congrArg₂ WFF.imp (WFF.subst_congr θ θ' hθ hθ' hc hc' hΓ hΔ hs φ)
        (WFF.subst_congr θ θ' hθ hθ' hc hc' hΓ hΔ hs ψ)
  | _, _, _, _, d, d', θ, θ', hθ, hθ', hc, hc', hΓ, hΔ, hs, .all T φ =>
      congrArg (WFF.all T) (WFF.subst_congr (θ.under d d' T hΔ.root) (θ'.under d d' T hΔ.root)
        (Subst.ok_under hθ T hΔ.root) (Subst.ok_under hθ' T hΔ.root)
        (Subst.coh_under hθ hc hΓ T hΔ.root) (Subst.coh_under hθ' hc' hΓ T hΔ.root)
        (hΓ.insert T) (hΔ.insert T) (Subst.sim_under hs T hΔ.root) φ)
  | _, _, _, _, d, d', θ, θ', hθ, hθ', hc, hc', hΓ, hΔ, hs, .ex T φ =>
      congrArg (WFF.ex T) (WFF.subst_congr (θ.under d d' T hΔ.root) (θ'.under d d' T hΔ.root)
        (Subst.ok_under hθ T hΔ.root) (Subst.ok_under hθ' T hΔ.root)
        (Subst.coh_under hθ hc hΓ T hΔ.root) (Subst.coh_under hθ' hc' hΓ T hΔ.root)
        (hΓ.insert T) (hΔ.insert T) (Subst.sim_under hs T hΔ.root) φ)
  | _, _, _, _, _, _, θ, θ', hθ, hθ', hc, hc', hΓ, hΔ, hs, .box φ =>
      congrArg WFF.box (WFF.subst_congr θ.box θ'.box (Subst.ok_box hθ) (Subst.ok_box hθ')
        (Subst.coh_box hθ hc) (Subst.coh_box hθ' hc') hΓ.boxIn hΔ.boxIn (Subst.sim_box hs) φ)
  | ι, ι', Γ, Δ, _, d', θ, θ', hθ, hθ', hc, hc', hΓ, hΔ, hs, .dia x hx φ => by
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have key : ∀ (y : VarSymb) (_hy : y = ι x) (P : ∃ Y, Δ.ref y = some (.VTypeDia Y))
          (p : Subst.Ok (Γ.diaIn x) (θ'.dia x y)) (q : Subst.Coh ι' (Γ.diaIn x) (θ'.dia x y))
          (hΔy : (Δ.diaIn y).SlotsFrom d'),
          WFF.subst ι θ hθ hc hΓ hΔ (.dia x hx φ) =
            .dia y P (WFF.subst ι' (θ'.dia x y) p q (hΓ.diaIn x) hΔy φ) := by
        intro y hy P p q hΔy
        subst hy
        exact congrArg (WFF.dia (ι x) _) (WFF.subst_congr (θ.dia x (ι x)) (θ'.dia x (ι x))
          (Subst.ok_dia hθ hx hw) p (Subst.coh_dia hθ hc hx) q (hΓ.diaIn x) hΔy
          (Subst.sim_dia hs hw) φ)
      exact key (ι' x) (Subst.idx_eq hc hc' hs hx) _ _ _ _
  | _, _, _, _, _, _, θ, θ', hθ, hθ', hc, hc', _, _, hs, .here hT s t =>
      WFF.here_congr hT (Term.subst_congr θ θ' hθ hθ' hc hc' hs s)
        (Term.subst_congr θ θ' hθ hθ' hc hc' hs t)
  | _, _, _, _, _, _, θ, θ', hθ, hθ', hc, hc', _, _, hs, .back hB L s t =>
      WFF.back_congr hB L (Term.subst_congr θ θ' hθ hθ' hc hc' hs s)
        (Term.subst_congr θ θ' hθ hθ' hc hc' hs t)
  | _, _, _, _, d, d', θ, θ', hθ, hθ', hc, hc', hΓ, hΔ, hs, .ret hB t Φ =>
      WFF.ret_congr hB (Term.subst_congr θ θ' hθ hθ' hc hc' hs t)
        (WFF.subst_congr (θ.box.under d d' _ hΔ.boxIn.root) (θ'.box.under d d' _ hΔ.boxIn.root)
          (Subst.ok_under (Subst.ok_box hθ) _ hΔ.boxIn.root)
          (Subst.ok_under (Subst.ok_box hθ') _ hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn _ hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ') (Subst.coh_box hθ' hc') hΓ.boxIn _ hΔ.boxIn.root)
          (hΓ.boxIn.insert _) (hΔ.boxIn.insert _)
          (Subst.sim_under (Subst.sim_box hs) _ hΔ.boxIn.root)
          Φ)

end Congr

end V12M
