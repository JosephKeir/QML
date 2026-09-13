import QML.QML_v12m_Shift

/-!
# QML v12m — substitution

A substitution at some modal level sends each VISIBLE source address to an ENTRY over the current
target: an address (`ren`) or a term (`tm`).  Projection components are reached by projection
(`Subst.at`).  Under `□`, `◇_x` and binders the substitution is transformed pointwise
(`Subst.box`, `Subst.dia`, `Subst.under`).  Annotations are mapped by an address map `ι`;
`Subst.Coh` says the entries agree with it.

* The `□` case is literally `boxtm` of the substituted body — no out-map commutation.
* The `◇` case builds the new witness `ι x` directly; a term entry `◇_y u` for the witness
  contributes its body `u` (modal β).
* Under T, the `here` component of a term entry `□t` is `t` collapsed to the current level
  (`Term.collapse`); its annotation indices collapse accordingly (`Ann.idxAt`).
* Under 4, the kept component (`keep`) of a term entry `□t` is `□t` with its body shifted one view
  further in (`Term.shift`), and its annotation shifts accordingly.
* Under a binder the source slot `bnd d` goes to the target slot `bnd d'`, the other entries are
  weakened, and the address map is re-rooted there.

The instances the proof rules need all replace ONE root and leave every other address alone
(`Subst.single`), in any context: instantiation, substituting for a free variable, binding a free
variable to a slot, and (twice) pair elimination.
-/

namespace V12M

variable [ModalSys]

inductive SubE (σ : Signature) (Δ : Ctx) : Type where
  | hide
  | ren (w : VarSymb)
  | tm {T : VarType} {a : Ann T} (s : Term σ Δ T a)

namespace SubE

variable {σ : Signature} {Δ : Ctx}

def proj : SubE σ Δ → Step → SubE σ Δ
  | .ren w, s => .ren (.step w s)
  | .tm (.pair s _), .fst => .tm s
  | .tm (.pair _ t), .snd => .tm t
  | .tm (.boxtm t), .here =>
      if hT : ModalSys.T = true then .tm (Term.collapse (Ctx.collapses_boxIn_self hT Δ) t)
      else .hide
  | _, _ => .hide

def unbox : SubE σ Δ → SubE σ Δ.boxIn
  | .ren w => .ren (.step w .box)
  | .tm (.boxtm t) => .tm t
  | _ => .hide

/-- The kept component of a necessary entry, one view further in (under 4). -/
def keepE : SubE σ Δ → SubE σ Δ.boxIn
  | .ren w => .ren (.step w .keep)
  | .tm (.boxtm t) =>
      if hF : ModalSys.Four = true then .tm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Δ) t))
      else .hide
  | _ => .hide

def mono {Δ₁ Δ₂ : Ctx} (h : Δ₁.Le Δ₂) : SubE σ Δ₁ → SubE σ Δ₂
  | .hide => .hide
  | .ren w => .ren w
  | .tm s => .tm (Term.mono h s)

/-- The entry at the witness body, for the new witness `ιx` (modal β for a term entry). -/
def diaBody (ιx : VarSymb) : SubE σ Δ → SubE σ (Δ.diaIn ιx)
  | .ren _ => .ren (.step ιx .dia)
  | .tm (.diatm y _hy u) =>
      if h : y = ιx then .tm (Term.mono (by subst h; exact Ctx.Le.refl _) u) else .hide
  | _ => .hide

/-- The entry has plain type `T` in the target. -/
def OkRef : SubE σ Δ → VarType → Prop
  | .ren w, T => Δ.ref w = some T
  | .tm (T := U) _, T => U = T
  | .hide, _ => False

/-- Where an index below this entry lands. -/
def idxAlong : SubE σ Δ → List Step → VarSymb
  | .ren w, p => w.ext p
  | .tm (a := a) _, p => a.idxAt p
  | .hide, _ => .root (.free 0)

/-- A base-typed entry, as a term. -/
def toVar : (e : SubE σ Δ) → e.OkRef .Var → Term σ Δ .Var .var
  | .ren w, h => .var w h
  | .tm (.var v hv), _ => .var v hv
  | .tm (.func f), _ => .func f
  | .tm .unit, h => nomatch h
  | .tm (.pair _ _), h => nomatch h
  | .tm (.boxtm _), h => nomatch h
  | .tm (.diatm _ _ _), h => nomatch h
  | .hide, h => False.elim h

theorem proj_boxtm_here {A : VarType} {a : Ann A} (t : Term σ Δ.boxIn A a)
    (hT : ModalSys.T = true) :
    (SubE.tm (Term.boxtm t)).proj .here = .tm (Term.collapse (Ctx.collapses_boxIn_self hT Δ) t) :=
  dif_pos hT

theorem keepE_tm {A : VarType} {a : Ann A} (t : Term σ Δ.boxIn A a)
    (hF : ModalSys.Four = true) :
    (SubE.tm (Term.boxtm t)).keepE = .tm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Δ) t)) :=
  dif_pos hF

theorem okRef_proj : ∀ {e : SubE σ Δ} {U T : VarType} {s : Step}, e.OkRef U → s.isProj = true →
    U.step s = some T → (e.proj s).OkRef T
  | .ren w, U, T, s, he, hs, hst => by
      change (if s.isProj then (Δ.ref w).bind (·.step s) else Δ (.step w s)) = some T
      rw [if_pos hs, he]
      exact hst
  | .hide, _, _, _, he, _, _ => False.elim he
  | .tm (T := U') s₀, U, T, s, he, hs, hst => by
      have hU : U' = U := he
      subst hU
      cases s with
      | fst =>
          cases s₀ <;> cases hst
          rfl
      | snd =>
          cases s₀ <;> cases hst
          rfl
      | box => cases hs
      | dia => cases hs
      | keep => cases hs
      | here =>
          cases s₀ with
          | boxtm t =>
              obtain ⟨hT, hAT⟩ := VarType.step_here hst
              subst hAT
              rw [proj_boxtm_here t hT]
              rfl
          | _ => cases hst

theorem idxAlong_proj : ∀ {e : SubE σ Δ} {U T : VarType} {s : Step} (p : List Step),
    e.OkRef U → s.isProj = true → U.step s = some T →
      (e.proj s).idxAlong p = e.idxAlong (s :: p)
  | .ren _, _, _, _, _, _, _, _ => rfl
  | .hide, _, _, _, _, he, _, _ => False.elim he
  | .tm (T := U') s₀, U, T, s, p, he, hs, hst => by
      have hU : U' = U := he
      subst hU
      cases s with
      | fst => cases s₀ <;> rfl
      | snd => cases s₀ <;> rfl
      | box => cases hs
      | dia => cases hs
      | keep => cases hs
      | here =>
          cases s₀ with
          | boxtm t =>
              obtain ⟨hT, hAT⟩ := VarType.step_here hst
              subst hAT
              rw [proj_boxtm_here t hT]
              change (Ann.collapse 0 _).idxAt p = (Ann.idxAt _ p).collapse (Step.levels p)
              rw [Ann.idxAt_collapse, Nat.zero_add]
          | _ => cases hst

theorem okRef_unbox : ∀ {e : SubE σ Δ} {A : VarType}, e.OkRef (.VTypeBox A) → e.unbox.OkRef A
  | .ren w, A, he => by
      change (match Δ.ref w with | some (.VTypeBox A) => some A | _ => none) = some A
      rw [he]
  | .hide, _, he => False.elim he
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s
      rfl

theorem idxAlong_unbox : ∀ {e : SubE σ Δ} {A : VarType} (p : List Step),
    e.OkRef (.VTypeBox A) → e.unbox.idxAlong p = e.idxAlong (.box :: p)
  | .ren _, _, _, _ => rfl
  | .hide, _, _, he => False.elim he
  | .tm (T := U) s, A, p, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s
      rfl

theorem okRef_keepE (hF : ModalSys.Four = true) : ∀ {e : SubE σ Δ} {A : VarType},
    e.OkRef (.VTypeBox A) → e.keepE.OkRef (.VTypeBox A)
  | .ren _, _, he => Ctx.ref_keep_of hF he
  | .hide, _, he => False.elim he
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s with
      | boxtm t =>
          rw [keepE_tm t hF]
          rfl

theorem idxAlong_keepE (hF : ModalSys.Four = true) : ∀ {e : SubE σ Δ} {A : VarType}
    (p : List Step), e.OkRef (.VTypeBox A) → e.keepE.idxAlong p = e.idxAlong (.keep :: p)
  | .ren _, _, _, _ => rfl
  | .hide, _, _, he => False.elim he
  | .tm (T := U) s, A, p, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s with
      | boxtm t =>
          rw [keepE_tm t hF]
          rfl

theorem okRef_mono {Δ₁ Δ₂ : Ctx} (h : Δ₁.Le Δ₂) :
    ∀ {e : SubE σ Δ₁} {T : VarType}, e.OkRef T → (e.mono h).OkRef T
  | .ren _, _, he => h.ref he
  | .tm _, _, he => he
  | .hide, _, he => False.elim he

theorem idxAlong_mono {Δ₁ Δ₂ : Ctx} (h : Δ₁.Le Δ₂) :
    ∀ (e : SubE σ Δ₁) (p : List Step), (e.mono h).idxAlong p = e.idxAlong p
  | .ren _, _ => rfl
  | .tm _, _ => rfl
  | .hide, _ => rfl

theorem okRef_diaBody {ιx : VarSymb} : ∀ {e : SubE σ Δ} {X : VarType},
    e.OkRef (.VTypeDia X) → e.idxAlong [] = ιx → (e.diaBody ιx).OkRef X
  | .ren w, X, he, hw => by
      have hw' : w = ιx := hw
      subst hw'
      change (if w = w then (match Δ.ref w with | some (.VTypeDia X) => some X | _ => none)
        else none) = some X
      rw [if_pos rfl, he]
  | .tm (.diatm y _hy u), X, he, hw => by
      have hw' : y = ιx := hw
      rw [show ((SubE.tm (Term.diatm y _hy u) : SubE σ Δ).diaBody ιx) =
        SubE.tm (Term.mono (by subst hw'; exact Ctx.Le.refl _) u) from dif_pos hw']
      exact VarType.VTypeDia.inj he
  | .tm (.var _ _), _, he, _ => nomatch he
  | .tm (.func _), _, he, _ => nomatch he
  | .tm .unit, _, he, _ => nomatch he
  | .tm (.pair _ _), _, he, _ => nomatch he
  | .tm (.boxtm _), _, he, _ => nomatch he
  | .hide, _, he, _ => False.elim he

theorem idxAlong_diaBody {ιx : VarSymb} : ∀ {e : SubE σ Δ} {X : VarType} (p : List Step),
    e.OkRef (.VTypeDia X) → e.idxAlong [] = ιx →
      (e.diaBody ιx).idxAlong p = e.idxAlong (.dia :: p)
  | .ren w, _, p, _, hw => by
      have hw' : w = ιx := hw
      subst hw'
      rfl
  | .tm (.diatm y _hy u), X, p, he, hw => by
      have hw' : y = ιx := hw
      rw [show ((SubE.tm (Term.diatm y _hy u) : SubE σ Δ).diaBody ιx) =
        SubE.tm (Term.mono (by subst hw'; exact Ctx.Le.refl _) u) from dif_pos hw']
      rfl
  | .tm (.var _ _), _, _, he, _ => nomatch he
  | .tm (.func _), _, _, he, _ => nomatch he
  | .tm .unit, _, _, he, _ => nomatch he
  | .tm (.pair _ _), _, _, he, _ => nomatch he
  | .tm (.boxtm _), _, _, he, _ => nomatch he
  | .hide, _, _, he, _ => False.elim he

theorem ref_witness {w : VarSymb} : ∀ {e : SubE σ Δ} {X : VarType},
    e.OkRef (.VTypeDia X) → e.idxAlong [] = w → ∃ Y, Δ.ref w = some (.VTypeDia Y)
  | .ren w', X, he, hw => by
      have hw' : w' = w := hw
      subst hw'
      exact ⟨X, he⟩
  | .tm (.diatm y hy _), _, _, hw => by
      have hw' : y = w := hw
      subst hw'
      exact hy
  | .tm (.var _ _), _, he, _ => nomatch he
  | .tm (.func _), _, he, _ => nomatch he
  | .tm .unit, _, he, _ => nomatch he
  | .tm (.pair _ _), _, he, _ => nomatch he
  | .tm (.boxtm _), _, he, _ => nomatch he
  | .hide, _, he, _ => False.elim he

end SubE

/-! ## Substitutions at a modal level -/

abbrev Subst (σ : Signature) (Δ : Ctx) := VarSymb → SubE σ Δ

namespace Subst

variable {σ : Signature} {Δ : Ctx}

/-- The entry reachable at an address: projection components by projection. -/
def «at» (θ : Subst σ Δ) : VarSymb → SubE σ Δ
  | .root r => θ (.root r)
  | .step v s => if s.isProj then (θ.at v).proj s else θ (.step v s)

/-- The entries fit the visible non-projection addresses (projections follow by projection). -/
def Ok (Γ : Ctx) (θ : Subst σ Δ) : Prop :=
  ∀ v T, v.lastProj = false → Γ v = some T → (θ v).OkRef T

def Coh (ι : VarSymb → VarSymb) (Γ : Ctx) (θ : Subst σ Δ) : Prop :=
  ∀ v T, Γ.ref v = some T → ∀ p, (θ.at v).idxAlong p = ι (v.ext p)

def box (θ : Subst σ Δ) : Subst σ Δ.boxIn := fun v =>
  match v with
  | .step u .box => (θ.at u).unbox
  | .step u .keep => (θ.at u).keepE
  | _ => .hide

def dia (θ : Subst σ Δ) (x ιx : VarSymb) : Subst σ (Δ.diaIn ιx) := fun v =>
  match v with
  | .step u .dia => if u = x then (θ.at x).diaBody ιx else .hide
  | .step u .box => (θ.at u).unbox.mono (Ctx.le_boxIn_diaIn Δ ιx)
  | .step u .keep => (θ.at u).keepE.mono (Ctx.le_boxIn_diaIn Δ ιx)
  | _ => .hide

/-- Under a binder: the source slot goes to the target slot; everything else is weakened. -/
def under (θ : Subst σ Δ) (d d' : ℕ) (T : VarType) (h : Δ (.root (.bnd d')) = none) :
    Subst σ (Δ.insert (.bnd d') T) := fun v =>
  if v = .root (.bnd d) then .ren (.root (.bnd d')) else (θ v).mono (Ctx.le_insert h T)

theorem at_nonproj (θ : Subst σ Δ) : ∀ {v : VarSymb}, v.lastProj = false → θ.at v = θ v
  | .root _, _ => rfl
  | .step v s, h => by
      change (if s.isProj then (θ.at v).proj s else θ (.step v s)) = _
      have hs : s.isProj = false := h
      rw [if_neg (Bool.eq_false_iff.mp hs)]

theorem okRef_at {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) :
    ∀ {v : VarSymb} {T : VarType}, Γ.ref v = some T → (θ.at v).OkRef T := by
  intro v
  induction v with
  | root r => intro T hv; exact hθ _ _ rfl hv
  | step v s ih =>
      intro T hv
      simp only [Ctx.ref, Subst.at] at hv ⊢
      split_ifs at hv ⊢ with hs
      · cases hU : Γ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U =>
            rw [hU] at hv
            exact SubE.okRef_proj (ih hU) hs hv
      · exact hθ _ _ (show (VarSymb.step v s).lastProj = false from Bool.eq_false_iff.mpr hs) hv

/-- Coherence follows from coherence on the visible non-projection addresses. -/
theorem coh_of {ι : VarSymb → VarSymb} {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ)
    (hvis : ∀ v T, v.lastProj = false → Γ v = some T → ∀ p, (θ v).idxAlong p = ι (v.ext p)) :
    Coh ι Γ θ := by
  intro v
  induction v with
  | root r => intro T hv p; exact hvis _ _ rfl hv p
  | step v s ih =>
      intro T hv p
      simp only [Ctx.ref] at hv
      simp only [Subst.at]
      split_ifs at hv ⊢ with hs
      · cases hU : Γ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U =>
            rw [hU] at hv
            rw [SubE.idxAlong_proj p (okRef_at hθ hU) hs hv, ih U hU (s :: p)]
            rfl
      · exact hvis _ _ (show (VarSymb.step v s).lastProj = false from Bool.eq_false_iff.mpr hs)
          hv p

theorem ok_box {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) : Ok Γ.boxIn θ.box := by
  intro v T _ hv
  match v with
  | .step u .box =>
      change (match Γ.ref u with | some (.VTypeBox A) => some A | _ => none) = some T at hv
      cases hu : Γ.ref u with
      | none => rw [hu] at hv; cases hv
      | some U =>
          rw [hu] at hv
          cases U <;> try cases hv
          exact SubE.okRef_unbox (okRef_at hθ hu)
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep hv
      exact SubE.okRef_keepE hF (okRef_at hθ hu)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem coh_box {ι : VarSymb → VarSymb} {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ)
    (hc : Coh ι Γ θ) : Coh ι Γ.boxIn θ.box := by
  refine coh_of (ok_box hθ) ?_
  intro v T _ hv p
  match v with
  | .step u .box =>
      change (match Γ.ref u with | some (.VTypeBox A) => some A | _ => none) = some T at hv
      cases hu : Γ.ref u with
      | none => rw [hu] at hv; cases hv
      | some U =>
          rw [hu] at hv
          cases U <;> try cases hv
          change ((θ.at u).unbox).idxAlong p = _
          rw [SubE.idxAlong_unbox p (okRef_at hθ hu), hc u _ hu (.box :: p)]
          rfl
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep hv
      change ((θ.at u).keepE).idxAlong p = _
      rw [SubE.idxAlong_keepE hF p (okRef_at hθ hu), hc u _ hu (.keep :: p)]
      rfl
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem ok_dia {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) {x ιx : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (hw : (θ.at x).idxAlong [] = ιx) :
    Ok (Γ.diaIn x) (θ.dia x ιx) := by
  obtain ⟨X, hx⟩ := hx
  intro v T _ hv
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with hux
      · rw [hx] at hv
        cases hv
        change (if u = x then (θ.at x).diaBody ιx else SubE.hide).OkRef X
        rw [if_pos hux]
        exact SubE.okRef_diaBody (okRef_at hθ hx) hw
  | .step u .box => exact SubE.okRef_mono _ (ok_box hθ (.step u .box) T rfl hv)
  | .step u .keep => exact SubE.okRef_mono _ (ok_box hθ (.step u .keep) T rfl hv)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

theorem coh_dia {ι : VarSymb → VarSymb} {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ)
    (hc : Coh ι Γ θ) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) :
    Coh ι (Γ.diaIn x) (θ.dia x (ι x)) := by
  have hw : (θ.at x).idxAlong [] = ι x := by
    obtain ⟨X, hX⟩ := hx
    exact hc x _ hX []
  refine coh_of (ok_dia hθ hx hw) ?_
  obtain ⟨X, hx⟩ := hx
  intro v T _ hv p
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with hux
      · subst hux
        change (if u = u then (θ.at u).diaBody (ι u) else SubE.hide).idxAlong p = _
        rw [if_pos rfl, SubE.idxAlong_diaBody p (okRef_at hθ hx) hw, hc u _ hx (.dia :: p)]
        rfl
  | .step u .box =>
      change (match Γ.ref u with | some (.VTypeBox A) => some A | _ => none) = some T at hv
      cases hu : Γ.ref u with
      | none => rw [hu] at hv; cases hv
      | some U =>
          rw [hu] at hv
          cases U <;> try cases hv
          change (((θ.at u).unbox).mono _).idxAlong p = _
          rw [SubE.idxAlong_mono, SubE.idxAlong_unbox p (okRef_at hθ hu), hc u _ hu (.box :: p)]
          rfl
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep (Γ := Γ) hv
      change (((θ.at u).keepE).mono _).idxAlong p = _
      rw [SubE.idxAlong_mono, SubE.idxAlong_keepE hF p (okRef_at hθ hu), hc u _ hu (.keep :: p)]
      rfl
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

theorem ok_under {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) {d d' : ℕ} (T : VarType)
    (h : Δ (.root (.bnd d')) = none) : Ok (Γ.insert (.bnd d) T) (θ.under d d' T h) := by
  intro v U hlp hv
  by_cases hvr : v = .root (.bnd d)
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    rw [show θ.under d d' T h (.root (.bnd d)) = .ren (.root (.bnd d')) from if_pos rfl]
    exact Ctx.ref_insert_root Δ _ T
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    rw [show θ.under d d' T h v = (θ v).mono (Ctx.le_insert h T) from if_neg hvr]
    exact SubE.okRef_mono _ (hθ v U hlp hv')

theorem coh_under {ι : VarSymb → VarSymb} {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ)
    (hc : Coh ι Γ θ) {d d' : ℕ} (hΓ : Γ.SlotsFrom d) (T : VarType)
    (h : Δ (.root (.bnd d')) = none) :
    Coh (VarSymb.shiftSlot ι d d') (Γ.insert (.bnd d) T) (θ.under d d' T h) := by
  refine coh_of (ok_under hθ T h) ?_
  intro v U hlp hv p
  by_cases hvr : v = .root (.bnd d)
  · subst hvr
    rw [show θ.under d d' T h (.root (.bnd d)) = .ren (.root (.bnd d')) from if_pos rfl]
    change (VarSymb.root (.bnd d')).ext p =
      (if ((VarSymb.root (.bnd d)).ext p).rt = .bnd d then
        ((VarSymb.root (.bnd d)).ext p).reroot (.bnd d') else ι _)
    have hc0 : (VarSymb.root (Root.bnd d)).rt = Root.bnd d := rfl
    rw [VarSymb.ext_rt, if_pos hc0]
    exact (VarSymb.reroot_ext (.bnd d') (.root (.bnd d)) p).symm
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    have hrt : v.rt ≠ .bnd d := fun he => by
      rw [hΓ v d he le_rfl] at hv'
      cases hv'
    rw [show θ.under d d' T h v = (θ v).mono (Ctx.le_insert h T) from if_neg hvr,
      SubE.idxAlong_mono, ← at_nonproj θ hlp, hc v U ((Ctx.ref_nonproj Γ hlp).trans hv') p]
    change ι (v.ext p) = if (v.ext p).rt = .bnd d then _ else ι (v.ext p)
    rw [VarSymb.ext_rt, if_neg hrt]

end Subst

/-! ## Substitution in terms and formulas -/

mutual
  def Func.subst {σ : Signature} (ι : VarSymb → VarSymb) : {Γ Δ : Ctx} → (θ : Subst σ Δ) →
      Subst.Ok Γ θ → Subst.Coh ι Γ θ → {n : ℕ} → Func σ Γ n → Func σ Δ n
    | _, _, _, _, _, _, .F f => .F f
    | _, _, θ, hθ, hc, _, .eval g t => .eval (Func.subst ι θ hθ hc g) (Term.subst ι θ hθ hc t)

  /-- ⭐**Substitution**, intrinsically typed, annotations mapped by `ι`. -/
  def Term.subst {σ : Signature} (ι : VarSymb → VarSymb) : {Γ Δ : Ctx} → (θ : Subst σ Δ) →
      Subst.Ok Γ θ → Subst.Coh ι Γ θ → {T : VarType} → {a : Ann T} →
      Term σ Γ T a → Term σ Δ T (a.mapIdx ι)
    | _, _, θ, hθ, _, _, _, .var _ hv => (θ.at _).toVar (Subst.okRef_at hθ hv)
    | _, _, θ, hθ, hc, _, _, .func f => .func (Func.subst ι θ hθ hc f)
    | _, _, _, _, _, _, _, .unit => .unit
    | _, _, θ, hθ, hc, _, _, .pair s t =>
        .pair (Term.subst ι θ hθ hc s) (Term.subst ι θ hθ hc t)
    | _, _, θ, hθ, hc, _, _, .boxtm t =>
        .boxtm (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) t)
    | _, _, θ, hθ, hc, _, _, .diatm x hx t =>
        have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
        .diatm (ι x) (hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw)
          (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) t)
end

def Rel.subst {σ : Signature} (ι : VarSymb → VarSymb) {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) : {n : ℕ} → Rel σ Γ n → Rel σ Δ n
  | _, .R r => .R r
  | _, .eval ρ t => .eval (Rel.subst ι θ hθ hc ρ) (Term.subst ι θ hθ hc t)

/-- ⭐Substitution in formulas. -/
def WFF.subst {σ : Signature} : (ι : VarSymb → VarSymb) → {Γ Δ : Ctx} → {d d' : ℕ} →
    (θ : Subst σ Δ) → Subst.Ok Γ θ → Subst.Coh ι Γ θ → Γ.SlotsFrom d → Δ.SlotsFrom d' →
    WFF σ Γ d → WFF σ Δ d'
  | ι, _, _, _, _, θ, hθ, hc, _, _, .atom ρ => .atom (Rel.subst ι θ hθ hc ρ)
  | ι, _, _, _, _, θ, hθ, hc, _, _, .eq t s =>
      .eq (Term.subst ι θ hθ hc t) (Term.subst ι θ hθ hc s)
  | _, _, _, _, _, _, _, _, _, _, .top => .top
  | _, _, _, _, _, _, _, _, _, _, .bot => .bot
  | ι, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .and φ ψ =>
      .and (WFF.subst ι θ hθ hc hΓ hΔ φ) (WFF.subst ι θ hθ hc hΓ hΔ ψ)
  | ι, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .or φ ψ =>
      .or (WFF.subst ι θ hθ hc hΓ hΔ φ) (WFF.subst ι θ hθ hc hΓ hΔ ψ)
  | ι, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .imp φ ψ =>
      .imp (WFF.subst ι θ hθ hc hΓ hΔ φ) (WFF.subst ι θ hθ hc hΓ hΔ ψ)
  | ι, _, _, d, d', θ, hθ, hc, hΓ, hΔ, .all T φ =>
      .all T (WFF.subst (VarSymb.shiftSlot ι d d') (θ.under d d' T hΔ.root)
        (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ T hΔ.root)
        (hΓ.insert T) (hΔ.insert T) φ)
  | ι, _, _, d, d', θ, hθ, hc, hΓ, hΔ, .ex T φ =>
      .ex T (WFF.subst (VarSymb.shiftSlot ι d d') (θ.under d d' T hΔ.root)
        (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ T hΔ.root)
        (hΓ.insert T) (hΔ.insert T) φ)
  | ι, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .box φ =>
      .box (WFF.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn hΔ.boxIn φ)
  | ι, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .dia x hx φ =>
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      .dia (ι x) (hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw)
        (WFF.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
          (hΓ.diaIn x) (hΔ.diaIn (ι x)) φ)

/-! ## Substituting one root -/

namespace Subst

variable {σ : Signature} {Δ : Ctx}

/-- `r ↦ e`, every other address to itself. -/
def single (r : Root) (e : SubE σ Δ) : Subst σ Δ := fun v => if v = .root r then e else .ren v

def singleIdx (r : Root) (e : SubE σ Δ) : VarSymb → VarSymb :=
  fun i => if i.rt = r then e.idxAlong i.path else i

theorem ok_single {Γ : Ctx} {r : Root} {T : VarType} {e : SubE σ Δ} (hle : Γ.Le Δ)
    (he : e.OkRef T) : Ok (Γ.insert r T) (single r e) := by
  intro v U hlp hv
  by_cases hvr : v = .root r
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    rw [show single r e (.root r) = e from if_pos rfl]
    exact he
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    rw [show single r e v = .ren v from if_neg hvr]
    exact (Ctx.ref_nonproj Δ hlp).trans (hle v U hv')

theorem coh_single {Γ : Ctx} {r : Root} {T : VarType} {e : SubE σ Δ} (hr : Γ.RootFresh r)
    (hle : Γ.Le Δ) (he : e.OkRef T) : Coh (singleIdx r e) (Γ.insert r T) (single r e) := by
  refine coh_of (ok_single hle he) ?_
  intro v U hlp hv p
  by_cases hvr : v = .root r
  · subst hvr
    rw [show single r e (.root r) = e from if_pos rfl]
    change e.idxAlong p = if ((VarSymb.root r).ext p).rt = r then
      e.idxAlong ((VarSymb.root r).ext p).path else _
    simp only [VarSymb.ext_rt, VarSymb.ext_path, VarSymb.rt, VarSymb.path, List.nil_append,
      if_true]
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    have hrt : v.rt ≠ r := fun he' => by
      rw [hr v he'] at hv'
      cases hv'
    rw [show single r e v = .ren v from if_neg hvr]
    change v.ext p = if (v.ext p).rt = r then _ else v.ext p
    rw [VarSymb.ext_rt, if_neg hrt]

end Subst

/-- ⭐Substituting a term for a root. -/
def WFF.substRoot {σ : Signature} {Γ : Ctx} {d d' : ℕ} (r : Root) {T : VarType}
    (hr : Γ.RootFresh r) (hs : Γ.SlotsFrom d) (hs' : (Γ.insert r T).SlotsFrom d') {a : Ann T}
    (s : Term σ Γ T a) (φ : WFF σ (Γ.insert r T) d') : WFF σ Γ d :=
  WFF.subst (Subst.singleIdx r (.tm s)) (Subst.single r (.tm s))
    (Subst.ok_single (Ctx.Le.refl Γ) rfl) (Subst.coh_single hr (Ctx.Le.refl Γ) rfl) hs' hs φ

/-- ⭐Instantiating the slot `bnd d` (for `∀`-elimination / `∃`-introduction). -/
def WFF.instantiate {σ : Signature} {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {T : VarType}
    {a : Ann T} (s : Term σ Γ T a) (φ : WFF σ (Γ.insert (.bnd d) T) (d + 1)) : WFF σ Γ d :=
  WFF.substRoot (.bnd d) (hs.rootFresh le_rfl) hs (hs.insert T) s φ

/-- Substituting a term for a free variable (for `=`-elimination). -/
def WFF.substFree {σ : Signature} {Γ : Ctx} {d : ℕ} (u : ℕ) (hu : Γ.RootFresh (.free u))
    (hs : Γ.SlotsFrom d) {T : VarType} {a : Ann T} (s : Term σ Γ T a)
    (φ : WFF σ (Γ.insert (.free u) T) d) : WFF σ Γ d :=
  WFF.substRoot (.free u) hu hs (hs.insertFree u T) s φ

/-- Renaming a fresh root `r` to the address `w` of the target. -/
def WFF.renameRoot {σ : Signature} {Γ Δ : Ctx} {d d' : ℕ} (r : Root) {T : VarType}
    (hr : Γ.RootFresh r) (hle : Γ.Le Δ) (w : VarSymb) (hw : Δ.ref w = some T)
    (hs : (Γ.insert r T).SlotsFrom d) (hs' : Δ.SlotsFrom d') (φ : WFF σ (Γ.insert r T) d) :
    WFF σ Δ d' :=
  WFF.subst (Subst.singleIdx r (.ren w)) (Subst.single r (.ren w))
    (Subst.ok_single (σ := σ) hle hw) (Subst.coh_single hr hle hw) hs hs' φ

/-- ⭐Binding a free variable to the slot `bnd d` (for `∀`-introduction / `∃`-elimination). -/
def WFF.bindFree {σ : Signature} {Γ : Ctx} {d : ℕ} (u : ℕ) (hu : Γ.RootFresh (.free u))
    (hs : Γ.SlotsFrom d) (T : VarType) (φ : WFF σ (Γ.insert (.free u) T) d) :
    WFF σ (Γ.insert (.bnd d) T) (d + 1) :=
  WFF.renameRoot (.free u) hu (Ctx.le_insert hs.root T) (.root (.bnd d))
    (Ctx.ref_insert_root Γ _ T) (hs.insertFree u T) (hs.insert T) φ

/-- ⭐Pair elimination: the components `u₁`, `u₂` become `z.fst`, `z.snd`. -/
def WFF.bindPair {σ : Signature} {Γ : Ctx} {d : ℕ} (u₁ u₂ z : ℕ) (hu : u₁ ≠ u₂)
    (hz₁ : z ≠ u₁) (hu₁ : Γ.RootFresh (.free u₁)) (hu₂ : Γ.RootFresh (.free u₂))
    (hzf : Γ.RootFresh (.free z)) (hs : Γ.SlotsFrom d) (A B : VarType)
    (φ : WFF σ ((Γ.insert (.free u₁) A).insert (.free u₂) B) d) :
    WFF σ (Γ.insert (.free z) (.VTypeProd A B)) d :=
  have hne₁₂ : Root.free u₁ ≠ Root.free u₂ := fun h => hu (Root.free.inj h)
  have hne_z₁ : Root.free z ≠ Root.free u₁ := fun h => hz₁ (Root.free.inj h)
  -- `u₂ ↦ z.snd`, over `Γ, u₁ : A`
  have φ₁ : WFF σ ((Γ.insert (.free u₁) A).insert (.free z) (.VTypeProd A B)) d :=
    WFF.renameRoot (.free u₂) (hu₂.insert_ne hne₁₂ A)
      (Ctx.le_insert (hzf.insert_ne hne_z₁.symm A).root _) (.step (.root (.free z)) .snd)
      (Ctx.ref_insert_snd _ _ A B) ((hs.insertFree u₁ A).insertFree u₂ B)
      ((hs.insertFree u₁ A).insertFree z _) φ
  -- reorder, then `u₁ ↦ z.fst`, over `Γ, z : A × B`
  WFF.renameRoot (.free u₁) (hu₁.insert_ne hne_z₁ _) (Ctx.Le.refl _)
    (.step (.root (.free z)) .fst) (Ctx.ref_insert_fst _ _ A B)
    ((hs.insertFree z _).insertFree u₁ A) (hs.insertFree z _)
    (WFF.mono (Ctx.insert_swap_le hne_z₁.symm _ _) φ₁)

end V12M
