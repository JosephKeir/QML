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
* The contents of an address entry `w` inside `□` are at `w.inner` (`w.box`, or `w.keep.here`
  under T and 4).
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
  | .ren w => .ren w.inner
  | .tm (.boxtm t) => .tm t
  | _ => .hide

/-- The kept component of a necessary or possible entry, one view further in (under 4): `□t`
    with its body shifted, and `◇_y t` along `y.keep` with its body shifted (restriction commutes
    with the operations a possible term is built by). -/
def keepE : SubE σ Δ → SubE σ Δ.boxIn
  | .ren w => .ren (.step w .keep)
  | .tm (.boxtm t) =>
      if hF : ModalSys.Four = true then .tm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Δ) t))
      else .hide
  | .tm (.diatm y hy t) =>
      if hK : ModalSys.Four = true then
        .tm (.diatm (.step y .keep) (Ctx.exists_keep_dia hK hy)
          (Term.shift (Ctx.shifts_diaIn_keep hK Δ y) t))
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

theorem keepE_dia {A : VarType} {a : Ann A} (y : VarSymb)
    (hy : ∃ X, Δ.ref y = some (.VTypeDia X)) (t : Term σ (Δ.diaIn y) A a)
    (hF : ModalSys.Four = true) :
    (SubE.tm (Term.diatm y hy t)).keepE = .tm (.diatm (.step y .keep)
      (Ctx.exists_keep_dia hF hy) (Term.shift (Ctx.shifts_diaIn_keep hF Δ y) t)) :=
  dif_pos hF

theorem keepE_dia_off {A : VarType} {a : Ann A} (y : VarSymb)
    (hy : ∃ X, Δ.ref y = some (.VTypeDia X)) (t : Term σ (Δ.diaIn y) A a)
    (hF : ¬ (ModalSys.Four = true)) :
    (SubE.tm (Term.diatm y hy t)).keepE = .hide :=
  dif_neg hF

theorem okRef_proj : ∀ {e : SubE σ Δ} {U T : VarType} {s : Step}, e.OkRef U → s.isStruct = true →
    U.step s = some T → (e.proj s).OkRef T
  | .ren w, U, T, s, he, hs, hst => by
      change (if s.isStruct then (Δ.ref w).bind (·.step s) else Δ (.step w s)) = some T
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
      | «at» => cases hs
      | here =>
          cases s₀ with
          | boxtm t =>
              obtain ⟨hT, hAT⟩ := VarType.step_here hst
              subst hAT
              rw [proj_boxtm_here t hT]
              rfl
          | _ => cases hst

theorem idxAlong_proj : ∀ {e : SubE σ Δ} {U T : VarType} {s : Step} (p : List Step),
    e.OkRef U → s.isStruct = true → U.step s = some T →
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
      | «at» => cases hs
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
  | .ren _, _, he => Ctx.ref_inner he
  | .hide, _, he => False.elim he
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s
      rfl

theorem idxAlong_unbox (hk : ModalSys.keepOnly = false) :
    ∀ {e : SubE σ Δ} {A : VarType} (p : List Step),
      e.OkRef (.VTypeBox A) → e.unbox.idxAlong p = e.idxAlong (.box :: p)
  | .ren w, _, p, _ => by
      change w.inner.ext p = (VarSymb.step w .box).ext p
      rw [VarSymb.inner_box hk]
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

theorem okRef_keepE' (hF : ModalSys.Four = true) : ∀ {e : SubE σ Δ} {T : VarType},
    T.keepable = true → e.OkRef T → e.keepE.OkRef T
  | .ren _, _, hk, he => Ctx.ref_keep_of' hF he hk
  | .hide, _, _, he => False.elim he
  | .tm (T := U) s, T, hk, he => by
      have hU : U = T := he
      subst hU
      cases U with
      | VTypeBox A =>
          cases s with
          | boxtm t =>
              rw [keepE_tm t hF]
              rfl
      | VTypeDia A =>
          cases s with
          | diatm y hy t =>
              rw [keepE_dia y hy t hF]
              rfl
      | _ => cases hk

theorem idxAlong_keepE' (hF : ModalSys.Four = true) : ∀ {e : SubE σ Δ} {T : VarType}
    (p : List Step), T.keepable = true → e.OkRef T →
      e.keepE.idxAlong p = e.idxAlong (.keep :: p)
  | .ren _, _, _, _, _ => rfl
  | .hide, _, _, _, he => False.elim he
  | .tm (T := U) s, T, p, hk, he => by
      have hU : U = T := he
      subst hU
      cases U with
      | VTypeBox A =>
          cases s with
          | boxtm t =>
              rw [keepE_tm t hF]
              rfl
      | VTypeDia A =>
          cases s with
          | diatm y hy t =>
              rw [keepE_dia y hy t hF]
              rfl
      | _ => cases hk

theorem okRef_mono {Δ₁ Δ₂ : Ctx} (h : Δ₁.Le Δ₂) :
    ∀ {e : SubE σ Δ₁} {T : VarType}, e.OkRef T → (e.mono h).OkRef T
  | .ren _, _, he => h.ref he
  | .tm _, _, he => he
  | .hide, _, he => False.elim he

theorem mono_mono {Δ₁ Δ₂ Δ₃ : Ctx} (h₁ : Δ₁.Le Δ₂) (h₂ : Δ₂.Le Δ₃) :
    ∀ (e : SubE σ Δ₁), (e.mono h₁).mono h₂ = e.mono (h₁.trans h₂)
  | .hide => rfl
  | .ren _ => rfl
  | .tm t => congrArg SubE.tm (Term.mono_mono h₁ h₂ t)

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

/-! ## Entries for witnesses (branch `wip/in-atom`, docs §12.16) -/

/-- ⭐**An entry for a witness**: another witness, or a witness read through a body — the image of
    the possible object `y : ◇X` one level out under `y ↦ ◇_z b` (`b` its content, modal β). -/
inductive WitE (σ : Signature) (Δ : Ctx) : Type where
  | hide
  | ren (z : VarSymb)
  | tm (z : VarSymb) {A : VarType} {a : Ann A} (b : Term σ (Δ.optIn z) A a)

namespace WitE

variable {σ : Signature} {Δ : Ctx}

def mono {Δ₁ Δ₂ : Ctx} (h : Δ₁.Le Δ₂) : WitE σ Δ₁ → WitE σ Δ₂
  | .hide => .hide
  | .ren z => .ren z
  | .tm z b => .tm z (Term.mono (h.optIn z) b)

/-- The entry is a witness of `Δ` whose content (read through the body) has type `X`. -/
def OkW : WitE σ Δ → VarType → Prop
  | .ren z, X => Δ.wit z = some X
  | .tm z (A := A) _, X => (∃ Z, Δ.wit z = some Z) ∧ A = X
  | .hide, _ => False

/-- Where an index below this entry lands: as for the possible object it stands for. -/
def idxAlong : WitE σ Δ → List Step → VarSymb
  | .ren z, p => z.ext p
  | .tm z (a := a) _, p => (Ann.dia z a).idxAt p
  | .hide, _ => .root (.free 0)

/-- The entry at the content, for the new witness `z` (modal β for a body), as `SubE.diaBody`. -/
def optBody (z : VarSymb) : WitE σ Δ → SubE σ (Δ.optIn z)
  | .ren _ => .ren (.step z .dia)
  | .tm w b => if h : w = z then .tm (Term.mono (by subst h; exact Ctx.Le.refl _) b) else .hide
  | .hide => .hide

theorem okW_mono {Δ₁ Δ₂ : Ctx} (h : Δ₁.Le Δ₂) :
    ∀ {e : WitE σ Δ₁} {X : VarType}, e.OkW X → (e.mono h).OkW X
  | .ren _, _, he => h.wit _ _ he
  | .tm _ _, _, he => ⟨he.1.elim fun Z hZ => ⟨Z, h.wit _ _ hZ⟩, he.2⟩
  | .hide, _, he => False.elim he

theorem idxAlong_mono {Δ₁ Δ₂ : Ctx} (h : Δ₁.Le Δ₂) :
    ∀ (e : WitE σ Δ₁) (p : List Step), (e.mono h).idxAlong p = e.idxAlong p
  | .ren _, _ => rfl
  | .tm _ _, _ => rfl
  | .hide, _ => rfl

/-- The witness an entry lands on is a witness of `Δ`. -/
theorem wit_of {z : VarSymb} : ∀ {e : WitE σ Δ} {X : VarType}, e.OkW X → e.idxAlong [] = z →
    ∃ Z, Δ.wit z = some Z
  | .ren w, X, he, hw => by
      have hw' : w = z := hw
      subst hw'
      exact ⟨X, he⟩
  | .tm w _, _, he, hw => by
      have hw' : w = z := hw
      subst hw'
      exact he.1
  | .hide, _, he, _ => False.elim he

theorem okRef_optBody {z : VarSymb} : ∀ {e : WitE σ Δ} {X : VarType}, e.OkW X →
    e.idxAlong [] = z → (e.optBody z).OkRef X
  | .ren w, _, he, hw => by
      have hw' : w = z := hw
      subst hw'
      exact (Ctx.ref_nonproj _ rfl).trans (Ctx.optIn_content he)
  | .tm w b, _, he, hw => by
      have hw' : w = z := hw
      rw [show (WitE.tm w b : WitE σ Δ).optBody z =
        SubE.tm (Term.mono (by subst hw'; exact Ctx.Le.refl _) b) from dif_pos hw']
      exact he.2
  | .hide, _, he, _ => False.elim he

theorem idxAlong_optBody {z : VarSymb} : ∀ {e : WitE σ Δ} {X : VarType} (p : List Step),
    e.OkW X → e.idxAlong [] = z → (e.optBody z).idxAlong p = e.idxAlong (.dia :: p)
  | .ren w, _, p, _, hw => by
      have hw' : w = z := hw
      subst hw'
      rfl
  | .tm w b, _, p, _, hw => by
      have hw' : w = z := hw
      rw [show (WitE.tm w b : WitE σ Δ).optBody z =
        SubE.tm (Term.mono (by subst hw'; exact Ctx.Le.refl _) b) from dif_pos hw']
      rfl
  | .hide, _, _, he, _ => False.elim he

theorem mono_mono {Δ₁ Δ₂ Δ₃ : Ctx} (h₁ : Δ₁.Le Δ₂) (h₂ : Δ₂.Le Δ₃) :
    ∀ e : WitE σ Δ₁, (e.mono h₁).mono h₂ = e.mono (h₁.trans h₂)
  | .hide => rfl
  | .ren _ => rfl
  | .tm z b => by
      change WitE.tm z (Term.mono (h₂.optIn z) (Term.mono (h₁.optIn z) b)) = _
      rw [Term.mono_mono]
      rfl

theorem optBody_mono {Δ' : Ctx} (h : Δ.Le Δ') (z : VarSymb) :
    ∀ e : WitE σ Δ, (e.optBody z).mono (h.optIn z) = (e.mono h).optBody z
  | .hide => rfl
  | .ren _ => rfl
  | .tm w b => by
      by_cases hw : w = z
      · subst hw
        rw [show (WitE.tm w b : WitE σ Δ).optBody w = SubE.tm (Term.mono (Ctx.Le.refl _) b)
            from dif_pos rfl,
          show ((WitE.tm w b : WitE σ Δ).mono h).optBody w =
            SubE.tm (Term.mono (Ctx.Le.refl _) (Term.mono (h.optIn w) b)) from dif_pos rfl]
        change SubE.tm (Term.mono _ (Term.mono _ b)) = SubE.tm (Term.mono _ (Term.mono _ b))
        rw [Term.mono_mono, Term.mono_mono]
      · rw [show (WitE.tm w b : WitE σ Δ).optBody z = .hide from dif_neg hw,
          show ((WitE.tm w b : WitE σ Δ).mono h).optBody z = .hide from dif_neg hw]
        rfl

end WitE

namespace SubE

variable {σ : Signature} {Δ : Ctx}

/-- ⭐The witness entry of a possible object's entry, one view in: the same address, or (for
    `◇_z b`, with `Opt` on) the witness `z` read through the same body. -/
def toWit : SubE σ Δ → WitE σ Δ.boxIn
  | .ren w => .ren w
  | .tm (.diatm z hz b) =>
      if hO : ModalSys.Opt = true then
        .tm z (Term.mono (by obtain ⟨X, hX⟩ := hz; exact Ctx.le_diaIn_boxIn_optIn hO hX) b)
      else .hide
  | _ => .hide

theorem okW_toWit (hO : ModalSys.Opt = true) :
    ∀ {e : SubE σ Δ} {X : VarType}, e.OkRef (.VTypeDia X) → e.toWit.OkW X
  | .ren _, _, he => Ctx.boxIn_wit.mpr ⟨hO, he⟩
  | .tm (.diatm z hz b), X, he => by
      change (if hO : ModalSys.Opt = true then _ else WitE.hide).OkW X
      rw [dif_pos hO]
      obtain ⟨Z, hZ⟩ := hz
      exact ⟨⟨Z, Ctx.boxIn_wit.mpr ⟨hO, hZ⟩⟩, VarType.VTypeDia.inj he⟩
  | .tm (.var _ _), _, he => nomatch he
  | .tm (.func _), _, he => nomatch he
  | .tm .unit, _, he => nomatch he
  | .tm (.pair _ _), _, he => nomatch he
  | .tm (.boxtm _), _, he => nomatch he
  | .hide, _, he => False.elim he

theorem idxAlong_toWit (hO : ModalSys.Opt = true) :
    ∀ {e : SubE σ Δ} {X : VarType} (p : List Step), e.OkRef (.VTypeDia X) →
      e.toWit.idxAlong p = e.idxAlong p
  | .ren _, _, _, _ => rfl
  | .tm (.diatm z hz b), X, p, _ => by
      change (if hO : ModalSys.Opt = true then _ else WitE.hide).idxAlong p = _
      rw [dif_pos hO]
      rfl
  | .tm (.var _ _), _, _, he => nomatch he
  | .tm (.func _), _, _, he => nomatch he
  | .tm .unit, _, _, he => nomatch he
  | .tm (.pair _ _), _, _, he => nomatch he
  | .tm (.boxtm _), _, _, he => nomatch he
  | .hide, _, _, he => False.elim he

/-- The witness entry's content is the body's, read in the witness's view. -/
theorem toWit_optBody (hO : ModalSys.Opt = true) (z : VarSymb) :
    ∀ {e : SubE σ Δ} {X : VarType}, e.OkRef (.VTypeDia X) →
      ∀ L : (Δ.diaIn z).Le (Δ.boxIn.optIn z), e.toWit.optBody z = (e.diaBody z).mono L
  | .ren _, _, _, _ => rfl
  | .tm (.diatm y hy u), _, _, L => by
      obtain ⟨Y, hY⟩ := hy
      change (if hO' : ModalSys.Opt = true then
        WitE.tm y (Term.mono (Ctx.le_diaIn_boxIn_optIn hO' hY) u) else WitE.hide).optBody z =
        (SubE.diaBody z (SubE.tm (Term.diatm y ⟨Y, hY⟩ u))).mono L
      rw [dif_pos hO]
      by_cases hyz : y = z
      · subst hyz
        rw [show (WitE.tm y (Term.mono (Ctx.le_diaIn_boxIn_optIn hO hY) u) :
              WitE σ Δ.boxIn).optBody y = SubE.tm (Term.mono (Ctx.Le.refl _)
                (Term.mono (Ctx.le_diaIn_boxIn_optIn hO hY) u)) from dif_pos rfl,
          show SubE.diaBody y (SubE.tm (Term.diatm y ⟨Y, hY⟩ u)) =
            SubE.tm (Term.mono (Ctx.Le.refl _) u) from dif_pos rfl]
        change SubE.tm _ = SubE.tm (Term.mono L (Term.mono (Ctx.Le.refl _) u))
        simp only [Term.mono_mono]
      · rw [show (WitE.tm y (Term.mono (Ctx.le_diaIn_boxIn_optIn hO hY) u) :
              WitE σ Δ.boxIn).optBody z = .hide from dif_neg hyz,
          show SubE.diaBody z (SubE.tm (Term.diatm y ⟨Y, hY⟩ u)) = .hide from dif_neg hyz]
        rfl
  | .tm (.var _ _), _, he, _ => nomatch he
  | .tm (.func _), _, he, _ => nomatch he
  | .tm .unit, _, he, _ => nomatch he
  | .tm (.pair _ _), _, he, _ => nomatch he
  | .tm (.boxtm _), _, he, _ => nomatch he
  | .hide, _, he, _ => False.elim he

end SubE

/-! ## Substitutions at a modal level -/

/-- A substitution at some modal level: an entry for every address, and one for every witness
    (branch `wip/in-atom`, docs §12.16). -/
structure Subst (σ : Signature) (Δ : Ctx) where
  ty : VarSymb → SubE σ Δ
  wit : VarSymb → WitE σ Δ := fun _ => .hide

theorem Subst.ext' {σ : Signature} {Δ : Ctx} {θ θ' : Subst σ Δ} (hty : ∀ v, θ.ty v = θ'.ty v)
    (hwit : ∀ y, θ.wit y = θ'.wit y) : θ = θ' := by
  cases θ
  cases θ'
  congr
  · funext v
    exact hty v
  · funext y
    exact hwit y

instance {σ : Signature} {Δ : Ctx} : CoeFun (Subst σ Δ) (fun _ => VarSymb → SubE σ Δ) :=
  ⟨Subst.ty⟩

/-- A substitution written as a function: no witness has an image. -/
instance {σ : Signature} {Δ : Ctx} : Coe (VarSymb → SubE σ Δ) (Subst σ Δ) :=
  ⟨fun f => { ty := f }⟩

namespace Subst

variable {σ : Signature} {Δ : Ctx}

/-- The entry reachable at an address: projection components by projection. -/
def «at» (θ : Subst σ Δ) : VarSymb → SubE σ Δ
  | .root r => θ (.root r)
  | .step v s => if s.isStruct then (θ.at v).proj s else θ (.step v s)

/-- `Opt` is off: an assumption, `NoOpt`, or a flag in context that excludes it (`optStage`).
    The default for constructions that exist only in the `◇⁰`-free language. -/
macro "opt_off" : tactic => `(tactic| first
  | assumption
  | exact ModalSys.NoOpt.noOpt
  | exact ModalSys.noOpt_of_T ‹_›
  | exact ModalSys.noOpt_of_Four ‹_›
  | exact ModalSys.noOpt_of_B ‹_›
  | exact ModalSys.noOpt_of_BStrong ‹_›
  | exact ModalSys.noOpt_of_Five ‹_›)

/-- A witness clause with nothing to check: `Opt` off (`opt_off`), or no witnesses. -/
macro "wit_triv" : tactic => `(tactic| first
  | exact fun hO => absurd hO (by rw [show ModalSys.Opt = false by opt_off]; decide)
  | exact fun _ _ _ h => nomatch h
  | exact fun _ _ _ _ h => nomatch h)

/-- The entries fit the visible non-projection addresses (projections follow by projection). -/
structure Ok (Γ : Ctx) (θ : Subst σ Δ) : Prop where
  ty : ∀ v T, v.lastProj = false → Γ v = some T → (θ v).OkRef T
  /-- Witness clauses are read only by `◇⁰`, which exists only with `Opt` on. -/
  wit : ModalSys.Opt = true → ∀ y X, Γ.wit y = some X → (θ.wit y).OkW X

instance {Γ : Ctx} {θ : Subst σ Δ} :
    CoeFun (Ok Γ θ) (fun _ => ∀ v T, v.lastProj = false → Γ v = some T → (θ v).OkRef T) :=
  ⟨Ok.ty⟩

structure Coh (ι : VarSymb → VarSymb) (Γ : Ctx) (θ : Subst σ Δ) : Prop where
  ty : ∀ v T, Γ.ref v = some T → ∀ p, (θ.at v).idxAlong p = ι (v.ext p)
  /-- A witness's image lands where the possible object it stands for does (its `dia` paths:
      the content, inside `◇⁰`). -/
  wit : ModalSys.Opt = true → ∀ y X, Γ.wit y = some X → ∀ p,
    (θ.wit y).idxAlong p = ι (y.ext p)
  /-- ⭐An **opened** witness (its content `y.dia` in view: inside `◇_y`, or `◇⁰_y`) has its
      content's entry read through its own entry: re-opening the image changes nothing. -/
  opened : ModalSys.Opt = true → ∀ y X z, Γ.wit y = some X → Γ (.step y .dia) = some X →
    (θ.wit y).idxAlong [] = z → (θ (.step y .dia)).mono (Ctx.le_optIn Δ z) = (θ.wit y).optBody z
  /-- ⭐An opened witness goes to an opened one: the image's content is in view as well.  What
      makes the environment a substitution induces respect its opened witnesses
      (`Model.substEnv`). -/
  openedTo : ModalSys.Opt = true → ∀ y X z, Γ.wit y = some X → Γ (.step y .dia) = some X →
    (θ.wit y).idxAlong [] = z → ∃ Z, Δ.wit z = some Z ∧ Δ (.step z .dia) = some Z

instance {ι : VarSymb → VarSymb} {Γ : Ctx} {θ : Subst σ Δ} :
    CoeFun (Coh ι Γ θ) (fun _ => ∀ v T, Γ.ref v = some T → ∀ p,
      (θ.at v).idxAlong p = ι (v.ext p)) :=
  ⟨Coh.ty⟩

/-- Into `□`: the contents, and each possible object's witness entry (`SubE.toWit`). -/
def box (θ : Subst σ Δ) : Subst σ Δ.boxIn where
  ty v :=
    match v with
    | .step u .box => (θ.at u).unbox
    | .step u .keep => (θ.at u).keepE
    | _ => .hide
  wit y := (θ.at y).toWit

def dia (θ : Subst σ Δ) (x ιx : VarSymb) : Subst σ (Δ.diaIn ιx) where
  ty v :=
    match v with
    | .step u .dia => if u = x then (θ.at x).diaBody ιx else .hide
    | .step u .box => (θ.at u).unbox.mono (Ctx.le_boxIn_diaIn Δ ιx)
    | .step u .keep => (θ.at u).keepE.mono (Ctx.le_boxIn_diaIn Δ ιx)
    | _ => .hide
  wit y := (θ.at y).toWit.mono (Ctx.le_boxIn_diaIn Δ ιx)

/-- Under a binder: the source slot goes to the target slot; everything else is weakened. -/
def under (θ : Subst σ Δ) (d d' : ℕ) (T : VarType) (h : Δ (.root (.bnd d')) = none) :
    Subst σ (Δ.insert (.bnd d') T) where
  ty v := if v = .root (.bnd d) then .ren (.root (.bnd d')) else (θ v).mono (Ctx.le_insert h T)
  wit y := (θ.wit y).mono (Ctx.le_insert h T)

/-- ⭐Into the view of the witness `y` (`◇⁰_y`), its image `z`: the content goes to `z.dia`, or
    to the body (modal β); everything else is weakened.  As `Subst.dia`. -/
def optIn (θ : Subst σ Δ) (y z : VarSymb) : Subst σ (Δ.optIn z) where
  ty v := if v = .step y .dia then (θ.wit y).optBody z else (θ v).mono (Ctx.le_optIn Δ z)
  wit y' := (θ.wit y').mono (Ctx.le_optIn Δ z)

theorem optIn_content (θ : Subst σ Δ) (y z : VarSymb) :
    θ.optIn y z (.step y .dia) = (θ.wit y).optBody z := if_pos rfl

theorem optIn_ne (θ : Subst σ Δ) {y v : VarSymb} (z : VarSymb) (hv : v ≠ .step y .dia) :
    θ.optIn y z v = (θ v).mono (Ctx.le_optIn Δ z) := if_neg hv

theorem at_nonproj (θ : Subst σ Δ) : ∀ {v : VarSymb}, v.lastProj = false → θ.at v = θ v
  | .root _, _ => rfl
  | .step v s, h => by
      change (if s.isStruct then (θ.at v).proj s else θ (.step v s)) = _
      have hs : s.isStruct = false := h
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
    (hvis : ∀ v T, v.lastProj = false → Γ v = some T → ∀ p, (θ v).idxAlong p = ι (v.ext p))
    (hwit : ModalSys.Opt = true → ∀ y X, Γ.wit y = some X → ∀ p,
      (θ.wit y).idxAlong p = ι (y.ext p) := by wit_triv)
    (hopen : ModalSys.Opt = true → ∀ y X z, Γ.wit y = some X → Γ (.step y .dia) = some X →
      (θ.wit y).idxAlong [] = z →
      (θ (.step y .dia)).mono (Ctx.le_optIn Δ z) = (θ.wit y).optBody z := by wit_triv)
    (hopenTo : ModalSys.Opt = true → ∀ y X z, Γ.wit y = some X → Γ (.step y .dia) = some X →
      (θ.wit y).idxAlong [] = z → ∃ Z, Δ.wit z = some Z ∧ Δ (.step z .dia) = some Z := by
      wit_triv) :
    Coh ι Γ θ := by
  refine ⟨?_, hwit, hopen, hopenTo⟩
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
  refine ⟨fun v T _ hv => ?_, fun _ y X hy => ?_⟩
  swap
  · obtain ⟨hO, hu⟩ := Ctx.boxIn_wit.mp hy
    exact SubE.okW_toWit hO (okRef_at hθ hu)
  match v with
  | .step u .box => exact SubE.okRef_unbox (okRef_at hθ (Ctx.boxIn_step_box hv))
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep hv
      exact SubE.okRef_keepE' hF hk (okRef_at hθ hu)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem coh_box {ι : VarSymb → VarSymb} {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ)
    (hc : Coh ι Γ θ) : Coh ι Γ.boxIn θ.box := by
  refine coh_of (ok_box hθ) ?_ ?_ (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)
  swap
  · intro _ y X hy p
    obtain ⟨hO, hu⟩ := Ctx.boxIn_wit.mp hy
    exact (SubE.idxAlong_toWit hO p (okRef_at hθ hu)).trans (hc y _ hu p)
  intro v T _ hv p
  match v with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hv
      change ((θ.at u).unbox).idxAlong p = _
      rw [SubE.idxAlong_unbox hk p (okRef_at hθ hu), hc u _ hu (.box :: p)]
      rfl
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep hv
      change ((θ.at u).keepE).idxAlong p = _
      rw [SubE.idxAlong_keepE' hF p hk (okRef_at hθ hu), hc u _ hu (.keep :: p)]
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
  refine ⟨fun v T _ hv => ?_, fun hO y Y hy =>
    WitE.okW_mono (Ctx.le_boxIn_diaIn Δ ιx) ((ok_box hθ).wit hO y Y hy)⟩
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
  refine coh_of (ok_dia hθ hx hw) ?_ ?_ ?_ ?_
  rotate_left
  · intro hO y Y hy p
    rw [show (θ.dia x (ι x)).wit y = ((θ.box).wit y).mono (Ctx.le_boxIn_diaIn Δ (ι x)) from rfl,
      WitE.idxAlong_mono]
    exact (coh_box hθ hc).wit hO y Y hy p
  · intro hO y Y z hy hyd hz
    have hyx : y = x := by
      change (if y = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some Y at hyd
      split_ifs at hyd with h
      exact h
    subst hyx
    obtain ⟨X, hX⟩ := hx
    have hYX : Y = X := by
      change (if y = y then (match Γ.ref y with | some (.VTypeDia X) => some X | _ => none)
        else none) = some Y at hyd
      rw [if_pos rfl, hX] at hyd
      exact (Option.some.inj hyd).symm
    subst hYX
    have hz' : z = ι y := by
      rw [← hz, show (θ.dia y (ι y)).wit y = ((θ.at y).toWit).mono
        (Ctx.le_boxIn_diaIn Δ (ι y)) from rfl, WitE.idxAlong_mono,
        SubE.idxAlong_toWit hO [] (okRef_at hθ hX)]
      exact hw
    subst hz'
    obtain ⟨X₂, hX₂⟩ := SubE.ref_witness (okRef_at hθ hX) hw
    change (if y = y then (θ.at y).diaBody (ι y) else SubE.hide).mono
        (Ctx.le_optIn (Δ.diaIn (ι y)) (ι y)) =
      (((θ.at y).toWit).mono (Ctx.le_boxIn_diaIn Δ (ι y))).optBody (ι y)
    rw [if_pos rfl, ← WitE.optBody_mono,
      SubE.toWit_optBody hO (ι y) (okRef_at hθ hX) (Ctx.le_diaIn_boxIn_optIn hO hX₂)]
    simp only [SubE.mono_mono]
  · intro hO y Y z hy hyd hz
    have hyx : y = x := by
      change (if y = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some Y at hyd
      split_ifs at hyd with h
      exact h
    subst hyx
    obtain ⟨X, hX⟩ := hx
    have hz' : z = ι y := by
      rw [← hz, show (θ.dia y (ι y)).wit y = ((θ.at y).toWit).mono
        (Ctx.le_boxIn_diaIn Δ (ι y)) from rfl, WitE.idxAlong_mono,
        SubE.idxAlong_toWit hO [] (okRef_at hθ hX)]
      exact hw
    subst hz'
    obtain ⟨X₂, hX₂⟩ := SubE.ref_witness (okRef_at hθ hX) hw
    exact ⟨X₂, Ctx.boxIn_wit.mpr ⟨hO, hX₂⟩,
      (Ctx.ref_nonproj _ rfl).symm.trans (Ctx.ref_diaIn_of hX₂)⟩
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
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box (Γ := Γ) hv
      change (((θ.at u).unbox).mono _).idxAlong p = _
      rw [SubE.idxAlong_mono, SubE.idxAlong_unbox hk p (okRef_at hθ hu), hc u _ hu (.box :: p)]
      rfl
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep (Γ := Γ) hv
      change (((θ.at u).keepE).mono _).idxAlong p = _
      rw [SubE.idxAlong_mono, SubE.idxAlong_keepE' hF p hk (okRef_at hθ hu),
        hc u _ hu (.keep :: p)]
      rfl
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

/-- The slot goes to the target slot. -/
theorem under_slot (θ : Subst σ Δ) (d d' : ℕ) (T : VarType) (h : Δ (.root (.bnd d')) = none) :
    θ.under d d' T h (.root (.bnd d)) = .ren (.root (.bnd d')) :=
  if_pos (e := (θ (.root (.bnd d))).mono (Ctx.le_insert h T)) rfl

theorem ok_under {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) {d d' : ℕ} (T : VarType)
    (h : Δ (.root (.bnd d')) = none) : Ok (Γ.insert (.bnd d) T) (θ.under d d' T h) := by
  refine ⟨fun v U hlp hv => ?_, fun hO y X hy =>
    WitE.okW_mono (Ctx.le_insert h T) (hθ.wit hO y X hy)⟩
  by_cases hvr : v = .root (.bnd d)
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    rw [show θ.under d d' T h (.root (.bnd d)) = .ren (.root (.bnd d')) from if_pos rfl]
    exact Ctx.ref_insert_root Δ _ T
  · have hv' : Γ v = some U := Ctx.insert_ne_some hv hvr
    rw [show θ.under d d' T h v = (θ v).mono (Ctx.le_insert h T) from if_neg hvr]
    exact SubE.okRef_mono _ (hθ v U hlp hv')

theorem coh_under {ι : VarSymb → VarSymb} {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ)
    (hc : Coh ι Γ θ) {d d' : ℕ} (hΓ : Γ.SlotsFrom d) (T : VarType)
    (h : Δ (.root (.bnd d')) = none) :
    Coh (VarSymb.shiftSlot ι d d') (Γ.insert (.bnd d) T) (θ.under d d' T h) := by
  refine coh_of (ok_under hθ T h) ?_ ?_ ?_ ?_
  rotate_left
  · intro hO y X hy p
    have hrt : y.rt ≠ .bnd d := fun he => by
      change Γ.wit y = some X at hy
      rw [hΓ.wit y d he le_rfl] at hy; cases hy
    change Γ.wit y = some X at hy
    change ((θ.wit y).mono (Ctx.le_insert h T)).idxAlong p =
      if (y.ext p).rt = .bnd d then _ else ι (y.ext p)
    rw [WitE.idxAlong_mono, VarSymb.ext_rt, if_neg hrt]
    exact hc.wit hO y X hy p
  · intro hO y X z hy hyd hz
    change Γ.wit y = some X at hy
    have hne : VarSymb.step y .dia ≠ .root (.bnd d) := fun he => by cases he
    replace hyd := Ctx.insert_ne_some hyd hne
    change ((θ.wit y).mono (Ctx.le_insert h T)).idxAlong [] = z at hz
    rw [WitE.idxAlong_mono] at hz
    rw [show θ.under d d' T h (.step y .dia) = (θ (.step y .dia)).mono (Ctx.le_insert h T)
        from if_neg (t := SubE.ren (.root (.bnd d'))) hne,
      show (θ.under d d' T h).wit y = (θ.wit y).mono (Ctx.le_insert h T) from rfl,
      ← WitE.optBody_mono, ← hc.opened hO y X z hy hyd hz]
    simp only [SubE.mono_mono]
  · intro hO y X z hy hyd hz
    change Γ.wit y = some X at hy
    have hne : VarSymb.step y .dia ≠ .root (.bnd d) := fun he => by cases he
    replace hyd := Ctx.insert_ne_some hyd hne
    change ((θ.wit y).mono (Ctx.le_insert h T)).idxAlong [] = z at hz
    rw [WitE.idxAlong_mono] at hz
    obtain ⟨Z, hZ, hZd⟩ := hc.openedTo hO y X z hy hyd hz
    exact ⟨Z, hZ, (Ctx.le_insert h T).ty _ _ hZd⟩
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
  · have hv' : Γ v = some U := Ctx.insert_ne_some hv hvr
    have hrt : v.rt ≠ .bnd d := fun he => by
      rw [hΓ v d he le_rfl] at hv'
      cases hv'
    rw [show θ.under d d' T h v = (θ v).mono (Ctx.le_insert h T) from if_neg hvr,
      SubE.idxAlong_mono, ← at_nonproj θ hlp, hc v U ((Ctx.ref_nonproj Γ hlp).trans hv') p]
    change ι (v.ext p) = if (v.ext p).rt = .bnd d then _ else ι (v.ext p)
    rw [VarSymb.ext_rt, if_neg hrt]

theorem ok_optIn {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) (hO : ModalSys.Opt = true)
    {y z : VarSymb} {X : VarType} (hy : Γ.wit y = some X) (hw : (θ.wit y).idxAlong [] = z) :
    Ok (Γ.optIn y) (θ.optIn y z) := by
  refine ⟨fun v T hlp hv => ?_, fun hO' y' X' hy' =>
    WitE.okW_mono (Ctx.le_optIn Δ z) (hθ.wit hO' y' X' hy')⟩
  by_cases hc : v = .step y .dia
  · subst hc
    rw [Ctx.optIn_content hy] at hv
    cases hv
    rw [optIn_content]
    exact WitE.okRef_optBody (hθ.wit hO y X hy) hw
  · rw [Ctx.optIn_ne hc] at hv
    rw [optIn_ne θ z hc]
    exact SubE.okRef_mono _ (hθ v T hlp hv)

theorem coh_optIn {ι : VarSymb → VarSymb} {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ)
    (hc : Coh ι Γ θ) (hO : ModalSys.Opt = true) {y : VarSymb} {X : VarType}
    (hy : Γ.wit y = some X) : Coh ι (Γ.optIn y) (θ.optIn y (ι y)) := by
  have hw : (θ.wit y).idxAlong [] = ι y := hc.wit hO y X hy []
  refine coh_of (ok_optIn hθ hO hy hw) ?_ ?_ ?_ ?_
  · intro v T hlp hv p
    by_cases hc' : v = .step y .dia
    · subst hc'
      rw [optIn_content, WitE.idxAlong_optBody p (hθ.wit hO y X hy) hw]
      exact hc.wit hO y X hy (.dia :: p)
    · rw [Ctx.optIn_ne hc'] at hv
      rw [optIn_ne θ _ hc', SubE.idxAlong_mono, ← at_nonproj θ hlp]
      exact hc v T ((Ctx.ref_nonproj Γ hlp).trans hv) p
  · intro hO' y' X' hy' p
    rw [show (θ.optIn y (ι y)).wit y' = (θ.wit y').mono (Ctx.le_optIn Δ _) from rfl,
      WitE.idxAlong_mono]
    exact hc.wit hO' y' X' hy' p
  · intro hO' y' X' z hy' hyd hz
    rw [show (θ.optIn y (ι y)).wit y' = (θ.wit y').mono (Ctx.le_optIn Δ _) from rfl] at hz ⊢
    rw [WitE.idxAlong_mono] at hz
    by_cases hc' : y' = y
    · subst hc'
      rw [hw] at hz
      subst hz
      rw [optIn_content, ← WitE.optBody_mono]
    · have hne : VarSymb.step y' .dia ≠ .step y .dia := fun he => hc' (by cases he; rfl)
      rw [Ctx.optIn_ne hne] at hyd
      rw [optIn_ne θ _ hne, ← WitE.optBody_mono, ← hc.opened hO' y' X' z hy' hyd hz]
      simp only [SubE.mono_mono]
  · intro hO' y' X' z hy' hyd hz
    rw [show (θ.optIn y (ι y)).wit y' = (θ.wit y').mono (Ctx.le_optIn Δ _) from rfl] at hz
    rw [WitE.idxAlong_mono] at hz
    have hZ : ∃ Z, Δ.wit z = some Z ∧ (Δ.optIn (ι y)) (.step z .dia) = some Z := by
      by_cases hc' : y' = y
      · subst hc'
        rw [hw] at hz
        subst hz
        obtain ⟨Z, hZ⟩ := WitE.wit_of (hθ.wit hO y' X hy) hw
        exact ⟨Z, hZ, Ctx.optIn_content hZ⟩
      · have hne : VarSymb.step y' .dia ≠ .step y .dia := fun he => hc' (by cases he; rfl)
        rw [Ctx.optIn_ne hne] at hyd
        obtain ⟨Z, hZ, hZd⟩ := hc.openedTo hO' y' X' z hy' hyd hz
        refine ⟨Z, hZ, ?_⟩
        by_cases hzy : z = ι y
        · subst hzy
          exact Ctx.optIn_content hZ
        · rw [Ctx.optIn_ne (fun he => hzy (by cases he; rfl))]
          exact hZd
    exact hZ

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
  | ι, _, _, _, _, θ, hθ, hc, _, _, .here hT s t =>
      .here hT (Term.subst ι θ hθ hc s) (Term.subst ι θ hθ hc t)
  | ι, _, _, _, _, θ, hθ, hc, _, _, .back hB L s t =>
      .back hB L (Term.subst ι θ hθ hc s) (Term.subst ι θ hθ hc t)
  | ι, _, _, d, d', θ, hθ, hc, hΓ, hΔ, .retS hB S t Φ =>
      .retS hB S (Term.subst ι θ hθ hc t)
        (WFF.subst (VarSymb.shiftSlot ι d d') (θ.box.under d d' _ hΔ.boxIn.root)
          (Subst.ok_under (Subst.ok_box hθ) _ hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn _ hΔ.boxIn.root)
          (hΓ.boxIn.insert _) (hΔ.boxIn.insert _) Φ)
  | ι, _, _, d, d', θ, hθ, hc, hΓ, hΔ, .retxS hB y hy S t Φ =>
      have hw : (θ.at y).idxAlong [] = ι y := hy.elim fun _ hY => hc y _ hY []
      .retxS hB (ι y) (hy.elim fun _ hY => SubE.ref_witness (Subst.okRef_at hθ hY) hw) S
        (Term.subst ι θ hθ hc t)
        (WFF.subst (VarSymb.shiftSlot ι d d') ((θ.dia y (ι y)).under d d' _ (hΔ.diaIn (ι y)).root)
          (Subst.ok_under (Subst.ok_dia hθ hy hw) _ (hΔ.diaIn (ι y)).root)
          (Subst.coh_under (Subst.ok_dia hθ hy hw) (Subst.coh_dia hθ hc hy) (hΓ.diaIn y) _
            (hΔ.diaIn (ι y)).root)
          ((hΓ.diaIn y).insert _) ((hΔ.diaIn (ι y)).insert _) Φ)
  | ι, _, _, d, d', θ, hθ, hc, hΓ, hΔ, .link hV hF t Φ =>
      .link hV hF (Term.subst ι θ hθ hc t)
        (WFF.subst (VarSymb.shiftSlot ι d d') (θ.box.under d d' _ hΔ.boxIn.root)
          (Subst.ok_under (Subst.ok_box hθ) _ hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn _ hΔ.boxIn.root)
          (hΓ.boxIn.insert _) (hΔ.boxIn.insert _) Φ)
  | ι, _, _, d, d', θ, hθ, hc, hΓ, hΔ, .linkx hV hF y hy t Φ =>
      have hw : (θ.at y).idxAlong [] = ι y := hy.elim fun _ hY => hc y _ hY []
      .linkx hV hF (ι y) (hy.elim fun _ hY => SubE.ref_witness (Subst.okRef_at hθ hY) hw)
        (Term.subst ι θ hθ hc t)
        (WFF.subst (VarSymb.shiftSlot ι d d') ((θ.dia y (ι y)).under d d' _ (hΔ.diaIn (ι y)).root)
          (Subst.ok_under (Subst.ok_dia hθ hy hw) _ (hΔ.diaIn (ι y)).root)
          (Subst.coh_under (Subst.ok_dia hθ hy hw) (Subst.coh_dia hθ hc hy) (hΓ.diaIn y) _
            (hΔ.diaIn (ι y)).root)
          ((hΓ.diaIn y).insert _) ((hΔ.diaIn (ι y)).insert _) Φ)
  | ι, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .optx hO y hy φ =>
      .optx hO (ι y) (hy.elim fun X hX => WitE.wit_of (hθ.wit hO y X hX) (hc.wit hO y X hX []))
        (WFF.subst ι (θ.optIn y (ι y))
          (hy.elim fun X hX => Subst.ok_optIn hθ hO hX (hc.wit hO y X hX []))
          (hy.elim fun _ hX => Subst.coh_optIn hθ hc hO hX) (hΓ.optIn y) (hΔ.optIn (ι y)) φ)

/-! ## Substituting one root -/

namespace Subst

variable {σ : Signature} {Δ : Ctx}

/-- `r ↦ e`, every other address to itself. -/
def single (r : Root) (e : SubE σ Δ) : Subst σ Δ where
  ty v := if v = .root r then e else .ren v
  wit y := .ren y

theorem single_self (r : Root) (e : SubE σ Δ) : single r e (.root r) = e :=
  if_pos (e := SubE.ren (.root r)) rfl

/-- A substitution's entry at the root it sets, by that construction's lemma (more constructions
    add rules: `toFree_slot`, `set_root`). -/
syntax "slot_rfl" : tactic
macro_rules | `(tactic| slot_rfl) => `(tactic| exact if_pos rfl)
macro_rules | `(tactic| slot_rfl) => `(tactic| exact Subst.under_slot _ _ _ _ _)
macro_rules | `(tactic| slot_rfl) => `(tactic| exact Subst.single_self _ _)

def singleIdx (r : Root) (e : SubE σ Δ) : VarSymb → VarSymb :=
  fun i => if i.rt = r then e.idxAlong i.path else i

theorem ok_single {Γ : Ctx} {r : Root} {T : VarType} {e : SubE σ Δ} (hle : Γ.Le Δ)
    (he : e.OkRef T) : Ok (Γ.insert r T) (single r e) := by
  refine ⟨fun v U hlp hv => ?_, fun _ y X hy => hle.wit y X hy⟩
  by_cases hvr : v = .root r
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    rw [show single r e (.root r) = e from if_pos rfl]
    exact he
  · have hv' : Γ v = some U := Ctx.insert_ne_some hv hvr
    rw [show single r e v = .ren v from if_neg hvr]
    exact (Ctx.ref_nonproj Δ hlp).trans (hle v U hv')

theorem coh_single {Γ : Ctx} {r : Root} {T : VarType} {e : SubE σ Δ} (hr : Γ.RootFresh r)
    (hle : Γ.Le Δ) (he : e.OkRef T) : Coh (singleIdx r e) (Γ.insert r T) (single r e) := by
  refine coh_of (ok_single hle he) ?_ ?_ ?_ ?_
  rotate_left
  · intro _ y X hy p
    have hrt : y.rt ≠ r := fun he' => by
      change Γ.wit y = some X at hy
      rw [hr.wit y he'] at hy; cases hy
    change y.ext p = if (y.ext p).rt = r then _ else y.ext p
    rw [VarSymb.ext_rt, if_neg hrt]
  · intro _ y X z _ _ hz
    have hz' : y = z := hz
    subst hz'
    have hne : VarSymb.step y .dia ≠ .root r := fun he => by cases he
    rw [show single r e (.step y .dia) = .ren (.step y .dia) from if_neg (t := e) hne]
    rfl
  · intro _ y X z hy hyd hz
    have hz' : y = z := hz
    subst hz'
    change Γ.wit y = some X at hy
    replace hyd := Ctx.insert_ne_some hyd (fun he => by cases he)
    exact ⟨X, hle.wit y X hy, hle.ty _ _ hyd⟩
  intro v U hlp hv p
  by_cases hvr : v = .root r
  · subst hvr
    rw [show single r e (.root r) = e from if_pos rfl]
    change e.idxAlong p = if ((VarSymb.root r).ext p).rt = r then
      e.idxAlong ((VarSymb.root r).ext p).path else _
    simp only [VarSymb.ext_rt, VarSymb.ext_path, VarSymb.rt, VarSymb.path, List.nil_append,
      if_true]
  · have hv' : Γ v = some U := Ctx.insert_ne_some hv hvr
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

/-- ⭐Substitution commutes with equality at a `◇`-free type: `eqRec` is structural there, so each
    clause is the corresponding clause of `WFF.subst`.  `◇`-free is exactly where `Proof.here_fun`
    states it (§2d), and it is what makes the clauses available: at a `◇` the equality is a `□_x`,
    whose substitution would have to be matched against the witness's own image. -/
theorem WFF.subst_eqRec {σ : Signature} {ι : VarSymb → VarSymb} :
    {Γ Δ : Ctx} → {d d' : ℕ} → (θ : Subst σ Δ) → (hθ : Subst.Ok Γ θ) → (hc : Subst.Coh ι Γ θ) →
    (hΓ : Γ.SlotsFrom d) → (hΔ : Δ.SlotsFrom d') → (T : VarType) → T.diaFree = true →
    {a : Ann T} → (t : Term σ Γ T a) → (s : Term σ Γ T a) →
    WFF.subst ι θ hθ hc hΓ hΔ (eqRec T t s : WFF σ Γ d) =
      eqRec T (Term.subst ι θ hθ hc t) (Term.subst ι θ hθ hc s)
  | _, _, _, _, _, _, _, _, _, .Var, _, .var, t, s => by
      have e : ∀ {Γ' : Ctx} {e' : ℕ} (u v : Term σ Γ' .Var .var),
          (eqRec .Var u v : WFF σ Γ' e') = .eq u v := by
        intro _ _ u v
        cases u <;> cases v <;> rfl
      rw [e t s, e _ _]
      rfl
  | _, _, _, _, _, _, _, _, _, .VTypeOne, _, .one, .unit, .unit => rfl
  | _, _, _, _, θ, hθ, hc, hΓ, hΔ, .VTypeProd A B, hdf, .prod _ _,
      .pair t₁ t₂, .pair s₁ s₂ => by
      simp only [VarType.diaFree, Bool.and_eq_true] at hdf
      change WFF.and (WFF.subst ι θ hθ hc hΓ hΔ (eqRec A t₁ s₁))
        (WFF.subst ι θ hθ hc hΓ hΔ (eqRec B t₂ s₂)) = _
      rw [WFF.subst_eqRec θ hθ hc hΓ hΔ A hdf.1 t₁ s₁,
        WFF.subst_eqRec θ hθ hc hΓ hΔ B hdf.2 t₂ s₂]
      rfl
  | _, _, _, _, θ, hθ, hc, hΓ, hΔ, .VTypeBox A, hdf, .box _, .boxtm t, .boxtm s => by
      change WFF.box (WFF.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc)
        hΓ.boxIn hΔ.boxIn (eqRec A t s)) = _
      rw [WFF.subst_eqRec θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn hΔ.boxIn A hdf t s]
      rfl


namespace Subst

/-- Away from the replaced root, a single-root substitution is the identity renaming. -/
theorem at_single_of_rt_ne {σ : Signature} {Δ : Ctx} {r : Root} {e : SubE σ Δ} :
    ∀ {v : VarSymb}, v.rt ≠ r → (single r e).at v = .ren v
  | .root r', h => by
      change (if (VarSymb.root r') = .root r then e else SubE.ren (.root r')) = _
      exact if_neg (fun he => h (VarSymb.root.inj he))
  | .step v s, h => by
      change (if s.isStruct then ((single r e).at v).proj s else single r e (.step v s)) = _
      by_cases hs : s.isStruct = true
      · rw [if_pos hs, at_single_of_rt_ne (v := v) h]
        rfl
      · rw [if_neg hs]
        change (if (VarSymb.step v s) = .root r then e else SubE.ren (.step v s)) = _
        exact if_neg (fun he => by cases he)

/-- At the replaced root it is the entry. -/
theorem at_single_root {σ : Signature} {Δ : Ctx} (r : Root) (e : SubE σ Δ) :
    (single r e).at (.root r) = e := by
  change (if (VarSymb.root r) = .root r then e else SubE.ren (.root r)) = _
  exact if_pos rfl

/-- At a projection of the replaced root, a pair entry gives that component.  This is what a hole
    term built from the slot's own `.fst` / `.snd` address reads off (`Proof.here_fst`). -/
theorem at_single_fst {σ : Signature} {Δ : Ctx} (r : Root) {A B : VarType} {a : Ann A} {b : Ann B}
    (s : Term σ Δ A a) (t : Term σ Δ B b) :
    (single r (.tm (Term.pair s t))).at (.step (.root r) .fst) = .tm s := by
  change (if Step.fst.isProj then ((single r (SubE.tm (Term.pair s t))).at (.root r)).proj .fst
    else _) = _
  rw [if_pos (show Step.fst.isProj = true from rfl), at_single_root]
  rfl

theorem at_single_snd {σ : Signature} {Δ : Ctx} (r : Root) {A B : VarType} {a : Ann A} {b : Ann B}
    (s : Term σ Δ A a) (t : Term σ Δ B b) :
    (single r (.tm (Term.pair s t))).at (.step (.root r) .snd) = .tm t := by
  change (if Step.snd.isProj then ((single r (SubE.tm (Term.pair s t))).at (.root r)).proj .snd
    else _) = _
  rw [if_pos (show Step.snd.isProj = true from rfl), at_single_root]
  rfl

end Subst

end V12M
