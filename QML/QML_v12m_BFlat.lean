import QML.QML_v12m_BRename

/-!
# QML v12m — flattening a context into a world language

`completenessB` speaks of a world language `ctxOf l`, whose variables are roots.  A presented
context may instead show **view items** (`u.box`, `x.dia`).  This file carries completeness across
such a translation.

* ⭐`Flat σ Γ Δ`: a translation of `Γ`'s formulas into `Δ` that provability follows backwards
  (`prov`) and truth follows along an environment map (`sat`).  Translations compose (`Flat.comp`),
  so a presentation can be flattened one constructor at a time.
* ⭐`Flat.ofPair`: a substitution and an inverse substitution that cancel give one — provability by
  `Proof.subst`, truth by `Model.sat_subst`.
* ⭐`completenessB_flat`: completeness for any context flattened into a world language.
* The arrow into a new child already is such a pair (`subst_pull_arrow`), so a `□` view over a
  world language is flattened by it (`flatBox`), and a `◇_x` view by the witness arrow
  (`flatDia`) — giving `completenessB_boxIn` and `completenessB_diaIn`.

Composing these for an arbitrary presentation needs two more pairs: one for a root declared after
a view, and the push of a pair under a view.  Neither is here yet.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## Translations that carry completeness -/

/-- ⭐A translation of `Γ` into `Δ`: provability comes back along it, and truth travels with an
    environment map. -/
structure Flat (σ : Signature) (Γ Δ : Ctx) where
  /-- The translation of formulas. -/
  tr : WFF σ Γ 0 → WFF σ Δ 0
  /-- A proof of the translated sequent gives one of the original. -/
  prov : ∀ {Δs : List (WFF σ Γ 0)} {φ : WFF σ Γ 0}, Provable (Δs.map tr) (tr φ) → Provable Δs φ
  /-- An environment of `Δ` reads as one of `Γ`. -/
  env : {M : Model.{0, 0} σ} → {w : M.frame.W} → M.Env Δ w → M.Env Γ w
  /-- The translation is truth-preserving. -/
  sat : ∀ {M : Model.{0, 0} σ} {w : M.frame.W} (e : M.Env Δ w) (φ : WFF σ Γ 0),
    M.sat e (tr φ) ↔ M.sat (env e) φ
  /-- It fixes `⊥`, so it carries consistency. -/
  bot : tr .bot = .bot

/-- Translations compose. -/
def Flat.comp {Γ Δ E : Ctx} (F : Flat σ Γ Δ) (G : Flat σ Δ E) : Flat σ Γ E where
  tr := G.tr ∘ F.tr
  prov {Δs φ} h := F.prov (G.prov (by rw [← List.map_map] at h; exact h))
  env e := F.env (G.env e)
  sat e φ := (G.sat e (F.tr φ)).trans (F.sat (G.env e) φ)
  bot := by
    change G.tr (F.tr .bot) = .bot
    rw [F.bot, G.bot]

/-- ⭐A substitution with an inverse that cancels it is a translation. -/
def Flat.ofPair {Γ Δ : Ctx} [Γ.Presented] [Δ.NoSlots] (hnp : Γ.NoProjLast)
    {ι ι' : VarSymb → VarSymb} (θ : Subst σ Δ) (θ' : Subst σ Γ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) (hθ' : Subst.Ok Δ θ') (hc' : Subst.Coh ι' Δ θ')
    (cancel : ∀ φ : WFF σ Γ 0,
      WFF.subst ι' θ' hθ' hc' Ctx.NoSlots.slots Ctx.NoSlots.slots
        (WFF.subst ι θ hθ hc Ctx.NoSlots.slots Ctx.NoSlots.slots φ) = φ) :
    Flat σ Γ Δ where
  tr := WFF.subst ι θ hθ hc Ctx.NoSlots.slots Ctx.NoSlots.slots
  prov {Δs φ} h := by
    obtain ⟨p⟩ := h
    have hq := Proof.subst p θ' hθ' hc' Ctx.NoSlots.slots
    rw [List.map_map] at hq
    simp only [Function.comp_def, cancel] at hq
    rw [show (fun x : WFF σ Γ 0 => x) = id from rfl, List.map_id] at hq
    exact ⟨hq⟩
  env e := Model.substEnv θ hθ hnp e
  sat e φ := Model.sat_subst θ hθ hc Ctx.NoSlots.slots Ctx.NoSlots.slots hnp e φ
  bot := rfl

variable [ModalSys.NoFour]

/-! ## Pairs of substitutions, and pushing them under a view -/

/-- A substitution similar to the identity stays so under `□`. -/
theorem sim_box_of {Γ : Ctx} {θ : Subst σ Γ} (h : Subst.Sim Γ θ (Subst.idS σ Γ)) :
    Subst.Sim Γ.boxIn θ.box (Subst.idS σ Γ.boxIn) := by
  have hk := ModalSys.NoFour.keepOnly
  refine Subst.sim_of ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      obtain ⟨_, hu⟩ := Ctx.boxIn_box hv
      have hs := (h u _ hu).unbox
      rw [Subst.at_idS] at hs
      change SubE.Sim T ((θ.at u).unbox) (.ren (.step u .box))
      rw [← VarSymb.inner_box hk]
      exact hs
  | .step u .keep =>
      obtain ⟨hF, _⟩ := Ctx.boxIn_keep hv
      exact absurd (ModalSys.NoFour.noFour.symm.trans hF) (by simp)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

/-- ⭐A substitution with an inverse that cancels it up to `Sim`: the data a `Flat` is built from,
    kept so that it can be pushed under a view. -/
structure Pair (σ : Signature) (Γ Δ : Ctx) where
  /-- The index map of the translation. -/
  ι : VarSymb → VarSymb
  /-- The index map of the translation back. -/
  ι' : VarSymb → VarSymb
  /-- The index map of the composite. -/
  ι₃ : VarSymb → VarSymb
  /-- The translation into `Δ`. -/
  θ : Subst σ Δ
  /-- The translation back. -/
  θ' : Subst σ Γ
  /-- A substitution of `Γ` standing for the composite. -/
  θ₃ : Subst σ Γ
  hθ : Subst.Ok Γ θ
  hc : Subst.Coh ι Γ θ
  hθ' : Subst.Ok Δ θ'
  hc' : Subst.Coh ι' Δ θ'
  hθ₃ : Subst.Ok Γ θ₃
  hc₃ : Subst.Coh ι₃ Γ θ₃
  /-- Going and coming back is the composite. -/
  sim : Subst.Sim Γ θ₃ (θ.comp θ' hθ' hc')
  /-- And the composite is the identity. -/
  simId : Subst.Sim Γ θ₃ (Subst.idS σ Γ)

variable {Γ Δ : Ctx}

omit [ModalSys.NoFour] in
/-- The two substitutions of a pair cancel. -/
theorem Pair.cancel [Γ.NoSlots] [Δ.NoSlots] (P : Pair σ Γ Δ) (φ : WFF σ Γ 0) :
    WFF.subst P.ι' P.θ' P.hθ' P.hc' Ctx.NoSlots.slots Ctx.NoSlots.slots
      (WFF.subst P.ι P.θ P.hθ P.hc Ctx.NoSlots.slots Ctx.NoSlots.slots φ) = φ := by
  refine (WFF.subst_comp _ _ P.θ₃ _ _ _ _ P.hθ₃ P.hc₃ _ _ _ P.sim φ).trans ?_
  refine (WFF.subst_congr _ _ _ Subst.ok_idS _ Subst.coh_idS _ _ P.simId φ).trans ?_
  exact WFF.subst_id _ _ _ φ

/-- A pair is a translation. -/
def Pair.toFlat [Γ.Presented] [Δ.NoSlots] (P : Pair σ Γ Δ) (hnp : Γ.NoProjLast) :
    Flat σ Γ Δ :=
  Flat.ofPair hnp P.θ P.θ' P.hθ P.hc P.hθ' P.hc' P.cancel

/-- ⭐A pair pushed under `□`. -/
def Pair.box (P : Pair σ Γ Δ) : Pair σ Γ.boxIn Δ.boxIn where
  ι := P.ι
  ι' := P.ι'
  ι₃ := P.ι₃
  θ := P.θ.box
  θ' := P.θ'.box
  θ₃ := P.θ₃.box
  hθ := Subst.ok_box P.hθ
  hc := Subst.coh_box P.hθ P.hc
  hθ' := Subst.ok_box P.hθ'
  hc' := Subst.coh_box P.hθ' P.hc'
  hθ₃ := Subst.ok_box P.hθ₃
  hc₃ := Subst.coh_box P.hθ₃ P.hc₃
  sim := Subst.sim_box_comp P.hθ P.hθ' P.hc' P.sim
  simId := sim_box_of P.simId


/-! ## Extending a pair by a declared root -/

omit [ModalSys.NoFour] in
/-- Substitutions agreeing on the addresses of a root agree at them. -/
theorem at_eq_of_agree {Δ : Ctx} {θ₁ θ₂ : Subst σ Δ} {p : Root → Prop}
    (h : ∀ w : VarSymb, p w.rt → θ₁ w = θ₂ w) :
    ∀ w : VarSymb, p w.rt → θ₁.at w = θ₂.at w
  | .root _, hw => h _ hw
  | .step w s, hw => by
      simp only [Subst.at]
      split_ifs with _
      · rw [at_eq_of_agree h w hw]
      · exact h _ hw

omit [ModalSys.NoFour] in
/-- A reachable address is not rooted at a fresh name. -/
theorem rt_ne_of_fresh {Δ : Ctx} {r : Root} (hfr : Δ.RootFresh r) :
    ∀ {w : VarSymb} {T : VarType}, Δ.ref w = some T → w.rt ≠ r
  | .root r', T, h, he => by
      change Δ (.root r') = some T at h
      have hrr : r' = r := he
      subst hrr
      rw [hfr.root] at h
      cases h
  | .step w s, T, h, he => by
      simp only [Ctx.ref] at h
      split_ifs at h with hs
      · cases hU : Δ.ref w with
        | none => rw [hU] at h; cases h
        | some U => exact rt_ne_of_fresh hfr hU he
      · rw [hfr _ he] at h
        cases h

/-- A substitution extended by one root, which goes to a root of the target. -/
def extS {Δ Δ' : Ctx} (θ : Subst σ Δ) (hle : Δ.Le Δ') (u v : ℕ) : Subst σ Δ' :=
  fun w => if w.rt = .free u then .ren (w.reroot (.free v)) else (θ.mono hle) w

/-- Where it sends annotation indices. -/
def extIdx (ι : VarSymb → VarSymb) (u v : ℕ) (a : VarSymb) : VarSymb :=
  if a.rt = .free u then a.reroot (.free v) else ι a

omit [ModalSys.NoFour] in
theorem ok_extS {Γ Δ Δ' : Ctx} {θ : Subst σ Δ} (hθ : Subst.Ok Γ θ) (hle : Δ.Le Δ')
    {u v : ℕ} {T : VarType} (hfr : Γ.RootFresh (.free u))
    (hv : Δ'.ref (.root (.free v)) = some T) :
    Subst.Ok (Γ.insert (.free u) T) (extS θ hle u v) := by
  intro w U hlp hw
  simp only [Ctx.insert] at hw
  by_cases hwu : w = .root (.free u)
  · subst hwu
    rw [if_pos rfl] at hw
    cases hw
    simp only [extS]
    rw [if_pos (show (VarSymb.root (Root.free u)).rt = Root.free u from rfl)]
    exact hv
  · rw [if_neg hwu] at hw
    have hrt : w.rt ≠ .free u := fun he => by rw [hfr w he] at hw; cases hw
    simp only [extS]
    rw [if_neg hrt]
    exact SubE.okRef_mono hle (hθ w U hlp hw)

omit [ModalSys.NoFour] in
theorem coh_extS {ι : VarSymb → VarSymb} {Γ Δ Δ' : Ctx} {θ : Subst σ Δ} (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) (hle : Δ.Le Δ') {u v : ℕ} {T : VarType}
    (hfr : Γ.RootFresh (.free u)) (hv : Δ'.ref (.root (.free v)) = some T) :
    Subst.Coh (extIdx ι u v) (Γ.insert (.free u) T) (extS θ hle u v) := by
  refine Subst.coh_of (ok_extS hθ hle hfr hv) ?_
  intro w U hlp hw p
  simp only [Ctx.insert] at hw
  by_cases hwu : w = .root (.free u)
  · subst hwu
    simp only [extS, extIdx]
    rw [if_pos (show (VarSymb.root (Root.free u)).rt = Root.free u from rfl),
      if_pos (show ((VarSymb.root (Root.free u)).ext p).rt = Root.free u by
        rw [VarSymb.ext_rt]; rfl)]
    change (VarSymb.root (Root.free v)).ext p = _
    rw [VarSymb.reroot_eq, VarSymb.ext_path]
    rfl
  · rw [if_neg hwu] at hw
    have hrt : w.rt ≠ .free u := fun he => by rw [hfr w he] at hw; cases hw
    simp only [extS, extIdx]
    rw [if_neg hrt, if_neg (show ¬ (w.ext p).rt = Root.free u by rw [VarSymb.ext_rt]; exact hrt)]
    change ((θ w).mono hle).idxAlong p = _
    rw [SubE.idxAlong_mono, ← Subst.at_nonproj θ hlp]
    exact hc w U ((Ctx.ref_nonproj Γ hlp).trans hw) p


omit [ModalSys.NoFour] in
/-- The extension of a substitution similar to the identity is similar to the identity. -/
theorem simId_extS {Γ : Ctx} {θ : Subst σ Γ} {u : ℕ} {T : VarType} (hfr : Γ.RootFresh (.free u))
    (h : Subst.Sim Γ θ (Subst.idS σ Γ)) :
    Subst.Sim (Γ.insert (.free u) T) (extS θ (Ctx.le_insert hfr.root T) u u)
      (Subst.idS σ (Γ.insert (.free u) T)) := by
  refine Subst.sim_of ?_
  intro w U hlp hw
  simp only [Ctx.insert] at hw
  by_cases hwu : w = .root (.free u)
  · subst hwu
    simp only [extS]
    rw [if_pos (show (VarSymb.root (Root.free u)).rt = Root.free u from rfl)]
    exact .refl _
  · rw [if_neg hwu] at hw
    have hrt : w.rt ≠ .free u := fun he => by rw [hfr w he] at hw; cases hw
    simp only [extS]
    rw [if_neg hrt]
    have hs := h w U ((Ctx.ref_nonproj Γ hlp).trans hw)
    rw [Subst.at_idS, Subst.at_nonproj θ hlp] at hs
    exact hs.mono (Ctx.le_insert hfr.root T)


omit [ModalSys.NoFour] in
theorem ref_insert_root (Γ : Ctx) (r : Root) (T : VarType) :
    (Γ.insert r T).ref (.root r) = some T := by
  change (Γ.insert r T) (.root r) = some T
  simp [Ctx.insert]

omit [ModalSys.NoFour] in
/-- Away from the new root, the extension is the old substitution. -/
theorem at_extS_of_ne {Δ Δ' : Ctx} {θ : Subst σ Δ} {hle : Δ.Le Δ'} {u v : ℕ} {y : VarSymb}
    (hy : y.rt ≠ .free u) : (extS θ hle u v).at y = (θ.at y).mono hle := by
  rw [at_eq_of_agree (p := fun r => r ≠ Root.free u) (θ₂ := θ.mono hle)
    (fun z hz => by simp only [extS]; rw [if_neg hz]) y hy, Subst.at_mono]

omit [ModalSys.NoFour] in
/-- ⭐Going out and back along extended substitutions is the extended composite. -/
theorem sim_extS {Γ Δ : Ctx} {ι' : VarSymb → VarSymb} {θ : Subst σ Δ} {θ' : Subst σ Γ}
    {θ₃ : Subst σ Γ} (hθ : Subst.Ok Γ θ) (hθ' : Subst.Ok Δ θ') (hc' : Subst.Coh ι' Δ θ')
    {u v : ℕ} {T : VarType} (hu : Γ.RootFresh (.free u)) (hv : Δ.RootFresh (.free v))
    (hsim : Subst.Sim Γ θ₃ (θ.comp θ' hθ' hc')) :
    Subst.Sim (Γ.insert (.free u) T) (extS θ₃ (Ctx.le_insert hu.root T) u u)
      ((extS θ (Ctx.le_insert hv.root T) u v).comp
        (extS θ' (Ctx.le_insert hu.root T) v u)
        (ok_extS hθ' (Ctx.le_insert hu.root T) hv (ref_insert_root Γ (.free u) T))
        (coh_extS hθ' hc' (Ctx.le_insert hu.root T) hv (ref_insert_root Γ (.free u) T))) := by
  have heq : ∀ (y : VarSymb) (U : VarType), Δ.ref y = some U →
      (extS θ' (Ctx.le_insert hu.root T) v u).at y = (θ'.at y).mono (Ctx.le_insert hu.root T) :=
    fun y U hy => at_extS_of_ne (rt_ne_of_fresh hv hy)
  refine Subst.sim_of ?_
  intro w U hlp hw
  simp only [Ctx.insert] at hw
  have hlu := Ctx.le_insert hu.root T
  have hlv := Ctx.le_insert hv.root T
  by_cases hwu : w = .root (.free u)
  · subst hwu
    change SubE.Sim U ((extS θ₃ hlu u u) (.root (.free u)))
      (SubE.comp (extS θ' hlu v u) _ _ ((extS θ hlv u v) (.root (.free u))))
    simp only [extS]
    rw [if_pos (show (VarSymb.root (Root.free u)).rt = Root.free u from rfl)]
    rw [if_pos (show (VarSymb.root (Root.free u)).rt = Root.free u from rfl)]
    change SubE.Sim U (.ren (VarSymb.root (Root.free u)))
      (if (VarSymb.root (Root.free v)).rt = Root.free v then
          SubE.ren ((VarSymb.root (Root.free v)).reroot (Root.free u))
        else (θ'.mono hlu) (VarSymb.root (Root.free v)))
    rw [if_pos (show (VarSymb.root (Root.free v)).rt = Root.free v from rfl)]
    exact .refl _
  · rw [if_neg hwu] at hw
    have hrt : w.rt ≠ .free u := fun he => by rw [hu w he] at hw; cases hw
    have hwr : Γ.ref w = some U := (Ctx.ref_nonproj Γ hlp).trans hw
    have hs := hsim w U hwr
    rw [Subst.at_nonproj _ hlp, Subst.at_comp hθ θ' hθ' hc' hwr,
      Subst.at_nonproj θ hlp] at hs
    change SubE.Sim U ((extS θ₃ hlu u u) w) (SubE.comp (extS θ' hlu v u) _ _ ((extS θ hlv u v) w))
    simp only [extS]
    rw [if_neg hrt]
    rw [if_neg hrt]
    change SubE.Sim U ((θ₃ w).mono hlu) (SubE.comp (extS θ' hlu v u) _ _ ((θ w).mono hlv))
    rw [SubE.comp_mono θ' hθ' hc' hlv hlu _ _ _ heq (hθ w U hlp hw)]
    exact hs.mono hlu

/-- ⭐A pair extended by a root declared on each side. -/
def Pair.insertRoot (P : Pair σ Γ Δ) {u v : ℕ} {T : VarType}
    (hu : Γ.RootFresh (.free u)) (hv : Δ.RootFresh (.free v)) :
    Pair σ (Γ.insert (.free u) T) (Δ.insert (.free v) T) where
  ι := extIdx P.ι u v
  ι' := extIdx P.ι' v u
  ι₃ := extIdx P.ι₃ u u
  θ := extS P.θ (Ctx.le_insert hv.root T) u v
  θ' := extS P.θ' (Ctx.le_insert hu.root T) v u
  θ₃ := extS P.θ₃ (Ctx.le_insert hu.root T) u u
  hθ := ok_extS P.hθ _ hu (ref_insert_root Δ (.free v) T)
  hc := coh_extS P.hθ P.hc _ hu (ref_insert_root Δ (.free v) T)
  hθ' := ok_extS P.hθ' _ hv (ref_insert_root Γ (.free u) T)
  hc' := coh_extS P.hθ' P.hc' _ hv (ref_insert_root Γ (.free u) T)
  hθ₃ := ok_extS P.hθ₃ _ hu (ref_insert_root Γ (.free u) T)
  hc₃ := coh_extS P.hθ₃ P.hc₃ _ hu (ref_insert_root Γ (.free u) T)
  sim := sim_extS P.hθ P.hθ' P.hc' hu hv P.sim
  simId := simId_extS hu P.simId


/-- The child arrow and its pull-back are similar to the identity, which is what makes them a
    pair rather than only a cancelling translation. -/
theorem sim_arrow_pull (l : List VarType) :
    Subst.Sim (ctxOf l).boxIn (Subst.idS σ (ctxOf l).boxIn)
      ((arrowS σ (ctxOf (l.map VarType.bc)) id).comp (pullS σ l) (ok_pullS l) (coh_pullS l)) := by
  refine Subst.sim_of ?_
  intro v T _ hv
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  obtain ⟨-, r, hr⟩ := reach_ppath hu
  change SubE.Sim T (.ren (.step u .box)) ((pullS σ l).at (itemAt (imgRoot id u.rt) u))
  rw [show imgRoot id u.rt = .free r by rw [hr]; rfl,
    at_item_of_tupB _ _ hu ModalSys.T rfl (at_pull_tup hu r hr)]
  exact .ren_eta _ _

/-- ⭐The `□` view of a world language, as a pair — so it can itself be pushed under further
    views. -/
def pairBox (l : List VarType) : Pair σ (ctxOf l).boxIn (ctxOf (l.map VarType.bc)) where
  ι := arrowIdx id
  ι' := pullIdx l
  ι₃ := id
  θ := arrowS σ (ctxOf (l.map VarType.bc)) id
  θ' := pullS σ l
  θ₃ := Subst.idS σ (ctxOf l).boxIn
  hθ := ok_arrowS (childImg l)
  hc := coh_arrowS (childImg l)
  hθ' := ok_pullS l
  hc' := coh_pullS l
  hθ₃ := Subst.ok_idS
  hc₃ := Subst.coh_idS
  sim := sim_arrow_pull l
  simId := fun _ _ _ => .refl _

/-- Views stacked on a context. -/
def Ctx.boxInN : ℕ → Ctx → Ctx
  | 0, Γ => Γ
  | n + 1, Γ => Ctx.boxInN n Γ.boxIn

/-- The world language after `n` views. -/
def bcN : ℕ → List VarType → List VarType
  | 0, l => l
  | n + 1, l => bcN n (l.map VarType.bc)

/-- A pair pushed under `n` views. -/
def Pair.boxN : (n : ℕ) → {Γ' Δ' : Ctx} → Pair σ Γ' Δ' →
    Pair σ (Ctx.boxInN n Γ') (Ctx.boxInN n Δ')
  | 0, _, _, P => P
  | n + 1, _, _, P => Pair.boxN n P.box


/-- The identity pair. -/
def Pair.id (Γ : Ctx) : Pair σ Γ Γ where
  ι := _root_.id
  ι' := _root_.id
  ι₃ := _root_.id
  θ := Subst.idS σ Γ
  θ' := Subst.idS σ Γ
  θ₃ := Subst.idS σ Γ
  hθ := Subst.ok_idS
  hc := Subst.coh_idS
  hθ' := Subst.ok_idS
  hc' := Subst.coh_idS
  hθ₃ := Subst.ok_idS
  hc₃ := Subst.coh_idS
  sim := by
    intro v T hv
    rw [Subst.at_comp Subst.ok_idS _ Subst.ok_idS Subst.coh_idS hv, Subst.at_idS]
    change SubE.Sim T (SubE.ren v) ((Subst.idS σ Γ).at v)
    rw [Subst.at_idS]
    exact .refl _
  simId := fun _ _ _ => .refl _

instance presented_boxInN : ∀ (n : ℕ) {Γ : Ctx} [Γ.Presented], (Ctx.boxInN n Γ).Presented
  | 0, _, h => h
  | n + 1, Γ, _ => presented_boxInN n (Γ := Γ.boxIn)

/-- ⭐Any number of `□` views over a world language is flattened into one. -/
def flatBoxN : (n : ℕ) → (l : List VarType) →
    Flat σ (Ctx.boxInN n (ctxOf l)) (ctxOf (bcN n l))
  | 0, l => (Pair.id (ctxOf l)).toFlat (Ctx.Presented.noProjLast _)
  | n + 1, l =>
      (((pairBox l).boxN n).toFlat (Ctx.Presented.noProjLast _)).comp
        (flatBoxN n (l.map VarType.bc))

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- ⭐**Completeness for weak B in any context flattened into a world language.** -/
theorem completenessB_flat (hB : ModalSys.B = true) {Γ : Ctx} {l : List VarType}
    (F : Flat σ Γ (ctxOf l)) (hnp : Γ.NoProjLast) {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0}
    (hval : ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W}
      (env : M.Env Γ w), Γ.NoProjLast →
      (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ := by
  refine F.prov (completenessB hB ?_)
  intro M hM w e _ hΔ
  rw [F.sat]
  exact hval M hM _ hnp fun ψ hψ => (F.sat e ψ).mp (hΔ _ (List.mem_map_of_mem hψ))



/-! ## Pushing a pair under a witness view -/

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A substitution similar to the identity stays so under `◇_x`. -/
theorem sim_dia_of {Γ : Ctx} {θ : Subst σ Γ} {x : VarSymb} {X : VarType}
    (hx : Γ.ref x = some (.VTypeDia X)) (hw : (θ.at x).idxAlong [] = x)
    (h : Subst.Sim Γ θ (Subst.idS σ Γ)) :
    Subst.Sim (Γ.diaIn x) (θ.dia x x) (Subst.idS σ (Γ.diaIn x)) := by
  refine Subst.sim_of ?_
  intro v T _ hv
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with hux
      · subst hux
        rw [hx] at hv
        cases hv
        have hs := (h u _ hx).diaBody hw
        rw [Subst.at_idS] at hs
        change SubE.Sim X (if u = u then (θ.at u).diaBody u else SubE.hide) (.ren (.step u .dia))
        rw [if_pos rfl]
        exact hs
  | .step u .box =>
      obtain ⟨_, hu⟩ := Ctx.boxIn_box (Γ := Γ) hv
      have hs := ((h u _ hu).unbox).mono (Ctx.le_boxIn_diaIn Γ x)
      rw [Subst.at_idS] at hs
      change SubE.Sim T ((θ.at u).unbox.mono (Ctx.le_boxIn_diaIn Γ x)) (.ren (.step u .box))
      rw [← VarSymb.inner_box ModalSys.NoFour.keepOnly]
      exact hs
  | .step u .keep =>
      obtain ⟨hF, _⟩ := Ctx.boxIn_keep (Γ := Γ) hv
      exact absurd (ModalSys.NoFour.noFour.symm.trans hF) (by simp)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

section
omit [ModalSys.NoFour] [Countable σ.FuncSyms] [Countable σ.RelSyms]

variable (P : Pair σ Γ Δ) {x : VarSymb} {X : VarType}

/-- The index of a pair's witness entry. -/
theorem Pair.hw (hx : Γ.ref x = some (.VTypeDia X)) : (P.θ.at x).idxAlong [] = P.ι x :=
  P.hc x _ hx []

/-- A pair sends a witness to a witness. -/
theorem Pair.witness (hx : Γ.ref x = some (.VTypeDia X)) :
    ∃ Y, Δ.ref (P.ι x) = some (.VTypeDia Y) :=
  SubE.ref_witness (Subst.okRef_at P.hθ hx) (P.hw hx)

/-- A pair's composite index map fixes a reachable `◇`-address. -/
theorem Pair.idx_id (hx : Γ.ref x = some (.VTypeDia X)) : P.ι₃ x = x := by
  have hs := (P.simId x _ hx).idx
  rw [Subst.at_idS] at hs
  have e₃ : (P.θ₃.at x).idxAlong [] = P.ι₃ x := P.hc₃ x _ hx []
  rw [hs] at e₃
  exact e₃.symm

/-- The index maps of a pair invert each other at a reachable `◇`-address. -/
theorem Pair.idx_dia (hx : Γ.ref x = some (.VTypeDia X)) : P.ι' (P.ι x) = x :=
  (Subst.idx_comp P.hθ P.hc P.hθ' P.hc' P.hc₃ P.sim ⟨X, hx⟩).symm.trans (P.idx_id hx)

theorem Pair.hw' (hx : Γ.ref x = some (.VTypeDia X)) : (P.θ'.at (P.ι x)).idxAlong [] = x := by
  obtain ⟨Y, hY⟩ := P.witness hx
  have h : (P.θ'.at (P.ι x)).idxAlong [] = P.ι' (P.ι x) := P.hc' (P.ι x) _ hY []
  rw [h, P.idx_dia hx]

theorem Pair.hw₃ (hx : Γ.ref x = some (.VTypeDia X)) : (P.θ₃.at x).idxAlong [] = x := by
  have h : (P.θ₃.at x).idxAlong [] = P.ι₃ x := P.hc₃ x _ hx []
  rw [h, P.idx_id hx]

variable {P}

/-- ⭐A pair pushed under `◇_x`: the witness goes to its image. -/
def Pair.dia (P : Pair σ Γ Δ) {x : VarSymb} {X : VarType} (hx : Γ.ref x = some (.VTypeDia X)) :
    Pair σ (Γ.diaIn x) (Δ.diaIn (P.ι x)) where
  ι := P.ι
  ι' := P.ι'
  ι₃ := P.ι₃
  θ := P.θ.dia x (P.ι x)
  θ' := P.θ'.dia (P.ι x) x
  θ₃ := P.θ₃.dia x x
  hθ := Subst.ok_dia P.hθ ⟨X, hx⟩ (P.hw hx)
  hc := Subst.coh_dia P.hθ P.hc ⟨X, hx⟩
  hθ' := Subst.ok_dia P.hθ' (P.witness hx) (P.hw' hx)
  hc' := by
    have h := Subst.coh_dia P.hθ' P.hc' (P.witness hx)
    rwa [P.idx_dia hx] at h
  hθ₃ := Subst.ok_dia P.hθ₃ ⟨X, hx⟩ (P.hw₃ hx)
  hc₃ := by
    have h := Subst.coh_dia P.hθ₃ P.hc₃ ⟨X, hx⟩
    rwa [P.idx_id hx] at h
  sim := by
    obtain ⟨Y, hY⟩ := P.witness hx
    have key : ∀ (w : VarSymb) (_ : P.ι' (P.ι x) = w)
        (hθw : Subst.Ok (Δ.diaIn (P.ι x)) (P.θ'.dia (P.ι x) w))
        (hcw : Subst.Coh P.ι' (Δ.diaIn (P.ι x)) (P.θ'.dia (P.ι x) w)),
        Subst.Sim (Γ.diaIn x) (P.θ₃.dia x w)
          ((P.θ.dia x (P.ι x)).comp (P.θ'.dia (P.ι x) w) hθw hcw) := by
      intro w hw hθw hcw
      subst hw
      exact Subst.sim_dia_comp P.hθ P.hc P.hθ' P.hc' P.sim ⟨X, hx⟩ ⟨Y, hY⟩
        (P.hc' (P.ι x) _ hY []) (by rw [P.hw₃ hx, P.idx_dia hx])
    exact key x (P.idx_dia hx) _ _
  simId := sim_dia_of hx (P.hw₃ hx) P.simId
end

/-! ## Chains of pairs

A presentation is flattened one constructor at a time, and each step is a `Pair`.  Pairs cannot be
composed — `Subst.Coh` for a composite substitution has no generic index map, because `Ann.idxAt`
returns junk away from `◇`-nodes — so the steps are kept as a **chain** and composed only as
translations, where `Flat.comp` already works.  Boxing and root-extension distribute over a chain,
which is what the construction itself does: arrows stay atomic, facts get chained. -/

/-- ⭐A chain of pairs from `Γ` to `Δ`, each context presented. -/
inductive Chain (σ : Signature) : Ctx → Ctx → Type where
  | nil {Γ : Ctx} (hΓ : Γ.Presented) : Chain σ Γ Γ
  | cons {Γ Δ E : Ctx} (hΓ : Γ.Presented) (P : Pair σ Γ Δ) (C : Chain σ Δ E) : Chain σ Γ E

/-- Every context of a chain is presented; here, its source. -/
def Chain.srcPresented : {Γ Δ : Ctx} → Chain σ Γ Δ → Γ.Presented
  | _, _, .nil hΓ => hΓ
  | _, _, .cons hΓ _ _ => hΓ

/-- ⭐A chain is a translation: compose the links. -/
def Chain.toFlat : {Γ Δ : Ctx} → (C : Chain σ Γ Δ) → Flat σ Γ Δ
  | _, _, .nil hΓ =>
      letI := hΓ
      (Pair.id _).toFlat (Ctx.Presented.noProjLast _)
  | _, _, .cons hΓ P C =>
      letI := hΓ
      letI := C.srcPresented
      (P.toFlat (Ctx.Presented.noProjLast _)).comp C.toFlat

/-- ⭐A chain pushed under `□`: box every link. -/
def Chain.box : {Γ Δ : Ctx} → Chain σ Γ Δ → Chain σ Γ.boxIn Δ.boxIn
  | _, _, .nil hΓ =>
      letI := hΓ
      .nil inferInstance
  | _, _, .cons hΓ P C =>
      letI := hΓ
      .cons inferInstance P.box C.box


/-- ⭐A chain extended by a declared root: extend every link.  The endpoints' names are given; each
    intermediate context uses its own presentation's fresh name, so adjacent links agree. -/
def Chain.insertRoot (T : VarType) : {Γ Δ : Ctx} → Chain σ Γ Δ → (u v : ℕ) →
    Γ.RootFresh (.free u) → Δ.RootFresh (.free v) →
    Chain σ (Γ.insert (.free u) T) (Δ.insert (.free v) T)
  | _, _, .nil hΓ, _, _, hu, hv =>
      letI := hΓ
      .cons (hΓ.insertFree _ hu _) ((Pair.id _).insertRoot hu hv)
        (.nil (hΓ.insertFree _ hv _))
  | _, _, .cons hΓ P C, _, v, hu, hv =>
      letI := hΓ
      letI := C.srcPresented
      .cons (hΓ.insertFree _ hu _)
        (P.insertRoot hu (Ctx.Presented.fresh_bound (Ctx.Presented.bound _) le_rfl))
        (C.insertRoot T (Ctx.Presented.bound _) v
          (Ctx.Presented.fresh_bound (Ctx.Presented.bound _) le_rfl) hv)


/-- Append a pair at the far end of a chain. -/
def Chain.snoc : {Γ Δ E : Ctx} → Chain σ Γ Δ → Pair σ Δ E → E.Presented → Chain σ Γ E
  | _, _, _, .nil hΔ, P, hE => .cons hΔ P (.nil hE)
  | _, _, _, .cons hΓ Q C, P, hE => .cons hΓ Q (C.snoc P hE)

/-- Where a chain sends a witness. -/
def Chain.diaIdx : {Γ Δ : Ctx} → Chain σ Γ Δ → VarSymb → VarSymb
  | _, _, .nil _, x => x
  | _, _, .cons _ P C, x => C.diaIdx (P.ι x)

omit [ModalSys.NoFour] [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A chain sends a witness to a witness. -/
theorem Chain.witness : {Γ Δ : Ctx} → (C : Chain σ Γ Δ) → {x : VarSymb} → {X : VarType} →
    Γ.ref x = some (.VTypeDia X) → ∃ Y, Δ.ref (C.diaIdx x) = some (.VTypeDia Y)
  | _, _, .nil _, _, X, hx => ⟨X, hx⟩
  | _, _, .cons _ P C, _, _, hx => by
      obtain ⟨Y, hY⟩ := P.witness hx
      exact C.witness hY

/-- ⭐A chain pushed under `◇_x`: the witness travels along the links. -/
noncomputable def Chain.dia : {Γ Δ : Ctx} → (C : Chain σ Γ Δ) → {x : VarSymb} → {X : VarType} →
    Γ.ref x = some (.VTypeDia X) → Chain σ (Γ.diaIn x) (Δ.diaIn (C.diaIdx x))
  | _, _, .nil hΓ, _, _, _ =>
      letI := hΓ
      .nil inferInstance
  | _, _, .cons hΓ P C, _, _, hx =>
      letI := hΓ
      .cons inferInstance (P.dia hx) (C.dia (P.witness hx).choose_spec)

/-! ## Views over a world language -/

/-- ⭐A `□` view over a world language is flattened by the arrow into a new child. -/
def flatBox (l : List VarType) : Flat σ (ctxOf l).boxIn (ctxOf (l.map VarType.bc)) :=
  Flat.ofPair (Ctx.noProjLast_boxIn _) _ (pullS σ l) (ok_arrowS (childImg l))
    (coh_arrowS (childImg l)) (ok_pullS l) (coh_pullS l) (subst_pull_arrow l)

/-- ⭐A `◇_x` view over a world language is flattened by the witness arrow. -/
noncomputable def flatDia (l : List VarType) {x : VarSymb} {X : VarType}
    (hx : (ctxOf l).ref x = some (.VTypeDia X)) :
    Flat σ ((ctxOf l).diaIn x) (ctxOf (X :: l.map VarType.bc)) :=
  Flat.ofPair (Ctx.noProjLast_diaIn _ x) _ (pullXS σ l x) (ok_arrowXS (childXImg l X) hx
    (childX_cx l X)) (coh_arrowXS (childXImg l X) hx (childX_cx l X)) (ok_pullXS l hx)
    (coh_pullXS l hx) (subst_pullX_arrowX l hx)


omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- The witness arrow and its pull-back are similar to the identity. -/
theorem sim_arrowX_pull (l : List VarType) {x : VarSymb} {X : VarType}
    (hx : (ctxOf l).ref x = some (.VTypeDia X)) :
    Subst.Sim ((ctxOf l).diaIn x) (Subst.idS σ ((ctxOf l).diaIn x))
      ((arrowXS σ (ctxOf (X :: l.map VarType.bc)) id x l.length).comp (pullXS σ l x)
        (ok_pullXS l hx) (coh_pullXS l hx)) := by
  refine Subst.sim_of ?_
  intro v T _ hv
  rcases diaIn_item hv with ⟨u, rfl, hu⟩ | ⟨rfl, _⟩
  · obtain ⟨-, r, hr⟩ := reach_ppath hu
    change SubE.Sim T (.ren (.step u .box)) ((pullXS σ l x).at (itemAt (imgRoot id u.rt) u))
    rw [show imgRoot id u.rt = u.rt by rw [hr]; rfl,
      at_item_of_tupB_mono _ _ _ hu ModalSys.T rfl (at_pullX_tup x hu), Term.mono_eta]
    exact .ren_eta _ _
  · change SubE.Sim T (.ren (.step x .dia))
      ((if x = x then SubE.ren (.root (.free l.length)) else .hide).comp _ _ _)
    rw [if_pos rfl]
    change SubE.Sim T _ (pullXS σ l x (.root (.free l.length)))
    rw [pullX_cx]
    exact .refl _

/-- ⭐The `◇_x` view of a world language, as a pair. -/
noncomputable def pairDia (l : List VarType) {x : VarSymb} {X : VarType}
    (hx : (ctxOf l).ref x = some (.VTypeDia X)) :
    Pair σ ((ctxOf l).diaIn x) (ctxOf (X :: l.map VarType.bc)) where
  ι := arrowXIdx id x l.length
  ι' := pullXIdx l x
  ι₃ := id
  θ := arrowXS σ (ctxOf (X :: l.map VarType.bc)) id x l.length
  θ' := pullXS σ l x
  θ₃ := Subst.idS σ ((ctxOf l).diaIn x)
  hθ := ok_arrowXS (childXImg l X) hx (childX_cx l X)
  hc := coh_arrowXS (childXImg l X) hx (childX_cx l X)
  hθ' := ok_pullXS l hx
  hc' := coh_pullXS l hx
  hθ₃ := Subst.ok_idS
  hc₃ := Subst.coh_idS
  sim := sim_arrowX_pull l hx
  simId := fun _ _ _ => .refl _

/-- ⭐Completeness in the `□` view of a world language. -/
theorem completenessB_boxIn (hB : ModalSys.B = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l).boxIn 0)} {φ : WFF σ (ctxOf l).boxIn 0}
    (hval : ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W}
      (env : M.Env (ctxOf l).boxIn w),
      (ctxOf l).boxIn.NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ :=
  completenessB_flat hB (flatBox l) (Ctx.noProjLast_boxIn _) hval

/-- ⭐Completeness in the `◇_x` view of a world language. -/
theorem completenessB_diaIn (hB : ModalSys.B = true) {l : List VarType} {x : VarSymb}
    {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X))
    {Δ : List (WFF σ ((ctxOf l).diaIn x) 0)} {φ : WFF σ ((ctxOf l).diaIn x) 0}
    (hval : ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W}
      (env : M.Env ((ctxOf l).diaIn x) w),
      ((ctxOf l).diaIn x).NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ :=
  completenessB_flat hB (flatDia l hx) (Ctx.noProjLast_diaIn _ x) hval


/-- ⭐Completeness in any number of stacked `□` views over a world language. -/
theorem completenessB_boxInN (hB : ModalSys.B = true) (n : ℕ) (l : List VarType)
    {Δ : List (WFF σ (Ctx.boxInN n (ctxOf l)) 0)} {φ : WFF σ (Ctx.boxInN n (ctxOf l)) 0}
    (hval : ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W}
      (env : M.Env (Ctx.boxInN n (ctxOf l)) w),
      (Ctx.boxInN n (ctxOf l)).NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ :=
  completenessB_flat hB (flatBoxN n l) (Ctx.Presented.noProjLast _) hval


/-! ## Every presentation flattens

`CtxExpr.insertFree` permits shadowing, which a renaming cannot undo, so the flattening asks each
declaration to be fresh in its own prefix — `CtxExpr.Fresh`, the one non-shadowing condition, which
lives with the presentations in `QML_v12m_Presented` and is carried by `Ctx.Presented` itself.  It
also takes the views apart, so it asks in addition that each be at a declared witness
(`CtxExpr.Views`); the two together are `CtxExpr.Wf`. -/

/-- ⭐**Every well-formed presentation flattens into a world language**, one constructor at a time:
    a declared root by `Chain.insertRoot`, a `□` view by `Chain.box` then the child arrow, a `◇_x`
    view by `Chain.dia` then the witness arrow. -/
noncomputable def _root_.V12M.CtxExpr.chain : (e : CtxExpr) → e.Fresh → e.Views →
    Σ l : List VarType, Chain σ e.denote (ctxOf l)
  | .empty, _, _ => ⟨[], .nil ⟨.empty, trivial, rfl⟩⟩
  | .insertFree e u T, h, hv =>
      ⟨T :: (e.chain h.1 hv).1,
        (e.chain h.1 hv).2.insertRoot T u (e.chain h.1 hv).1.length h.2
          (ctxOf_fresh le_rfl)⟩
  | .boxIn e, h, hv =>
      ⟨(e.chain h hv).1.map VarType.bc, ((e.chain h hv).2.box).snoc (pairBox _) inferInstance⟩
  | .diaIn e _, h, hv =>
      ⟨((e.chain h hv.1).2.witness hv.2.choose_spec).choose :: (e.chain h hv.1).1.map VarType.bc,
        ((e.chain h hv.1).2.dia hv.2.choose_spec).snoc
          (pairDia _ ((e.chain h hv.1).2.witness hv.2.choose_spec).choose_spec) inferInstance⟩

/-- ⭐**Completeness for weak B in every presented context** whose views are at declared
    witnesses. -/
theorem completenessB_presented (hB : ModalSys.B = true) (e : CtxExpr) (he : e.Wf)
    {Δ : List (WFF σ e.denote 0)} {φ : WFF σ e.denote 0}
    (hval : ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W}
      (env : M.Env e.denote w),
      e.denote.NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ :=
  letI : e.denote.Presented := ⟨e, he.1, rfl⟩
  completenessB_flat hB (e.chain he.1 he.2).2.toFlat (Ctx.Presented.noProjLast _) hval

end BArrow

end V12M
