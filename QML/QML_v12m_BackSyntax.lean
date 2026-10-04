import QML.QML_v12m_SubstEta

/-!
# QML v12m — strong B: the syntax its rules are stated in

Roadmap milestone 2, step 4 (`docs/v12-modal-extensions.md` §11.2, §11.14).

* **Hole formulas and terms**, closed apart from one hole (§11.2): `WFF.holeRead`, `Term.holeRead`
  read them in a context with a term in the hole.  A round trip carries no addresses, so the two
  ends of a `Back` meet only through the hole.
* ⭐`OutLeg`: the out leg of a round trip — every arrow (`nec`, row 1) or a witness's extent
  (`pos y`, row 2) — with its view, its `◇` and `□`, and the `Back` atom of a carrier given by its
  body (`OutLeg.back`).  The rules are stated once over it; substitution sends a leg to a leg
  (`OutLeg.subst`) and acts on its pieces definitionally (`OutLeg.subst_dia`, `subst_box`,
  `subst_back`).
-/

namespace V12M

variable [ModalSys]

namespace Subst

variable {σ : Signature} {Δ : Ctx}

/-! ## Changing one root's entry -/

/-- `r ↦ e`, every other address as in `θ`. -/
def set (θ : Subst σ Δ) (r : Root) (e : SubE σ Δ) : Subst σ Δ :=
  fun v => if v = .root r then e else θ v

def setIdx (ι : VarSymb → VarSymb) (r : Root) (e : SubE σ Δ) : VarSymb → VarSymb :=
  fun i => if i.rt = r then e.idxAlong i.path else ι i

theorem set_root (θ : Subst σ Δ) (r : Root) (e : SubE σ Δ) : θ.set r e (.root r) = e :=
  if_pos rfl

theorem set_ne (θ : Subst σ Δ) {r : Root} (e : SubE σ Δ) {v : VarSymb} (h : v ≠ .root r) :
    θ.set r e v = θ v :=
  if_neg h

theorem ok_set {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) {r : Root} {T : VarType}
    {e : SubE σ Δ} (he : e.OkRef T) : Ok (Γ.insert r T) (θ.set r e) := by
  intro v U hlp hv
  by_cases hvr : v = .root r
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    rw [set_root]
    exact he
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    rw [set_ne _ _ hvr]
    exact hθ v U hlp hv'

theorem coh_set {ι : VarSymb → VarSymb} {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ)
    (hc : Coh ι Γ θ) {r : Root} {T : VarType} {e : SubE σ Δ} (hr : Γ.RootFresh r)
    (he : e.OkRef T) : Coh (setIdx ι r e) (Γ.insert r T) (θ.set r e) := by
  refine coh_of (ok_set hθ he) ?_
  intro v U hlp hv p
  by_cases hvr : v = .root r
  · subst hvr
    rw [set_root]
    change e.idxAlong p = if ((VarSymb.root r).ext p).rt = r then
      e.idxAlong ((VarSymb.root r).ext p).path else _
    simp only [VarSymb.ext_rt, VarSymb.ext_path, VarSymb.rt, VarSymb.path, List.nil_append,
      if_true]
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    have hrt : v.rt ≠ r := fun he' => by
      rw [hr v he'] at hv'
      cases hv'
    rw [set_ne _ _ hvr, ← at_nonproj θ hlp, hc v U ((Ctx.ref_nonproj Γ hlp).trans hv') p]
    change ι (v.ext p) = if (v.ext p).rt = r then _ else ι (v.ext p)
    rw [VarSymb.ext_rt, if_neg hrt]

end Subst

/-- A **hole formula** — closed apart from its hole — read in `Γ` with `t` in the hole. -/
def WFF.holeRead {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) : WFF σ Γ 0 :=
  WFF.instantiate Ctx.NoSlots.slots t (WFF.mono ((Ctx.empty_le Γ).insert (.bnd 0) A) ψ)

/-- A **hole term** — closed apart from its hole — read in `Γ` with `t` in the hole: what `Back`'s
    β-rule maps a carrier and its value by. -/
def Term.holeRead {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) {B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    Term σ Γ B (b.mapIdx (Subst.singleIdx (.bnd 0) (.tm t))) :=
  Term.subst (Subst.singleIdx (.bnd 0) (.tm t)) (Subst.single (.bnd 0) (.tm t))
    (Subst.ok_single (Ctx.Le.refl Γ) rfl)
    (Subst.coh_single ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) (Ctx.Le.refl Γ) rfl)
    (Term.mono ((Ctx.empty_le Γ).insert (.bnd 0) A) s)

/-! ## The returning possibility's syntax (§11.14)

`WFF.ret hS hA t Φ` binds one necessary object `d : □A` of the far world, at the slot of its body
`Φ`.  Several items are packed into one by pairing; the operations below move between the packed
and unpacked forms, by substitutions of the body's slots. -/

omit [ModalSys] in
theorem Ctx.slotsFrom_empty : Ctx.empty.SlotsFrom 0 := fun _ _ _ _ => rfl

/-- A hole formula read at **any** binder depth, with `t` in the hole: a substitution from the
    hole's own context, so no weakening and no slot bookkeeping.  Inside a returning
    possibility's body, which has a slot, this replaces `WFF.holeRead`. -/
def WFF.holeAt {σ : Signature} {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) : WFF σ Γ d :=
  WFF.subst (Subst.singleIdx (.bnd 0) (.tm t)) (Subst.single (.bnd 0) (.tm t))
    (Subst.ok_single (Ctx.empty_le Γ) rfl)
    (Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le Γ) rfl)
    (Ctx.slotsFrom_empty.insert A) hs ψ

/-- A hole term read with `t` in the hole, at any depth. -/
def Term.holeAt {σ : Signature} {Γ : Ctx} {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    {B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    Term σ Γ B (b.mapIdx (Subst.singleIdx (.bnd 0) (.tm t))) :=
  Term.subst (Subst.singleIdx (.bnd 0) (.tm t)) (Subst.single (.bnd 0) (.tm t))
    (Subst.ok_single (Ctx.empty_le Γ) rfl)
    (Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le Γ) rfl) s

/-- The first component of a necessary pair, as a necessary object: `□(fst v.box)`. -/
def Term.boxFst {σ : Signature} {Γ : Ctx} {v : VarSymb} {A B : VarType}
    (h : Γ.ref v = some (.VTypeBox (.VTypeProd A B))) :
    Term σ Γ (.VTypeBox A) (.box (Ann.eta (.step v.inner .fst) A)) :=
  .boxtm (Term.eta (.step v.inner .fst) A (Ctx.ref_fst_of (Ctx.ref_inner h)))

/-- The second component of a necessary pair, as a necessary object. -/
def Term.boxSnd {σ : Signature} {Γ : Ctx} {v : VarSymb} {A B : VarType}
    (h : Γ.ref v = some (.VTypeBox (.VTypeProd A B))) :
    Term σ Γ (.VTypeBox B) (.box (Ann.eta (.step v.inner .snd) B)) :=
  .boxtm (Term.eta (.step v.inner .snd) B (Ctx.ref_snd_of (Ctx.ref_inner h)))

section Body

variable {σ : Signature} {V : Ctx} [V.NoSlots]

omit [ModalSys] in
theorem body_le (T : VarType) : V.Le (V.insert (.bnd 0) T) :=
  Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root T

/-- ⭐**Replacing the bound item** by a term over a new one: a body about `e : □B` becomes a body
    about `d : □A`, with `e := X(d)`.  What β moves a returning possibility by, and how a carrier
    joins its item (`Proof.ret_beta`, `Proof.ret_back`). -/
def WFF.bodyRepl {A B : VarType} {b : Ann (.VTypeBox B)}
    (X : Term σ (V.insert (.bnd 0) (.VTypeBox A)) (.VTypeBox B) b)
    (Φ : WFF σ (V.insert (.bnd 0) (.VTypeBox B)) 1) : WFF σ (V.insert (.bnd 0) (.VTypeBox A)) 1 :=
  WFF.subst (Subst.setIdx id (.bnd 0) (.tm X)) ((Subst.idS σ _).set (.bnd 0) (.tm X))
    (Subst.ok_set (Subst.ok_idS_le (body_le _)) rfl)
    (Subst.coh_set (Subst.ok_idS_le (body_le _)) (Subst.coh_idS_le (body_le _))
      ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) rfl)
    ((Ctx.NoSlots.slots (Γ := V)).insert _) ((Ctx.NoSlots.slots (Γ := V)).insert _) Φ

/-- ⭐**Splitting a paired item**: a body about two items `d : □A`, `b : □B` becomes a body about
    one `e : □C`, with `d := X₀(e)`, `b := X₁(e)` — the components `Term.boxFst`, `Term.boxSnd` of
    `e : □(A×B)` in `Proof.ret_ext`.  One more item of the same child, packed with the others. -/
def WFF.bodySplit {A B C : VarType} {b₀ : Ann (.VTypeBox A)} {b₁ : Ann (.VTypeBox B)}
    (X₀ : Term σ (V.insert (.bnd 0) (.VTypeBox C)) (.VTypeBox A) b₀)
    (X₁ : Term σ (V.insert (.bnd 0) (.VTypeBox C)) (.VTypeBox B) b₁)
    (Φ : WFF σ ((V.insert (.bnd 0) (.VTypeBox A)).insert (.bnd 1) (.VTypeBox B)) 2) :
    WFF σ (V.insert (.bnd 0) (.VTypeBox C)) 1 :=
  have h₀ := Subst.ok_set (r := .bnd 0) (T := .VTypeBox A) (e := .tm X₀)
    (Subst.ok_idS_le (σ := σ) (body_le (V := V) (.VTypeBox C))) rfl
  have c₀ := Subst.coh_set (r := .bnd 0) (T := .VTypeBox A) (e := .tm X₀)
    (Subst.ok_idS_le (σ := σ) (body_le (V := V) (.VTypeBox C)))
    (Subst.coh_idS_le (body_le (V := V) (.VTypeBox C)))
    ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) rfl
  WFF.subst (Subst.setIdx (Subst.setIdx id (.bnd 0) (.tm X₀)) (.bnd 1) (.tm X₁))
    (((Subst.idS σ _).set (.bnd 0) (.tm X₀)).set (.bnd 1) (.tm X₁))
    (Subst.ok_set (r := .bnd 1) (T := .VTypeBox B) (e := .tm X₁) h₀ rfl)
    (Subst.coh_set (r := .bnd 1) (T := .VTypeBox B) (e := .tm X₁) h₀ c₀
      (((Ctx.NoSlots.slots (Γ := V)).insert _).rootFresh (le_refl 1)) rfl)
    (((Ctx.NoSlots.slots (Γ := V)).insert _).insert _) ((Ctx.NoSlots.slots (Γ := V)).insert _) Φ

end Body

/-- ⭐The **out leg** of a round trip (§11.1): every arrow out of the world (`nec`, row 1, carrier
    `□□A`) or the extent of a witness `y` (`pos`, row 2, carrier `◇□A`). -/
inductive OutLeg (Γ : Ctx) where
  | nec
  | pos (y : VarSymb) (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y))

namespace OutLeg

variable {σ : Signature} {Γ : Ctx}

/-- The leg of the `Back` atom. -/
def leg : OutLeg Γ → BLeg
  | .nec => .nec
  | .pos _ _ => .pos

/-- The view at the far end of the out leg. -/
def view : OutLeg Γ → Ctx
  | .nec => Γ.boxIn
  | .pos y _ => Γ.diaIn y

instance instNoSlots [Γ.NoSlots] {O : OutLeg Γ} : O.view.NoSlots := by
  cases O <;> (dsimp only [view]; infer_instance)

theorem slotsFrom {d : ℕ} (h : Γ.SlotsFrom d) : (O : OutLeg Γ) → O.view.SlotsFrom d
  | .nec => h.boxIn
  | .pos y _ => h.diaIn y

/-- Some arrow of the leg: `◇` or `◇_y`. -/
def dia {d : ℕ} : (O : OutLeg Γ) → WFF σ O.view d → WFF σ Γ d
  | .nec, φ => (WFF.box φ.neg).neg
  | .pos y hy, φ => WFF.dia y hy φ

/-- Every arrow of the leg: `□` or `□_y`. -/
def box {d : ℕ} : (O : OutLeg Γ) → WFF σ O.view d → WFF σ Γ d
  | .nec, φ => WFF.box φ
  | .pos y hy, φ => WFF.boxx y hy φ

/-- ⭐The `Back` atom of the carrier with body `bd` — `boxtm (boxtm bd)` or `diatm y (boxtm bd)`:
    every term of type `□□A` or `◇□A` has this shape, so the rules are stated at the body and
    survive substitution (§10.11). -/
def back {d : ℕ} (hS : ModalSys.BStrong = true) : (O : OutLeg Γ) → {A : VarType} →
    A.diaFree = true → {a₀ : Ann A} → Term σ O.view.boxIn A a₀ → {a : Ann A} → Term σ Γ A a →
    WFF σ Γ d
  | .nec, _, hA, _, bd, _, t => WFF.back hS .nec hA (Term.boxtm (Term.boxtm bd)) t
  | .pos y hy, _, hA, _, bd, _, t => WFF.back hS .pos hA (Term.diatm y hy (Term.boxtm bd)) t

/-- The atom depends on its terms only as dependent pairs. -/
theorem back_congr {d : ℕ} (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    (hA : A.diaFree = true) {a₁ a₂ : Ann A} {bd₁ : Term σ O.view.boxIn A a₁}
    {bd₂ : Term σ O.view.boxIn A a₂}
    (hbd : (⟨a₁, bd₁⟩ : Σ b, Term σ O.view.boxIn A b) = ⟨a₂, bd₂⟩) {c₁ c₂ : Ann A}
    {t₁ : Term σ Γ A c₁} {t₂ : Term σ Γ A c₂} (ht : (⟨c₁, t₁⟩ : Σ b, Term σ Γ A b) = ⟨c₂, t₂⟩) :
    (O.back hS hA bd₁ t₁ : WFF σ Γ d) = O.back hS hA bd₂ t₂ := by
  cases hbd
  cases ht
  rfl

/-- The `□` view lies inside the leg's view. -/
theorem le_view : (O : OutLeg Γ) → Γ.boxIn.Le O.view
  | .nec => Ctx.Le.refl _
  | .pos y _ => Ctx.le_boxIn_diaIn Γ y

/-- A returning possibility's body read at the far end of the leg, with the carrier's image `c` in
    its slot: what the bridging rule asks to be possible (`Proof.ret_bridge`). -/
def bodyRead [Γ.NoSlots] (O : OutLeg Γ) {A : VarType} {b : Ann (.VTypeBox A)}
    (c : Term σ O.view (.VTypeBox A) b) (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1) :
    WFF σ O.view 0 :=
  WFF.instantiate Ctx.NoSlots.slots c (WFF.mono (O.le_view.insert (.bnd 0) _) Φ)

/-! ### Substitution -/

section Subst

variable {ι : VarSymb → VarSymb} {Δ : Ctx} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
  (hc : Subst.Coh ι Γ θ)

/-- The leg a substitution sends a leg to: the witness goes where `ι` sends it. -/
def subst : OutLeg Γ → OutLeg Δ
  | .nec => .nec
  | .pos y hy =>
      have hw : (θ.at y).idxAlong [] = ι y := hy.elim fun _ hY => hc y _ hY []
      .pos (ι y) (hy.elim fun _ hY => SubE.ref_witness (Subst.okRef_at hθ hY) hw)

/-- The substitution on the leg's view. -/
def viewSubst : (O : OutLeg Γ) → Subst σ (O.subst θ hθ hc).view
  | .nec => θ.box
  | .pos y _ => θ.dia y (ι y)

theorem viewOk : (O : OutLeg Γ) → Subst.Ok O.view (O.viewSubst θ hθ hc)
  | .nec => Subst.ok_box hθ
  | .pos y hy => Subst.ok_dia hθ hy (hy.elim fun _ hY => hc y _ hY [])

theorem viewCoh : (O : OutLeg Γ) → Subst.Coh ι O.view (O.viewSubst θ hθ hc)
  | .nec => Subst.coh_box hθ hc
  | .pos _ hy => Subst.coh_dia hθ hc hy

theorem subst_dia {d d' : ℕ} (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d') :
    (O : OutLeg Γ) → (φ : WFF σ O.view d) →
    WFF.subst ι θ hθ hc hΓ hΔ (O.dia φ) =
      (O.subst θ hθ hc).dia (WFF.subst ι (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc)
        (O.viewCoh θ hθ hc) (slotsFrom hΓ O) (slotsFrom hΔ _) φ)
  | .nec, _ => rfl
  | .pos _ _, _ => rfl

theorem subst_box {d d' : ℕ} (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d') :
    (O : OutLeg Γ) → (φ : WFF σ O.view d) →
    WFF.subst ι θ hθ hc hΓ hΔ (O.box φ) =
      (O.subst θ hθ hc).box (WFF.subst ι (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc)
        (O.viewCoh θ hθ hc) (slotsFrom hΓ O) (slotsFrom hΔ _) φ)
  | .nec, _ => rfl
  | .pos _ _, _ => rfl

theorem subst_back {d d' : ℕ} (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d')
    (hS : ModalSys.BStrong = true) :
    (O : OutLeg Γ) → {A : VarType} → (hA : A.diaFree = true) → {a₀ : Ann A} →
    (bd : Term σ O.view.boxIn A a₀) → {a : Ann A} → (t : Term σ Γ A a) →
    WFF.subst ι θ hθ hc hΓ hΔ (O.back hS hA bd t : WFF σ Γ d) =
      ((O.subst θ hθ hc).back hS hA
        (Term.subst ι (O.viewSubst θ hθ hc).box (Subst.ok_box (O.viewOk θ hθ hc))
          (Subst.coh_box (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)) bd)
        (Term.subst ι θ hθ hc t) : WFF σ Δ d')
  | .nec, _, _, _, _, _, _ => rfl
  | .pos _ _, _, _, _, _, _, _ => rfl

end Subst

end OutLeg

end V12M
