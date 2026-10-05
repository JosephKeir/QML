import QML.QML_v12m_SemHere

/-!
# QML v12m — strong B: the semantics of `Back` and the returning possibility

Roadmap milestone 2, step 3 (`docs/v12-modal-extensions.md` §11).  What the rules of step 4 need,
proved at the level of values, once for both rows:

* ⭐`Model.RoundTrip`: `Back`'s truth condition with the out leg a parameter.  A `□□`-carrier's
  body (`backs_nec_boxtm`) and a `◇□`-carrier's (`backs_pos_diatm`) both unfold to it.
* **Hole formulas**, closed apart from the hole (`WFF.holeRead`, `Model.holeSat`): what a round
  trip carries home (§11.2).  `IndInvariant` moves them across `Ind` (`holeSat_ind`).
* At **every** content type (§11.15): β and pairing return values up to `Ind` because a model
  proper's `Ind` is a congruence (`IndInvariant.map`, `IndInvariant.pair`), and the own arrow
  returns a value indistinguishable from the carrier read here twice.  (`Model.eq_of_ind`: at a
  `◇`-free type, `Ind` to a named object is equality.)
* The rules' semantics: `RoundTrip.ne`, `.elim`, `.intro`, `.of_def` (weak B's arrows home),
  `.map` (β), `.pair` (unique ways home), `.own` (T); for the returning possibility `ret_exists`
  (weak B), `ret_counit` and the counit with a carrier (`sat_ret_counitC`).
* ⭐`Model.sat_back_ex`: surjectivity — `∃c:□□A. Back c t` wherever there is a way out, the law
  `Model.backRet_exists` read at a fresh carrier.
-/

namespace V12M

variable [ModalSys]

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

/-! ## Round trips over any out leg -/

/-- ⭐A **round trip** over an out leg indexed by `ι`: each index is an arrow out of `w` (`acc`),
    and `val i b` is the carrier's value at the end of a further arrow `b`.  It comes back as `o`
    when the leg is nonempty and from each of its arrows some way home returns a value
    indistinguishable from `o` — `Model.Backs` with the leg made a parameter. -/
def RoundTrip {A : VarType} {w : M.frame.W} {ι : Type*} (acc : ι → M.frame.Acc w)
    (val : ∀ i, ∀ b : M.frame.Acc (acc i).1, M.frame.Dom A b.1) (o : M.frame.Dom A w) : Prop :=
  Nonempty ι ∧ ∀ i, ∃ r : M.frame.R (acc i).1 w, M.Ind (val i ⟨w, ⟨r⟩⟩) o

/-- ⭐Row 1: a `□□`-carrier comes back through its body, read two `□` views in. -/
theorem backs_nec_boxtm {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {A : VarType} {a₀ : Ann A}
    (bd : Term σ Γ.boxIn.boxIn A a₀) (o : M.frame.Dom A w) :
    M.Backs .nec (A := A) (interp env (Term.boxtm (Term.boxtm bd))) o ↔
      RoundTrip (M := M) (w := w) (fun a : M.frame.Acc w => a)
        (fun a b => interp ((env.boxPush a).boxPush b) bd) o := by
  refine and_congr Iff.rfl (forall_congr' fun a => exists_congr fun r => ?_)
  change M.Ind (M.necEval (M.necEval (interp env (Term.boxtm (Term.boxtm bd))) a) ⟨w, ⟨r⟩⟩) o ↔ _
  rw [box_beta env (Term.boxtm bd) a, box_beta (env.boxPush a) bd]

/-- ⭐Row 2: a `◇□`-carrier comes back through its body, read in its witness's view and one `□`
    view further in; the out leg is the witness's extent. -/
theorem backs_pos_diatm {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {y : VarSymb}
    (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)) {Y : VarType} (h : Γ.ref y = some (.VTypeDia Y))
    {A : VarType} {a₀ : Ann A} (bd : Term σ (Γ.diaIn y).boxIn A a₀) (o : M.frame.Dom A w) :
    M.Backs .pos (A := A) (interp env (Term.diatm y hy (Term.boxtm bd))) o ↔
      RoundTrip (M := M) (w := w) (fun a : (M.posEval (env.ref y h)).1 => a.1)
        (fun a b => interp ((env.diaPush y h a).boxPush b) bd) o := by
  change Nonempty (M.posEval (interp env (Term.diatm y hy (Term.boxtm bd)))).1 ∧
      (∀ a : (M.posEval (interp env (Term.diatm y hy (Term.boxtm bd)))).1,
        ∃ r : M.frame.R a.1.1 w, M.Ind (M.necEval
          ((M.posEval (interp env (Term.diatm y hy (Term.boxtm bd)))).2 a) ⟨w, ⟨r⟩⟩) o) ↔ _
  rw [dia_beta env hy h (Term.boxtm bd)]
  refine and_congr Iff.rfl (forall_congr' fun a => exists_congr fun r => ?_)
  change M.Ind (M.necEval (interp (env.diaPush y h a) (Term.boxtm bd)) ⟨w, ⟨r⟩⟩) o ↔ _
  rw [box_beta (env.diaPush y h a) bd]

/-! ## Hole formulas -/

/-- A hole formula is true of `o`. -/
def holeSat {A : VarType} (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) {v : M.frame.W}
    (o : M.frame.Dom A v) : Prop :=
  M.sat ((Env.empty v).extend (.bnd 0) o) ψ

/-- A hole formula read in a context says the same of the value in its hole. -/
theorem sat_holeRead {Γ : Ctx} [Γ.NoSlots] (hnp : Γ.NoProjLast) {w : M.frame.W}
    (env : M.Env Γ w) {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) :
    M.sat env (WFF.holeRead t ψ) ↔ M.holeSat ψ (interp env t) :=
  (sat_instantiate env hnp Ctx.NoSlots.slots t _).trans
    (sat_mono (Env.extend_agree (h := Ctx.empty_le Γ) (env := Env.empty w) (env' := env)
      (fun _ _ h => nomatch h) (.bnd 0) (interp env t)) ψ)

/-- In a model proper, indistinguishable objects satisfy the same hole formulas. -/
theorem holeSat_ind (hM : M.IndInvariant) {A : VarType}
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) {w : M.frame.W} {o o' : M.frame.Dom A w}
    (h : M.Ind o o') : M.holeSat ψ o ↔ M.holeSat ψ o' :=
  hM.inv (Ctx.Presented.tame _) (fun _ _ h => by simp [Ctx.empty] at h) (Env.empty w) ψ o o' h

/-- ⭐**At a `◇`-free type, `Ind` to a named object is equality**, in a model proper: the slot
    formula `z = t` holds of `t`'s value, so of everything indistinguishable from it.  This is what
    the `◇`-freeness of `Back`'s contents buys (§11.11 (c)). -/
theorem eq_of_ind (hM : M.IndInvariant) {Γ : Ctx} [Γ.NoSlots] (hfin : Γ.Tame)
    (hnp : Γ.NoProjLast) {w : M.frame.W} (env : M.Env Γ w) {A : VarType} (hA : A.diaFree = true)
    {a : Ann A} (t : Term σ Γ A a) {x : M.frame.Dom A w} (h : M.Ind x (interp env t)) :
    x = interp env t := by
  obtain rfl := Ann.eq_of_diaFree hA a (Ann.eta (.root (.bnd 0)) A)
  have hr : Γ.RootFresh (.bnd 0) := (Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)
  let φ : WFF σ (Γ.insert (.bnd 0) A) 1 :=
    eqRec A (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root Γ (.bnd 0) A))
      (Term.mono (Ctx.le_insert hr.root A) t)
  have key : ∀ o : M.frame.Dom A w, M.sat (env.extend (.bnd 0) o) φ ↔ o = interp env t := by
    intro o
    have hag : Env.Agree (Ctx.le_insert hr.root A) env (env.extend (.bnd 0) o) := by
      intro v U hv
      have hne : v ≠ .root (.bnd 0) := fun hvr => by rw [hvr, hr.root] at hv; cases hv
      simp only [Env.extend, dif_neg hne]
    rw [sat_eqRec, interp_eta, interp_mono hag]
    exact iff_of_eq (congrArg (· = interp env t)
      (Env.extend_root env (.bnd 0) o (Ctx.ref_insert_root Γ (.bnd 0) A)))
  exact (key x).mp ((hM.inv hfin hnp env φ x _ h).mpr ((key _).mpr rfl))

/-! ## The rules, at the level of values -/

namespace RoundTrip

variable {A : VarType} {w : M.frame.W} {ι : Type*} {acc : ι → M.frame.Acc w}
  {val : ∀ i, ∀ b : M.frame.Acc (acc i).1, M.frame.Dom A b.1} {o : M.frame.Dom A w}

/-- The out leg is nonempty (`back_ne`). -/
theorem ne (h : RoundTrip acc val o) : Nonempty ι := h.1

/-- ⭐**Counit** (`back_counit`): a hole formula true at the end of every way on from some arrow
    of the out leg is true of the round trip's value — along that arrow's way home. -/
theorem counit (hM : M.IndInvariant) (h : RoundTrip acc val o)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) (hψ : ∃ i, ∀ b, M.holeSat ψ (val i b)) :
    M.holeSat ψ o := by
  obtain ⟨i, hi⟩ := hψ
  obtain ⟨r, hr⟩ := h.2 i
  exact (holeSat_ind hM ψ hr).mp (hi _)

/-- ⭐**Unit** (`back_unit`): what is true of the value is, from every arrow of the out
    leg, true at the end of some way on — the way home. -/
theorem unit (hM : M.IndInvariant) (h : RoundTrip acc val o)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) (hψ : M.holeSat ψ o) :
    ∀ i, ∃ b, M.holeSat ψ (val i b) := fun i => by
  obtain ⟨r, hr⟩ := h.2 i
  exact ⟨_, (holeSat_ind hM ψ hr).mpr hψ⟩

/-- ⭐**Definition** (`back_def`, §11.5 (3)): under weak B every arrow of the out leg has a way
    home; if a hole formula true at the end of every way on singles out `o` here, every return is
    `o`. -/
theorem of_def (hB : ModalSys.B = true) (hne : Nonempty ι)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) (hθ : ∀ i b, M.holeSat θ (val i b))
    (hdef : ∀ z : M.frame.Dom A w, M.holeSat θ z → z = o) : RoundTrip acc val o := by
  refine ⟨hne, fun i => ?_⟩
  obtain ⟨r⟩ := M.frame.symm hB (acc i).2.down
  refine ⟨r, ?_⟩
  rw [hdef _ (hθ i ⟨w, ⟨r⟩⟩)]
  exact M.Ind_refl o

/-- ⭐**β** (`back_beta`): mapping every value by a hole term maps the return — `Ind` is preserved
    by the map in a model proper (`IndInvariant.map`). -/
theorem map (hM : M.IndInvariant) {B : VarType} {b : Ann B}
    (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) (h : RoundTrip acc val o) :
    RoundTrip acc (fun i b => M.holeVal s (val i b)) (M.holeVal s o) := by
  refine ⟨h.1, fun i => ?_⟩
  obtain ⟨r, hr⟩ := h.2 i
  exact ⟨r, hM.map s hr⟩

/-- ⭐**Pairing** (`back_pair`, §11.14 check 3): two carriers over one out leg return their pair —
    because each arrow of the leg has only **one** way home (`Frame.homeUnique`), so the two returns
    are read along the same arrow, and `Ind` is preserved by pairing (`IndInvariant.pair`). -/
theorem pair (hM : M.IndInvariant) (hS : ModalSys.BStrong = true) {B : VarType}
    {val' : ∀ i, ∀ b : M.frame.Acc (acc i).1, M.frame.Dom B b.1} {o' : M.frame.Dom B w}
    (h : RoundTrip acc val o) (h' : RoundTrip acc val' o') :
    RoundTrip (A := .VTypeProd A B) acc
      (fun i b => ((val i b, val' i b) : M.frame.Dom (.VTypeProd A B) b.1))
      ((o, o') : M.frame.Dom (.VTypeProd A B) w) := by
  refine ⟨h.1, fun i => ?_⟩
  obtain ⟨r, hr⟩ := h.2 i
  obtain ⟨r', hr'⟩ := h'.2 i
  obtain rfl : r' = r := @Subsingleton.elim _ (M.frame.homeUnique hS) r' r
  exact ⟨r', hM.pair hr hr'⟩

/-- ⭐**The own arrow** (`back_here`, §11.5 (4)): under T the identity is an arrow of the plain
    out leg, and its only way home is the identity again, so the round trip along it is
    indistinguishable from the value. -/
theorem own (hT : ModalSys.T = true) (hS : ModalSys.BStrong = true)
    {val : ∀ a : M.frame.Acc w, ∀ b : M.frame.Acc a.1, M.frame.Dom A b.1}
    (h : RoundTrip (fun a : M.frame.Acc w => a) val o) :
    M.Ind (val (M.frame.reflAcc hT w) (M.frame.reflAcc hT w)) o := by
  obtain ⟨r, hr⟩ := h.2 (M.frame.reflAcc hT w)
  obtain rfl : r = M.frame.refl hT w := @Subsingleton.elim _ (M.frame.homeUnique hS) _ _
  exact hr

end RoundTrip

/-! ## The returning possibility -/

/-- ⭐**Existence** (`ret_exists`): under weak B every accessible world has a way home, so a
    necessary object found there comes back as something — its value along that way. -/
theorem ret_exists (hB : ModalSys.B = true) {A : VarType} {w : M.frame.W}
    {P : ∀ a : M.frame.Acc w, M.frame.Dom (.VTypeBox A) a.1 → Prop}
    (h : ∃ (a : M.frame.Acc w) (e : M.frame.Dom (.VTypeBox A) a.1), P a e) :
    ∃ o : M.frame.Dom A w, ∃ (a : M.frame.Acc w) (e : M.frame.Dom (.VTypeBox A) a.1),
      P a e ∧ ∃ r : M.frame.R a.1 w, M.Ind (M.necEval (e : M.frame.Nec A a.1) ⟨w, ⟨r⟩⟩) o := by
  obtain ⟨a, e, he⟩ := h
  obtain ⟨r⟩ := M.frame.symm hB a.2.down
  exact ⟨_, a, e, he, r, M.Ind_refl _⟩

/-- ⭐**Counit** (`ret_counit`, no carriers): what is necessary of the object out there holds of
    its value here — read along the way home. -/
theorem ret_counit (hM : M.IndInvariant) {A : VarType} {w : M.frame.W}
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) {o : M.frame.Dom A w}
    (h : ∃ (a : M.frame.Acc w) (e : M.frame.Dom (.VTypeBox A) a.1),
      (∀ b : M.frame.Acc a.1, M.holeSat ψ (M.necEval (e : M.frame.Nec A a.1) b)) ∧
        ∃ r : M.frame.R a.1 w, M.Ind (M.necEval (e : M.frame.Nec A a.1) ⟨w, ⟨r⟩⟩) o) :
    M.holeSat ψ o := by
  obtain ⟨a, e, hψ, r, hr⟩ := h
  exact (holeSat_ind hM ψ hr).mp (hψ _)

/-! ## Surjectivity -/

/-- A fresh carrier, declared at the root `r`, comes back as `t` exactly when its value does. -/
theorem sat_back_eta_extend (hS : ModalSys.BStrong = true) {Γ : Ctx} {w : M.frame.W}
    (env : M.Env Γ w) {A : VarType} (r : Root) (hr : Γ.RootFresh r)
    (c : M.frame.Dom (.VTypeBox (.VTypeBox A)) w) {a : Ann A} (t : Term σ Γ A a) :
    M.sat (env.extend r c) (WFF.back hS .nec
        (Term.eta (.root r) _ (Ctx.ref_insert_root Γ r (.VTypeBox (.VTypeBox A))))
        (Term.weaken hr.root _ t) : WFF σ (Γ.insert r (.VTypeBox (.VTypeBox A))) 0) ↔
      M.Backs .nec (A := A) c (interp env t) := by
  have hag : Env.Agree (Ctx.le_insert hr.root (.VTypeBox (.VTypeBox A))) env (env.extend r c) := by
    intro v U hv
    have hne : v ≠ .root r := fun hvr => by rw [hvr, hr.root] at hv; cases hv
    simp only [Env.extend, dif_neg hne]
  have hslot : (env.extend r c).ref (.root r)
      (Ctx.ref_insert_root Γ r (.VTypeBox (.VTypeBox A))) = c :=
    Env.extend_root env r c (Ctx.ref_insert_root Γ r (.VTypeBox (.VTypeBox A)))
  change M.Backs .nec (interp (env.extend r c) (Term.eta _ _ _))
    (interp (env.extend r c) (Term.mono _ t)) ↔ _
  rw [interp_eta, interp_mono hag t, hslot]

/-- ⭐**Every object comes back** (`B_strong`, row 1): wherever there is a way out,
    `∃c:□□A. Back c t` — the law `Model.backRet_exists`, read at a fresh carrier. -/
theorem sat_back_ex (hS : ModalSys.BStrong = true) {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w)
    {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    (hr : Γ.RootFresh (.bnd 0)) (hne : Nonempty (M.frame.Acc w)) :
    M.sat env (WFF.ex (.VTypeBox (.VTypeBox A))
      (WFF.back hS .nec
        (Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeBox (.VTypeBox A))))
        (Term.weaken hr.root _ t)) : WFF σ Γ 0) := by
  obtain ⟨c₀, hc⟩ := M.backRet_exists hS hne (interp env t)
  let c : M.frame.Dom (.VTypeBox (.VTypeBox A)) w := c₀
  exact ⟨c, (sat_back_eta_extend hS env (.bnd 0) hr c t).mpr ⟨hne, hc⟩⟩

/-! ## Hole terms and annotations -/

/-- A hole term read in a context is its value at the value in its hole. -/
theorem interp_holeRead {Γ : Ctx} [Γ.NoSlots] (hnp : Γ.NoProjLast) {w : M.frame.W}
    (env : M.Env Γ w) {A : VarType} {a : Ann A} (t : Term σ Γ A a) {B : VarType} {b : Ann B}
    (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    interp env (Term.holeRead t s) = M.holeVal s (interp env t) := by
  simp only [Term.holeRead]
  rw [interp_subst _ _ _ (hnp.insert (.bnd 0) A) env, substEnv_single_tm env hnp (.bnd 0) t,
    interp_mono (Env.extend_agree (h := Ctx.empty_le Γ) (env := Env.empty w) (env' := env)
      (fun _ _ h => nomatch h) (.bnd 0) (interp env t))]
  rfl

/-- Reading a `◇`-free term at another annotation does not change its value. -/
theorem interp_castAnn {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {A : VarType}
    (hA : A.diaFree = true) {a a' : Ann A} (t : Term σ Γ A a) :
    interp env (Term.castAnn (a' := a') hA t) = interp env t := by
  obtain rfl := Ann.eq_of_diaFree hA a a'
  rfl

end Model

/-! ## The out leg in a model -/

namespace OutLeg

variable {σ : Signature} {M : Model.{u, v} σ} {Γ : Ctx}

/-- The arrows of the out leg: every arrow out, or the witness's extent. -/
noncomputable def Arr {w : M.frame.W} (env : M.Env Γ w) : OutLeg Γ → Type (max u v)
  | .nec => M.frame.Acc w
  | .pos y hy => (M.posEval (env.ref y hy.choose_spec)).1

/-- An arrow of the leg, as an arrow out. -/
noncomputable def acc {w : M.frame.W} (env : M.Env Γ w) :
    (O : OutLeg Γ) → O.Arr env → M.frame.Acc w
  | .nec, a => a
  | .pos _ _, a => a.1

/-- The environment of the leg's view at the end of one of its arrows. -/
noncomputable def push {w : M.frame.W} (env : M.Env Γ w) :
    (O : OutLeg Γ) → (i : O.Arr env) → M.Env O.view (O.acc env i).1
  | .nec, a => env.boxPush a
  | .pos y hy, a => env.diaPush y hy.choose_spec a

theorem sat_dia {d : ℕ} {w : M.frame.W} (env : M.Env Γ w) :
    (O : OutLeg Γ) → (φ : WFF σ O.view d) →
    (M.sat env (O.dia φ) ↔ ∃ i : O.Arr env, M.sat (O.push env i) φ)
  | .nec, φ => by
      change ((∀ a : M.frame.Acc w, M.sat (env.boxPush a) φ → False) → False) ↔ _
      exact not_forall_not
  | .pos y hy, φ => by
      change (∃ (X : VarType) (h : Γ.ref y = some (.VTypeDia X))
        (a : (M.posEval (env.ref y h)).1), M.sat (env.diaPush y h a) φ) ↔ _
      constructor
      · rintro ⟨X, h, a, hs⟩
        have hX : X = hy.choose := by
          have e := h.symm.trans hy.choose_spec
          simp only [Option.some.injEq, VarType.VTypeDia.injEq] at e
          exact e
        subst hX
        exact ⟨a, hs⟩
      · rintro ⟨a, hs⟩
        exact ⟨_, hy.choose_spec, a, hs⟩

theorem sat_box {d : ℕ} {w : M.frame.W} (env : M.Env Γ w) :
    (O : OutLeg Γ) → (φ : WFF σ O.view d) →
    (M.sat env (O.box φ) ↔ ∀ i : O.Arr env, M.sat (O.push env i) φ)
  | .nec, _ => Iff.rfl
  | .pos y hy, φ => by
      change ¬ M.sat env ((OutLeg.pos y hy).dia φ.neg) ↔ _
      rw [sat_dia]
      exact not_exists_not

/-- ⭐A `Back` atom is a round trip over its leg. -/
theorem sat_back {d : ℕ} (hS : ModalSys.BStrong = true) {w : M.frame.W} (env : M.Env Γ w)
    (O : OutLeg Γ) {A : VarType} {a₀ : Ann A}
    (bd : Term σ O.view.boxIn A a₀) {a : Ann A} (t : Term σ Γ A a) :
    M.sat env (O.back hS bd t : WFF σ Γ d) ↔
      Model.RoundTrip (O.acc env) (fun i b => Model.interp ((O.push env i).boxPush b) bd)
        (Model.interp env t) := by
  cases O with
  | nec => exact Model.backs_nec_boxtm env bd (Model.interp env t)
  | pos y hy => exact Model.backs_pos_diatm env hy hy.choose_spec bd (Model.interp env t)

end OutLeg

/-! ## The rules are sound -/

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ} {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W}
  (env : M.Env Γ w) (hnp : Γ.NoProjLast) (hfin : Γ.Tame) (hM : M.IndInvariant)

include hnp hM in
theorem sat_back_counit (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1)
    (hb : M.sat env (O.back hS bd t : WFF σ Γ 0))
    (hd : M.sat env (O.dia (WFF.box (WFF.holeRead bd ψ)))) :
    M.sat env (WFF.holeRead t ψ) := by
  rw [sat_holeRead hnp]
  obtain ⟨i, hi⟩ := (OutLeg.sat_dia env O _).mp hd
  exact ((OutLeg.sat_back hS env O bd t).mp hb).counit hM ψ
    ⟨i, fun b => (sat_holeRead (Ctx.noProjLast_boxIn _) _ bd ψ).mp (hi b)⟩

include hnp hM in
theorem sat_back_unit (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1)
    (hb : M.sat env (O.back hS bd t : WFF σ Γ 0)) (hψ : M.sat env (WFF.holeRead t ψ)) :
    M.sat env (O.box (WFF.box (WFF.holeRead bd ψ).neg).neg) := by
  refine (OutLeg.sat_box env O _).mpr fun i hall => ?_
  obtain ⟨b, hb'⟩ := ((OutLeg.sat_back hS env O bd t).mp hb).unit hM ψ
    ((sat_holeRead hnp env t ψ).mp hψ) i
  exact hall b ((sat_holeRead (Ctx.noProjLast_boxIn _) _ bd ψ).mpr hb')

omit [Γ.NoSlots] in
theorem sat_back_ne (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) (hb : M.sat env (O.back hS bd t : WFF σ Γ 0)) :
    M.sat env (O.dia (.top : WFF σ O.view 0)) := by
  obtain ⟨i⟩ := ((OutLeg.sat_back hS env O bd t).mp hb).ne
  exact (OutLeg.sat_dia env O _).mpr ⟨i, trivial⟩

include hnp hM in
theorem sat_back_beta (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) {B : VarType} {b : Ann B}
    (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b)
    (hb : M.sat env (O.back hS bd t : WFF σ Γ 0)) :
    M.sat env (O.back hS (Term.holeRead bd s) (Term.holeRead t s) : WFF σ Γ 0) := by
  rw [OutLeg.sat_back] at hb ⊢
  have hval : (fun i (b : M.frame.Acc (O.acc env i).1) =>
      interp ((O.push env i).boxPush b) (Term.holeRead bd s)) =
      fun i b => M.holeVal s (interp ((O.push env i).boxPush b) bd) := by
    funext i b
    exact interp_holeRead (Ctx.noProjLast_boxIn _) _ bd s
  rw [hval, interp_holeRead hnp env t s]
  exact hb.map hM s

omit [Γ.NoSlots] in
include hM in
theorem sat_back_pair (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) {B : VarType} {b₀ : Ann B}
    (bd' : Term σ O.view.boxIn B b₀) {b : Ann B} (t' : Term σ Γ B b)
    (hb : M.sat env (O.back hS bd t : WFF σ Γ 0))
    (hb' : M.sat env (O.back hS bd' t' : WFF σ Γ 0)) :
    M.sat env (O.back hS (Term.pair bd bd') (Term.pair t t') :
      WFF σ Γ 0) := by
  rw [OutLeg.sat_back] at hb hb' ⊢
  exact hb.pair hM hS hb'

omit [Γ.NoSlots] in
theorem sat_back_eq (hS : ModalSys.BStrong = true) (L : BLeg) {A : VarType}
    {b : Ann (L.carrier A)} (s : Term σ Γ (L.carrier A) b) {a : Ann A}
    (t t' : Term σ Γ A a) (hb : M.sat env (WFF.back hS L s t : WFF σ Γ 0))
    (he : M.sat env (eqRec A t t' : WFF σ Γ 0)) :
    M.sat env (WFF.back hS L s t' : WFF σ Γ 0) := by
  change M.Backs L (interp env s) (interp env t')
  rw [← (sat_eqRec env A t t').mp he]
  exact hb

include hnp hfin hM in
/-- ⭐The own arrow (T): the carrier read here twice is interchangeable with its value. -/
theorem sat_back_here (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true) {A : VarType}
    {a₀ : Ann A} (bd : Term σ Γ.boxIn.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) (φ : WFF σ (Γ.insert (.bnd 0) A) 1)
    (hb : M.sat env ((OutLeg.nec : OutLeg Γ).back hS bd t : WFF σ Γ 0))
    (hφ : M.sat env (WFF.instantiate Ctx.NoSlots.slots t φ)) :
    M.sat env (WFF.instantiate Ctx.NoSlots.slots (Term.collapse (Ctx.collapses_boxIn_self hT Γ)
      (Term.collapse (Ctx.collapses_boxIn_self hT Γ.boxIn) bd)) φ) := by
  have hown := ((OutLeg.sat_back hS env .nec bd t).mp hb).own hT hS
  rw [sat_instantiate env hnp] at hφ ⊢
  rw [interp_collapse (Env.collapseAgree_self hT env),
    interp_collapse (Env.collapseAgree_self hT (env.boxPush (M.frame.reflAcc hT w)))]
  exact (hM.inv hfin hnp env φ _ _ hown).mpr hφ

theorem sat_back_def (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true) (O : OutLeg Γ)
    {A : VarType} (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀)
    {a : Ann A} (t : Term σ Γ A a) (θ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1)
    (hne : M.sat env (O.dia (.top : WFF σ O.view 0)))
    (hall : M.sat env (O.box (WFF.box (WFF.holeRead bd θ))))
    (hdef : M.sat env (WFF.all A (WFF.imp (WFF.mono ((Ctx.empty_le Γ).insert (.bnd 0) A) θ)
      (eqRec A (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root Γ (.bnd 0) A))
        (Term.castAnn hA (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root A) t))))
      : WFF σ Γ 0)) :
    M.sat env (O.back hS bd t : WFF σ Γ 0) := by
  rw [OutLeg.sat_back]
  refine RoundTrip.of_def hB ?_ θ ?_ ?_
  · obtain ⟨i, _⟩ := (OutLeg.sat_dia env O _).mp hne
    exact ⟨i⟩
  · intro i b
    exact (sat_holeRead (Ctx.noProjLast_boxIn _) _ bd θ).mp ((OutLeg.sat_box env O _).mp hall i b)
  · intro z hz
    have hr : Γ.RootFresh (.bnd 0) := (Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)
    have hag : Env.Agree (Ctx.le_insert hr.root A) env (env.extend (.bnd 0) z) := by
      intro v U hv
      have hne : v ≠ .root (.bnd 0) := fun hvr => by rw [hvr, hr.root] at hv; cases hv
      simp only [Env.extend, dif_neg hne]
    have hθ : M.sat (env.extend (.bnd 0) z) (WFF.mono ((Ctx.empty_le Γ).insert (.bnd 0) A) θ) :=
      (sat_mono (Env.extend_agree (h := Ctx.empty_le Γ) (env := Env.empty w) (env' := env)
        (fun _ _ h => nomatch h) (.bnd 0) z) θ).mpr hz
    have he := (sat_eqRec _ A _ _).mp (hdef z hθ)
    have hslot : (env.extend (.bnd 0) z).ref (.root (.bnd 0)) (Ctx.ref_insert_root Γ (.bnd 0) A) =
        z := Env.extend_root env (.bnd 0) z (Ctx.ref_insert_root Γ (.bnd 0) A)
    rwa [interp_eta, interp_castAnn, interp_mono hag, hslot] at he

end Model


/-! ## The returning possibility: its syntax in a model -/

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

omit [ModalSys] in
theorem noProjLast_hole (A : VarType) : (Ctx.empty.insert (.bnd 0) A).NoProjLast :=
  (show Ctx.empty.NoProjLast from fun _ _ h => by simp [Ctx.empty] at h).insert (.bnd 0) A

/-- On the hole's context, substituting a term is extending the empty environment by its value. -/
theorem substEnv_hole {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) :
    substEnv (Subst.single (.bnd 0) (.tm t)) (Subst.ok_single (Ctx.empty_le Γ) rfl)
      (noProjLast_hole A) env = (Env.empty w).extend (.bnd 0) (interp env t) := by
  funext v U hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    have hTU : A = U := by simpa [Ctx.insert] using hv
    subst hTU
    exact (entryVal_congr env
      (show Subst.single (.bnd 0) (.tm t) (.root (.bnd 0)) = .tm t from if_pos rfl) _ rfl).trans
      (Env.extend_root (Env.empty w) (.bnd 0) _ hv).symm
  · simp [Ctx.insert, hvr, Ctx.empty] at hv

/-- A hole formula read at any depth says the same of the value in its hole. -/
theorem sat_holeAt {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {w : M.frame.W} (env : M.Env Γ w)
    {A : VarType} {a : Ann A} (t : Term σ Γ A a) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) :
    M.sat env (WFF.holeAt hs t ψ) ↔ M.holeSat ψ (interp env t) := by
  unfold WFF.holeAt
  rw [sat_subst _ _ _ _ _ (noProjLast_hole A) env ψ, substEnv_hole env t]
  rfl

/-- A hole term read at any depth is its value at the value in its hole. -/
theorem interp_holeAt {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) {B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    interp env (Term.holeAt t s) = M.holeVal s (interp env t) := by
  unfold Term.holeAt
  rw [interp_subst _ _ _ (noProjLast_hole A) env s, substEnv_hole env t]
  rfl

/-- The first box component of a necessary pair is the necessary object of its first
    components. -/
theorem necEval_boxFst {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {x : VarSymb} {A B : VarType}
    (h : Γ.ref x = some (.VTypeBox (.VTypeProd A B))) (a : M.frame.Acc w) :
    M.necEval (interp env (Term.boxFst (σ := σ) h) : M.frame.Nec A w) a =
      (M.necEval (env.ref x h : M.frame.Nec (.VTypeProd A B) w) a).1 := by
  unfold Term.boxFst
  rw [box_beta, interp_eta, Env.ref_fst _ (Ctx.ref_inner h), Env.ref_inner env a h]

theorem necEval_boxSnd {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {x : VarSymb} {A B : VarType}
    (h : Γ.ref x = some (.VTypeBox (.VTypeProd A B))) (a : M.frame.Acc w) :
    M.necEval (interp env (Term.boxSnd (σ := σ) h) : M.frame.Nec B w) a =
      (M.necEval (env.ref x h : M.frame.Nec (.VTypeProd A B) w) a).2 := by
  unfold Term.boxSnd
  rw [box_beta, interp_eta, Env.ref_snd _ (Ctx.ref_inner h), Env.ref_inner env a h]

/-- The components of a necessary pair of `d` and `b`, read at the item's address, are `d` and
    `b`. -/
theorem boxFst_necPair {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {A B : VarType}
    (d : M.frame.Dom (.VTypeBox A) w) (b : M.frame.Dom (.VTypeBox B) w) :
    interp (env.extend (T := .VTypeBox (.VTypeProd A B)) (.bnd 0)
        (M.ops.necPair (d : M.frame.Nec A w) (b : M.frame.Nec B w)))
      (Term.boxFst (σ := σ) (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeBox (.VTypeProd A B)))) = d ∧
    interp (env.extend (T := .VTypeBox (.VTypeProd A B)) (.bnd 0)
        (M.ops.necPair (d : M.frame.Nec A w) (b : M.frame.Nec B w)))
      (Term.boxSnd (σ := σ) (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeBox (.VTypeProd A B)))) = b := by
  have hslot : (env.extend (T := .VTypeBox (.VTypeProd A B)) (.bnd 0)
      (M.ops.necPair (d : M.frame.Nec A w) (b : M.frame.Nec B w))).ref (.root (.bnd 0))
      (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeBox (.VTypeProd A B))) =
      M.ops.necPair (d : M.frame.Nec A w) (b : M.frame.Nec B w) :=
    Env.extend_root env (.bnd 0) _ _
  constructor
  · refine M.nec_inj (funext fun a => ?_)
    rw [necEval_boxFst, hslot, M.necPair_eval]
  · refine M.nec_inj (funext fun a => ?_)
    rw [necEval_boxSnd, hslot, M.necPair_eval]

section Body

variable {V : Ctx} [V.NoSlots]

/-- ⭐Replacing the bound item: the body holds of `d` exactly when the old body holds of `X(d)`. -/
theorem sat_bodyRepl (hnp : V.NoProjLast) {w : M.frame.W} (env : M.Env V w)
    {A B : VarType} {b : Ann (.VTypeBox B)}
    (X : Term σ (V.insert (.bnd 0) (.VTypeBox A)) (.VTypeBox B) b)
    (Φ : WFF σ (V.insert (.bnd 0) (.VTypeBox B)) 1) (d : M.frame.Dom (.VTypeBox A) w) :
    M.sat (env.extend (.bnd 0) d) (WFF.bodyRepl X Φ) ↔
      M.sat (env.extend (.bnd 0) (interp (env.extend (.bnd 0) d) X)) Φ := by
  unfold WFF.bodyRepl
  rw [sat_subst _ _ _ _ _ (hnp.insert _ _)]
  refine iff_of_eq (congrArg (fun E => M.sat E Φ) ?_)
  funext v U hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    have hTU : (VarType.VTypeBox B) = U := by simpa [Ctx.insert] using hv
    subst hTU
    exact (entryVal_congr _
      (show ((Subst.idS σ _).set (.bnd 0) (.tm X)) (.root (.bnd 0)) = .tm X from if_pos rfl)
      _ rfl).trans (Env.extend_root _ (.bnd 0) _ hv).symm
  · have hv' : V v = some U := by simpa [Ctx.insert, hvr] using hv
    have hlp := hnp v U hv'
    have hE : (V.insert (.bnd 0) (.VTypeBox A)) v = some U := body_le _ v U hv'
    refine (entryVal_congr _
      (show ((Subst.idS σ _).set (.bnd 0) (.tm X)) v = .ren v from if_neg hvr) _
      ((Ctx.ref_nonproj _ hlp).trans hE)).trans ?_
    refine (Env.ref_of_nonproj _ hlp _ hE).trans ?_
    rw [Env.extend_ne env (.bnd 0) d hE hvr hv', Env.extend_ne env (.bnd 0) _ hv hvr hv']

/-- ⭐Splitting a paired item: the body holds of `e` exactly when the old body holds of its two
    components. -/
theorem sat_bodySplit (hnp : V.NoProjLast) {w : M.frame.W} (env : M.Env V w)
    {A B C : VarType} {b₀ : Ann (.VTypeBox A)} {b₁ : Ann (.VTypeBox B)}
    (X₀ : Term σ (V.insert (.bnd 0) (.VTypeBox C)) (.VTypeBox A) b₀)
    (X₁ : Term σ (V.insert (.bnd 0) (.VTypeBox C)) (.VTypeBox B) b₁)
    (Φ : WFF σ ((V.insert (.bnd 0) (.VTypeBox A)).insert (.bnd 1) (.VTypeBox B)) 2)
    (e : M.frame.Dom (.VTypeBox C) w) :
    M.sat (env.extend (.bnd 0) e) (WFF.bodySplit X₀ X₁ Φ) ↔
      M.sat ((env.extend (.bnd 0) (interp (env.extend (.bnd 0) e) X₀)).extend
        (.bnd 1) (interp (env.extend (.bnd 0) e) X₁)) Φ := by
  unfold WFF.bodySplit
  rw [sat_subst _ _ _ _ _ ((hnp.insert _ _).insert _ _)]
  refine iff_of_eq (congrArg (fun E => M.sat E Φ) ?_)
  funext v U hv
  by_cases hv1 : v = .root (.bnd 1)
  · subst hv1
    have hTU : (VarType.VTypeBox B) = U := by simpa [Ctx.insert] using hv
    subst hTU
    exact (entryVal_congr _
      (show (((Subst.idS σ _).set (.bnd 0) (.tm X₀)).set (.bnd 1) (.tm X₁)) (.root (.bnd 1)) =
        .tm X₁ from Subst.set_root _ _ _) _ rfl).trans
      (Env.extend_root _ (.bnd 1) _ hv).symm
  · by_cases hv0 : v = .root (.bnd 0)
    · subst hv0
      have hv0' : (V.insert (.bnd 0) (.VTypeBox A)) (.root (.bnd 0)) = some U := by
        simpa [Ctx.insert, hv1] using hv
      have hTU : (VarType.VTypeBox A) = U := by simpa [Ctx.insert] using hv0'
      subst hTU
      refine (entryVal_congr _
        (show (((Subst.idS σ _).set (.bnd 0) (.tm X₀)).set (.bnd 1) (.tm X₁)) (.root (.bnd 0)) =
          .tm X₀ from (Subst.set_ne _ _ hv1).trans (Subst.set_root _ _ _)) _ rfl).trans ?_
      rw [Env.extend_ne _ (.bnd 1) _ hv hv1 hv0', Env.extend_root _ (.bnd 0) _ hv0']
      rfl
    · have hv' : V v = some U := by simpa [Ctx.insert, hv0, hv1] using hv
      have hv0' : (V.insert (.bnd 0) (.VTypeBox A)) v = some U := by
        simpa [Ctx.insert, hv1] using hv
      have hlp := hnp v U hv'
      have hE : (V.insert (.bnd 0) (.VTypeBox C)) v = some U := body_le _ v U hv'
      refine (entryVal_congr _
        (show (((Subst.idS σ _).set (.bnd 0) (.tm X₀)).set (.bnd 1) (.tm X₁)) v = .ren v from
          (Subst.set_ne _ _ hv1).trans (Subst.set_ne _ _ hv0)) _
        ((Ctx.ref_nonproj _ hlp).trans hE)).trans ?_
      refine (Env.ref_of_nonproj _ hlp _ hE).trans ?_
      rw [Env.extend_ne env (.bnd 0) e hE hv0 hv',
        Env.extend_ne _ (.bnd 1) _ hv hv1 hv0', Env.extend_ne env (.bnd 0) _ hv0' hv0 hv']

end Body

/-- The `□`-view formula read at the current world, with `t` in its hole (T). -/
theorem sat_hereRead {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true) (hnp : Γ.NoProjLast)
    {w : M.frame.W} (env : M.Env Γ w) {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    M.sat env (WFF.hereRead hT t ψ) ↔
      M.sat ((env.boxPush (M.frame.reflAcc hT w)).extend (.bnd 0) (interp env t)) ψ :=
  (sat_instantiate env hnp Ctx.NoSlots.slots t _).trans
    (sat_collapse ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A)
      ((Env.collapseAgree_self hT env).extend
        ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) (interp env t)) ψ)

end Model

namespace OutLeg

variable {σ : Signature} {M : Model.{u, v} σ} {Γ : Ctx}

theorem noProjLast : (O : OutLeg Γ) → O.view.NoProjLast
  | .nec => Ctx.noProjLast_boxIn Γ
  | .pos y _ => Ctx.noProjLast_diaIn Γ y

/-- At the far end of an arrow of the leg, the leg's view agrees with the `□` view there. -/
theorem agree_push {w : M.frame.W} (env : M.Env Γ w) :
    (O : OutLeg Γ) → (i : O.Arr env) →
      Model.Env.Agree O.le_view (env.boxPush (O.acc env i)) (O.push env i)
  | .nec, _ => fun _ _ _ => rfl
  | .pos _ hy, i => Model.Env.diaPush_boxIn env hy.choose_spec i

/-- The bridge's body read at the far end of an arrow of the leg holds of the carrier's image
    there. -/
theorem sat_bodyRead [Γ.NoSlots] {w : M.frame.W} (env : M.Env Γ w) (O : OutLeg Γ)
    (i : O.Arr env) {A : VarType} {b : Ann (.VTypeBox A)} (c : Term σ O.view (.VTypeBox A) b)
    (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1) :
    M.sat (O.push env i) (O.bodyRead c Φ) ↔
      M.sat ((env.boxPush (O.acc env i)).extend (.bnd 0) (Model.interp (O.push env i) c)) Φ := by
  unfold OutLeg.bodyRead
  rw [Model.sat_instantiate _ O.noProjLast Ctx.NoSlots.slots c _]
  exact Model.sat_mono (Model.Env.extend_agree (agree_push env O i) (.bnd 0) _) Φ

end OutLeg

/-! ## The returning possibility's rules are sound -/

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ} {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W}
  (env : M.Env Γ w) (hnp : Γ.NoProjLast) (hfin : Γ.Tame) (hM : M.IndInvariant)

omit [Γ.NoSlots] in
/-- What `ret_new` hands its subproof: the fresh value is the returning possibility's. -/
theorem sat_ret_fresh (hS : ModalSys.BStrong = true) {A : VarType}
    (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1) (c : ℕ) (hc : Γ.RootFresh (.free c))
    (o : M.frame.Dom A w) (a : M.frame.Acc w) (e : M.frame.Dom (.VTypeBox A) a.1)
    (hΦ : M.sat ((env.boxPush a).extend (.bnd 0) e) Φ) (r : M.frame.R a.1 w)
    (hr : M.Ind (M.necEval (e : M.frame.Nec A a.1) ⟨w, ⟨r⟩⟩) o) :
    M.sat (env.extend (.free c) o) (WFF.ret hS
      (Term.eta (.root (.free c)) A (Ctx.ref_insert_root Γ (.free c) A))
      (WFF.mono ((Ctx.le_insert hc.root A).boxIn.insert (.bnd 0) _) Φ)) := by
  have hslot : (env.extend (.free c) o).ref (.root (.free c)) (Ctx.ref_insert_root Γ (.free c) A) =
      o := Env.extend_root env (.free c) o (Ctx.ref_insert_root Γ (.free c) A)
  refine ⟨a, e, ?_, r, ?_⟩
  · exact (sat_mono (Env.extend_agree (Env.boxPush_agree (Env.agree_extend env hc.root o) a)
      (.bnd 0) e) Φ).mpr hΦ
  · change M.Ind _ (interp (env.extend (.free c) o) (Term.eta _ _ _))
    rw [interp_eta, hslot]
    exact hr

include hM in
/-- What `ret_ext` hands its subproof, from the premise's object, its companion and the way
    home: the pair comes back as the pair of values — `Ind` is preserved by pairing. -/
theorem sat_ret_ext (hS : ModalSys.BStrong = true) {A B : VarType} {a : Ann A}
    (t : Term σ Γ A a)
    (Φ : WFF σ ((Γ.boxIn.insert (.bnd 0) (.VTypeBox A)).insert (.bnd 1) (.VTypeBox B)) 2)
    (c : ℕ) (hc : Γ.RootFresh (.free c)) (ac : M.frame.Acc w) (d : M.frame.Dom (.VTypeBox A) ac.1)
    (b : M.frame.Dom (.VTypeBox B) ac.1)
    (hΦ : M.sat (((env.boxPush ac).extend (.bnd 0) d).extend (.bnd 1) b) Φ)
    (r : M.frame.R ac.1 w)
    (hr : M.Ind (M.necEval (d : M.frame.Nec A ac.1) ⟨w, ⟨r⟩⟩) (interp env t)) :
    M.sat (env.extend (.free c) (M.necEval (b : M.frame.Nec B ac.1) ⟨w, ⟨r⟩⟩))
      (WFF.ret hS
        (Term.pair (Term.weaken hc.root B t)
          (Term.eta (.root (.free c)) B (Ctx.ref_insert_root Γ (.free c) B)))
        (WFF.mono ((Ctx.le_insert hc.root B).boxIn.insert (.bnd 0) _) (WFF.bodySplit
          (Term.boxFst (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox (.VTypeProd A B))))
          (Term.boxSnd (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox (.VTypeProd A B))))
          Φ))) := by
  set o := M.necEval (b : M.frame.Nec B ac.1) ⟨w, ⟨r⟩⟩
  have hag := Env.agree_extend env hc.root o
  have hslot : (env.extend (.free c) o).ref (.root (.free c)) (Ctx.ref_insert_root Γ (.free c) B) =
      o := Env.extend_root env (.free c) o (Ctx.ref_insert_root Γ (.free c) B)
  obtain ⟨hfst, hsnd⟩ := boxFst_necPair (σ := σ) (env.boxPush ac) d b
  refine ⟨ac, (M.ops.necPair (d : M.frame.Nec A ac.1) (b : M.frame.Nec B ac.1) :
    M.frame.Dom (.VTypeBox (.VTypeProd A B)) ac.1), ?_, r, ?_⟩
  · refine (sat_mono (Env.extend_agree (Env.boxPush_agree hag ac) (.bnd 0) _) _).mpr ?_
    rw [sat_bodySplit (Ctx.noProjLast_boxIn Γ), hfst, hsnd]
    exact hΦ
  · have h1 : interp (env.extend (.free c) o) (Term.pair (Term.weaken hc.root B t)
        (Term.eta (.root (.free c)) B (Ctx.ref_insert_root Γ (.free c) B))) =
        ((interp env t, o) : M.frame.Dom (.VTypeProd A B) w) :=
      Prod.ext (interp_mono hag t) ((interp_eta _ _ _).trans hslot)
    rw [M.necPair_eval, h1]
    exact hM.pair hr (M.Ind_refl _)

include hM in
theorem sat_ret_counit (hS : ModalSys.BStrong = true) {A : VarType}
    {a : Ann A} (t : Term σ Γ A a) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1)
    (h : M.sat env (WFF.ret hS t (WFF.box (WFF.holeAt
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert (.VTypeBox A)).boxIn
      (Term.eta (VarSymb.root (.bnd 0)).inner A
        (Ctx.ref_inner (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox A)))) ψ)) : WFF σ Γ 0)) :
    M.holeSat ψ (interp env t) := by
  obtain ⟨ac, e, hbox, r, hr⟩ := h
  refine ret_counit hM ψ ⟨ac, e, fun b => ?_, r, hr⟩
  have hb := (sat_holeAt _ _ _ ψ).mp (hbox b)
  rwa [interp_eta, Env.ref_inner _ b (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox A)),
    show ((env.boxPush ac).extend (.bnd 0) e).ref (.root (.bnd 0))
      (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox A)) = e from
      Env.extend_root _ (.bnd 0) e _] at hb

include hM in
/-- ⭐**Counit with a carrier** (§11.14): the object out there and the carrier's image there
    come home along the one way back, as the returning possibility's value and the carrier's —
    `Ind` is preserved by pairing. -/
theorem sat_ret_counitC (hS : ModalSys.BStrong = true) {A C : VarType} {a : Ann A}
    (y : Term σ Γ A a) {c₀ : Ann C} (bd : Term σ Γ.boxIn.boxIn C c₀) {c : Ann C}
    (t : Term σ Γ C c) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A C)) 1)
    (hret : M.sat env (WFF.ret hS y (WFF.box (WFF.holeAt
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert (.VTypeBox A)).boxIn
      (Term.pair (Term.eta (VarSymb.root (.bnd 0)).inner A
          (Ctx.ref_inner (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox A))))
        (Term.mono ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root (.VTypeBox A)).boxIn)
          bd)) ψ)) : WFF σ Γ 0))
    (hb : M.sat env ((OutLeg.nec : OutLeg Γ).back hS bd t : WFF σ Γ 0)) :
    M.holeSat ψ ((interp env y, interp env t) : M.frame.Dom (.VTypeProd A C) w) := by
  obtain ⟨ac, e, hbox, r, hr⟩ := hret
  obtain ⟨_, hall⟩ := (OutLeg.sat_back hS env .nec bd t).mp hb
  obtain ⟨r', hr'⟩ := hall ac
  obtain rfl : r' = r := @Subsingleton.elim _ (M.frame.homeUnique hS) r' r
  have hag := Env.boxPush_agree (Env.agree_extend (env.boxPush ac)
    (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root e) ⟨w, ⟨r'⟩⟩
  have hb' := (sat_holeAt _ _ _ ψ).mp (hbox ⟨w, ⟨r'⟩⟩)
  change M.holeSat ψ ((interp (((env.boxPush ac).extend (.bnd 0) e).boxPush ⟨w, ⟨r'⟩⟩)
      (Term.eta (VarSymb.root (.bnd 0)).inner A
        (Ctx.ref_inner (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox A)))),
    interp (((env.boxPush ac).extend (.bnd 0) e).boxPush ⟨w, ⟨r'⟩⟩)
      (Term.mono ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root (.VTypeBox A)).boxIn)
        bd)) : M.frame.Dom (.VTypeProd A C) w) at hb'
  rw [interp_eta, Env.ref_inner _ _ (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox A)),
    show ((env.boxPush ac).extend (.bnd 0) e).ref (.root (.bnd 0))
      (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox A)) = e from
      Env.extend_root _ (.bnd 0) e _, interp_mono hag bd] at hb'
  exact (holeSat_ind hM ψ (hM.pair hr hr')).mp hb'

include hM in
/-- ⭐**The unit** (`ret_unit`): at the far end of the returning possibility the way home `r` is an
    arrow out, leading here, where `s` is the object; it comes back along the arrow out as `sb`'s
    value there, and `θ` holds of it and of `d₁`'s return, which is `Ind` to `y`.  No uniqueness of
    ways home is used: the arrow out is itself a way home for `r`. -/
theorem sat_ret_unit (hS : ModalSys.BStrong = true) {C A : VarType} {c : Ann C}
    (y : Term σ Γ C c) (Ψ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox C)) 1) {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1)
    (hret : M.sat env (WFF.ret hS y Ψ : WFF σ Γ 0))
    (hθ : M.holeSat θ ((interp env y, interp env (Term.boxtm sb)) :
      M.frame.Dom (.VTypeProd C (.VTypeBox A)) w)) :
    M.sat env (WFF.ret hS y (WFF.and Ψ (WFF.unitBody hS sb θ)) : WFF σ Γ 0) := by
  obtain ⟨ac, e, hΨ, r, hr⟩ := hret
  refine ⟨ac, e, ⟨hΨ, ?_⟩, r, hr⟩
  have hu := Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox C)
  refine ⟨⟨w, ⟨r⟩⟩, interp env (Term.boxtm sb), ?_, ac.2.down, ?_⟩
  · rw [sat_holeAt]
    have hag := Env.agree_extend (((env.boxPush ac).extend (.bnd 0) e).boxPush ⟨w, ⟨r⟩⟩)
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert (.VTypeBox C)).boxIn.root
      (interp env (Term.boxtm sb))
    change M.holeSat θ (interp _ _, interp _ _)
    rw [interp_eta, interp_eta, ← Env.ref_agree hag _ (Ctx.ref_inner hu), Env.ref_inner _ _ hu]
    rw [show ((env.boxPush ac).extend (.bnd 0) e).ref (.root (.bnd 0)) hu = e from
        Env.extend_root _ (.bnd 0) e _,
      show ((((env.boxPush ac).extend (.bnd 0) e).boxPush ⟨w, ⟨r⟩⟩).extend (.bnd (0 + 1))
          (interp env (Term.boxtm sb))).ref (.root (.bnd 1))
          (Ctx.ref_insert_root _ (.bnd 1) _) = interp env (Term.boxtm sb) from
        Env.extend_root _ _ _ _]
    exact (holeSat_ind hM θ (hM.pair hr (M.Ind_refl _))).mpr hθ
  · rw [interp_mono
        (Env.agree_extend (env.boxPush ac) (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root e) sb,
      box_beta]
    exact M.Ind_refl _

omit [Γ.NoSlots] in
theorem sat_ret_mono (hS : ModalSys.BStrong = true) {A : VarType}
    {a : Ann A} (t : Term σ Γ A a) (Φ Φ' : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
    (h : M.sat env (WFF.ret hS t Φ : WFF σ Γ 0))
    (himp : M.sat env (WFF.box (WFF.all (.VTypeBox A) (WFF.imp Φ Φ')) : WFF σ Γ 0)) :
    M.sat env (WFF.ret hS t Φ' : WFF σ Γ 0) := by
  obtain ⟨ac, e, hΦ, r, hr⟩ := h
  exact ⟨ac, e, himp ac e hΦ, r, hr⟩

omit [Γ.NoSlots] in
theorem sat_ret_dia (hS : ModalSys.BStrong = true) {A : VarType}
    {a : Ann A} (t : Term σ Γ A a) (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
    (h : M.sat env (WFF.ret hS t Φ : WFF σ Γ 0)) :
    M.sat env ((OutLeg.nec : OutLeg Γ).dia (WFF.ex (.VTypeBox A) Φ)) := by
  obtain ⟨ac, e, hΦ, _, _⟩ := h
  exact (OutLeg.sat_dia env .nec _).mpr ⟨ac, e, hΦ⟩

include hnp hM in
theorem sat_ret_beta (hS : ModalSys.BStrong = true) {A B : VarType} {a : Ann A}
    (y : Term σ Γ A a) {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b)
    (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox B)) 1)
    (h : M.sat env (WFF.ret hS y (WFF.bodyRepl
      (Term.boxtm (Term.holeAt (Term.eta (VarSymb.root (.bnd 0)).inner A
        (Ctx.ref_inner (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox A)))) s)) Φ) :
      WFF σ Γ 0)) :
    M.sat env (WFF.ret hS (Term.holeRead y s) Φ : WFF σ Γ 0) := by
  obtain ⟨ac, e, hΦ, r, hr⟩ := h
  rw [sat_bodyRepl (Ctx.noProjLast_boxIn Γ)] at hΦ
  refine ⟨ac, _, hΦ, r, ?_⟩
  rw [box_beta, interp_holeAt, interp_eta,
    Env.ref_inner _ _ (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox A)),
    show ((env.boxPush ac).extend (.bnd 0) e).ref (.root (.bnd 0))
      (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox A)) = e from
      Env.extend_root _ (.bnd 0) e _,
    interp_holeRead hnp env y s]
  exact hM.map s hr

omit [Γ.NoSlots] in
theorem sat_ret_eq (hS : ModalSys.BStrong = true) {A : VarType}
    {a : Ann A} (t t' : Term σ Γ A a) (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
    (h : M.sat env (WFF.ret hS t Φ : WFF σ Γ 0)) (he : M.sat env (eqRec A t t' : WFF σ Γ 0)) :
    M.sat env (WFF.ret hS t' Φ : WFF σ Γ 0) := by
  obtain ⟨ac, e, hΦ, r, hr⟩ := h
  exact ⟨ac, e, hΦ, r, (sat_eqRec env A t t').mp he ▸ hr⟩

include hnp in
theorem sat_ret_here (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true) {A : VarType}
    {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀)
    (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
    (h : M.sat env (WFF.hereRead hT (Term.boxtm sb) Φ)) :
    M.sat env (WFF.ret hS (Term.collapse (Ctx.collapses_boxIn_self hT Γ) sb) Φ :
      WFF σ Γ 0) := by
  refine ⟨M.frame.reflAcc hT w, interp env (Term.boxtm sb), (sat_hereRead hT hnp env _ Φ).mp h,
    M.frame.refl hT w, ?_⟩
  rw [box_beta, interp_collapse (Env.collapseAgree_self hT env)]
  exact M.Ind_refl _

theorem sat_ret_bridge (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
    (hb : M.sat env (O.back hS bd t : WFF σ Γ 0))
    (hd : M.sat env (O.dia (O.bodyRead (Term.boxtm bd) Φ))) :
    M.sat env (WFF.ret hS t Φ : WFF σ Γ 0) := by
  obtain ⟨i, hi⟩ := (OutLeg.sat_dia env O _).mp hd
  obtain ⟨r, hr⟩ := ((OutLeg.sat_back hS env O bd t).mp hb).2 i
  refine ⟨O.acc env i, interp (O.push env i) (Term.boxtm bd),
    (OutLeg.sat_bodyRead env O i _ Φ).mp hi, r, ?_⟩
  rw [box_beta]
  exact hr

end Model
end V12M
