import QML.QML_v12m_SemHere

/-!
# QML v12m — strong B: the semantics of `Back` and the returning possibility

Roadmap milestone 2, step 3 (`docs/v12-modal-extensions.md` §11).  What the rules of step 4 need,
proved at the level of values, once for both rows:

* ⭐`Model.RoundTrip`: what `Back` implies (`Model.Ret_fwd`), with the out leg a parameter, and
  at `◇`-free contents what it is (`Model.Ret_conv`; docs §11.20).  A `□□`-carrier's body
  (`backs_nec_boxtm`) and a `◇□`-carrier's (`backs_pos_diatm`) unfold `Back` to the model's `Ret`
  at the leg (`OutLeg.sat_back`); `OutLeg.sat_back_rt` and `OutLeg.ret_of_roundTrip` go between.
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
    and `val i b` is the carrier's value at the end of a further arrow `b`.  It holds of `o` when
    the leg is nonempty and from each of its arrows some way home returns a value
    indistinguishable from `o` — what "comes back as" implies (`Model.Ret_fwd`). -/
def RoundTrip {A : VarType} {w : M.frame.W} {ι : Type*} (acc : ι → M.frame.Acc w)
    (val : ∀ i, ∀ b : M.frame.Acc (acc i).1, M.frame.Dom A b.1) (o : M.frame.Dom A w) : Prop :=
  Nonempty ι ∧ ∀ i, ∃ r : M.frame.R (acc i).1 w, M.Ind (val i ⟨w, ⟨r⟩⟩) o

/-- ⭐Row 1: a `□□`-carrier comes back through its body, read two `□` views in. -/
theorem backs_nec_boxtm {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {A : VarType} {a₀ : Ann A}
    (bd : Term σ Γ.boxIn.boxIn A a₀) (o : M.frame.Dom A w) :
    M.Backs .nec (A := A) (interp env (Term.boxtm (Term.boxtm bd))) o ↔
      M.Ret (Set.univ : Set (M.frame.Acc w))
        (fun a b => interp ((env.boxPush a.1).boxPush b) bd) o := by
  have h : (fun (a : (Set.univ : Set (M.frame.Acc w))) (b : M.frame.Acc a.1.1) =>
      M.necEval (M.necEval (interp env (Term.boxtm (Term.boxtm bd)) :
        M.frame.Nec (.VTypeBox A) w) a.1) b) =
      fun (a : (Set.univ : Set (M.frame.Acc w))) (b : M.frame.Acc a.1.1) =>
        interp ((env.boxPush a.1).boxPush b) bd := by
    funext a b
    rw [box_beta env (Term.boxtm bd) a.1, box_beta (env.boxPush a.1) bd]
  exact iff_of_eq (congrArg (fun v => M.Ret _ v o) h)

/-- ⭐Row 2: a `◇□`-carrier comes back through its body, read in its witness's view and one `□`
    view further in; the out leg is the witness's extent. -/
theorem backs_pos_diatm {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {y : VarSymb}
    (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)) {Y : VarType} (h : Γ.ref y = some (.VTypeDia Y))
    {A : VarType} {a₀ : Ann A} (bd : Term σ (Γ.diaIn y).boxIn A a₀) (o : M.frame.Dom A w) :
    M.Backs .pos (A := A) (interp env (Term.diatm y hy (Term.boxtm bd))) o ↔
      M.Ret (M.posEval (env.ref y h)).1
        (fun a b => interp ((env.diaPush y h a).boxPush b) bd) o := by
  change M.Ret (M.posEval (interp env (Term.diatm y hy (Term.boxtm bd)))).1
      (fun a b => M.necEval ((M.posEval (interp env (Term.diatm y hy (Term.boxtm bd)))).2 a) b)
      o ↔ _
  rw [dia_beta env hy h (Term.boxtm bd)]
  have e : (fun (a : (M.posEval (env.ref y h)).1) (b : M.frame.Acc a.1.1) =>
      M.necEval (interp (env.diaPush y h a) (Term.boxtm bd) : M.frame.Nec A a.1.1) b) =
      fun (a : (M.posEval (env.ref y h)).1) (b : M.frame.Acc a.1.1) =>
        interp ((env.diaPush y h a).boxPush b) bd := by
    funext a b
    exact box_beta (env.diaPush y h a) bd b
  exact iff_of_eq (congrArg (fun v => M.Ret _ v o) e)

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

/-- **Definition** (§11.5 (3)): under weak B every arrow of the out leg has a way home; if a
    hole formula true at the end of every way on singles out `o` here, every return is `o` — the
    validity of `back_def`, which `back_ret` subsumes. -/
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
  exact ⟨c, (sat_back_eta_extend hS env (.bnd 0) hr c t).mpr hc⟩

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

/-- The out leg's arrows, as a set of arrows out: all of them, or the witness's extent. -/
noncomputable def legSet {w : M.frame.W} (env : M.Env Γ w) : OutLeg Γ → Set (M.frame.Acc w)
  | .nec => Set.univ
  | .pos y hy => (M.posEval (env.ref y hy.choose_spec)).1

/-- The environment of the leg's view at the end of one of its arrows, given as a member of the
    leg's set. -/
noncomputable def pushS {w : M.frame.W} (env : M.Env Γ w) :
    (O : OutLeg Γ) → (a : O.legSet env) → M.Env O.view a.1.1
  | .nec, a => env.boxPush a.1
  | .pos y hy, a => env.diaPush y hy.choose_spec a

/-- ⭐A `Back` atom is the model's "comes back as" at its leg (`Model.Ret`, docs §11.20). -/
theorem sat_back {d : ℕ} (hS : ModalSys.BStrong = true) {w : M.frame.W} (env : M.Env Γ w)
    (O : OutLeg Γ) {A : VarType} {a₀ : Ann A}
    (bd : Term σ O.view.boxIn A a₀) {a : Ann A} (t : Term σ Γ A a) :
    M.sat env (O.back hS bd t : WFF σ Γ d) ↔
      M.Ret (O.legSet env) (fun a b => Model.interp ((O.pushS env a).boxPush b) bd)
        (Model.interp env t) := by
  cases O with
  | nec => exact Model.backs_nec_boxtm env bd (Model.interp env t)
  | pos y hy => exact Model.backs_pos_diatm env hy hy.choose_spec bd (Model.interp env t)

/-- What comes back over the leg makes the round trip over its arrows (`Model.Ret_fwd`). -/
theorem roundTrip_of_ret (hS : ModalSys.BStrong = true) {w : M.frame.W} (env : M.Env Γ w)
    (O : OutLeg Γ) {A : VarType} {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀)
    {o : M.frame.Dom A w}
    (h : M.Ret (O.legSet env) (fun a b => Model.interp ((O.pushS env a).boxPush b) bd) o) :
    Model.RoundTrip (O.acc env) (fun i b => Model.interp ((O.push env i).boxPush b) bd) o := by
  obtain ⟨⟨a⟩, h₂⟩ := M.Ret_fwd hS h
  cases O with
  | nec => exact ⟨⟨a.1⟩, fun i => h₂ ⟨i, trivial⟩⟩
  | pos y hy => exact ⟨⟨a⟩, h₂⟩

/-- ⭐At a `◇`-free content the round trip over the leg comes back (`Model.Ret_conv`). -/
theorem ret_of_roundTrip (hS : ModalSys.BStrong = true) {w : M.frame.W} (env : M.Env Γ w)
    (O : OutLeg Γ) {A : VarType} (hA : A.diaFree = true) {a₀ : Ann A}
    (bd : Term σ O.view.boxIn A a₀) {o : M.frame.Dom A w}
    (h : Model.RoundTrip (O.acc env) (fun i b => Model.interp ((O.push env i).boxPush b) bd) o) :
    M.Ret (O.legSet env) (fun a b => Model.interp ((O.pushS env a).boxPush b) bd) o := by
  refine M.Ret_conv hS hA ?_
  obtain ⟨⟨i⟩, h₂⟩ := h
  cases O with
  | nec => exact ⟨⟨⟨i, trivial⟩⟩, fun a => h₂ a.1⟩
  | pos y hy => exact ⟨⟨i⟩, h₂⟩

/-- A carrier term's data at its leg is its interpretation's (`Model.carrierData`). -/
theorem isCarrierData {w : M.frame.W} (env : M.Env Γ w) (O : OutLeg Γ) {A : VarType}
    {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) :
    M.IsCarrierData (O.legSet env) (fun a b => Model.interp ((O.pushS env a).boxPush b) bd) := by
  cases O with
  | nec =>
      refine ⟨.nec, Model.interp env (Term.boxtm (Term.boxtm bd)), ?_⟩
      refine Sigma.ext rfl (heq_of_eq (funext fun a => funext fun b => ?_))
      change M.necEval (M.necEval (Model.interp env (Term.boxtm (Term.boxtm bd)) :
        M.frame.Nec (.VTypeBox A) w) a.1) b = _
      rw [Model.box_beta env (Term.boxtm bd) a.1, Model.box_beta (env.boxPush a.1) bd]
      rfl
  | pos y hy =>
      refine ⟨.pos, Model.interp env (Term.diatm y hy (Term.boxtm bd)), ?_⟩
      dsimp only [Model.carrierData]
      rw [Model.dia_beta env hy hy.choose_spec (Term.boxtm bd)]
      refine Sigma.ext rfl (heq_of_eq (funext fun a => funext fun b => ?_))
      exact Model.box_beta (env.diaPush y hy.choose_spec a) bd b

/-- A true `Back` atom makes the round trip over its leg. -/
theorem sat_back_rt {d : ℕ} (hS : ModalSys.BStrong = true) {w : M.frame.W} (env : M.Env Γ w)
    (O : OutLeg Γ) {A : VarType} {a₀ : Ann A}
    (bd : Term σ O.view.boxIn A a₀) {a : Ann A} (t : Term σ Γ A a)
    (hb : M.sat env (O.back hS bd t : WFF σ Γ d)) :
    Model.RoundTrip (O.acc env) (fun i b => Model.interp ((O.push env i).boxPush b) bd)
      (Model.interp env t) :=
  roundTrip_of_ret hS env O bd ((sat_back hS env O bd t).mp hb)

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
  exact (OutLeg.sat_back_rt hS env O bd t hb).counit hM ψ
    ⟨i, fun b => (sat_holeRead (Ctx.noProjLast_boxIn _) _ bd ψ).mp (hi b)⟩

include hnp hM in
theorem sat_back_unit (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1)
    (hb : M.sat env (O.back hS bd t : WFF σ Γ 0)) (hψ : M.sat env (WFF.holeRead t ψ)) :
    M.sat env (O.box (WFF.box (WFF.holeRead bd ψ).neg).neg) := by
  refine (OutLeg.sat_box env O _).mpr fun i hall => ?_
  obtain ⟨b, hb'⟩ := (OutLeg.sat_back_rt hS env O bd t hb).unit hM ψ
    ((sat_holeRead hnp env t ψ).mp hψ) i
  exact hall b ((sat_holeRead (Ctx.noProjLast_boxIn _) _ bd ψ).mpr hb')

omit [Γ.NoSlots] in
theorem sat_back_ne (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) (hb : M.sat env (O.back hS bd t : WFF σ Γ 0)) :
    M.sat env (O.dia (.top : WFF σ O.view 0)) := by
  obtain ⟨i⟩ := (OutLeg.sat_back_rt hS env O bd t hb).ne
  exact (OutLeg.sat_dia env O _).mpr ⟨i, trivial⟩

include hnp hM in
theorem sat_back_beta (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) {B : VarType} {b : Ann B}
    (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b)
    (hb : M.sat env (O.back hS bd t : WFF σ Γ 0)) :
    M.sat env (O.back hS (Term.holeRead bd s) (Term.holeRead t s) : WFF σ Γ 0) := by
  rw [OutLeg.sat_back] at hb ⊢
  have hval : (fun (i : O.legSet env) (b : M.frame.Acc i.1.1) =>
      interp ((O.pushS env i).boxPush b) (Term.holeRead bd s)) =
      fun i b => M.holeVal s (interp ((O.pushS env i).boxPush b) bd) := by
    funext i b
    exact interp_holeRead (Ctx.noProjLast_boxIn _) _ bd s
  rw [hval, interp_holeRead hnp env t s]
  exact (hM.ret hS).map s hb

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
  exact (hM.ret hS).pair (OutLeg.isCarrierData env O bd) (OutLeg.isCarrierData env O bd') hb hb'

omit [Γ.NoSlots] in
theorem sat_back_eq (hS : ModalSys.BStrong = true) (L : BLeg) {A : VarType}
    {b : Ann (L.carrier A)} (s : Term σ Γ (L.carrier A) b) {a : Ann A}
    (t t' : Term σ Γ A a) (hb : M.sat env (WFF.back hS L s t : WFF σ Γ 0))
    (he : M.sat env (eqRec A t t' : WFF σ Γ 0)) :
    M.sat env (WFF.back hS L s t' : WFF σ Γ 0) := by
  change M.Backs L (interp env s) (interp env t')
  rw [← (sat_eqRec env A t t').mp he]
  exact hb

omit [Γ.NoSlots] in
/-- **Leibniz for the carrier**: equal carriers are one object, so they come back alike. -/
theorem sat_back_eqC (hS : ModalSys.BStrong = true) (L : BLeg) {A : VarType}
    {b : Ann (L.carrier A)} (s s' : Term σ Γ (L.carrier A) b) {a : Ann A}
    (t : Term σ Γ A a) (hb : M.sat env (WFF.back hS L s t : WFF σ Γ 0))
    (he : M.sat env (eqRec (L.carrier A) s s' : WFF σ Γ 0)) :
    M.sat env (WFF.back hS L s' t : WFF σ Γ 0) := by
  change M.Backs L (interp env s') (interp env t)
  rw [← (sat_eqRec env (L.carrier A) s s').mp he]
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
  have hown := (OutLeg.sat_back_rt hS env .nec bd t hb).own hT hS
  rw [sat_instantiate env hnp] at hφ ⊢
  rw [interp_collapse (Env.collapseAgree_self hT env),
    interp_collapse (Env.collapseAgree_self hT (env.boxPush (M.frame.reflAcc hT w)))]
  exact (hM.inv hfin hnp env φ _ _ hown).mpr hφ

include hnp hfin hM in
/-- ⭐The own arrow along `◇_y` (T): with the identity in `y`'s extent, both the value and the
    `Here` atom's term are indistinguishable from the carrier's body read twice there. -/
theorem sat_back_hereX (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true) (y : VarSymb)
    (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)) {A : VarType} {a₀ : Ann A}
    (bd : Term σ (Γ.diaIn y).boxIn A a₀) {a : Ann A} (t : Term σ Γ A a) {a' : Ann A}
    (t₀ : Term σ Γ A a') (φ : WFF σ (Γ.insert (.bnd 0) A) 1)
    (hb : M.sat env ((OutLeg.pos y hy : OutLeg Γ).back hS bd t : WFF σ Γ 0))
    (hh : M.sat env (WFF.here hT
      (Term.diatm y hy (Term.collapse (Ctx.collapses_boxIn_self hT (Γ.diaIn y)) bd)) t₀ :
        WFF σ Γ 0))
    (hφ : M.sat env (WFF.instantiate Ctx.NoSlots.slots t φ)) :
    M.sat env (WFF.instantiate Ctx.NoSlots.slots t₀ φ) := by
  obtain ⟨hm, hval⟩ := (sat_here_diatm hT env hy hy.choose_spec t₀ _).mp hh
  rw [interp_collapse (Env.collapseAgree_self hT _)] at hval
  obtain ⟨r, hr⟩ := (OutLeg.sat_back_rt hS env (.pos y hy) bd t hb).2 ⟨M.frame.reflAcc hT w, hm⟩
  obtain rfl : r = M.frame.refl hT w := @Subsingleton.elim _ (M.frame.homeUnique hS) _ _
  rw [sat_instantiate env hnp] at hφ ⊢
  exact (hM.inv hfin hnp env φ _ _ hval).mp ((hM.inv hfin hnp env φ _ _ hr).mpr hφ)

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
    {A B : VarType} {b : Ann B}
    (X : Term σ (V.insert (.bnd 0) A) B b)
    (Φ : WFF σ (V.insert (.bnd 0) B) 1) (d : M.frame.Dom A w) :
    M.sat (env.extend (.bnd 0) d) (WFF.bodyRepl X Φ) ↔
      M.sat (env.extend (.bnd 0) (interp (env.extend (.bnd 0) d) X)) Φ := by
  unfold WFF.bodyRepl
  rw [sat_subst _ _ _ _ _ (hnp.insert _ _)]
  refine iff_of_eq (congrArg (fun E => M.sat E Φ) ?_)
  funext v U hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    have hTU : B = U := by simpa [Ctx.insert] using hv
    subst hTU
    exact (entryVal_congr _
      (show ((Subst.idS σ _).set (.bnd 0) (.tm X)) (.root (.bnd 0)) = .tm X from if_pos rfl)
      _ rfl).trans (Env.extend_root _ (.bnd 0) _ hv).symm
  · have hv' : V v = some U := by simpa [Ctx.insert, hvr] using hv
    have hlp := hnp v U hv'
    have hE : (V.insert (.bnd 0) A) v = some U := body_le _ v U hv'
    refine (entryVal_congr _
      (show ((Subst.idS σ _).set (.bnd 0) (.tm X)) v = .ren v from if_neg hvr) _
      ((Ctx.ref_nonproj _ hlp).trans hE)).trans ?_
    refine (Env.ref_of_nonproj _ hlp _ hE).trans ?_
    rw [Env.extend_ne env (.bnd 0) d hE hvr hv', Env.extend_ne env (.bnd 0) _ hv hvr hv']

/-- ⭐Splitting a paired item: the body holds of `e` exactly when the old body holds of its two
    components. -/
theorem sat_bodySplit (hnp : V.NoProjLast) {w : M.frame.W} (env : M.Env V w)
    {A B C : VarType} {b₀ : Ann A} {b₁ : Ann B}
    (X₀ : Term σ (V.insert (.bnd 0) C) A b₀)
    (X₁ : Term σ (V.insert (.bnd 0) C) B b₁)
    (Φ : WFF σ ((V.insert (.bnd 0) A).insert (.bnd 1) B) 2)
    (e : M.frame.Dom C w) :
    M.sat (env.extend (.bnd 0) e) (WFF.bodySplit X₀ X₁ Φ) ↔
      M.sat ((env.extend (.bnd 0) (interp (env.extend (.bnd 0) e) X₀)).extend
        (.bnd 1) (interp (env.extend (.bnd 0) e) X₁)) Φ := by
  unfold WFF.bodySplit
  rw [sat_subst _ _ _ _ _ ((hnp.insert _ _).insert _ _)]
  refine iff_of_eq (congrArg (fun E => M.sat E Φ) ?_)
  funext v U hv
  by_cases hv1 : v = .root (.bnd 1)
  · subst hv1
    have hTU : B = U := by simpa [Ctx.insert] using hv
    subst hTU
    exact (entryVal_congr _
      (show (((Subst.idS σ _).set (.bnd 0) (.tm X₀)).set (.bnd 1) (.tm X₁)) (.root (.bnd 1)) =
        .tm X₁ from Subst.set_root _ _ _) _ rfl).trans
      (Env.extend_root _ (.bnd 1) _ hv).symm
  · by_cases hv0 : v = .root (.bnd 0)
    · subst hv0
      have hv0' : (V.insert (.bnd 0) A) (.root (.bnd 0)) = some U := by
        simpa [Ctx.insert, hv1] using hv
      have hTU : A = U := by simpa [Ctx.insert] using hv0'
      subst hTU
      refine (entryVal_congr _
        (show (((Subst.idS σ _).set (.bnd 0) (.tm X₀)).set (.bnd 1) (.tm X₁)) (.root (.bnd 0)) =
          .tm X₀ from (Subst.set_ne _ _ hv1).trans (Subst.set_root _ _ _)) _ rfl).trans ?_
      rw [Env.extend_ne _ (.bnd 1) _ hv hv1 hv0', Env.extend_root _ (.bnd 0) _ hv0']
      rfl
    · have hv' : V v = some U := by simpa [Ctx.insert, hv0, hv1] using hv
      have hv0' : (V.insert (.bnd 0) A) v = some U := by
        simpa [Ctx.insert, hv1] using hv
      have hlp := hnp v U hv'
      have hE : (V.insert (.bnd 0) C) v = some U := body_le _ v U hv'
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

/-- ⭐A returning possibility along the leg: an arrow of the leg, a necessary object at its far
    end with the body, and a way home along which the object comes back as the value. -/
theorem sat_retS {d : ℕ} (hS : ModalSys.BStrong = true) {w : M.frame.W} (env : M.Env Γ w) :
    (O : OutLeg Γ) → (S : RShape) → {a : Ann S.flat} → (t : Term σ Γ S.flat a) →
    (Φ : WFF σ (O.view.insert (.bnd d) S.ty) (d + 1)) →
    (M.sat env (O.retS hS S t Φ) ↔ ∃ (i : O.Arr env) (e : M.frame.Dom S.ty (O.acc env i).1),
      M.sat ((O.push env i).extend (.bnd d) e) Φ ∧
        ∃ r : M.frame.R (O.acc env i).1 w, M.ComesBack S e r (Model.interp env t))
  | .nec, _, _, _, _ => Iff.rfl
  | .pos y hy, _, _, _, _ => by
      constructor
      · rintro ⟨Y, h, a, e, hs, hr⟩
        have hY : Y = hy.choose := by
          have e' := h.symm.trans hy.choose_spec
          simp only [Option.some.injEq, VarType.VTypeDia.injEq] at e'
          exact e'
        subst hY
        exact ⟨a, e, hs, hr⟩
      · rintro ⟨a, e, hs, hr⟩
        exact ⟨_, hy.choose_spec, a, e, hs, hr⟩

theorem sat_ret {d : ℕ} (hS : ModalSys.BStrong = true) {w : M.frame.W} (env : M.Env Γ w) :
    (O : OutLeg Γ) → {A : VarType} → {a : Ann A} → (t : Term σ Γ A a) →
    (Φ : WFF σ (O.view.insert (.bnd d) (.VTypeBox A)) (d + 1)) →
    (M.sat env (O.ret hS t Φ) ↔ ∃ (i : O.Arr env) (e : M.frame.Dom (.VTypeBox A) (O.acc env i).1),
      M.sat ((O.push env i).extend (.bnd d) e) Φ ∧
        ∃ r : M.frame.R (O.acc env i).1 w,
          M.Ind (M.necEval (e : M.frame.Nec A (O.acc env i).1) ⟨w, ⟨r⟩⟩) (Model.interp env t))
  | .nec, _, _, _, _ => Iff.rfl
  | .pos y hy, _, _, _, _ => by
      constructor
      · rintro ⟨Y, h, a, e, hs, hr⟩
        have hY : Y = hy.choose := by
          have e' := h.symm.trans hy.choose_spec
          simp only [Option.some.injEq, VarType.VTypeDia.injEq] at e'
          exact e'
        subst hY
        exact ⟨a, e, hs, hr⟩
      · rintro ⟨a, e, hs, hr⟩
        exact ⟨_, hy.choose_spec, a, e, hs, hr⟩

/-- A returning possibility along the leg, weakened, holds in an agreeing environment of the
    larger context when the old leg has an arrow with the body and a way home to the new value. -/
theorem sat_retS_agree {Γ' : Ctx} {h : Γ.Le Γ'} {w : M.frame.W} {env : M.Env Γ w}
    {env' : M.Env Γ' w} (hag : Model.Env.Agree h env env') (hS : ModalSys.BStrong = true)
    (O : OutLeg Γ) (S : RShape) {a : Ann S.flat} (t' : Term σ Γ' S.flat a)
    (Φ : WFF σ (O.view.insert (.bnd 0) S.ty) 1) (i : O.Arr env)
    (e : M.frame.Dom S.ty (O.acc env i).1)
    (hΦ : M.sat ((O.push env i).extend (.bnd 0) e) Φ) (r : M.frame.R (O.acc env i).1 w)
    (hr : M.ComesBack S e r (Model.interp env' t')) :
    M.sat env' ((O.mono h).retS hS S t' (WFF.mono ((O.le_view_mono h).insert (.bnd 0) _) Φ)) := by
  cases O with
  | nec =>
      exact ⟨i, e, (Model.sat_mono (Model.Env.extend_agree (Model.Env.boxPush_agree hag i)
        (.bnd 0) e) Φ).mpr hΦ, r, hr⟩
  | pos y hy =>
      have href := Model.Env.ref_agree hag y hy.choose_spec
      exact ⟨_, h.ref hy.choose_spec, ⟨i.1, by rw [← href]; exact i.2⟩, e,
        (Model.sat_mono (Model.Env.extend_agree
          (Model.Env.diaPush_agree hag hy.choose_spec i _) (.bnd 0) e) Φ).mpr hΦ, r, hr⟩

theorem sat_ret_agree {Γ' : Ctx} {h : Γ.Le Γ'} {w : M.frame.W} {env : M.Env Γ w}
    {env' : M.Env Γ' w} (hag : Model.Env.Agree h env env') (hS : ModalSys.BStrong = true)
    (O : OutLeg Γ) {A : VarType} {a : Ann A} (t' : Term σ Γ' A a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1) (i : O.Arr env)
    (e : M.frame.Dom (.VTypeBox A) (O.acc env i).1)
    (hΦ : M.sat ((O.push env i).extend (.bnd 0) e) Φ) (r : M.frame.R (O.acc env i).1 w)
    (hr : M.Ind (M.necEval (e : M.frame.Nec A (O.acc env i).1) ⟨w, ⟨r⟩⟩)
      (Model.interp env' t')) :
    M.sat env' ((O.mono h).ret hS t' (WFF.mono ((O.le_view_mono h).insert (.bnd 0) _) Φ)) := by
  cases O with
  | nec =>
      exact ⟨i, e, (Model.sat_mono (Model.Env.extend_agree (Model.Env.boxPush_agree hag i)
        (.bnd 0) e) Φ).mpr hΦ, r, hr⟩
  | pos y hy =>
      have href := Model.Env.ref_agree hag y hy.choose_spec
      exact ⟨_, h.ref hy.choose_spec, ⟨i.1, by rw [← href]; exact i.2⟩, e,
        (Model.sat_mono (Model.Env.extend_agree
          (Model.Env.diaPush_agree hag hy.choose_spec i _) (.bnd 0) e) Φ).mpr hΦ, r, hr⟩

/-- A lifted body holds at the far end of an arrow of the leg as the body does in the `□` view
    there. -/
theorem sat_lift {d : ℕ} {w : M.frame.W} (env : M.Env Γ w) :
    (O : OutLeg Γ) → (i : O.Arr env) → {T : VarType} → (o : M.frame.Dom T (O.acc env i).1) →
    (φ : WFF σ (Γ.boxIn.insert (.bnd d) T) (d + 1)) →
    (M.sat ((O.push env i).extend (.bnd d) o) (O.lift φ) ↔
      M.sat ((env.boxPush (O.acc env i)).extend (.bnd d) o) φ)
  | .nec, _, _, _, _ => Iff.rfl
  | .pos y hy, i, _, o, φ =>
      Model.sat_mono (Model.Env.extend_agree (agree_push env (.pos y hy) i) (.bnd d) o) φ

end OutLeg

/-! ## The returning possibility's rules are sound -/

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ} {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W}
  (env : M.Env Γ w) (hnp : Γ.NoProjLast) (hfin : Γ.Tame) (hM : M.IndInvariant)

omit [Γ.NoSlots] in
/-- What `ret_new` hands its subproof: the fresh value is the returning possibility's. -/
theorem sat_ret_fresh (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1) (c : ℕ) (hc : Γ.RootFresh (.free c))
    (o : M.frame.Dom A w) (i : O.Arr env) (e : M.frame.Dom (.VTypeBox A) (O.acc env i).1)
    (hΦ : M.sat ((O.push env i).extend (.bnd 0) e) Φ) (r : M.frame.R (O.acc env i).1 w)
    (hr : M.Ind (M.necEval (e : M.frame.Nec A (O.acc env i).1) ⟨w, ⟨r⟩⟩) o) :
    M.sat (env.extend (.free c) o) ((O.mono (Ctx.le_insert hc.root A)).ret hS
      (Term.eta (.root (.free c)) A (Ctx.ref_insert_root Γ (.free c) A))
      (WFF.mono ((O.le_view_mono (Ctx.le_insert hc.root A)).insert (.bnd 0) _) Φ)) := by
  have hslot : (env.extend (.free c) o).ref (.root (.free c)) (Ctx.ref_insert_root Γ (.free c) A) =
      o := Env.extend_root env (.free c) o (Ctx.ref_insert_root Γ (.free c) A)
  refine OutLeg.sat_ret_agree (Env.agree_extend env hc.root o) hS O _ Φ i e hΦ r ?_
  change M.Ind _ (interp (env.extend (.free c) o) (Term.eta _ _ _))
  rw [interp_eta, hslot]
  exact hr

omit [Γ.NoSlots] in
/-- `back_ret`'s body holds at the far end of every arrow, of the carrier's object. -/
theorem sat_backRetBody (hs : Γ.SlotsFrom 0) (O : OutLeg Γ) {A : VarType}
    (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) (i : O.Arr env) :
    M.sat ((O.push env i).extend (.bnd 0) (interp (O.push env i) (Term.boxtm bd)))
      (WFF.backRetBody (OutLeg.slotsFrom hs O) hA bd) := by
  unfold WFF.backRetBody
  have hslot : ((O.push env i).extend (.bnd 0) (interp (O.push env i) (Term.boxtm bd))).ref
      (.root (.bnd 0)) (Ctx.ref_insert_root O.view (.bnd 0) (.VTypeBox A)) =
      interp (O.push env i) (Term.boxtm bd) :=
    Env.extend_root (O.push env i) (.bnd 0) (interp (O.push env i) (Term.boxtm bd))
      (Ctx.ref_insert_root O.view (.bnd 0) (.VTypeBox A))
  rw [sat_eqRec, interp_castAnn,
    interp_mono (Env.agree_extend _ (OutLeg.slotsFrom hs O).root _), interp_eta, hslot]

/-- ⭐**`back_ret` is sound**: every arrow of the out leg has a way home (weak B), along which
    the carrier's object returns some value; that value is one of the returning possibility's, so
    the subproof makes it `t`. -/
theorem sat_back_ret (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true) (O : OutLeg Γ)
    {A : VarType} (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀)
    {a : Ann A} (t : Term σ Γ A a) (c : ℕ) (hc : Γ.RootFresh (.free c))
    (hne : M.sat env (O.dia (.top : WFF σ O.view 0)))
    (hret : ∀ o : M.frame.Dom A w,
      M.sat (env.extend (.free c) o) ((O.mono (Ctx.le_insert hc.root A)).ret hS
        (Term.eta (.root (.free c)) A (Ctx.ref_insert_root Γ (.free c) A))
        (WFF.mono ((O.le_view_mono (Ctx.le_insert hc.root A)).insert (.bnd 0) _)
          (WFF.backRetBody (OutLeg.slotsFrom Ctx.NoSlots.slots O) hA bd))) →
      M.sat (env.extend (.free c) o) (eqRec A
        (Term.eta (.root (.free c)) A (Ctx.ref_insert_root Γ (.free c) A))
        (Term.castAnn hA (Term.weaken hc.root A t)) : WFF σ (Γ.insert (.free c) A) 0)) :
    M.sat env (O.back hS bd t : WFF σ Γ 0) := by
  rw [OutLeg.sat_back]
  refine OutLeg.ret_of_roundTrip hS env O hA bd ⟨?_, fun i => ?_⟩
  · obtain ⟨i, _⟩ := (OutLeg.sat_dia env O _).mp hne
    exact ⟨i⟩
  · obtain ⟨r⟩ := M.frame.symm hB (O.acc env i).2.down
    refine ⟨r, ?_⟩
    have hval : M.necEval (interp (O.push env i) (Term.boxtm bd) : M.frame.Nec A (O.acc env i).1)
        ⟨w, ⟨r⟩⟩ = interp ((O.push env i).boxPush ⟨w, ⟨r⟩⟩) bd := box_beta _ bd _
    have h := hret _ (sat_ret_fresh env hS O _ c hc _ i _
      (sat_backRetBody env Ctx.NoSlots.slots O hA bd i) r (by rw [hval]; exact M.Ind_refl _))
    have hslot : (env.extend (.free c) (interp ((O.push env i).boxPush ⟨w, ⟨r⟩⟩) bd)).ref
        (.root (.free c)) (Ctx.ref_insert_root Γ (.free c) A) =
        interp ((O.push env i).boxPush ⟨w, ⟨r⟩⟩) bd :=
      Env.extend_root env (.free c)
        (interp ((O.push env i).boxPush ⟨w, ⟨r⟩⟩) bd) (Ctx.ref_insert_root Γ (.free c) A)
    rw [sat_eqRec, interp_castAnn, Term.weaken, interp_mono (Env.agree_extend env hc.root _),
      interp_eta, hslot] at h
    change M.Ind (interp ((O.push env i).boxPush ⟨w, ⟨r⟩⟩) bd) _
    rw [h]
    exact M.Ind_refl _

include hM in
theorem sat_ret_counit (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    {a : Ann A} (t : Term σ Γ A a) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1)
    (h : M.sat env (O.ret hS t (O.lift (WFF.box (WFF.holeAt
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert (.VTypeBox A)).boxIn
      (Term.eta (VarSymb.root (.bnd 0)).inner A
        (Ctx.ref_inner (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox A)))) ψ))) :
      WFF σ Γ 0)) :
    M.holeSat ψ (interp env t) := by
  obtain ⟨i, e, hbox, r, hr⟩ := (OutLeg.sat_ret hS env O t _).mp h
  rw [OutLeg.sat_lift] at hbox
  refine ret_counit hM ψ ⟨O.acc env i, e, fun b => ?_, r, hr⟩
  have hb := (sat_holeAt _ _ _ ψ).mp (hbox b)
  rwa [interp_eta, Env.ref_inner _ b (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox A)),
    show ((env.boxPush (O.acc env i)).extend (.bnd 0) e).ref (.root (.bnd 0))
      (Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox A)) = e from
      Env.extend_root _ (.bnd 0) e _] at hb

include hM in
/-- ⭐**Counit with a carrier** (§11.14): the object out there and the carrier's image there
    come home along the one way back, as the returning possibility's value and the carrier's —
    `Ind` is preserved by pairing. -/
theorem sat_ret_counitC (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A C : VarType}
    {a : Ann A} (y : Term σ Γ A a) {c₀ : Ann C} (bd : Term σ O.view.boxIn C c₀) {c : Ann C}
    (t : Term σ Γ C c) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A C)) 1)
    (hret : M.sat env (O.ret hS y (WFF.box (WFF.holeAt
      ((Ctx.NoSlots.slots (Γ := O.view)).insert (.VTypeBox A)).boxIn
      (Term.pair (Term.eta (VarSymb.root (.bnd 0)).inner A
          (Ctx.ref_inner (Ctx.ref_insert_root O.view (.bnd 0) (.VTypeBox A))))
        (Term.mono ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := O.view)).root (.VTypeBox A)).boxIn)
          bd)) ψ)) : WFF σ Γ 0))
    (hb : M.sat env (O.back hS bd t : WFF σ Γ 0)) :
    M.holeSat ψ ((interp env y, interp env t) : M.frame.Dom (.VTypeProd A C) w) := by
  obtain ⟨i, e, hbox, r, hr⟩ := (OutLeg.sat_ret hS env O y _).mp hret
  obtain ⟨_, hall⟩ := OutLeg.sat_back_rt hS env O bd t hb
  obtain ⟨r', hr'⟩ := hall i
  obtain rfl : r' = r := @Subsingleton.elim _ (M.frame.homeUnique hS) r' r
  have hag := Env.boxPush_agree (Env.agree_extend (O.push env i)
    (Ctx.NoSlots.slots (Γ := O.view)).root e) ⟨w, ⟨r'⟩⟩
  have hb' := (sat_holeAt _ _ _ ψ).mp (hbox ⟨w, ⟨r'⟩⟩)
  change M.holeSat ψ ((interp (((O.push env i).extend (.bnd 0) e).boxPush ⟨w, ⟨r'⟩⟩)
      (Term.eta (VarSymb.root (.bnd 0)).inner A
        (Ctx.ref_inner (Ctx.ref_insert_root O.view (.bnd 0) (.VTypeBox A)))),
    interp (((O.push env i).extend (.bnd 0) e).boxPush ⟨w, ⟨r'⟩⟩)
      (Term.mono ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := O.view)).root (.VTypeBox A)).boxIn)
        bd)) : M.frame.Dom (.VTypeProd A C) w) at hb'
  rw [interp_eta, Env.ref_inner _ _ (Ctx.ref_insert_root O.view (.bnd 0) (.VTypeBox A)),
    show ((O.push env i).extend (.bnd 0) e).ref (.root (.bnd 0))
      (Ctx.ref_insert_root O.view (.bnd 0) (.VTypeBox A)) = e from
      Env.extend_root _ (.bnd 0) e _, interp_mono hag bd] at hb'
  exact (holeSat_ind hM ψ (hM.pair hr hr')).mp hb'

omit [Γ.NoSlots] in
/-- Under T, the value here of a necessary object is its reading at the own arrow. -/
theorem Env.ref_here {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) (hT : ModalSys.T = true)
    {u : VarSymb} {A : VarType} (hu : Δ.ref u = some (.VTypeBox A))
    (h : Δ.ref (.step u .here) = some A) :
    env.ref (.step u .here) h =
      M.necEval (env.ref u hu : M.frame.Nec A w) (M.frame.reflAcc hT w) := by
  have hhs : Step.here.isProj = true := rfl
  rw [Env.ref, dif_pos hhs]
  split
  · rename_i U hU
    have hUU : U = .VTypeBox A := Option.some.inj (hU.symm.trans hu)
    subst hUU
    rfl
  · rename_i hU
    exact absurd (hU.symm.trans hu) (by simp)

omit [Γ.NoSlots] in
/-- A companion comes back as its own contents read along the way home. -/
theorem compBack_ref (hT : ModalSys.T = true) {Δ : Ctx} {v w : M.frame.W} (env : M.Env Δ v)
    (r : M.frame.R v w) (p : List Step) : ∀ {u : VarSymb} {A : VarType}
    (hu : Δ.ref u = some A)
    (hp : Δ.ref (u.ext p) = some (.VTypeBox ((A.compAt p).getD .VTypeOne))),
    (A.compAt p).isSome = true →
    M.compBack A p (env.ref u hu) r (M.necEval (env.ref (u.ext p) hp : M.frame.Nec _ v)
      ⟨w, ⟨r⟩⟩) := by
  induction p with
  | nil =>
      intro u A hu hp hs
      cases A <;> simp only [VarType.compAt, Option.isSome_none, Bool.false_eq_true] at hs
      exact M.Ind_refl _
  | cons s p ih =>
      intro u A hu hp hs
      cases A <;> cases s <;>
        simp only [VarType.compAt, Option.isSome_none, Bool.false_eq_true] at hs
      · have h := ih (Ctx.ref_fst_of hu) hp hs
        rw [Env.ref_fst env hu] at h
        exact h
      · have h := ih (Ctx.ref_snd_of hu) hp hs
        rw [Env.ref_snd env hu] at h
        exact h
      · rename_i C
        have h := ih (Ctx.ref_here_of hT hu) hp hs
        rw [Env.ref_here env hT hu] at h
        have e : M.compBack (.VTypeBox C) (.here :: p) (env.ref u hu) r
            (M.necEval (env.ref (u.ext (.here :: p)) hp : M.frame.Nec _ v) ⟨w, ⟨r⟩⟩) =
            M.compBack C p (M.necEval (env.ref u hu : M.frame.Nec C v) (M.frame.reflAcc hT v)) r
              (M.necEval (env.ref (u.ext (.here :: p)) hp : M.frame.Nec _ v) ⟨w, ⟨r⟩⟩) :=
          dif_pos hT
        rw [e]
        exact h

omit [Γ.NoSlots] in
/-- A companion comes back as `o` exactly when its own reading along the way home is `Ind` to
    `o`. -/
theorem compBack_iff_ind (hT : ModalSys.T = true) {Δ : Ctx} {v w : M.frame.W} (env : M.Env Δ v)
    (r : M.frame.R v w) (p : List Step) : ∀ {u : VarSymb} {A : VarType}
    (hu : Δ.ref u = some A)
    (hp : Δ.ref (u.ext p) = some (.VTypeBox ((A.compAt p).getD .VTypeOne))),
    (A.compAt p).isSome = true → ∀ o : M.frame.Dom ((A.compAt p).getD .VTypeOne) w,
    (M.compBack A p (env.ref u hu) r o ↔
      M.Ind (M.necEval (env.ref (u.ext p) hp : M.frame.Nec _ v) ⟨w, ⟨r⟩⟩) o) := by
  induction p with
  | nil =>
      intro u A hu hp hs o
      cases A <;> simp only [VarType.compAt, Option.isSome_none, Bool.false_eq_true] at hs
      exact Iff.rfl
  | cons s p ih =>
      intro u A hu hp hs o
      cases A <;> cases s <;>
        simp only [VarType.compAt, Option.isSome_none, Bool.false_eq_true] at hs
      · have h := ih (Ctx.ref_fst_of hu) hp hs o
        rw [Env.ref_fst env hu] at h
        exact h
      · have h := ih (Ctx.ref_snd_of hu) hp hs o
        rw [Env.ref_snd env hu] at h
        exact h
      · rename_i C
        have h := ih (Ctx.ref_here_of hT hu) hp hs o
        rw [Env.ref_here env hT hu] at h
        exact (iff_of_eq (dif_pos hT)).trans h

omit [Γ.NoSlots] in
/-- A value with companions that comes back gives each companion's component. -/
theorem compsBack_at (hT : ModalSys.T = true) {A : VarType} {v w : M.frame.W}
    (e : M.frame.Dom (.VTypeBox A) v) (r : M.frame.R v w) :
    ∀ (cs : List (List Step)) {Δ' : Ctx} (env' : M.Env Δ' w) {a : VarSymb}
      (ha : Δ'.ref a = some (A.compsFlat cs)), M.compsBack A cs e r (env'.ref a ha) →
      ∀ q, q ∈ cs → ∀ h, M.compBack (.VTypeBox A) (.here :: q) e r
        (env'.ref (a.ext (compsIdx cs q)) h)
  | [], _, _, _, _, _, _, hq, _ => absurd hq List.not_mem_nil
  | p :: ps, Δ', env', a, ha, hb, q, hq, h => by
      by_cases hqp : q = p
      · subst hqp
        have key : ∀ (a' : VarSymb) (h' : Δ'.ref a' = some ((A.compAt q).getD .VTypeOne)),
            a' = .step a .snd → env'.ref a' h' = (env'.ref a ha).2 := by
          rintro _ h' rfl
          exact Env.ref_snd env' ha h'
        rw [key _ h (by simp [compsIdx, VarSymb.ext])]
        exact (iff_of_eq (dif_pos hT)).mp hb.2
      · have hq' : q ∈ ps := (List.mem_cons.mp hq).resolve_left hqp
        have ha' := Ctx.ref_fst_of ha
        have key : ∀ (h' : Δ'.ref ((VarSymb.step a .fst).ext (compsIdx ps q)) =
              some ((A.compAt q).getD .VTypeOne)) (a' : VarSymb)
            (h'' : Δ'.ref a' = some ((A.compAt q).getD .VTypeOne)),
            a' = (VarSymb.step a .fst).ext (compsIdx ps q) → env'.ref a' h'' = env'.ref _ h' := by
          rintro _ _ _ rfl
          rfl
        rw [key (Ctx.ref_compsIdx ps q hq' ha') _ h (by simp [compsIdx, hqp, VarSymb.ext])]
        refine compsBack_at hT e r ps env' ha' ?_ q hq' _
        rw [Env.ref_fst env' ha ha']
        exact hb.1

include hM in
omit [Γ.NoSlots] in
/-- Two trees of items are `Ind` when their leaves are. -/
theorem bcTree_ind : ∀ (Z : VarType) {Γ₁ Γ₂ : Ctx} {w : M.frame.W} (env₁ : M.Env Γ₁ w)
    (env₂ : M.Env Γ₂ w)
    (get₁ : ∀ q, q ∈ Z.hereChains → Σ c, Term σ Γ₁ ((Z.compAt q).getD .VTypeOne) c)
    (get₂ : ∀ q, q ∈ Z.hereChains → Σ c, Term σ Γ₂ ((Z.compAt q).getD .VTypeOne) c),
    (∀ q hq, M.Ind (interp env₁ (get₁ q hq).2) (interp env₂ (get₂ q hq).2)) →
    M.Ind (interp env₁ (bcTree Z get₁).2) (interp env₂ (bcTree Z get₂).2)
  | .VTypeBox C, _, _, _, env₁, env₂, _, _, h =>
      hM.pair (h [] _) (bcTree_ind C env₁ env₂ _ _ fun q _ => h (.here :: q) _)
  | .VTypeProd X Y, _, _, _, env₁, env₂, _, _, h =>
      hM.pair (bcTree_ind X env₁ env₂ _ _ fun q _ => h (.fst :: q) _)
        (bcTree_ind Y env₁ env₂ _ _ fun q _ => h (.snd :: q) _)
  | .Var, _, _, _, _, _, _, _, _ => M.Ind_refl _
  | .VTypeOne, _, _, _, _, _, _, _, _ => M.Ind_refl _
  | .VTypeDia _, _, _, _, _, _, _, _, _ => M.Ind_refl _

omit [Γ.NoSlots] in
/-- ⭐**A tuple's companion comes back as its root's** (T): along a companion path of the tree of
    `u`'s items read at the identity, coming back is coming back along the path it decodes to
    (`bcDec`).  The value is the same entry of `env'`, typed both ways. -/
theorem compBack_itemsTree (hT : ModalSys.T = true) {Δ : Ctx} {v w : M.frame.W}
    (env : M.Env Δ v) (r : M.frame.R v w) : ∀ (R : VarType) (u : VarSymb) (hu : Δ.ref u = some R)
    (q' : List Step), q' ∈ (R.bcB true).hereChains → ∀ {Δ' : Ctx} (env' : M.Env Δ' w)
    (a : VarSymb) (h₁ : Δ'.ref a = some (((R.bcB true).compAt q').getD .VTypeOne))
    (h₂ : Δ'.ref a = some ((R.compAt (R.bcDec q')).getD .VTypeOne)),
    (M.compBack (R.bcB true) q'
        (interp (env.boxPush (M.frame.reflAcc hT v)) (itemsTree hT u R hu).2) r
        (env'.ref a h₁) ↔
      M.compBack R (R.bcDec q') (env.ref u hu) r (env'.ref a h₂))
  | .VTypeBox C, u, hu, q', hq', _, env', a, h₁, h₂ => by
      rcases List.mem_append.mp hq' with hq | hq
      · obtain ⟨q, -, rfl⟩ := List.mem_map.mp hq
        have hin := Ctx.ref_inner (Γ := Δ) hu
        change M.compBack C q (interp (env.boxPush (M.frame.reflAcc hT v))
            (Term.eta (σ := σ) u.inner C _)) r (env'.ref a h₁) ↔
          (if hT' : ModalSys.T = true then M.compBack C q
            (M.necEval (env.ref u hu : M.frame.Nec C v) (M.frame.reflAcc hT' v)) r
            (env'.ref a h₂) else True)
        rw [dif_pos hT, interp_eta, Env.ref_inner env _ hu]
      · obtain ⟨q, hq₀, rfl⟩ := List.mem_map.mp hq
        have hu' := Ctx.ref_here_of hT hu
        refine (compBack_itemsTree hT env r C (.step u .here) hu' q hq₀ env' a h₁ h₂).trans ?_
        rw [Env.ref_here env hT hu hu']
        change _ ↔ (if hT' : ModalSys.T = true then M.compBack C (C.bcDec q)
          (M.necEval (env.ref u hu : M.frame.Nec C v) (M.frame.reflAcc hT' v)) r (env'.ref a h₂)
          else True)
        rw [dif_pos hT]
  | .VTypeProd X Y, u, hu, q', hq', _, env', a, h₁, h₂ => by
      rcases List.mem_append.mp hq' with hq | hq
      · obtain ⟨q, hq₀, rfl⟩ := List.mem_map.mp hq
        refine (compBack_itemsTree hT env r X (.step u .fst) (Ctx.ref_fst_of hu) q hq₀ env' a h₁
          h₂).trans ?_
        rw [Env.ref_fst env hu]
        exact Iff.rfl
      · obtain ⟨q, hq₀, rfl⟩ := List.mem_map.mp hq
        refine (compBack_itemsTree hT env r Y (.step u .snd) (Ctx.ref_snd_of hu) q hq₀ env' a h₁
          h₂).trans ?_
        rw [Env.ref_snd env hu]
        exact Iff.rfl
  | .Var, _, _, _, hq', _, _, _, _, _ => by cases hq'
  | .VTypeOne, _, _, _, hq', _, _, _, _, _ => by cases hq'
  | .VTypeDia _, _, _, _, hq', _, _, _, _, _ => by cases hq'

omit [Γ.NoSlots] in
theorem necEval_unboxtm {Δ : Ctx} {v : M.frame.W} (env : M.Env Δ v) {A : VarType}
    {a : Ann (.VTypeBox A)} (x : Term σ Δ (.VTypeBox A) a) (ac : M.frame.Acc v) :
    interp (env.boxPush ac) (Term.unboxtm x).2 = M.necEval (interp env x : M.frame.Nec A v) ac := by
  cases x with
  | boxtm t => exact (box_beta env t ac).symm

omit [Γ.NoSlots] in
/-- `□sb` and its companions come back, along the arrow out, as their contents read there
    (`compsVal`). -/
theorem compsBack_compsVal {Δ : Ctx} {v : M.frame.W} (env : M.Env Δ v) {A : VarType}
    {a₀ : Ann A} (sb : Term σ Δ.boxIn A a₀) (ac : M.frame.Acc v) :
    ∀ (cs : List (List Step)) (h : A.CompOk cs),
      M.compsBack A cs (interp env (Term.boxtm sb)) ac.2.down
        (interp (env.boxPush ac) (compsVal sb cs h).2)
  | [], _ => by
      change M.Ind (M.necEval _ _) _
      rw [box_beta]
      exact M.Ind_refl _
  | p :: ps, h => by
      obtain ⟨hT, hall⟩ := h.resolve_left (List.cons_ne_nil _ _)
      refine ⟨compsBack_compsVal env sb ac ps h.tail, ?_⟩
      rw [dif_pos hT]
      have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox A)
      have hp := h.ref_head hu
      have e : interp (env.boxPush ac) (compVal sb p h).2 =
          M.necEval (((Env.empty v).extend (.bnd 0) (interp env (Term.boxtm sb))).ref _ hp :
            M.frame.Nec _ v) ac := by
        unfold compVal
        rw [necEval_unboxtm, interp_holeAt]
        unfold holeVal
        rw [box_beta, interp_eta, Env.ref_inner _ _ hp]
      change M.compBack (.VTypeBox A) (.here :: p) (interp env (Term.boxtm sb)) ac.2.down
        (interp (env.boxPush ac) (compVal sb p h).2)
      rw [e]
      have h2 := compBack_ref hT ((Env.empty v).extend (.bnd 0) (interp env (Term.boxtm sb)))
        ac.2.down (.here :: p) hu hp (hall p List.mem_cons_self)
      rw [show ((Env.empty v).extend (.bnd 0) (interp env (Term.boxtm sb))).ref (.root (.bnd 0)) hu
        = interp env (Term.boxtm sb) from Env.extend_root _ _ _ _] at h2
      exact h2

omit [Γ.NoSlots] in
theorem Env.Agree.trans {Γ₁ Γ₂ Γ₃ : Ctx} {h₁ : Γ₁.Le Γ₂} {h₂ : Γ₂.Le Γ₃} {v : M.frame.W}
    {env₁ : M.Env Γ₁ v} {env₂ : M.Env Γ₂ v} {env₃ : M.Env Γ₃ v} (a₁ : Env.Agree h₁ env₁ env₂)
    (a₂ : Env.Agree h₂ env₂ env₃) : Env.Agree (h₁.trans h₂) env₁ env₃ :=
  fun x T hx => (a₁ x T hx).trans (a₂ x T (h₁ x T hx))

include hM in
omit [Γ.NoSlots] in
/-- ⭐A value with companions read at a slot whose object comes back with them is `Ind` to the
    value it comes back as: its contents and each companion's contents, read along the way home. -/
theorem compsSlot_ind {Δ Δ' : Ctx} {u : VarSymb} {C : VarType}
    (hu : Δ.ref u = some (.VTypeBox C)) (hle : Δ.boxIn.Le Δ') {v w : M.frame.W}
    (env₁ : M.Env Δ v) (r : M.frame.R v w) (env' : M.Env Δ' w)
    (hag : Env.Agree hle (env₁.boxPush ⟨w, ⟨r⟩⟩) env') :
    ∀ (cs : List (List Step)) (h : C.CompOk cs) (o : M.frame.Dom (C.compsFlat cs) w),
      M.compsBack C cs (env₁.ref u hu) r o →
      M.Ind (interp env' (compsSlot (σ := σ) hu hle cs h).2) o
  | [], _, o, hb => by
      change M.Ind (interp env' (Term.eta (σ := σ) u.inner C _)) o
      rw [interp_eta, ← Env.ref_agree hag _ (Ctx.ref_inner hu), Env.ref_inner _ _ hu]
      exact hb
  | p :: ps, h, o, hb => by
      obtain ⟨hT, hall⟩ := h.resolve_left (List.cons_ne_nil _ _)
      have hp := h.ref_head hu
      refine hM.pair (compsSlot_ind hu hle env₁ r env' hag ps h.tail o.1 hb.1) ?_
      change M.Ind (interp env' (Term.eta (σ := σ) ((VarSymb.step u .here).ext p).inner _ _)) o.2
      rw [interp_eta, ← Env.ref_agree hag _ (Ctx.ref_inner hp), Env.ref_inner _ _ hp]
      exact (compBack_iff_ind hT env₁ r (.here :: p) hu hp (hall p List.mem_cons_self) o.2).mp
        ((iff_of_eq (dif_pos hT)).mp hb.2)

include hM in
/-- ⭐**The unit** (`ret_unit`): at the far end of the returning possibility the way home `r` is an
    arrow out, leading here, where `s` is the object; it comes back along the arrow out as `sb`'s
    value there, and `θ` holds of it and of `d₁`'s return, which is `Ind` to `y`.  No uniqueness of
    ways home is used: the arrow out is itself a way home for `r`. -/
theorem sat_ret_unitC (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {C A : VarType}
    (co : List (List Step)) (ho : C.CompOk co) {c : Ann (C.compsFlat co)}
    (y : Term σ Γ (C.compsFlat co) c) (Ψ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox C)) 1)
    {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) (cs : List (List Step)) (h : A.CompOk cs)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (C.compsFlat co) (.VTypeBox A))) 1)
    (hret : M.sat env (O.retS hS (.nec (.boxC C co ho)) y Ψ : WFF σ Γ 0))
    (hθ : M.holeSat θ ((interp env y, interp env (Term.boxtm sb)) :
      M.frame.Dom (.VTypeProd (C.compsFlat co) (.VTypeBox A)) w)) :
    M.sat env (O.retS hS (.nec (.boxC C co ho)) y
      (WFF.and Ψ (O.lift (WFF.unitBodyC hS co ho sb cs h θ))) : WFF σ Γ 0) := by
  obtain ⟨i, e, hΨ, r, hr⟩ := (OutLeg.sat_retS hS env O (.nec (.boxC C co ho)) y Ψ).mp hret
  refine (OutLeg.sat_retS hS env O (.nec (.boxC C co ho)) y _).mpr
    ⟨i, e, ⟨hΨ, (OutLeg.sat_lift env O i e _).mpr ?_⟩, r, hr⟩
  have hu := Ctx.ref_insert_root Γ.boxIn (.bnd 0) (.VTypeBox C)
  refine ⟨⟨w, ⟨r⟩⟩, interp env (Term.boxtm sb), ?_, (O.acc env i).2.down, ?_⟩
  · rw [sat_holeAt]
    have hag := Env.agree_extend (((env.boxPush (O.acc env i)).extend (.bnd 0) e).boxPush ⟨w, ⟨r⟩⟩)
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert (.VTypeBox C)).boxIn.root
      (interp env (Term.boxtm sb))
    change M.holeSat θ (interp _ _, interp _ _)
    rw [interp_eta,
      show ((((env.boxPush (O.acc env i)).extend (.bnd 0) e).boxPush ⟨w, ⟨r⟩⟩).extend (.bnd (0 + 1))
          (interp env (Term.boxtm sb))).ref (.root (.bnd 1))
          (Ctx.ref_insert_root _ (.bnd 1) _) = interp env (Term.boxtm sb) from
        Env.extend_root _ _ _ _]
    have hr' : M.compsBack C co (((env.boxPush (O.acc env i)).extend (.bnd 0) e).ref
        (.root (.bnd 0)) hu) r (interp env y) := by
      rw [show ((env.boxPush (O.acc env i)).extend (.bnd 0) e).ref (.root (.bnd 0)) hu = e from
        Env.extend_root _ (.bnd 0) e _]
      exact hr
    exact (holeSat_ind hM θ (hM.pair (compsSlot_ind hM hu _ _ r _ hag co ho _ hr')
      (M.Ind_refl _))).mpr hθ
  · dsimp only [ComesBack, NComesBack]
    rw [interp_mono
        (Env.agree_extend (env.boxPush (O.acc env i)) (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root e)]
    exact compsBack_compsVal env sb (O.acc env i) cs h

omit [Γ.NoSlots] in
theorem sat_ret_mono (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {S : RShape}
    {a : Ann S.flat} (t : Term σ Γ S.flat a) (Φ Φ' : WFF σ (O.view.insert (.bnd 0) S.ty) 1)
    (h : M.sat env (O.retS hS S t Φ : WFF σ Γ 0))
    (himp : M.sat env (O.box (WFF.all S.ty (WFF.imp Φ Φ')) : WFF σ Γ 0)) :
    M.sat env (O.retS hS S t Φ' : WFF σ Γ 0) := by
  obtain ⟨i, e, hΦ, r, hr⟩ := (OutLeg.sat_retS hS env O S t Φ).mp h
  exact (OutLeg.sat_retS hS env O S t Φ').mpr
    ⟨i, e, (OutLeg.sat_box env O _).mp himp i e hΦ, r, hr⟩

omit [Γ.NoSlots] in
theorem sat_ret_dia (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {S : RShape}
    {a : Ann S.flat} (t : Term σ Γ S.flat a) (Φ : WFF σ (O.view.insert (.bnd 0) S.ty) 1)
    (h : M.sat env (O.retS hS S t Φ : WFF σ Γ 0)) :
    M.sat env (O.dia (WFF.ex S.ty Φ)) := by
  obtain ⟨i, e, hΦ, _, _⟩ := (OutLeg.sat_retS hS env O S t Φ).mp h
  exact (OutLeg.sat_dia env O _).mpr ⟨i, e, hΦ⟩

omit [Γ.NoSlots] in
theorem sat_ret_eqS (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {S : RShape}
    {a : Ann S.flat} (t t' : Term σ Γ S.flat a) (Φ : WFF σ (O.view.insert (.bnd 0) S.ty) 1)
    (h : M.sat env (O.retS hS S t Φ : WFF σ Γ 0))
    (he : M.sat env (eqRec S.flat t t' : WFF σ Γ 0)) :
    M.sat env (O.retS hS S t' Φ : WFF σ Γ 0) := by
  obtain ⟨i, e, hΦ, r, hr⟩ := (OutLeg.sat_retS hS env O S t Φ).mp h
  exact (OutLeg.sat_retS hS env O S t' Φ).mpr
    ⟨i, e, hΦ, r, (sat_eqRec env S.flat t t').mp he ▸ hr⟩

include hnp in
theorem sat_ret_hereWC (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true) {A Y : VarType}
    {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) (cs : List (List Step)) (hcs : A.CompOk cs)
    {b : Ann (.VTypeDia Y)} (p : Term σ Γ (.VTypeDia Y) b) {c : Ann Y} (u : Term σ Γ Y c)
    (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeProd (.VTypeBox A) (.VTypeDia Y))) 1)
    (hh : M.sat env (WFF.here hT p u : WFF σ Γ 0))
    (h : M.sat env (WFF.hereRead hT (Term.pair (Term.boxtm sb) p) Φ)) :
    M.sat env (WFF.retS hS (.wit (.boxC A cs hcs) Y)
      (Term.pair (Term.collapse (Ctx.collapses_boxIn_self hT Γ) (compsVal sb cs hcs).2) u) Φ :
        WFF σ Γ 0) := by
  refine ⟨M.frame.reflAcc hT w, interp env (Term.pair (Term.boxtm sb) p),
    (sat_hereRead hT hnp env _ Φ).mp h, M.frame.refl hT w, ?_, hh⟩
  change M.compsBack A cs (interp env (Term.boxtm sb)) (M.frame.refl hT w)
    (interp env (Term.collapse (Ctx.collapses_boxIn_self hT Γ) (compsVal sb cs hcs).2))
  rw [interp_collapse (Env.collapseAgree_self hT env)]
  exact compsBack_compsVal env sb (M.frame.reflAcc hT w) cs hcs

/-- A body along `◇_x` given by a hole formula, at the identity in `x`'s extent: the hole formula
    read in the `□` view there, with the content's value and the object in its hole. -/
theorem sat_viewBody_here (hT : ModalSys.T = true) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {X T : VarType} {a₁ : Ann X}
    (bd : Term σ (Γ.diaIn x) X a₁) (χ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeProd X T)) 1)
    (hm : M.frame.reflAcc hT w ∈ (M.posEval (env.ref x hx.choose_spec)).1)
    (e : M.frame.Dom T w) :
    M.sat ((env.diaPush x hx.choose_spec ⟨M.frame.reflAcc hT w, hm⟩).extend (.bnd 0) e)
        (WFF.viewBody hx bd χ) ↔
      M.sat ((env.boxPush (M.frame.reflAcc hT w)).extend (T := .VTypeProd X T) (.bnd 0)
        (interp (env.diaPush x hx.choose_spec ⟨M.frame.reflAcc hT w, hm⟩) bd, e)) χ := by
  set en := env.diaPush x hx.choose_spec ⟨M.frame.reflAcc hT w, hm⟩
  unfold WFF.viewBody
  rw [sat_bodyRepl (Ctx.noProjLast_diaIn Γ x)]
  have hpair : interp (en.extend (.bnd 0) e)
      (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root T) bd)
        (Term.eta (.root (.bnd 0)) T (Ctx.ref_insert_root (Γ.diaIn x) (.bnd 0) T))) =
      ((interp en bd, e) : M.frame.Dom (.VTypeProd X T) w) := by
    change (interp _ (Term.mono _ bd), interp _ (Term.eta _ _ _)) = _
    rw [interp_mono (Env.agree_extend en (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root e),
      interp_eta]
    exact congrArg _ (Env.extend_root _ _ _ _)
  rw [hpair]
  exact sat_mono (Env.extend_agree (Env.diaPush_boxIn env hx.choose_spec
    ⟨M.frame.reflAcc hT w, hm⟩) (.bnd 0) _) χ

include hnp hfin hM in
/-- The `◇_x` reading of a hole formula at the identity, moved from the content's value to `t₀`
    (`Ind`, from a `Here` atom), the object kept: `sat_viewReadTm` at a pair. -/
theorem sat_viewBody_of_here (hT : ModalSys.T = true) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {X T : VarType} {a₁ : Ann X}
    (bd : Term σ (Γ.diaIn x) X a₁) {a' : Ann X} (t₀ : Term σ Γ X a')
    (χ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeProd X T)) 1)
    (hm : M.frame.reflAcc hT w ∈ (M.posEval (env.ref x hx.choose_spec)).1)
    (hval : M.Ind (interp (env.diaPush x hx.choose_spec ⟨M.frame.reflAcc hT w, hm⟩) bd)
      (interp env t₀))
    {b : Ann T} (e₀ : Term σ Γ T b)
    (h : M.sat env (WFF.hereRead hT (Term.pair t₀ e₀) χ)) :
    M.sat ((env.diaPush x hx.choose_spec ⟨M.frame.reflAcc hT w, hm⟩).extend (.bnd 0)
      (interp env e₀)) (WFF.viewBody hx bd χ) := by
  refine (sat_viewBody_here env hT hx bd χ hm _).mpr ?_
  have hag := fun o => (Env.collapseAgree_self hT env).extend
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) (T := .VTypeProd X T) o
  refine (sat_collapse ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert _) (hag _) χ).mp ?_
  refine (hM.inv hfin hnp env _ _ _ (hM.pair hval (M.Ind_refl _))).mpr ?_
  exact (sat_collapse ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert _) (hag _) χ).mpr
    ((sat_hereRead hT hnp env _ χ).mp h)

include hnp hfin hM in
theorem sat_ret_hereXC (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true) (x : VarSymb)
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {X A : VarType} {a₁ : Ann X}
    (bd : Term σ (Γ.diaIn x) X a₁) {a' : Ann X} (t₀ : Term σ Γ X a') {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) (cs : List (List Step)) (hcs : A.CompOk cs)
    (χ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeProd X (.VTypeBox A))) 1)
    (hh : M.sat env (WFF.here hT (Term.diatm x hx bd) t₀ : WFF σ Γ 0))
    (h : M.sat env (WFF.hereRead hT (Term.pair t₀ (Term.boxtm sb)) χ)) :
    M.sat env (WFF.retxS hS x hx (.nec (.boxC A cs hcs))
      (Term.collapse (Ctx.collapses_boxIn_self hT Γ) (compsVal sb cs hcs).2)
      (WFF.viewBody hx bd χ) : WFF σ Γ 0) := by
  obtain ⟨hm, hval⟩ := (sat_here_diatm hT env hx hx.choose_spec t₀ bd).mp hh
  refine ⟨_, hx.choose_spec, ⟨M.frame.reflAcc hT w, hm⟩, interp env (Term.boxtm sb),
    sat_viewBody_of_here env hnp hfin hM hT hx bd t₀ χ hm hval _ h, M.frame.refl hT w, ?_⟩
  change M.compsBack A cs (interp env (Term.boxtm sb)) (M.frame.refl hT w)
    (interp env (Term.collapse (Ctx.collapses_boxIn_self hT Γ) (compsVal sb cs hcs).2))
  rw [interp_collapse (Env.collapseAgree_self hT env)]
  exact compsBack_compsVal env sb (M.frame.reflAcc hT w) cs hcs

include hnp hfin hM in
theorem sat_ret_hereXWC (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true) (x : VarSymb)
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {X A Y : VarType} {a₁ : Ann X}
    (bd : Term σ (Γ.diaIn x) X a₁) {a' : Ann X} (t₀ : Term σ Γ X a') {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) (cs : List (List Step)) (hcs : A.CompOk cs)
    {b : Ann (.VTypeDia Y)} (p : Term σ Γ (.VTypeDia Y) b) {c : Ann Y} (u : Term σ Γ Y c)
    (χ : WFF σ (Γ.boxIn.insert (.bnd 0)
      (.VTypeProd X (.VTypeProd (.VTypeBox A) (.VTypeDia Y)))) 1)
    (hh : M.sat env (WFF.here hT (Term.diatm x hx bd) t₀ : WFF σ Γ 0))
    (hhp : M.sat env (WFF.here hT p u : WFF σ Γ 0))
    (h : M.sat env (WFF.hereRead hT (Term.pair t₀ (Term.pair (Term.boxtm sb) p)) χ)) :
    M.sat env (WFF.retxS hS x hx (.wit (.boxC A cs hcs) Y)
      (Term.pair (Term.collapse (Ctx.collapses_boxIn_self hT Γ) (compsVal sb cs hcs).2) u)
      (WFF.viewBody hx bd χ) : WFF σ Γ 0) := by
  obtain ⟨hm, hval⟩ := (sat_here_diatm hT env hx hx.choose_spec t₀ bd).mp hh
  refine ⟨_, hx.choose_spec, ⟨M.frame.reflAcc hT w, hm⟩,
    interp env (Term.pair (Term.boxtm sb) p),
    sat_viewBody_of_here env hnp hfin hM hT hx bd t₀ χ hm hval _ h, M.frame.refl hT w, ?_, hhp⟩
  change M.compsBack A cs (interp env (Term.boxtm sb)) (M.frame.refl hT w)
    (interp env (Term.collapse (Ctx.collapses_boxIn_self hT Γ) (compsVal sb cs hcs).2))
  rw [interp_collapse (Env.collapseAgree_self hT env)]
  exact compsBack_compsVal env sb (M.frame.reflAcc hT w) cs hcs

include hnp in
theorem sat_ret_hereC (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true) {A : VarType}
    {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) (cs : List (List Step)) (hcs : A.CompOk cs)
    (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
    (h : M.sat env (WFF.hereRead hT (Term.boxtm sb) Φ)) :
    M.sat env (WFF.retS hS (.nec (.boxC A cs hcs))
      (Term.collapse (Ctx.collapses_boxIn_self hT Γ) (compsVal sb cs hcs).2) Φ : WFF σ Γ 0) := by
  refine ⟨M.frame.reflAcc hT w, interp env (Term.boxtm sb), (sat_hereRead hT hnp env _ Φ).mp h,
    M.frame.refl hT w, ?_⟩
  dsimp only [ComesBack, NComesBack]
  rw [interp_collapse (Env.collapseAgree_self hT env)]
  exact compsBack_compsVal env sb (M.frame.reflAcc hT w) cs hcs

theorem sat_ret_bridge (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
    (hb : M.sat env (O.back hS bd t : WFF σ Γ 0))
    (hd : M.sat env (O.dia (O.bodyRead (Term.boxtm bd) Φ))) :
    M.sat env (WFF.ret hS t Φ : WFF σ Γ 0) := by
  obtain ⟨i, hi⟩ := (OutLeg.sat_dia env O _).mp hd
  obtain ⟨r, hr⟩ := (OutLeg.sat_back_rt hS env O bd t hb).2 i
  refine ⟨O.acc env i, interp (O.push env i) (Term.boxtm bd),
    (OutLeg.sat_bodyRead env O i _ Φ).mp hi, r, ?_⟩
  dsimp only [ComesBack, NComesBack, compsBack]
  rw [box_beta]
  exact hr

/-! ## Maps between shapes are sound -/

omit [Γ.NoSlots] in
/-- The slot's η-expansion reads the slot's object. -/
theorem interp_eta_slot {Δ : Ctx} {v : M.frame.W} (en : M.Env Δ v) {T : VarType}
    (o : M.frame.Dom T v) (h : (Δ.insert (.bnd 0) T).ref (.root (.bnd 0)) = some T) :
    interp (en.extend (.bnd 0) o) (Term.eta (σ := σ) (.root (.bnd 0)) T h) = o := by
  rw [interp_eta]
  exact Env.extend_root _ _ _ _

omit [Γ.NoSlots] in
theorem interp_eta_slot_fst {Δ : Ctx} {v : M.frame.W} (en : M.Env Δ v) {A B : VarType}
    (o : M.frame.Dom (.VTypeProd A B) v)
    (h : (Δ.insert (.bnd 0) (.VTypeProd A B)).ref (.step (.root (.bnd 0)) .fst) = some A) :
    interp (en.extend (.bnd 0) o) (Term.eta (σ := σ) (.step (.root (.bnd 0)) .fst) A h) = o.1 := by
  rw [interp_eta, Env.ref_fst _ (Ctx.ref_insert_root _ _ _) h]
  exact congrArg Prod.fst (Env.extend_root _ _ _ _)

omit [Γ.NoSlots] in
theorem interp_eta_slot_snd {Δ : Ctx} {v : M.frame.W} (en : M.Env Δ v) {A B : VarType}
    (o : M.frame.Dom (.VTypeProd A B) v)
    (h : (Δ.insert (.bnd 0) (.VTypeProd A B)).ref (.step (.root (.bnd 0)) .snd) = some B) :
    interp (en.extend (.bnd 0) o) (Term.eta (σ := σ) (.step (.root (.bnd 0)) .snd) B h) = o.2 := by
  rw [interp_eta, Env.ref_snd _ (Ctx.ref_insert_root _ _ _) h]
  exact congrArg Prod.snd (Env.extend_root _ _ _ _)

omit [Γ.NoSlots] in
/-- A companion that comes back (`compBack`) has its contents, read along the way home, `Ind` to
    its value. -/
theorem compBack_ind (hT : ModalSys.T = true) {Δ : Ctx} {v w : M.frame.W} (env : M.Env Δ v)
    (r : M.frame.R v w) (p : List Step) : ∀ {u : VarSymb} {A : VarType}
    (hu : Δ.ref u = some A)
    (hp : Δ.ref (u.ext p) = some (.VTypeBox ((A.compAt p).getD .VTypeOne)))
    (o : M.frame.Dom ((A.compAt p).getD .VTypeOne) w), (A.compAt p).isSome = true →
    M.compBack A p (env.ref u hu) r o →
    M.Ind (M.necEval (env.ref (u.ext p) hp : M.frame.Nec _ v) ⟨w, ⟨r⟩⟩) o := by
  induction p with
  | nil =>
      intro u A hu hp o hs h
      cases A <;> simp only [VarType.compAt, Option.isSome_none, Bool.false_eq_true] at hs
      exact h
  | cons s p ih =>
      intro u A hu hp o hs h
      cases A <;> cases s <;>
        simp only [VarType.compAt, Option.isSome_none, Bool.false_eq_true] at hs
      · exact ih (Ctx.ref_fst_of hu) hp o hs (by rw [Env.ref_fst env hu]; exact h)
      · exact ih (Ctx.ref_snd_of hu) hp o hs (by rw [Env.ref_snd env hu]; exact h)
      · rename_i C
        have h' : M.compBack C p (M.necEval (env.ref u hu : M.frame.Nec C v)
            (M.frame.reflAcc hT v)) r o := by
          have e : M.compBack (.VTypeBox C) (.here :: p) (env.ref u hu) r o =
              M.compBack C p (M.necEval (env.ref u hu : M.frame.Nec C v)
                (M.frame.reflAcc hT v)) r o := dif_pos hT
          rw [← e]
          exact h
        exact ih (Ctx.ref_here_of hT hu) hp o hs (by rw [Env.ref_here env hT hu]; exact h')

omit [Γ.NoSlots] in
/-- A value with companions' own value: its first component, once per companion. -/
def compsProj (A : VarType) : (cs : List (List Step)) → {w : M.frame.W} →
    M.frame.Dom (A.compsFlat cs) w → M.frame.Dom A w
  | [], _, o => o
  | _ :: ps, _, o => compsProj A ps o.1

omit [Γ.NoSlots] in
theorem Env.ref_compsFst {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) {A : VarType} :
    ∀ (cs : List (List Step)) {u : VarSymb} (hu : Δ.ref u = some (A.compsFlat cs))
      (h : Δ.ref (u.ext (compsFst cs)) = some A),
      env.ref (u.ext (compsFst cs)) h = M.compsProj A cs (env.ref u hu)
  | [], _, _, _ => rfl
  | _ :: ps, _, hu, h => by
      change env.ref ((VarSymb.step _ .fst).ext (compsFst ps)) h = _
      rw [Env.ref_compsFst env ps (Ctx.ref_fst_of hu) h, Env.ref_fst env hu]
      rfl

omit [Γ.NoSlots] in
/-- An object that comes back with its companions comes back with its own value. -/
theorem compsBack_proj {A : VarType} {v w : M.frame.W} (e : M.frame.Dom (.VTypeBox A) v)
    (r : M.frame.R v w) : ∀ (cs : List (List Step)) (o : M.frame.Dom (A.compsFlat cs) w),
      M.compsBack A cs e r o → M.Ind (M.necEval (e : M.frame.Nec A v) ⟨w, ⟨r⟩⟩)
        (M.compsProj A cs o)
  | [], _, h => h
  | _ :: ps, o, h => compsBack_proj e r ps o.1 h.1

include hM in
/-- A `□A` object and its companions that come back make a packed body (`compsBody`) whose
    reading along the way home is `Ind` to the value. -/
theorem compsBody_ind {A : VarType} {v w : M.frame.W} (e : M.frame.Dom (.VTypeBox A) v)
    (r : M.frame.R v w) : ∀ (cs : List (List Step)) (hcs : A.CompOk cs)
    (o : M.frame.Dom (A.compsFlat cs) w), M.compsBack A cs e r o →
    M.Ind (interp (((Env.empty v).extend (.bnd 0) e).boxPush ⟨w, ⟨r⟩⟩)
      (compsBody (σ := σ) A cs hcs).2) o
  | [], _, o, h => by
      have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox A)
      change M.Ind (interp _ (Term.eta _ A _)) o
      rw [interp_eta, Env.ref_inner _ _ hu,
        show ((Env.empty v).extend (.bnd 0) e).ref (.root (.bnd 0)) hu = e from
          Env.extend_root _ _ _ _]
      exact h
  | p :: ps, hcs, o, h => by
      have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox A)
      obtain ⟨hT, hall⟩ := hcs.resolve_left (List.cons_ne_nil _ _)
      refine hM.pair (compsBody_ind e r ps hcs.tail o.1 h.1) ?_
      have h₂ : M.compBack (.VTypeBox A) (.here :: p) e r o.2 := by
        have e' := h.2
        rw [dif_pos hT] at e'
        exact e'
      have hp := hcs.ref_head hu
      rw [interp_eta, Env.ref_inner _ _ hp]
      have hee : ((Env.empty v).extend (.bnd 0) e).ref (.root (.bnd 0)) hu = e :=
        Env.extend_root _ _ _ _
      exact compBack_ind hT ((Env.empty v).extend (.bnd 0) e) r (.here :: p) hu hp o.2
        (hall p List.mem_cons_self) (by rw [hee]; exact h₂)

omit [Γ.NoSlots] in
include hM in
include hM in
/-- ⭐**A born root's tuple comes back with its companions** (T), when the root does: the tuple's
    contents leaf by leaf (`bcTree_ind`), each companion as the root's companion it decodes to
    (`compBack_itemsTree`, `compsBack_at`). -/
theorem tupC_back (A : VarType) (hb : ModalSys.T = true) {v w : M.frame.W}
    (e : M.frame.Dom (.VTypeBox A) v) (r : M.frame.R v w)
    (o : M.frame.Dom (A.compsFlat A.hereChains) w) (h : M.compsBack A A.hereChains e r o) :
    ∀ (cs : List (List Step)) (hcs : ∀ p ∈ cs, p ∈ (tupOneTy A true).hereChains),
      M.compsBack (tupOneTy A true) cs (M.holeVal (ShapeMap.tupC (σ := σ) A true hb).obj.2 e) r
        (M.holeVal (tupCVal (σ := σ) A hb cs hcs).2 o)
  | [], _ => by
      have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (VarType.VTypeBox A)
      have hw := Ctx.ref_insert_root Ctx.empty (.bnd 0) (A.compsFlat A.hereChains)
      have he : ((Env.empty v).extend (.bnd 0) e).ref (.root (.bnd 0)) hu = e :=
        Env.extend_root _ _ _ _
      have ho : ((Env.empty w).extend (.bnd 0) o).ref (.root (.bnd 0)) hw = o :=
        Env.extend_root _ _ _ _
      change M.Ind (M.necEval (interp ((Env.empty v).extend (.bnd 0) e) (Term.boxtm _)) ⟨w, ⟨r⟩⟩)
        (interp ((Env.empty w).extend (.bnd 0) o) _)
      rw [box_beta]
      refine hM.pair (M.Ind_refl _) (hM.pair ?_ ?_)
      · change M.Ind (interp _ (Term.eta (σ := σ) (VarSymb.root (.bnd 0)).inner A _))
          (interp _ (Term.eta (σ := σ) _ A _))
        rw [interp_eta, interp_eta, Env.ref_inner _ _ hu, Env.ref_compsFst _ _ hw, he, ho]
        exact compsBack_proj e r _ o h
      · refine bcTree_ind hM A _ _ _ _ fun q hq => ?_
        have hp : (Ctx.empty.insert (.bnd 0) (VarType.VTypeBox A)).ref
            ((VarSymb.root (.bnd 0)).ext (.here :: q)) =
            some (.VTypeBox ((A.compAt q).getD .VTypeOne)) := Ctx.ref_compMem hb hq hu
        dsimp only
        erw [interp_eta, interp_eta, Env.ref_inner _ _ hp]
        refine (compBack_iff_ind hb ((Env.empty v).extend (.bnd 0) e) r (.here :: q) hu hp
          (VarType.compAt_hereChains A q hq) _).mp ?_
        rw [he]
        exact compsBack_at hb e r _ _ hw (by rw [ho]; exact h) q hq _
  | p :: ps, hcs => by
      have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (VarType.VTypeBox A)
      have hw := Ctx.ref_insert_root Ctx.empty (.bnd 0) (A.compsFlat A.hereChains)
      have he : ((Env.empty v).extend (.bnd 0) e).ref (.root (.bnd 0)) hu = e :=
        Env.extend_root _ _ _ _
      have ho : ((Env.empty w).extend (.bnd 0) o).ref (.root (.bnd 0)) hw = o :=
        Env.extend_root _ _ _ _
      refine ⟨tupC_back A hb e r o h ps _, ?_⟩
      rw [dif_pos hb]
      have hp := hcs p List.mem_cons_self
      obtain ⟨hmem, -⟩ := tupCompOf_spec A p hp
      rcases List.mem_append.mp hp with hp' | hp'
      · obtain ⟨_, hq, _⟩ := List.mem_map.mp hp'
        cases hq
      obtain ⟨p', hp₀, rfl⟩ := List.mem_map.mp hp'
      change (if hT' : ModalSys.T = true then M.compBack (tupOneTy A true) (.snd :: p')
        (M.necEval (M.holeVal (ShapeMap.tupC (σ := σ) A true hb).obj.2 e :
          M.frame.Nec (tupOneTy A true) v) (M.frame.reflAcc hT' v)) r
        (interp ((Env.empty w).extend (.bnd 0) o) (Term.eta (σ := σ) _ _ _)) else True)
      rw [dif_pos hb, interp_eta]
      unfold holeVal
      dsimp only [ShapeMap.obj]
      rw [box_beta]
      have key : ∀ (P : List Step) (hP : P = .here :: tupCompOf A (.snd :: p'))
          (h₂ : ((Ctx.empty.insert (.bnd 0) (A.compsFlat A.hereChains))).ref
            ((VarSymb.root (.bnd 0)).ext (compsIdx A.hereChains (tupCompOf A (.snd :: p')))) =
            some (((VarType.VTypeBox A).compAt P).getD .VTypeOne)),
          M.compBack (.VTypeBox A) P e r (((Env.empty w).extend (.bnd 0) o).ref _ h₂) := by
        rintro _ rfl h₂
        exact compsBack_at hb e r _ _ hw (by rw [ho]; exact h) _ hmem _
      have h₂ := Ctx.ref_compsIdx (Γ := Ctx.empty.insert (.bnd 0) (A.compsFlat A.hereChains))
        A.hereChains (tupCompOf A (.snd :: p')) hmem hw
      rw [← (tupCompOf_spec A _ hp).2] at h₂
      refine (compBack_itemsTree hb ((Env.empty v).extend (.bnd 0) e) r (.VTypeBox A)
        (.root (.bnd 0)) hu p' hp₀ _ _ _ ?_).mpr ?_
      · rw [← VarType.compAt_bcDec _ p' hp₀]
        exact h₂
      · rw [he]
        exact key _ (VarType.bcDec_box A p' hp₀) _

include hM in
/-- A padded object comes back with its companions when the object does. -/
theorem padC_back (Z : VarType) (hb : ModalSys.T = true) {v w : M.frame.W}
    (e : M.frame.Dom (.VTypeBox Z) v) (r : M.frame.R v w)
    (o : M.frame.Dom (Z.compsFlat Z.hereChains) w) (h : M.compsBack Z Z.hereChains e r o) :
    ∀ (cs : List (List Step)) (hcs : ∀ p ∈ cs, p ∈ (VarType.VTypeProd Z .VTypeOne).hereChains),
      M.compsBack (.VTypeProd Z .VTypeOne) cs
        (M.holeVal (ShapeMap.padC (σ := σ) Z true hb).obj.2 e) r
        (M.holeVal (padCVal (σ := σ) Z cs hcs).2 o)
  | [], _ => by
      have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (VarType.VTypeBox Z)
      have hw := Ctx.ref_insert_root Ctx.empty (.bnd 0) (Z.compsFlat Z.hereChains)
      change M.Ind (M.necEval (interp ((Env.empty v).extend (.bnd 0) e) (Term.boxtm _)) ⟨w, ⟨r⟩⟩)
        (interp ((Env.empty w).extend (.bnd 0) o) _)
      rw [box_beta]
      refine hM.pair ?_ (M.Ind_refl _)
      change M.Ind (interp _ (Term.eta (σ := σ) (VarSymb.root (.bnd 0)).inner Z _))
        (interp _ (Term.eta (σ := σ) _ Z _))
      rw [interp_eta, interp_eta, Env.ref_inner _ _ hu, Env.ref_compsFst _ _ hw,
        show ((Env.empty v).extend (.bnd 0) e).ref (.root (.bnd 0)) hu = e from
          Env.extend_root _ _ _ _,
        show ((Env.empty w).extend (.bnd 0) o).ref (.root (.bnd 0)) hw = o from
          Env.extend_root _ _ _ _]
      exact compsBack_proj e r _ o h
  | p :: ps, hcs => by
      have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (VarType.VTypeBox Z)
      have hw := Ctx.ref_insert_root Ctx.empty (.bnd 0) (Z.compsFlat Z.hereChains)
      refine ⟨padC_back Z hb e r o h ps _, ?_⟩
      rw [dif_pos hb]
      obtain ⟨hp, hq⟩ := padC_mem (hcs p List.mem_cons_self)
      generalize hq' : p.tail = q at hq hp
      subst hp
      change (if hT' : ModalSys.T = true then M.compBack (.VTypeProd Z .VTypeOne) (.fst :: q)
        (M.necEval (M.holeVal (ShapeMap.padC (σ := σ) Z true hb).obj.2 e :
          M.frame.Nec (.VTypeProd Z .VTypeOne) v) (M.frame.reflAcc hT' v)) r
        (interp ((Env.empty w).extend (.bnd 0) o) (Term.eta (σ := σ) _ _ _)) else True)
      rw [dif_pos hb, interp_eta]
      unfold holeVal
      dsimp only [ShapeMap.obj]
      rw [box_beta]
      change M.compBack Z q (interp _ (Term.eta (σ := σ) (VarSymb.root (.bnd 0)).inner Z _)) r _
      rw [interp_eta, Env.ref_inner _ _ hu,
        show ((Env.empty v).extend (.bnd 0) e).ref (.root (.bnd 0)) hu = e from
          Env.extend_root _ _ _ _]
      have key := compsBack_at hb e r _ _ hw
        (by rw [show ((Env.empty w).extend (.bnd 0) o).ref (.root (.bnd 0)) hw = o from
          Env.extend_root _ _ _ _]; exact h) q hq
        (Ctx.ref_compsIdx _ q hq hw)
      exact (iff_of_eq (dif_pos hb)).mp key

omit [Γ.NoSlots] in
/-- A companion of a necessary object, read through `here`. -/
theorem compBack_here (hT : ModalSys.T = true) (C : VarType) (p : List Step) {v w : M.frame.W}
    (x : M.frame.Dom (.VTypeBox C) v) (r : M.frame.R v w)
    (o : M.frame.Dom ((C.compAt p).getD .VTypeOne) w) :
    M.compBack (.VTypeBox C) (.here :: p) x r o ↔
      M.compBack C p (M.necEval (x : M.frame.Nec C v) (M.frame.reflAcc hT v)) r o := by
  change (if hT' : ModalSys.T = true then
    M.compBack C p (M.necEval (x : M.frame.Nec C v) (M.frame.reflAcc hT' v)) r o else True) ↔ _
  rw [dif_pos hT]

omit [Γ.NoSlots] in
/-- A value with companions built from parts comes back when its own value and each companion
    do. -/
theorem compsBack_build {A : VarType} {v w : M.frame.W} (e : M.frame.Dom (.VTypeBox A) v)
    (r : M.frame.R v w) {Δ : Ctx} (env : M.Env Δ w) (main : Σ a, Term σ Δ A a) :
    ∀ (cs : List (List Step)) (get : ∀ p ∈ cs, Σ c, Term σ Δ ((A.compAt p).getD .VTypeOne) c),
      M.Ind (M.necEval (e : M.frame.Nec A v) ⟨w, ⟨r⟩⟩) (interp env main.2) →
      (∀ (p : List Step) (hp : p ∈ cs), ModalSys.T = true →
        M.compBack (.VTypeBox A) (.here :: p) e r (interp env (get p hp).2)) →
      M.compsBack A cs e r (interp env (compsBuild A main cs get).2)
  | [], _, hm, _ => hm
  | p :: ps, get, hm, hc => by
      refine ⟨compsBack_build e r env main ps _ hm
        (fun p' hp' hT => hc p' (List.mem_cons_of_mem _ hp') hT), ?_⟩
      by_cases hT : ModalSys.T = true
      · rw [dif_pos hT]
        exact hc p List.mem_cons_self hT
      · rw [dif_neg hT]
        trivial

/-! ### The hole map with companions -/

omit [Γ.NoSlots] in
/-- A value with companions that comes back gives its own value's component. -/
theorem compsBack_main {A : VarType} {v w : M.frame.W} (e : M.frame.Dom (.VTypeBox A) v)
    (r : M.frame.R v w) :
    ∀ (cs : List (List Step)) {Δ' : Ctx} (env' : M.Env Δ' w) {a : VarSymb}
      (ha : Δ'.ref a = some (A.compsFlat cs)), M.compsBack A cs e r (env'.ref a ha) →
      ∀ h, M.Ind (M.necEval (e : M.frame.Nec A v) ⟨w, ⟨r⟩⟩) (env'.ref (a.ext (compsFst cs)) h)
  | [], _, _, _, _, hb, _ => hb
  | _ :: ps, _, env', _, ha, hb, h => by
      refine compsBack_main e r ps env' (Ctx.ref_fst_of ha) ?_ h
      rw [Env.ref_fst env' ha]
      exact hb.1

omit [Γ.NoSlots] in
/-- The value with companions read through the view, at its own value's component: the
    contents. -/
theorem ref_compsFst_compsSlot {Δ Δ' : Ctx} {u : VarSymb} {C : VarType}
    (hu : Δ.ref u = some (.VTypeBox C)) (hle : Δ.boxIn.Le Δ') {w : M.frame.W} (E : M.Env Δ' w) :
    ∀ (cs : List (List Step)) (h : C.CompOk cs) {Δ'' : Ctx} (E' : M.Env Δ'' w) {a : VarSymb}
      (ha : Δ''.ref a = some (C.compsFlat cs)),
      E'.ref a ha = interp E (compsSlot (σ := σ) hu hle cs h).2 →
      ∀ h', E'.ref (a.ext (compsFst cs)) h' = E.ref u.inner (hle.ref (Ctx.ref_inner hu))
  | [], _, _, E', _, ha, he, h' => by
      rw [show E'.ref _ h' = E'.ref _ ha from rfl, he]
      exact interp_eta E _ _
  | _ :: ps, h, _, E', _, ha, he, h' => by
      refine ref_compsFst_compsSlot hu hle E ps h.tail E' (Ctx.ref_fst_of ha) ?_ h'
      rw [Env.ref_fst E' ha, he]
      rfl

omit [Γ.NoSlots] in
/-- The value with companions read through the view, at a companion's component: that
    companion's contents. -/
theorem ref_compsIdx_compsSlot {Δ Δ' : Ctx} {u : VarSymb} {C : VarType}
    (hu : Δ.ref u = some (.VTypeBox C)) (hle : Δ.boxIn.Le Δ') {w : M.frame.W} (E : M.Env Δ' w) :
    ∀ (cs : List (List Step)) (h : C.CompOk cs) {Δ'' : Ctx} (E' : M.Env Δ'' w) {a : VarSymb}
      (ha : Δ''.ref a = some (C.compsFlat cs)),
      E'.ref a ha = interp E (compsSlot (σ := σ) hu hle cs h).2 →
      ∀ q, q ∈ cs → ∀ {T : VarType} (h' : Δ''.ref (a.ext (compsIdx cs q)) = some T)
        (h'' : Δ'.ref ((VarSymb.step u .here).ext q).inner = some T),
        E'.ref (a.ext (compsIdx cs q)) h' = E.ref ((VarSymb.step u .here).ext q).inner h''
  | [], _, _, _, _, _, _, q, hq, _, _, _ => absurd hq List.not_mem_nil
  | p :: ps, h, Δ'', E', a, ha, he, q, hq, T, h', h'' => by
      obtain rfl : T = (C.compAt q).getD .VTypeOne :=
        Option.some.inj (h'.symm.trans (Ctx.ref_compsIdx _ q hq ha))
      by_cases hqp : q = p
      · subst hqp
        have key : ∀ (a' : VarSymb) (k : Δ''.ref a' = some ((C.compAt q).getD .VTypeOne)),
            a' = .step a .snd → E'.ref a' k = (E'.ref a ha).2 := by
          rintro _ k rfl
          exact Env.ref_snd E' ha k
        rw [key _ h' (by simp [compsIdx, VarSymb.ext]), he]
        exact interp_eta E _ _
      · have hq' : q ∈ ps := (List.mem_cons.mp hq).resolve_left hqp
        have key : ∀ (k : Δ''.ref ((VarSymb.step a .fst).ext (compsIdx ps q)) =
              some ((C.compAt q).getD .VTypeOne)) (a' : VarSymb)
            (k' : Δ''.ref a' = some ((C.compAt q).getD .VTypeOne)),
            a' = (VarSymb.step a .fst).ext (compsIdx ps q) → E'.ref a' k' = E'.ref _ k := by
          rintro _ _ _ rfl
          rfl
        rw [key (Ctx.ref_compsIdx ps q hq' (Ctx.ref_fst_of ha)) _ h'
          (by simp [compsIdx, hqp, VarSymb.ext])]
        refine ref_compsIdx_compsSlot hu hle E ps h.tail E' (Ctx.ref_fst_of ha) ?_ q hq' _ h''
        rw [Env.ref_fst E' ha, he]
        rfl

omit [Γ.NoSlots] in
/-- ⭐**The companion renaming, semantically**: `d`'s view read along an arrow is the renaming
    read at `d`'s value with companions there. -/
theorem agree_compsRen (hF : ModalSys.Four = false) (A : VarType) (b : Bool)
    (hb : ModalSys.T = b) {w : M.frame.W}
    (E : M.Env (Ctx.empty.insert (.bnd 0) (.VTypeBox A)).boxIn w) :
    Env.Agree (Ctx.Le.refl _)
      (substEnv (compsRen σ _ (A.compsAllB b)) (ok_compsRen hF A b hb) (Ctx.noProjLast_boxIn _)
        ((Env.empty w).extend (.bnd 0) (interp E (compsSlot (Ctx.ref_insert_root Ctx.empty (.bnd 0)
          (.VTypeBox A)) (Ctx.Le.refl _) (A.compsAllB b)
          (VarType.compOk_compsAllB b hb A)).2))) E := by
  have hk : ModalSys.keepOnly = false := by simp [ModalSys.keepOnly, hF]
  have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox A)
  have hE₁ : ((Env.empty w).extend (.bnd 0) (interp E (compsSlot (σ := σ) hu (Ctx.Le.refl _)
      (A.compsAllB b) (VarType.compOk_compsAllB b hb A)).2)).ref (.root (.bnd 0))
      (Ctx.ref_insert_root _ _ _) = interp E (compsSlot (σ := σ) hu (Ctx.Le.refl _)
      (A.compsAllB b) (VarType.compOk_compsAllB b hb A)).2 := Env.extend_root _ _ _ _
  -- an address's reading depends on it only up to equality
  have ref_eq : ∀ {Δ : Ctx} (env : M.Env Δ w) (a a' : VarSymb) {T : VarType}
      (k : Δ.ref a = some T) (k' : Δ.ref a' = some T), a = a' → env.ref a k = env.ref a' k' := by
    rintro _ _ _ _ _ _ _ rfl
    rfl
  intro v T hv
  match v with
  | .step u .box =>
      obtain ⟨-, hu'⟩ := Ctx.boxIn_box hv
      obtain ⟨hrt, -, hc⟩ := Ctx.ref_insert_box hu'
      have hθ : compsRen σ (Ctx.empty.insert (.bnd 0) (A.compsFlat (A.compsAllB b)))
          (A.compsAllB b) (.step u .box) = .ren (compsItemAddr (A.compsAllB b) u.path) := by
        dsimp only [compsRen]
        rw [if_pos hrt]
      change entryVal _ _ _ = E.ref (.step u .box) hv
      rw [entryVal_congr _ hθ _ (by rw [← hθ]; exact ok_compsRen hF A b hb _ _ rfl hv)]
      change Env.ref _ (compsItemAddr _ u.path) _ = _
      have hu₀ := VarSymb.root_ext_path u
      rcases hc with ⟨hpath, rfl⟩ | ⟨hT, p, hpath, hp⟩
      · rw [hrt, hpath] at hu₀
        obtain rfl : u = .root (.bnd 0) := hu₀.symm
        refine (ref_eq _ (compsItemAddr _ (VarSymb.root (.bnd 0)).path) _ _
          (Ctx.ref_compsFst _ (Ctx.ref_insert_root _ _ _)) rfl).trans ?_
        refine (ref_compsFst_compsSlot hu (Ctx.Le.refl _) E _ _ _ _ hE₁ _).trans ?_
        exact ref_eq _ _ _ _ _ (VarSymb.inner_box hk)
      · rw [hrt, hpath] at hu₀
        subst hu₀
        have hm : p ∈ A.compsAllB b := by
          rw [← hb, hT]
          exact VarType.mem_hereChains A p hp
        have hk₁ : (Ctx.empty.insert (.bnd 0) (A.compsFlat (A.compsAllB b))).ref
            ((VarSymb.root (.bnd 0)).ext (compsIdx (A.compsAllB b) p)) = some T := by
          have := Ctx.ref_compsIdx _ p hm (Ctx.ref_insert_root Ctx.empty (.bnd 0)
            (A.compsFlat (A.compsAllB b)))
          rwa [hp] at this
        refine (ref_eq _ (compsItemAddr _ ((VarSymb.root (.bnd 0)).ext (.here :: p)).path) _ _
          hk₁ (by rw [VarSymb.ext_path]; rfl)).trans ?_
        refine (ref_compsIdx_compsSlot hu (Ctx.Le.refl _) E _ _ _ _ hE₁ p hm _
          (by rw [VarSymb.inner_box hk]; exact hv)).trans ?_
        exact ref_eq _ _ _ _ _ (VarSymb.inner_box hk)
  | .step u .keep => exact absurd ((Ctx.boxIn_keep hv).1.symm.trans hF) (by decide)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

omit [Γ.NoSlots] in
/-- The contents of `□sb`'s companion, read along an arrow out: the companion's own reading. -/
theorem interp_compVal {Δ : Ctx} {v : M.frame.W} (env : M.Env Δ v) {A : VarType}
    {a₀ : Ann A} (sb : Term σ Δ.boxIn A a₀) (ac : M.frame.Acc v) (p : List Step)
    {ps : List (List Step)} (h : A.CompOk (p :: ps)) :
    interp (env.boxPush ac) (compVal sb p h).2 =
      M.necEval (((Env.empty v).extend (.bnd 0) (interp env (Term.boxtm sb))).ref _
        (h.ref_head (Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox A))) :
        M.frame.Nec _ v) ac := by
  unfold compVal
  rw [necEval_unboxtm, interp_holeAt]
  unfold holeVal
  rw [box_beta, interp_eta, Env.ref_inner _ _ (h.ref_head (Ctx.ref_insert_root _ _ _))]

include hM in
omit [Γ.NoSlots] in
/-- ⭐**The hole map with companions preserves coming back**: its contents by `hole`'s argument,
    and each companion of `□s[d.inner]` as `compVal` read along the way home, which is the
    renaming read at `d`'s value with companions there (`agree_compsRen`), `Ind` to the source's
    value (`compsSlot_ind`) and so, mapped, to `holeC`'s. -/
theorem holeC_back {A B : VarType} {bB : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B bB)
    (b : Bool) (hb : ModalSys.T = b) (hF : ModalSys.Four = false) (cs : List (List Step))
    (h : B.CompOk cs) {v w : M.frame.W} (e : M.frame.Dom (.VTypeBox A) v) (r : M.frame.R v w)
    (o : M.frame.Dom (A.compsFlat (A.compsAllB b)) w)
    (hback : M.compsBack A (A.compsAllB b) e r o) :
    M.compsBack B cs (M.holeVal (ShapeMap.holeC s b hb hF cs h).obj.2 e) r
      (M.holeVal (ShapeMap.holeC s b hb hF cs h).val.2 o) := by
  have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox A)
  have he₀ : ((Env.empty v).extend (.bnd 0) e).ref (.root (.bnd 0)) hu = e :=
    Env.extend_root _ _ _ _
  set env₀ : M.Env (Ctx.empty.insert (.bnd 0) (.VTypeBox A)) v := (Env.empty v).extend (.bnd 0) e
  set E := env₀.boxPush ⟨w, ⟨r⟩⟩
  have he₁ : ((Env.empty w).extend (.bnd 0) o).ref (.root (.bnd 0))
      (Ctx.ref_insert_root Ctx.empty (.bnd 0) (A.compsFlat (A.compsAllB b))) = o :=
    Env.extend_root _ _ _ _
  set env₁ : M.Env (Ctx.empty.insert (.bnd 0) (A.compsFlat (A.compsAllB b))) w :=
    (Env.empty w).extend (.bnd 0) o
  set R := interp E (compsSlot (σ := σ) hu (Ctx.Le.refl _) (A.compsAllB b)
    (VarType.compOk_compsAllB b hb A)).2
  have hR : M.Ind R o := compsSlot_ind hM hu (Ctx.Le.refl _) env₀ r E
    (fun _ _ _ => rfl) _ _ o (by rw [he₀]; exact hback)
  set sb : Term σ (Ctx.empty.insert (.bnd 0) (.VTypeBox A)).boxIn B _ :=
    Term.holeAt (Term.eta (VarSymb.root (.bnd 0)).inner A (Ctx.ref_inner hu)) s
  change M.compsBack B cs (interp env₀ (Term.boxtm sb)) r (interp env₁ (holeCVal s b hb hF cs h).2)
  refine compsBack_build _ r env₁ _ cs _ ?_ ?_
  · -- the contents, as for `hole`
    rw [box_beta, interp_holeAt, interp_holeAt]
    refine hM.map s ?_
    rw [interp_eta, interp_eta, Env.ref_inner _ _ hu, he₀]
    exact compsBack_main e r _ env₁ _ (by rw [he₁]; exact hback) _
  · -- each companion, through the renaming
    intro q hq hT
    have hq1 := h.single hq
    obtain ⟨-, hall⟩ := hq1.resolve_left (List.cons_ne_nil _ _)
    have hp := hq1.ref_head (Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox B))
    refine (compBack_iff_ind hT ((Env.empty v).extend (.bnd 0) (interp env₀ (Term.boxtm sb)))
      r (.here :: q) (Ctx.ref_insert_root _ _ _) hp (hall q List.mem_cons_self) _).mpr ?_
    change M.Ind (M.necEval (Env.ref ((Env.empty v).extend (.bnd 0) (interp env₀ (Term.boxtm sb)))
      ((VarSymb.step (.root (.bnd 0)) .here).ext q) hp : M.frame.Nec _ v) _) _
    rw [← interp_compVal env₀ sb ⟨w, ⟨r⟩⟩ q hq1]
    change M.Ind _ (interp env₁ (Term.subst _ _ (ok_compsRen hF A b hb) (coh_compsRen hF A b hb)
      (compVal sb q hq1).2))
    have e₀ : interp E (compVal sb q hq1).2 = M.holeVal (Term.subst _ _ (ok_compsRen (σ := σ) hF
        A b hb) (coh_compsRen hF A b hb) (compVal sb q hq1).2) R := by
      unfold holeVal
      rw [interp_subst _ _ _ (Ctx.noProjLast_boxIn _),
        ← interp_mono (agree_compsRen hF A b hb E) (compVal sb q hq1).2, Term.mono_refl]
    rw [e₀]
    exact hM.map _ hR

/-! ### Readings home, with companions -/

/-- The readings home of a `□A` object and its companions `cs` along `r`: its contents, then each
    companion's (`compRead`). -/
def compsRead (A : VarType) : (cs : List (List Step)) → A.CompOk cs → {v w : M.frame.W} →
    M.frame.Dom (.VTypeBox A) v → M.frame.R v w → M.frame.Dom (A.compsFlat cs) w
  | [], _, _, w, e, r => M.necEval (e : M.frame.Nec A _) ⟨w, ⟨r⟩⟩
  | p :: ps, h, _, _, e, r => (compsRead A ps h.tail e r,
      M.compRead (h.resolve_left (List.cons_ne_nil _ _)).1 (.VTypeBox A) (.here :: p) e r)

/-- ⭐**The readings home of a necessary object** out there, with its companions. -/
def NRead : (N : NShape) → {v w : M.frame.W} → M.frame.Dom N.ty v → M.frame.R v w →
    M.frame.Dom N.flat w
  | .boxC A cs h, _, _, e, r => M.compsRead A cs h e r
  | .prod R S, _, _, e, r => (NRead R e.1 r, NRead S e.2 r)

omit [Γ.NoSlots] in
/-- A companion's contents read along the way home is its reading (`compRead`). -/
theorem necEval_ref_compRead (hT : ModalSys.T = true) {Δ : Ctx} {v w : M.frame.W}
    (env : M.Env Δ v) (r : M.frame.R v w) (p : List Step) : ∀ {u : VarSymb} {A : VarType}
    (hu : Δ.ref u = some A)
    (hp : Δ.ref (u.ext p) = some (.VTypeBox ((A.compAt p).getD .VTypeOne))),
    (A.compAt p).isSome = true →
    M.necEval (env.ref (u.ext p) hp : M.frame.Nec _ v) ⟨w, ⟨r⟩⟩ =
      M.compRead hT A p (env.ref u hu) r := by
  induction p with
  | nil =>
      intro u A hu hp hs
      cases A <;> simp only [VarType.compAt, Option.isSome_none, Bool.false_eq_true] at hs
      rfl
  | cons s p ih =>
      intro u A hu hp hs
      cases A <;> cases s <;>
        simp only [VarType.compAt, Option.isSome_none, Bool.false_eq_true] at hs
      · have h := ih (Ctx.ref_fst_of hu) hp hs
        rw [Env.ref_fst env hu] at h
        exact h
      · have h := ih (Ctx.ref_snd_of hu) hp hs
        rw [Env.ref_snd env hu] at h
        exact h
      · have h := ih (Ctx.ref_here_of hT hu) hp hs
        rw [Env.ref_here env hT hu] at h
        exact h

omit [Γ.NoSlots] in
/-- A companion that comes back as `o` has its reading `Ind` to `o`. -/
theorem ind_compRead (hT : ModalSys.T = true) : ∀ (A : VarType) (p : List Step)
    {v w : M.frame.W} (x : M.frame.Dom A v) (r : M.frame.R v w)
    (o : M.frame.Dom ((A.compAt p).getD .VTypeOne) w), (A.compAt p).isSome = true →
    M.compBack A p x r o → M.Ind (M.compRead hT A p x r) o := by
  intro A p
  induction p generalizing A with
  | nil =>
      intro v w x r o hs hb
      cases A <;> simp only [VarType.compAt, Option.isSome_none, Bool.false_eq_true] at hs
      exact hb
  | cons s p ih =>
      intro v w x r o hs hb
      cases A <;> cases s <;>
        simp only [VarType.compAt, Option.isSome_none, Bool.false_eq_true] at hs
      · exact ih _ x.1 r o hs hb
      · exact ih _ x.2 r o hs hb
      · exact ih _ _ r o hs ((iff_of_eq (dif_pos hT)).mp hb)

omit [Γ.NoSlots] in
/-- A `□A` object with companions that comes back as `o` has its readings `Ind` to `o`, given that
    `Ind` pairs. -/
theorem ind_compsRead
    (hpair : ∀ {X Y : VarType} {w : M.frame.W} {a a' : M.frame.Dom X w}
      {b b' : M.frame.Dom Y w}, M.Ind a a' → M.Ind b b' →
        M.Ind (A := .VTypeProd X Y) (a, b) (a', b'))
    (A : VarType) {v w : M.frame.W} (e : M.frame.Dom (.VTypeBox A) v) (r : M.frame.R v w) :
    ∀ (cs : List (List Step)) (h : A.CompOk cs) (o : M.frame.Dom (A.compsFlat cs) w),
      M.compsBack A cs e r o → M.Ind (M.compsRead A cs h e r) o
  | [], _, _, hb => hb
  | p :: ps, h, o, hb => by
      obtain ⟨hT, hall⟩ := h.resolve_left (List.cons_ne_nil _ _)
      exact hpair (ind_compsRead hpair A e r ps h.tail o.1 hb.1)
        (ind_compRead hT (.VTypeBox A) (.here :: p) e r o.2 (hall p List.mem_cons_self)
          ((iff_of_eq (dif_pos hT)).mp hb.2))

omit [Γ.NoSlots] in
/-- ⭐A necessary object that comes back as `o` has its readings `Ind` to `o`, given that `Ind`
    pairs. -/
theorem ind_NRead
    (hpair : ∀ {X Y : VarType} {w : M.frame.W} {a a' : M.frame.Dom X w}
      {b b' : M.frame.Dom Y w}, M.Ind a a' → M.Ind b b' →
        M.Ind (A := .VTypeProd X Y) (a, b) (a', b')) :
    ∀ (N : NShape) {v w : M.frame.W} (e : M.frame.Dom N.ty v) (r : M.frame.R v w)
      (o : M.frame.Dom N.flat w), M.NComesBack N e r o → M.Ind (M.NRead N e r) o
  | .boxC A cs h, _, _, e, r, o, hb => ind_compsRead hpair A e r cs h o hb
  | .prod R S, _, _, e, r, o, hb =>
      hpair (ind_NRead hpair R e.1 r o.1 hb.1) (ind_NRead hpair S e.2 r o.2 hb.2)

omit [Γ.NoSlots] in
/-- ⭐The value with companions of a slot, read along the way home: the object's readings. -/
theorem interp_compsSlot {Δ Δ' : Ctx} {u : VarSymb} {C : VarType}
    (hu : Δ.ref u = some (.VTypeBox C)) (hle : Δ.boxIn.Le Δ') {v w : M.frame.W}
    (env₁ : M.Env Δ v) (r : M.frame.R v w) (env' : M.Env Δ' w)
    (hag : Env.Agree hle (env₁.boxPush ⟨w, ⟨r⟩⟩) env') :
    ∀ (cs : List (List Step)) (h : C.CompOk cs),
      interp env' (compsSlot (σ := σ) hu hle cs h).2 = M.compsRead C cs h (env₁.ref u hu) r
  | [], _ => by
      change interp env' (Term.eta (σ := σ) u.inner C _) = _
      rw [interp_eta, ← Env.ref_agree hag _ (Ctx.ref_inner hu), Env.ref_inner _ _ hu]
      rfl
  | p :: ps, h => by
      obtain ⟨hT, hall⟩ := h.resolve_left (List.cons_ne_nil _ _)
      have hp := h.ref_head hu
      change (interp env' (compsSlot hu hle ps h.tail).2,
        interp env' (Term.eta (σ := σ) ((VarSymb.step u .here).ext p).inner _ _)) = _
      rw [interp_compsSlot hu hle env₁ r env' hag ps h.tail, interp_eta,
        ← Env.ref_agree hag _ (Ctx.ref_inner hp), Env.ref_inner _ _ hp]
      exact congrArg _ (necEval_ref_compRead hT env₁ r (.here :: p) hu hp
        (hall p List.mem_cons_self))

omit [Γ.NoSlots] in
/-- ⭐The value with companions of `□sb`, read along an arrow out: its readings. -/
theorem interp_compsVal {Δ : Ctx} {v : M.frame.W} (env : M.Env Δ v) {A : VarType} {a₀ : Ann A}
    (sb : Term σ Δ.boxIn A a₀) (w : M.frame.W) (r : M.frame.R v w) :
    ∀ (cs : List (List Step)) (h : A.CompOk cs),
      interp (env.boxPush ⟨w, ⟨r⟩⟩) (compsVal sb cs h).2 =
        M.compsRead A cs h (interp env (Term.boxtm sb)) r
  | [], _ => (box_beta env sb _).symm
  | p :: ps, h => by
      obtain ⟨hT, hall⟩ := h.resolve_left (List.cons_ne_nil _ _)
      change (interp _ (compsVal sb ps h.tail).2, interp _ (compVal sb p h).2) = _
      rw [interp_compsVal env sb w r ps h.tail, interp_compVal env sb ⟨w, ⟨r⟩⟩ p h]
      have h2 := necEval_ref_compRead hT ((Env.empty v).extend (.bnd 0)
        (interp env (Term.boxtm sb))) r (.here :: p) (Ctx.ref_insert_root _ _ _)
        (h.ref_head (Ctx.ref_insert_root _ _ _)) (hall p List.mem_cons_self)
      rw [show ((Env.empty v).extend (.bnd 0) (interp env (Term.boxtm sb))).ref (.root (.bnd 0))
        (Ctx.ref_insert_root _ _ _) = interp env (Term.boxtm sb) from Env.extend_root _ _ _ _]
        at h2
      exact congrArg _ h2

omit [Γ.NoSlots] in
/-- A value with companions built from its parts, at readings: the readings. -/
theorem interp_compsBuild_compsRead {B : VarType} {v w : M.frame.W}
    (X : M.frame.Dom (.VTypeBox B) v) (r : M.frame.R v w) {Δ : Ctx} (env : M.Env Δ w)
    (main : Σ a, Term σ Δ B a) (hm : interp env main.2 = M.necEval (X : M.frame.Nec B v) ⟨w, ⟨r⟩⟩) :
    ∀ (cs : List (List Step)) (h : B.CompOk cs)
      (get : ∀ p ∈ cs, Σ c, Term σ Δ ((B.compAt p).getD .VTypeOne) c),
      (∀ (q : List Step) (hq : q ∈ cs) (hT : ModalSys.T = true),
        interp env (get q hq).2 = M.compRead hT (.VTypeBox B) (.here :: q) X r) →
      interp env (compsBuild B main cs get).2 = M.compsRead B cs h X r
  | [], _, _, _ => hm
  | p :: ps, h, get, hg => by
      change (interp env (compsBuild B main ps _).2, interp env (get p List.mem_cons_self).2) = _
      rw [interp_compsBuild_compsRead X r env main hm ps h.tail _
        (fun q hq hT => hg q (List.mem_cons_of_mem _ hq) hT),
        hg p List.mem_cons_self (h.resolve_left (List.cons_ne_nil _ _)).1]
      rfl

omit [Γ.NoSlots] in
/-- ⭐**`holeC` at readings**: its value at the source's readings is the image's readings. -/
theorem holeC_compsRead {A B : VarType} {bB : Ann B}
    (s : Term σ (Ctx.empty.insert (.bnd 0) A) B bB) (b : Bool) (hb : ModalSys.T = b)
    (hF : ModalSys.Four = false) (cs : List (List Step)) (h : B.CompOk cs) {v w : M.frame.W}
    (e : M.frame.Dom (.VTypeBox A) v) (r : M.frame.R v w) :
    M.holeVal (ShapeMap.holeC s b hb hF cs h).val.2
        (M.compsRead A (A.compsAllB b) (VarType.compOk_compsAllB b hb A) e r) =
      M.compsRead B cs h (M.holeVal (ShapeMap.holeC s b hb hF cs h).obj.2 e) r := by
  have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox A)
  have he₀ : ((Env.empty v).extend (.bnd 0) e).ref (.root (.bnd 0)) hu = e :=
    Env.extend_root _ _ _ _
  set env₀ : M.Env (Ctx.empty.insert (.bnd 0) (.VTypeBox A)) v := (Env.empty v).extend (.bnd 0) e
  set E := env₀.boxPush ⟨w, ⟨r⟩⟩
  have hR : interp E (compsSlot (σ := σ) hu (Ctx.Le.refl _) (A.compsAllB b)
      (VarType.compOk_compsAllB b hb A)).2 =
      M.compsRead A (A.compsAllB b) (VarType.compOk_compsAllB b hb A) e r := by
    rw [interp_compsSlot hu (Ctx.Le.refl _) env₀ r E (fun _ _ _ => rfl), he₀]
  rw [← hR]
  set R := interp E (compsSlot (σ := σ) hu (Ctx.Le.refl _) (A.compsAllB b)
    (VarType.compOk_compsAllB b hb A)).2
  have hE₁ : ((Env.empty w).extend (.bnd 0) R).ref (.root (.bnd 0))
      (Ctx.ref_insert_root Ctx.empty (.bnd 0) (A.compsFlat (A.compsAllB b))) = R :=
    Env.extend_root _ _ _ _
  set sb : Term σ (Ctx.empty.insert (.bnd 0) (.VTypeBox A)).boxIn B _ :=
    Term.holeAt (Term.eta (VarSymb.root (.bnd 0)).inner A (Ctx.ref_inner hu)) s
  change interp ((Env.empty w).extend (.bnd 0) R) (holeCVal s b hb hF cs h).2 =
    M.compsRead B cs h (interp env₀ (Term.boxtm sb)) r
  refine interp_compsBuild_compsRead _ r _ _ ?_ cs h _ ?_
  · rw [box_beta, interp_holeAt, interp_holeAt]
    refine congrArg (M.holeVal s) ?_
    rw [interp_eta, interp_eta]
    exact ref_compsFst_compsSlot hu (Ctx.Le.refl _) E _ _ _ _ hE₁ _
  · intro q hq hT
    have hq1 := h.single hq
    obtain ⟨-, hall⟩ := hq1.resolve_left (List.cons_ne_nil _ _)
    have hp := hq1.ref_head (Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox B))
    change interp _ (Term.subst _ _ (ok_compsRen hF A b hb) (coh_compsRen hF A b hb)
      (compVal sb q hq1).2) = _
    rw [interp_subst _ _ _ (Ctx.noProjLast_boxIn _),
      ← interp_mono (agree_compsRen hF A b hb E) (compVal sb q hq1).2, Term.mono_refl,
      interp_compVal env₀ sb ⟨w, ⟨r⟩⟩ q hq1]
    have h2 := necEval_ref_compRead hT ((Env.empty v).extend (.bnd 0) (interp env₀ (Term.boxtm sb)))
      r (.here :: q) (Ctx.ref_insert_root _ _ _) hp (hall q List.mem_cons_self)
    rw [show ((Env.empty v).extend (.bnd 0) (interp env₀ (Term.boxtm sb))).ref (.root (.bnd 0))
      (Ctx.ref_insert_root _ _ _) = interp env₀ (Term.boxtm sb) from Env.extend_root _ _ _ _]
      at h2
    exact h2

include hM in
/-- ⭐**A map between shapes preserves coming back**: if the object comes back as `o`, its image
    comes back as the value's image. -/
theorem ShapeMap.comesBack : ∀ {S T : NShape} (F : ShapeMap σ S T) {v w : M.frame.W}
    (e : M.frame.Dom S.ty v) (r : M.frame.R v w) (o : M.frame.Dom S.flat w),
    M.NComesBack S e r o → M.NComesBack T (M.holeVal F.obj.2 e) r (M.holeVal F.val.2 o)
  | _, _, .id S, _, _, e, r, o, h => by
      change M.NComesBack S (interp _ (Term.eta _ _ _)) r (interp _ (Term.eta _ _ _))
      rw [interp_eta_slot, interp_eta_slot]
      exact h
  | _, _, .comp F G, v, w, e, r, o, h => by
      change M.NComesBack _ (interp ((Env.empty v).extend (.bnd 0) e) (Term.holeAt _ _)) r
        (interp ((Env.empty w).extend (.bnd 0) o) (Term.holeAt _ _))
      rw [interp_holeAt, interp_holeAt]
      exact ShapeMap.comesBack G _ r _ (ShapeMap.comesBack F e r o h)
  | _, _, .fst S T, _, _, e, r, o, h => by
      change M.NComesBack S (interp _ (Term.eta _ _ _)) r (interp _ (Term.eta _ _ _))
      rw [interp_eta_slot_fst, interp_eta_slot_fst]
      exact h.1
  | _, _, .snd S T, _, _, e, r, o, h => by
      change M.NComesBack T (interp _ (Term.eta _ _ _)) r (interp _ (Term.eta _ _ _))
      rw [interp_eta_slot_snd, interp_eta_slot_snd]
      exact h.2
  | _, _, .pair F G, _, _, e, r, o, h =>
      ⟨ShapeMap.comesBack F e r o h, ShapeMap.comesBack G e r o h⟩
  | _, _, .pack A B, v, w, e, r, o, h => by
      have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (NShape.prod (.box A) (.box B)).ty
      have he : ((Env.empty v).extend (.bnd 0) e).ref (.root (.bnd 0)) hu = e :=
        Env.extend_root _ _ _ _
      have h1 : interp ((((Env.empty v).extend (.bnd 0) e)).boxPush ⟨w, ⟨r⟩⟩)
          (Term.eta (σ := σ) (VarSymb.step (.root (.bnd 0)) .fst).inner A
            (Ctx.ref_inner (Ctx.ref_fst_of hu))) =
          M.necEval (e.1 : M.frame.Nec A v) ⟨w, ⟨r⟩⟩ := by
        rw [interp_eta, Env.ref_inner _ _ (Ctx.ref_fst_of hu), Env.ref_fst _ hu, he]
      have h2 : interp ((((Env.empty v).extend (.bnd 0) e)).boxPush ⟨w, ⟨r⟩⟩)
          (Term.eta (σ := σ) (VarSymb.step (.root (.bnd 0)) .snd).inner B
            (Ctx.ref_inner (Ctx.ref_snd_of hu))) =
          M.necEval (e.2 : M.frame.Nec B v) ⟨w, ⟨r⟩⟩ := by
        rw [interp_eta, Env.ref_inner _ _ (Ctx.ref_snd_of hu), Env.ref_snd _ hu, he]
      have hv : M.holeVal (ShapeMap.pack (σ := σ) A B).val.2 o = o := by
        unfold holeVal
        dsimp only [ShapeMap.val]
        exact interp_eta_slot _ _ _
      have ho : M.necEval (M.holeVal (ShapeMap.pack (σ := σ) A B).obj.2 e : M.frame.Nec _ v)
          ⟨w, ⟨r⟩⟩ = ((M.necEval (e.1 : M.frame.Nec A v) ⟨w, ⟨r⟩⟩,
            M.necEval (e.2 : M.frame.Nec B v) ⟨w, ⟨r⟩⟩) : M.frame.Dom (.VTypeProd A B) w) := by
        unfold holeVal
        dsimp only [ShapeMap.obj]
        rw [box_beta]
        exact Prod.ext h1 h2
      change M.Ind (M.necEval _ _) _
      rw [ho, hv]
      exact hM.pair h.1 h.2
  | _, _, .hole (A := A) s, v, w, e, r, o, h => by
      change M.Ind (M.necEval (interp ((Env.empty v).extend (.bnd 0) e) (Term.boxtm _)) ⟨w, ⟨r⟩⟩)
        (M.holeVal s o)
      rw [box_beta, interp_holeAt, interp_eta,
        Env.ref_inner _ _ (Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox A)),
        show ((Env.empty v).extend (.bnd 0) e).ref (.root (.bnd 0))
          (Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox A)) = e from Env.extend_root _ _ _ _]
      exact hM.map s h
  | _, _, .packC A cs hcs, v, w, e, r, o, h => by
      have hv : M.holeVal (ShapeMap.packC (σ := σ) A cs hcs).val.2 o = o := by
        unfold holeVal
        dsimp only [ShapeMap.val]
        exact interp_eta_slot _ _ _
      change M.Ind (M.necEval (interp ((Env.empty v).extend (.bnd 0) e)
        (Term.boxtm (compsBody A cs hcs).2)) ⟨w, ⟨r⟩⟩)
        (M.holeVal (ShapeMap.packC (σ := σ) A cs hcs).val.2 o)
      rw [box_beta, hv]
      exact compsBody_ind hM e r cs hcs o h
  | _, _, .forgetC A cs hcs, v, w, e, r, o, h => by
      have he : M.holeVal (ShapeMap.forgetC (σ := σ) A cs hcs).obj.2 e = e := by
        unfold holeVal
        dsimp only [ShapeMap.obj]
        exact interp_eta_slot _ _ _
      have ho : M.holeVal (ShapeMap.forgetC (σ := σ) A cs hcs).val.2 o = M.compsProj A cs o := by
        unfold holeVal
        dsimp only [ShapeMap.val]
        refine (interp_eta (σ := σ) _ _ _).trans ?_
        rw [Env.ref_compsFst _ cs (Ctx.ref_insert_root Ctx.empty (.bnd 0) _)]
        exact congrArg _ (Env.extend_root _ _ _ _)
      change M.Ind (M.necEval (M.holeVal (ShapeMap.forgetC (σ := σ) A cs hcs).obj.2 e :
        M.frame.Nec A v) ⟨w, ⟨r⟩⟩) (M.holeVal (ShapeMap.forgetC (σ := σ) A cs hcs).val.2 o)
      rw [he, ho]
      exact compsBack_proj e r cs o h
  | _, _, .tupC A false hb, v, w, e, r, o, h => by
      have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (VarType.VTypeBox A)
      change M.Ind (M.necEval (interp ((Env.empty v).extend (.bnd 0) e) (Term.boxtm _)) ⟨w, ⟨r⟩⟩)
        (interp ((Env.empty w).extend (.bnd 0) o) _)
      rw [box_beta]
      refine hM.pair (M.Ind_refl _) ?_
      change M.Ind (interp _ (Term.eta (σ := σ) (VarSymb.root (.bnd 0)).inner A _))
        (interp _ (Term.eta (σ := σ) _ A _))
      erw [interp_eta, interp_eta_slot, Env.ref_inner _ _ hu,
        show ((Env.empty v).extend (.bnd 0) e).ref (.root (.bnd 0)) hu = e from
          Env.extend_root _ _ _ _]
      exact h
  | _, _, .tupC A true hb, v, w, e, r, o, h => tupC_back hM A hb e r o h _ _
  | _, _, .holeC s b hb hF cs hc, _, _, e, r, o, h => holeC_back hM s b hb hF cs hc e r o h
  | _, _, .padC Z false hb, v, w, e, r, o, h => by
      have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (VarType.VTypeBox Z)
      change M.Ind (M.necEval (interp ((Env.empty v).extend (.bnd 0) e) (Term.boxtm _)) ⟨w, ⟨r⟩⟩)
        (interp ((Env.empty w).extend (.bnd 0) o) _)
      rw [box_beta]
      refine hM.pair ?_ (M.Ind_refl _)
      change M.Ind (interp _ (Term.eta (σ := σ) (VarSymb.root (.bnd 0)).inner Z _))
        (interp _ (Term.eta (σ := σ) _ Z _))
      erw [interp_eta, interp_eta_slot, Env.ref_inner _ _ hu,
        show ((Env.empty v).extend (.bnd 0) e).ref (.root (.bnd 0)) hu = e from
          Env.extend_root _ _ _ _]
      exact h
  | _, _, .padC Z true hb, v, w, e, r, o, h => padC_back hM Z hb e r o h _ _
  | _, _, .packCC X Y csX csY hX hY, v, w, e, r, o, h => by
      have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0)
        (VarType.VTypeProd (.VTypeBox X) (.VTypeBox Y))
      have hw := Ctx.ref_insert_root Ctx.empty (.bnd 0)
        (VarType.VTypeProd (X.compsFlat csX) (Y.compsFlat csY))
      have ho : ((Env.empty w).extend (.bnd 0) o).ref (.root (.bnd 0)) hw = o :=
        Env.extend_root _ _ _ _
      have hD : ∀ a, M.necEval (M.holeVal (ShapeMap.packCC (σ := σ) X Y csX csY hX hY).obj.2 e :
          M.frame.Nec (.VTypeProd X Y) v) a =
          (M.necEval (e.1 : M.frame.Nec X v) a, M.necEval (e.2 : M.frame.Nec Y v) a) := by
        intro a
        unfold holeVal
        dsimp only [ShapeMap.obj]
        rw [box_beta]
        change (interp _ (Term.eta (σ := σ) (VarSymb.step (.root (.bnd 0)) .fst).inner X _),
          interp _ (Term.eta (σ := σ) (VarSymb.step (.root (.bnd 0)) .snd).inner Y _)) = _
        rw [interp_eta, interp_eta, Env.ref_inner _ _ (Ctx.ref_fst_of hu),
          Env.ref_inner _ _ (Ctx.ref_snd_of hu), Env.ref_fst _ hu, Env.ref_snd _ hu,
          show ((Env.empty v).extend (.bnd 0) e).ref (.root (.bnd 0)) hu = e from
            Env.extend_root _ _ _ _]
      change M.compsBack (.VTypeProd X Y) (pairComps csX csY) _ r
        (interp ((Env.empty w).extend (.bnd 0) o)
          (ShapeMap.packCC (σ := σ) X Y csX csY hX hY).val.2)
      dsimp only [ShapeMap.val]
      refine compsBack_build _ r _ _ _ _ ?_ (fun p hp hT => ?_)
      · rw [hD]
        refine hM.pair ?_ ?_
        · change M.Ind _ (interp _ (Term.eta (σ := σ) _ X _))
          rw [interp_eta, Env.ref_compsFst _ csX (Ctx.ref_fst_of hw), Env.ref_fst _ hw, ho]
          exact compsBack_proj e.1 r csX o.1 h.1
        · change M.Ind _ (interp _ (Term.eta (σ := σ) _ Y _))
          rw [interp_eta, Env.ref_compsFst _ csY (Ctx.ref_snd_of hw), Env.ref_snd _ hw, ho]
          exact compsBack_proj e.2 r csY o.2 h.2
      · rcases pairComps_mem hp with ⟨e', hq⟩ | ⟨e', hq⟩
        · generalize p.tail = q at e' hq
          subst e'
          rw [compBack_here hT, hD]
          dsimp only
          erw [interp_eta]
          have key : ∀ (a' : VarSymb) (h' : _ = some ((X.compAt q).getD .VTypeOne)),
              a' = (VarSymb.step (.root (.bnd 0)) .fst).ext (compsIdx csX q) →
              ((Env.empty w).extend (.bnd 0) o).ref a' h' =
                ((Env.empty w).extend (.bnd 0) o).ref _
                  (Ctx.ref_compsIdx csX q hq (Ctx.ref_fst_of hw)) := by
            rintro _ _ rfl
            rfl
          rw [key _ _ (by simp [pairCompAddr])]
          exact (compBack_here hT X q e.1 r _).mp (compsBack_at hT e.1 r csX _
            (Ctx.ref_fst_of hw) (by rw [Env.ref_fst _ hw, ho]; exact h.1) q hq _)
        · generalize p.tail = q at e' hq
          subst e'
          rw [compBack_here hT, hD]
          dsimp only
          erw [interp_eta]
          have key : ∀ (a' : VarSymb) (h' : _ = some ((Y.compAt q).getD .VTypeOne)),
              a' = (VarSymb.step (.root (.bnd 0)) .snd).ext (compsIdx csY q) →
              ((Env.empty w).extend (.bnd 0) o).ref a' h' =
                ((Env.empty w).extend (.bnd 0) o).ref _
                  (Ctx.ref_compsIdx csY q hq (Ctx.ref_snd_of hw)) := by
            rintro _ _ rfl
            rfl
          rw [key _ _ (by simp [pairCompAddr])]
          exact (compBack_here hT Y q e.2 r _).mp (compsBack_at hT e.2 r csY _
            (Ctx.ref_snd_of hw) (by rw [Env.ref_snd _ hw, ho]; exact h.2) q hq _)
  | _, _, .fstC X Y csX csY hX hY, v, w, e, r, o, h => by
      have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (VarType.VTypeBox (.VTypeProd X Y))
      have hw := Ctx.ref_insert_root Ctx.empty (.bnd 0)
        ((VarType.VTypeProd X Y).compsFlat (pairComps csX csY))
      have ho : ((Env.empty w).extend (.bnd 0) o).ref (.root (.bnd 0)) hw = o :=
        Env.extend_root _ _ _ _
      have hD : ∀ a, M.necEval (M.holeVal (ShapeMap.fstC (σ := σ) X Y csX csY hX hY).obj.2 e :
          M.frame.Nec X v) a = (M.necEval (e : M.frame.Nec (.VTypeProd X Y) v) a).1 := by
        intro a
        unfold holeVal
        dsimp only [ShapeMap.obj]
        rw [box_beta, interp_eta, Env.ref_fst _ (Ctx.ref_inner hu), Env.ref_inner _ _ hu,
          show ((Env.empty v).extend (.bnd 0) e).ref (.root (.bnd 0)) hu = e from
            Env.extend_root _ _ _ _]
      have hs : ∀ x : M.frame.Dom (.VTypeProd X Y) w, M.holeVal (σ := σ)
          (Term.eta (.step (.root (.bnd 0)) .fst) X
            (Ctx.ref_fst_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeProd X Y)))) x =
          x.1 := by
        intro x
        unfold holeVal
        rw [interp_eta, Env.ref_fst _ (Ctx.ref_insert_root _ _ _)]
        exact congrArg Prod.fst (Env.extend_root _ _ _ _)
      change M.compsBack X csX _ r (interp ((Env.empty w).extend (.bnd 0) o)
        (ShapeMap.fstC (σ := σ) X Y csX csY hX hY).val.2)
      dsimp only [ShapeMap.val]
      refine compsBack_build _ r _ _ _ _ ?_ (fun q hq hT => ?_)
      · rw [hD]
        change M.Ind _ (interp _ (Term.eta (σ := σ) _ X _))
        rw [interp_eta, Env.ref_fst _ (Ctx.ref_compsFst _ hw), Env.ref_compsFst _ _ hw, ho]
        have := hM.map (Term.eta (σ := σ) (.step (.root (.bnd 0)) .fst) X
          (Ctx.ref_fst_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeProd X Y))))
          (compsBack_proj e r _ o h)
        rwa [hs, hs] at this
      · rw [compBack_here hT, hD]
        dsimp only
        erw [interp_eta]
        exact (compBack_here hT (.VTypeProd X Y) (.fst :: q) e r _).mp (compsBack_at hT e r _ _
          hw (by rw [ho]; exact h) (.fst :: q)
          (List.mem_append_left _ (List.mem_map_of_mem hq)) _)
  | _, _, .sndC X Y csX csY hX hY, v, w, e, r, o, h => by
      have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (VarType.VTypeBox (.VTypeProd X Y))
      have hw := Ctx.ref_insert_root Ctx.empty (.bnd 0)
        ((VarType.VTypeProd X Y).compsFlat (pairComps csX csY))
      have ho : ((Env.empty w).extend (.bnd 0) o).ref (.root (.bnd 0)) hw = o :=
        Env.extend_root _ _ _ _
      have hD : ∀ a, M.necEval (M.holeVal (ShapeMap.sndC (σ := σ) X Y csX csY hX hY).obj.2 e :
          M.frame.Nec Y v) a = (M.necEval (e : M.frame.Nec (.VTypeProd X Y) v) a).2 := by
        intro a
        unfold holeVal
        dsimp only [ShapeMap.obj]
        rw [box_beta, interp_eta, Env.ref_snd _ (Ctx.ref_inner hu), Env.ref_inner _ _ hu,
          show ((Env.empty v).extend (.bnd 0) e).ref (.root (.bnd 0)) hu = e from
            Env.extend_root _ _ _ _]
      have hs : ∀ x : M.frame.Dom (.VTypeProd X Y) w, M.holeVal (σ := σ)
          (Term.eta (.step (.root (.bnd 0)) .snd) Y
            (Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeProd X Y)))) x =
          x.2 := by
        intro x
        unfold holeVal
        rw [interp_eta, Env.ref_snd _ (Ctx.ref_insert_root _ _ _)]
        exact congrArg Prod.snd (Env.extend_root _ _ _ _)
      change M.compsBack Y csY _ r (interp ((Env.empty w).extend (.bnd 0) o)
        (ShapeMap.sndC (σ := σ) X Y csX csY hX hY).val.2)
      dsimp only [ShapeMap.val]
      refine compsBack_build _ r _ _ _ _ ?_ (fun q hq hT => ?_)
      · rw [hD]
        change M.Ind _ (interp _ (Term.eta (σ := σ) _ Y _))
        rw [interp_eta, Env.ref_snd _ (Ctx.ref_compsFst _ hw), Env.ref_compsFst _ _ hw, ho]
        have := hM.map (Term.eta (σ := σ) (.step (.root (.bnd 0)) .snd) Y
          (Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeProd X Y))))
          (compsBack_proj e r _ o h)
        rwa [hs, hs] at this
      · rw [compBack_here hT, hD]
        dsimp only
        erw [interp_eta]
        exact (compBack_here hT (.VTypeProd X Y) (.snd :: q) e r _).mp (compsBack_at hT e r _ _
          hw (by rw [ho]; exact h) (.snd :: q)
          (List.mem_append_right _ (List.mem_map_of_mem hq)) _)
  | _, _, .subC A cs cs' hcs hcs' hsub, v, w, e, r, o, h => by
      have hw := Ctx.ref_insert_root Ctx.empty (.bnd 0) (A.compsFlat cs)
      have ho : ((Env.empty w).extend (.bnd 0) o).ref (.root (.bnd 0)) hw = o :=
        Env.extend_root _ _ _ _
      have he : M.holeVal (ShapeMap.subC (σ := σ) A cs cs' hcs hcs' hsub).obj.2 e = e := by
        unfold holeVal
        dsimp only [ShapeMap.obj]
        exact interp_eta_slot _ _ _
      change M.compsBack A cs' _ r (interp ((Env.empty w).extend (.bnd 0) o)
        (ShapeMap.subC (σ := σ) A cs cs' hcs hcs' hsub).val.2)
      rw [he]
      dsimp only [ShapeMap.val]
      refine compsBack_build e r _ _ cs' _ ?_ (fun q hq hT => ?_)
      · change M.Ind _ (interp _ (Term.eta (σ := σ) _ A _))
        rw [interp_eta, Env.ref_compsFst _ cs hw, ho]
        exact compsBack_proj e r cs o h
      · dsimp only
        erw [interp_eta]
        exact compsBack_at hT e r cs _ hw (by rw [ho]; exact h) q (hsub q hq) _

omit [Γ.NoSlots] in
theorem interp_eta_slot_fst_fst {Δ : Ctx} {v : M.frame.W} (en : M.Env Δ v) {A B C : VarType}
    (o : M.frame.Dom (.VTypeProd (.VTypeProd A B) C) v)
    (h : (Δ.insert (.bnd 0) (.VTypeProd (.VTypeProd A B) C)).ref
      (.step (.step (.root (.bnd 0)) .fst) .fst) = some A) :
    interp (en.extend (.bnd 0) o)
      (Term.eta (σ := σ) (.step (.step (.root (.bnd 0)) .fst) .fst) A h) = o.1.1 := by
  have hu := Ctx.ref_insert_root Δ (.bnd 0) (.VTypeProd (.VTypeProd A B) C)
  have e : (en.extend (.bnd 0) o).ref (.root (.bnd 0)) hu = o := Env.extend_root _ _ _ _
  rw [interp_eta, Env.ref_fst _ (Ctx.ref_fst_of hu) h, Env.ref_fst _ hu (Ctx.ref_fst_of hu), e]

omit [Γ.NoSlots] in
theorem interp_eta_slot_fst_snd {Δ : Ctx} {v : M.frame.W} (en : M.Env Δ v) {A B C : VarType}
    (o : M.frame.Dom (.VTypeProd (.VTypeProd A B) C) v)
    (h : (Δ.insert (.bnd 0) (.VTypeProd (.VTypeProd A B) C)).ref
      (.step (.step (.root (.bnd 0)) .fst) .snd) = some B) :
    interp (en.extend (.bnd 0) o)
      (Term.eta (σ := σ) (.step (.step (.root (.bnd 0)) .fst) .snd) B h) = o.1.2 := by
  have hu := Ctx.ref_insert_root Δ (.bnd 0) (.VTypeProd (.VTypeProd A B) C)
  have e : (en.extend (.bnd 0) o).ref (.root (.bnd 0)) hu = o := Env.extend_root _ _ _ _
  rw [interp_eta, Env.ref_snd _ (Ctx.ref_fst_of hu) h, Env.ref_fst _ hu (Ctx.ref_fst_of hu), e]

omit [Γ.NoSlots] in
include hM in
/-- A map on the necessary part preserves coming back at a returnable shape: the witness, carried
    along, comes back as before. -/
theorem ShapeMap.liftComesBack : ∀ (S : RShape) {T : NShape} (F : ShapeMap σ S.necPart T)
    {v w : M.frame.W} (e : M.frame.Dom S.ty v) (r : M.frame.R v w) (o : M.frame.Dom S.flat w),
    M.ComesBack S e r o →
      M.ComesBack (S.withNec T) (M.holeVal (ShapeMap.liftObj S F).2 e) r
        (M.holeVal (ShapeMap.liftVal S F).2 o)
  | .nec _, _, F, _, _, e, r, o, h => ShapeMap.comesBack hM F e r o h
  | .wit N X, _, F, v, w, e, r, o, h => by
      obtain ⟨h₁, h₂⟩ := h
      refine ⟨?_, ?_⟩
      · change M.NComesBack _ (interp ((Env.empty v).extend (.bnd 0) e) (Term.holeAt _ _)) r
          (interp ((Env.empty w).extend (.bnd 0) o) (Term.holeAt _ _))
        rw [interp_holeAt, interp_holeAt, interp_eta_slot_fst, interp_eta_slot_fst]
        exact ShapeMap.comesBack hM F e.1 r o.1 h₁
      · have key : ∀ (p : M.frame.Pos X v) (q : M.frame.Dom X w), p = e.2 → q = o.2 →
            ∃ h : (⟨w, ⟨r⟩⟩ : M.frame.Acc v) ∈ (M.posEval p).1,
            M.Ind ((M.posEval p).2 ⟨_, h⟩) q := by
          rintro _ _ rfl rfl
          exact h₂
        exact key _ _ (interp_eta_slot_snd _ _ _) (interp_eta_slot_snd _ _ _)

include hnp in
/-- What `ret_extS` hands its subproof: the object with its companion comes back as the value
    with the companion's value along the same way home, the companion joining the necessary
    part. -/
theorem sat_ret_extS (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {S : RShape} {B : VarType}
    {a : Ann S.flat} (t : Term σ Γ S.flat a)
    (Φ : WFF σ ((O.view.insert (.bnd 0) S.ty).insert (.bnd 1) (.VTypeBox B)) 2)
    (c : ℕ) (hc : Γ.RootFresh (.free c)) (i : O.Arr env)
    (d : M.frame.Dom S.ty (O.acc env i).1) (b : M.frame.Dom (.VTypeBox B) (O.acc env i).1)
    (hΦ : M.sat (((O.push env i).extend (.bnd 0) d).extend (.bnd 1) b) Φ)
    (r : M.frame.R (O.acc env i).1 w) (hr : M.ComesBack S d r (interp env t)) :
    M.sat (env.extend (.free c) (M.necEval (b : M.frame.Nec B (O.acc env i).1) ⟨w, ⟨r⟩⟩))
      ((O.mono (Ctx.le_insert hc.root B)).retS hS (S.ext B)
        (S.extTm (Term.weaken hc.root B t)
          (Term.eta (.root (.free c)) B (Ctx.ref_insert_root Γ (.free c) B))).2
        (WFF.mono ((O.le_view_mono (Ctx.le_insert hc.root B)).insert (.bnd 0) _)
          (WFF.bodySplit (S.extL O.view B).2 (S.extR O.view B).2 Φ))) := by
  set o := M.necEval (b : M.frame.Nec B (O.acc env i).1) ⟨w, ⟨r⟩⟩
  have hag := Env.agree_extend env hc.root o
  have hslot : (env.extend (.free c) o).ref (.root (.free c)) (Ctx.ref_insert_root Γ (.free c) B) =
      o := Env.extend_root env (.free c) o (Ctx.ref_insert_root Γ (.free c) B)
  have hcv : M.Ind (M.necEval (b : M.frame.Nec B (O.acc env i).1) ⟨w, ⟨r⟩⟩)
      (interp (env.extend (.free c) o)
        (Term.eta (.root (.free c)) B (Ctx.ref_insert_root Γ (.free c) B))) := by
    rw [interp_eta, hslot]
    exact M.Ind_refl _
  have ip : ∀ {Δ : Ctx} {v : M.frame.W} (en : M.Env Δ v) {A C : VarType} {a : Ann A}
      {c : Ann C} (s : Term σ Δ A a) (u : Term σ Δ C c),
      interp en (Term.pair s u) = (interp en s, interp en u) := by intros; rfl
  cases S with
  | nec N =>
      refine OutLeg.sat_retS_agree hag hS O (RShape.ext (.nec N) B) _ _ i
        ((d, b) : M.frame.Dom (RShape.ext (.nec N) B).ty (O.acc env i).1) ?_ r ?_
      · rw [sat_bodySplit O.noProjLast]
        dsimp only [RShape.extL, RShape.extR]
        rw [interp_eta_slot_fst (A := N.ty) (B := .VTypeBox B),
          interp_eta_slot_snd (A := N.ty) (B := .VTypeBox B)]
        exact hΦ
      · refine ⟨?_, hcv⟩
        change M.NComesBack N d r (interp _ (Term.mono _ t))
        rw [interp_mono hag t]
        exact hr
  | wit N X =>
      refine OutLeg.sat_retS_agree hag hS O (RShape.ext (.wit N X) B) _ _ i
        (((d.1, b), d.2) : M.frame.Dom (RShape.ext (.wit N X) B).ty (O.acc env i).1) ?_ r ?_
      · rw [sat_bodySplit O.noProjLast]
        dsimp only [RShape.extL, RShape.extR]
        rw [ip, interp_eta_slot_fst_fst (A := N.ty) (B := .VTypeBox B) (C := .VTypeDia X),
          interp_eta_slot_snd (A := .VTypeProd N.ty (.VTypeBox B)) (B := .VTypeDia X),
          interp_eta_slot_fst_snd (A := N.ty) (B := .VTypeBox B) (C := .VTypeDia X)]
        exact hΦ
      · have hv : interp (env.extend (.free c) o) ((RShape.wit N X).extTm (Term.weaken hc.root B t)
            (Term.eta (.root (.free c)) B (Ctx.ref_insert_root Γ (.free c) B))).2 =
            (((interp env t).1, interp (env.extend (.free c) o)
              (Term.eta (.root (.free c)) B (Ctx.ref_insert_root Γ (.free c) B))),
              (interp env t).2) := by
          dsimp only [RShape.extTm]
          rw [interp_holeRead (hnp.insert (.free c) B), ip]
          unfold holeVal
          rw [ip, ip, interp_eta_slot_fst_fst, interp_eta_slot_snd, interp_eta_slot_fst_snd]
          have hw : interp (env.extend (.free c) o) (Term.weaken hc.root B t) = interp env t :=
            interp_mono hag t
          rw [hw]
        rw [hv]
        exact ⟨⟨hr.1, hcv⟩, hr.2⟩

include hnp in
/-- What `ret_compS` hands its subproof: the object comes back with its new companion's reading
    along the same way home as the companion's value. -/
theorem sat_ret_compS (hS : ModalSys.BStrong = true) (O : OutLeg Γ) (S : RShape) {A : VarType}
    {cs : List (List Step)} {h : A.CompOk cs} (p : List Step) (h' : A.CompOk (p :: cs))
    {a : Ann (S.withNec (.boxC A cs h)).flat} (t : Term σ Γ (S.withNec (.boxC A cs h)).flat a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (S.withNec (.boxC A cs h)).ty) 1)
    (c : ℕ) (hc : Γ.RootFresh (.free c)) (i : O.Arr env)
    (d : M.frame.Dom (S.withNec (.boxC A cs h)).ty (O.acc env i).1)
    (hΦ : M.sat ((O.push env i).extend (.bnd 0) d) Φ) (r : M.frame.R (O.acc env i).1 w)
    (hr : M.ComesBack (S.withNec (.boxC A cs h)) d r (interp env t)) :
    ∃ o : M.frame.Dom ((A.compAt p).getD .VTypeOne) w,
      M.sat (env.extend (.free c) o)
        ((O.mono (Ctx.le_insert hc.root _)).retS hS (S.withNec (.boxC A (p :: cs) h'))
          (RShape.compTm A cs h p h' S (Term.weaken hc.root _ t)
            (Term.eta (.root (.free c)) _ (Ctx.ref_insert_root Γ (.free c) _))).2
          (WFF.mono ((O.le_view_mono (Ctx.le_insert hc.root _)).insert (.bnd 0) _)
            (WFF.bodyRepl (RShape.compL O.view A cs h p h' S).2 Φ))) := by
  have hT := (h'.resolve_left (List.cons_ne_nil _ _)).1
  have ip : ∀ {Δ : Ctx} {v : M.frame.W} (en : M.Env Δ v) {A C : VarType} {a : Ann A}
      {c : Ann C} (s : Term σ Δ A a) (u : Term σ Δ C c),
      interp en (Term.pair s u) = (interp en s, interp en u) := by intros; rfl
  cases S with
  | nec N =>
      refine ⟨M.compRead hT (.VTypeBox A) (.here :: p) d r, ?_⟩
      set o := M.compRead hT (.VTypeBox A) (.here :: p) d r
      have hag := Env.agree_extend env hc.root o
      have hslot : (env.extend (.free c) o).ref (.root (.free c))
          (Ctx.ref_insert_root Γ (.free c) _) = o := Env.extend_root env (.free c) o _
      refine OutLeg.sat_retS_agree hag hS O _ _ _ i d ?_ r ?_
      · rw [sat_bodyRepl O.noProjLast]
        dsimp only [RShape.compL]
        convert hΦ using 2
        exact interp_eta_slot _ _ _
      · change M.compsBack A (p :: cs) d r (interp _ (Term.pair _ _))
        rw [ip]
        refine ⟨?_, ?_⟩
        · dsimp only
          erw [interp_mono hag t]
          exact hr
        · rw [dif_pos hT]
          change M.compBack (.VTypeBox A) (.here :: p) d r (interp _ (Term.eta _ _ _))
          rw [interp_eta, hslot]
          exact M.compBack_compRead hT _ _ d r
  | wit N X =>
      refine ⟨M.compRead hT (.VTypeBox A) (.here :: p) d.1 r, ?_⟩
      set o := M.compRead hT (.VTypeBox A) (.here :: p) d.1 r
      have hag := Env.agree_extend env hc.root o
      have hslot : (env.extend (.free c) o).ref (.root (.free c))
          (Ctx.ref_insert_root Γ (.free c) _) = o := Env.extend_root env (.free c) o _
      refine OutLeg.sat_retS_agree hag hS O _ _ _ i d ?_ r ?_
      · rw [sat_bodyRepl O.noProjLast]
        dsimp only [RShape.compL]
        convert hΦ using 2
        exact interp_eta_slot _ _ _
      · have hv : interp (env.extend (.free c) o) (RShape.compTm A cs h p h' (.wit N X)
            (Term.weaken hc.root _ t)
            (Term.eta (.root (.free c)) _ (Ctx.ref_insert_root Γ (.free c) _))).2 =
            (((interp env t).1, o), (interp env t).2) := by
          dsimp only [RShape.compTm]
          rw [interp_holeRead (hnp.insert (.free c) _), ip]
          unfold holeVal
          rw [ip, ip]
          erw [interp_eta_slot_fst_fst, interp_eta_slot_snd, interp_eta_slot_fst_snd]
          rw [interp_eta, hslot]
          have hw : interp (env.extend (.free c) o) (Term.weaken hc.root _ t) = interp env t :=
            interp_mono hag t
          dsimp only
          exact congrArg (fun z => ((z.1, o), z.2)) hw
        rw [hv]
        refine ⟨⟨hr.1, ?_⟩, hr.2⟩
        rw [dif_pos hT]
        exact M.compBack_compRead hT _ _ d.1 r

omit [Γ.NoSlots] in
include hM in
/-- ⭐**β on the possible part preserves coming back**: the mapped possible part has the same
    worlds, so the way home still lies in its extent, and its content there is `h` of things `Ind`
    to the value's components. -/
theorem ShapeMap.possComesBack₀ {C X Z : VarType} {b : Ann Z}
    (h : Term σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C X)) Z b) {v w : M.frame.W}
    (e : M.frame.Dom (RShape.wit (.box C) X).ty v) (r : M.frame.R v w)
    (o : M.frame.Dom (RShape.wit (.box C) X).flat w)
    (hcb : M.ComesBack (.wit (.box C) X) e r o) :
    M.ComesBack (.wit (.box C) Z) (M.holeVal (ShapeMap.possObj h).2 e) r
      (M.holeVal (ShapeMap.possVal h).2 o) := by
  obtain ⟨h₁, hm, h₂⟩ := hcb
  have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (RShape.wit (.box C) X).ty
  have hsnd := Ctx.ref_snd_of hu
  set env₁ := (Env.empty v).extend (.bnd 0) e
  have he1 : env₁.ref (.root (.bnd 0)) hu = e := Env.extend_root _ _ _ hu
  have he2 : env₁.ref (.step (.root (.bnd 0)) .snd) hsnd = e.2 := by
    rw [Env.ref_snd _ hu hsnd]
    exact congrArg Prod.snd he1
  refine ⟨?_, ?_⟩
  · change M.NComesBack (.box C) (interp env₁ (Term.eta _ _ _)) r
      (interp ((Env.empty w).extend (.bnd 0) o) (Term.eta _ _ _))
    rw [interp_eta_slot_fst, interp_eta_slot_fst]
    exact h₁
  · let tin : Term σ ((Ctx.empty.insert (.bnd 0) (RShape.wit (.box C) X).ty).diaIn
        (.step (.root (.bnd 0)) .snd)) Z _ :=
      Term.holeAt
        (Term.pair
          (Term.eta (VarSymb.step (.root (.bnd 0)) .fst).inner C
            ((Ctx.le_boxIn_diaIn _ _).ref (Ctx.ref_inner (Ctx.ref_fst_of hu))))
          (Term.eta (VarSymb.step (.step (.root (.bnd 0)) .snd) .dia) X
            (Ctx.ref_diaIn_of hsnd)))
        h
    have hD : M.posEval ((M.holeVal (ShapeMap.possObj h).2 e).2 : M.frame.Pos Z v) =
        ⟨(M.posEval (env₁.ref _ hsnd)).1, fun w' => interp (env₁.diaPush _ hsnd w') tin⟩ :=
      dia_beta env₁ ⟨X, hsnd⟩ hsnd tin
    let bb : (M.posEval (env₁.ref (.step (.root (.bnd 0)) .snd) hsnd)).1 := ⟨⟨w, ⟨r⟩⟩, he2 ▸ hm⟩
    have hcont : (M.posEval (env₁.ref (.step (.root (.bnd 0)) .snd) hsnd)).2 bb =
        (M.posEval (e.2 : M.frame.Pos X v)).2 ⟨_, hm⟩ := by
      have key : ∀ (P : M.frame.Pos X v) (hP : P = e.2)
          (hmP : (⟨w, ⟨r⟩⟩ : M.frame.Acc v) ∈ (M.posEval P).1),
          (M.posEval P).2 ⟨_, hmP⟩ = (M.posEval (e.2 : M.frame.Pos X v)).2 ⟨_, hm⟩ := by
        intro P hP hmP
        subst hP
        rfl
      exact key _ he2 _
    have hv : (M.holeVal (ShapeMap.possVal h).2 o).2 =
        interp ((Env.empty w).extend (.bnd 0) o) h := rfl
    rw [hv]
    generalize hQ : M.posEval ((M.holeVal (ShapeMap.possObj h).2 e).2 : M.frame.Pos Z v) = Q
    obtain rfl := hQ.symm.trans hD
    refine ⟨bb.2, ?_⟩
    change M.Ind (interp (env₁.diaPush _ hsnd bb) tin) _
    rw [interp_holeAt]
    change M.Ind (M.holeVal h (interp _ _, interp _ _)) _
    rw [interp_eta, interp_eta,
      ← Env.ref_agree (Env.diaPush_boxIn env₁ hsnd bb) _ (Ctx.ref_inner (Ctx.ref_fst_of hu)),
      Env.ref_inner _ _ (Ctx.ref_fst_of hu), Env.ref_fst _ hu, he1,
      Env.ref_dia env₁ hsnd bb (Ctx.ref_diaIn_of hsnd), hcont]
    exact hM.map h (hM.pair h₁ h₂)

omit [Γ.NoSlots] in
include hM in
/-- ⭐**β on the possible part preserves coming back**, at a necessary part with companions: the
    necessary part and its companions are kept, and the content is mapped by `h` of things `Ind`
    to the value's contents (`compsBack_main`) and content. -/
theorem ShapeMap.possComesBack {C X Z : VarType} {b : Ann Z}
    (h : Term σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C X)) Z b) :
    ∀ (cs : List (List Step)) (hcs : C.CompOk cs) {v w : M.frame.W}
      (e : M.frame.Dom (RShape.wit (.boxC C cs hcs) X).ty v) (r : M.frame.R v w)
      (o : M.frame.Dom (RShape.wit (.boxC C cs hcs) X).flat w),
      M.ComesBack (.wit (.boxC C cs hcs) X) e r o →
      M.ComesBack (.wit (.boxC C cs hcs) Z) (M.holeVal (ShapeMap.possObj h).2 e) r
        (M.holeVal (ShapeMap.possValC h cs hcs).2 o)
  | [], _, _, _, e, r, o, hcb => ShapeMap.possComesBack₀ hM h e r o hcb
  | p :: ps, hcs, v, w, e, r, o, hcb => by
      obtain ⟨h₁, hm, h₂⟩ := hcb
      have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (RShape.wit (.box C) X).ty
      have hsnd := Ctx.ref_snd_of hu
      set env₁ := (Env.empty v).extend (.bnd 0) e
      have he1 : env₁.ref (.root (.bnd 0)) hu = e := Env.extend_root _ _ _ hu
      have he2 : env₁.ref (.step (.root (.bnd 0)) .snd) hsnd = e.2 := by
        rw [Env.ref_snd _ hu hsnd]
        exact congrArg Prod.snd he1
      have hu' := Ctx.ref_insert_root Ctx.empty (.bnd 0)
        (RShape.wit (.boxC C (p :: ps) hcs) X).flat
      set env₂ := (Env.empty w).extend (.bnd 0) o
      have he₂ : env₂.ref (.root (.bnd 0)) hu' = o := Env.extend_root _ _ _ hu'
      refine ⟨?_, ?_⟩
      · change M.NComesBack (.boxC C (p :: ps) hcs) (interp env₁ (Term.eta _ _ _)) r
          (interp env₂ (Term.eta _ _ _))
        rw [interp_eta_slot_fst, interp_eta_slot_fst]
        exact h₁
      · let tin : Term σ ((Ctx.empty.insert (.bnd 0) (RShape.wit (.box C) X).ty).diaIn
            (.step (.root (.bnd 0)) .snd)) Z _ :=
          Term.holeAt
            (Term.pair
              (Term.eta (VarSymb.step (.root (.bnd 0)) .fst).inner C
                ((Ctx.le_boxIn_diaIn _ _).ref (Ctx.ref_inner (Ctx.ref_fst_of hu))))
              (Term.eta (VarSymb.step (.step (.root (.bnd 0)) .snd) .dia) X
                (Ctx.ref_diaIn_of hsnd)))
            h
        have hD : M.posEval ((M.holeVal (ShapeMap.possObj h).2 e).2 : M.frame.Pos Z v) =
            ⟨(M.posEval (env₁.ref _ hsnd)).1, fun w' => interp (env₁.diaPush _ hsnd w') tin⟩ :=
          dia_beta env₁ ⟨X, hsnd⟩ hsnd tin
        let bb : (M.posEval (env₁.ref (.step (.root (.bnd 0)) .snd) hsnd)).1 :=
          ⟨⟨w, ⟨r⟩⟩, he2 ▸ hm⟩
        have hcont : (M.posEval (env₁.ref (.step (.root (.bnd 0)) .snd) hsnd)).2 bb =
            (M.posEval (e.2 : M.frame.Pos X v)).2 ⟨_, hm⟩ := by
          have key : ∀ (P : M.frame.Pos X v) (hP : P = e.2)
              (hmP : (⟨w, ⟨r⟩⟩ : M.frame.Acc v) ∈ (M.posEval P).1),
              (M.posEval P).2 ⟨_, hmP⟩ = (M.posEval (e.2 : M.frame.Pos X v)).2 ⟨_, hm⟩ := by
            intro P hP hmP
            subst hP
            rfl
          exact key _ he2 _
        generalize hQ : M.posEval ((M.holeVal (ShapeMap.possObj h).2 e).2 : M.frame.Pos Z v) = Q
        obtain rfl := hQ.symm.trans hD
        refine ⟨bb.2, ?_⟩
        change M.Ind (interp (env₁.diaPush _ hsnd bb) tin)
          (interp env₂ (Term.holeAt (Term.pair (Term.eta _ C _) (Term.eta _ X _)) h))
        rw [interp_holeAt, interp_holeAt]
        change M.Ind (M.holeVal h (interp _ _, interp _ _))
          (M.holeVal h (interp env₂ (Term.eta _ C _), interp env₂ (Term.eta _ X _)))
        rw [interp_eta, interp_eta, interp_eta, interp_eta,
          ← Env.ref_agree (Env.diaPush_boxIn env₁ hsnd bb) _ (Ctx.ref_inner (Ctx.ref_fst_of hu)),
          Env.ref_inner _ _ (Ctx.ref_fst_of hu), Env.ref_fst _ hu, he1,
          Env.ref_dia env₁ hsnd bb (Ctx.ref_diaIn_of hsnd), hcont, Env.ref_snd _ hu', he₂]
        refine hM.map h (hM.pair ?_ h₂)
        exact compsBack_main e.1 r (p :: ps) env₂ (Ctx.ref_fst_of hu')
          (by rw [Env.ref_fst _ hu', he₂]; exact h₁) _

include hnp hM in
/-- ⭐`ret_mapD` is sound: the mapped object has the body, and comes back with the content
    mapped. -/
theorem sat_ret_mapD (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {C X Z : VarType}
    {cs : List (List Step)} {hcs : C.CompOk cs}
    {b : Ann Z} (h : Term σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C X)) Z b)
    {a : Ann (RShape.wit (.boxC C cs hcs) X).flat}
    (y : Term σ Γ (RShape.wit (.boxC C cs hcs) X).flat a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit (.boxC C cs hcs) Z).ty) 1)
    (hs : M.sat env (O.retS hS (.wit (.boxC C cs hcs) X) y (WFF.bodyRepl
      (Term.mono ((Ctx.empty_le O.view).insert (.bnd 0) _) (ShapeMap.possObj h).2) Φ) :
        WFF σ Γ 0)) :
    M.sat env (O.retS hS (.wit (.boxC C cs hcs) Z)
      (Term.holeRead y (ShapeMap.possValC h cs hcs).2) Φ : WFF σ Γ 0) := by
  obtain ⟨i, e, hΦ, r, hr⟩ := (OutLeg.sat_retS hS env O _ y _).mp hs
  rw [sat_bodyRepl O.noProjLast] at hΦ
  refine (OutLeg.sat_retS hS env O (.wit (.boxC C cs hcs) Z) _ Φ).mpr ⟨i, _, hΦ, r, ?_⟩
  rw [interp_holeRead hnp env y, interp_mono (Env.extend_agree (h := Ctx.empty_le O.view)
    (env := Env.empty _) (env' := O.push env i) (fun _ _ h => nomatch h) (.bnd 0) e)]
  exact ShapeMap.possComesBack hM h cs hcs e r _ hr

include hnp hM in
/-- ⭐`ret_map` is sound: the image of the object out there has the body, and comes back as the
    image of the value. -/
theorem sat_ret_map (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {S : RShape} {T : NShape}
    (F : ShapeMap σ S.necPart T) {a : Ann S.flat} (y : Term σ Γ S.flat a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (S.withNec T).ty) 1)
    (h : M.sat env (O.retS hS S y (WFF.bodyRepl
      (Term.mono ((Ctx.empty_le O.view).insert (.bnd 0) S.ty) (ShapeMap.liftObj S F).2) Φ) :
        WFF σ Γ 0)) :
    M.sat env (O.retS hS (S.withNec T) (Term.holeRead y (ShapeMap.liftVal S F).2) Φ :
      WFF σ Γ 0) := by
  obtain ⟨i, e, hΦ, r, hr⟩ := (OutLeg.sat_retS hS env O S y _).mp h
  rw [sat_bodyRepl O.noProjLast] at hΦ
  refine (OutLeg.sat_retS hS env O (S.withNec T) _ Φ).mpr ⟨i, _, hΦ, r, ?_⟩
  rw [interp_holeRead hnp env y, interp_mono (Env.extend_agree (h := Ctx.empty_le O.view)
    (env := Env.empty _) (env' := O.push env i) (fun _ _ h => nomatch h) (.bnd 0) e)]
  exact ShapeMap.liftComesBack hM S F e r _ hr

include hM in
/-- ⭐**The witnessed unit is sound**: at the far end of `x`'s arrow `a`, the way home `r` goes back
    here, where `sb`'s object comes back along `a` as `sb` and `x` itself is realised along `a`
    with content `u`. -/
theorem sat_ret_unitWC (hS : ModalSys.BStrong = true) {x : VarSymb}
    (hx : ∃ X', Γ.ref x = some (.VTypeDia X')) {C A X : VarType} (co : List (List Step))
    (ho : C.CompOk co) {c : Ann (C.compsFlat co)} (y : Term σ Γ (C.compsFlat co) c)
    (Ψ : WFF σ ((Γ.diaIn x).insert (.bnd 0) (.VTypeBox C)) 1) {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X} (u : Term σ (Γ.diaIn x) X b₀)
    (cs : List (List Step)) (hcs : A.CompOk cs)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (C.compsFlat co) (RShape.wit (.box A) X).ty)) 1)
    (hret : M.sat env (WFF.retxS hS x hx (.nec (.boxC C co ho)) y Ψ : WFF σ Γ 0))
    (hθ : M.holeSat θ ((interp env y, (interp env (Term.boxtm sb),
      interp env (Term.diatm x hx u))) :
        M.frame.Dom (.VTypeProd (C.compsFlat co) (RShape.wit (.box A) X).ty) w)) :
    M.sat env (WFF.retxS hS x hx (.nec (.boxC C co ho)) y
      (WFF.and Ψ (WFF.unitBodyWC hS co ho sb u cs hcs θ)) : WFF σ Γ 0) := by
  obtain ⟨Y, h, a, e, hΨ, r, hr⟩ := hret
  refine ⟨Y, h, a, e, ⟨hΨ, ?_⟩, r, hr⟩
  have hu := Ctx.ref_insert_root (Γ.diaIn x) (.bnd 0) (.VTypeBox C)
  let val : M.frame.Dom (RShape.wit (.boxC A cs hcs) X).ty w :=
    (interp env (Term.boxtm sb), interp env (Term.diatm x hx u))
  refine ⟨⟨w, ⟨r⟩⟩, val, ?_, a.1.2.down, ?_, ?_⟩
  · rw [sat_holeAt]
    have hag := Env.agree_extend (T := (RShape.wit (.boxC A cs hcs) X).ty)
      (((env.diaPush x h a).extend (.bnd 0) e).boxPush ⟨w, ⟨r⟩⟩)
      ((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert (.VTypeBox C)).boxIn.root val
    change M.holeSat θ (interp _ _, interp _ _)
    erw [interp_eta]
    rw [show ((((env.diaPush x h a).extend (.bnd 0) e).boxPush ⟨w, ⟨r⟩⟩).extend
          (T := (RShape.wit (.boxC A cs hcs) X).ty) (.bnd (0 + 1)) val).ref (.root (.bnd 1))
          (Ctx.ref_insert_root _ (.bnd 1) _) = val from Env.extend_root _ _ _ _]
    have hr' : M.compsBack C co (((env.diaPush x h a).extend (.bnd 0) e).ref
        (.root (.bnd 0)) hu) r (interp env y) := by
      rw [show ((env.diaPush x h a).extend (.bnd 0) e).ref (.root (.bnd 0)) hu = e from
        Env.extend_root _ (.bnd 0) e _]
      exact hr
    exact (holeSat_ind hM θ (hM.pair (compsSlot_ind hM hu _ _ r _ hag co ho _ hr')
      (M.Ind_refl _))).mpr hθ
  · change M.compsBack A cs (interp env (Term.boxtm sb)) a.1.2.down
      (interp _ (Term.mono _ (compsVal sb cs hcs).2))
    rw [← Term.mono_mono (Ctx.le_boxIn_diaIn Γ x)
        (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root (.VTypeBox C)),
      interp_mono (Env.agree_extend (env.diaPush x h a)
        (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root e),
      interp_mono (Env.diaPush_boxIn env h a)]
    exact compsBack_compsVal env sb a.1 cs hcs
  · change ∃ hm : _ ∈ (M.posEval (interp env (Term.diatm x hx u))).1,
      M.Ind ((M.posEval (interp env (Term.diatm x hx u))).2 ⟨_, hm⟩)
        (interp ((env.diaPush x h a).extend (.bnd 0) e) (Term.mono _ u))
    rw [dia_beta env hx h u]
    refine ⟨a.2, ?_⟩
    rw [interp_mono (Env.agree_extend (env.diaPush x h a)
      (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root e)]
    exact M.Ind_refl _

include hM in
/-- The unit along a returned possible part, at the far end of an arrow `ac` whose object `e`
    comes back as `y` along `r`. -/
theorem sat_unitBodyDC_at (hS : ModalSys.BStrong = true) {C X A : VarType}
    (co : List (List Step)) (ho : C.CompOk co)
    {c : Ann (.VTypeProd (C.compsFlat co) X)} (y : Term σ Γ (.VTypeProd (C.compsFlat co) X) c)
    {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) (cs : List (List Step)) (hcs : A.CompOk cs)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd (C.compsFlat co) X) (.VTypeBox A))) 1)
    (ac : M.frame.Acc w) (e : M.frame.Dom (RShape.wit (.box C) X).ty ac.1)
    (r : M.frame.R ac.1 w) (hr : M.ComesBack (.wit (.boxC C co ho) X) e r (interp env y))
    (hθ : M.holeSat θ ((interp env y, interp env (Term.boxtm sb)) :
      M.frame.Dom (.VTypeProd (.VTypeProd (C.compsFlat co) X) (.VTypeBox A)) w)) :
    M.sat ((env.boxPush ac).extend (.bnd 0) e) (WFF.unitBodyDC hS co ho sb cs hcs θ) := by
  obtain ⟨hr1, hm, hr2⟩ := hr
  have hu := Ctx.ref_insert_root Γ.boxIn (.bnd 0) (RShape.wit (.box C) X).ty
  have hsnd := Ctx.ref_snd_of hu
  have he2 : ((env.boxPush ac).extend (.bnd 0) e).ref (.step (.root (.bnd 0)) .snd) hsnd = e.2 := by
    rw [Env.ref_snd _ hu hsnd]
    exact congrArg Prod.snd (Env.extend_root _ _ _ _)
  let env₁ := (env.boxPush ac).extend (.bnd 0) e
  let bb : (M.posEval (env₁.ref (.step (.root (.bnd 0)) .snd) hsnd)).1 := ⟨⟨w, ⟨r⟩⟩, he2 ▸ hm⟩
  have hcont : (M.posEval (env₁.ref (.step (.root (.bnd 0)) .snd) hsnd)).2 bb =
      (M.posEval (e.2 : M.frame.Pos X ac.1)).2 ⟨_, hm⟩ := by
    have key : ∀ (P : M.frame.Pos X ac.1) (hP : P = e.2)
        (hmP : (⟨w, ⟨r⟩⟩ : M.frame.Acc ac.1) ∈ (M.posEval P).1),
        (M.posEval P).2 ⟨_, hmP⟩ = (M.posEval (e.2 : M.frame.Pos X ac.1)).2 ⟨_, hm⟩ := by
      intro P hP hmP
      subst hP
      rfl
    exact key _ he2 _
  have he1 : env₁.ref (.root (.bnd 0)) hu = e := Env.extend_root (env.boxPush ac) (.bnd 0) e hu
  refine ⟨X, hsnd, bb, interp env (Term.boxtm sb), ?_, ac.2.down, ?_⟩
  · rw [sat_holeAt]
    have hag := Env.agree_extend (env₁.diaPush (.step (.root (.bnd 0)) .snd) hsnd bb)
      ((((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert _).diaIn _).root)
      (interp env (Term.boxtm sb))
    have hf : ((Γ.boxIn.insert (.bnd 0) (RShape.wit (.box C) X).ty).diaIn
        (.step (.root (.bnd 0)) .snd)).ref (VarSymb.step (.root (.bnd 0)) .fst).inner = some C :=
      (Ctx.le_boxIn_diaIn _ _).ref (Ctx.ref_inner (Ctx.ref_fst_of hu))
    have hd := Ctx.ref_diaIn_of hsnd
    change M.holeSat θ ((interp _ _, interp _ _), interp _ _)
    rw [interp_eta, interp_eta, ← Env.ref_agree hag _ hd,
      show (((env₁.diaPush (.step (.root (.bnd 0)) .snd) hsnd bb).extend (.bnd 1)
          (interp env (Term.boxtm sb))).ref (.root (.bnd 1)) (Ctx.ref_insert_root _ _ _)) =
          interp env (Term.boxtm sb) from Env.extend_root _ _ _ _,
      Env.ref_dia env₁ hsnd bb hd, hcont]
    have hr1' : M.compsBack C co (env₁.ref _ (Ctx.ref_fst_of hu)) r (interp env y).1 := by
      rw [Env.ref_fst _ hu, he1]
      exact hr1
    have hslot := compsSlot_ind hM (Ctx.ref_fst_of hu) _ env₁ r _
      ((Env.diaPush_boxIn env₁ hsnd bb).trans hag) co ho _ hr1'
    exact (holeSat_ind hM θ (hM.pair (hM.pair hslot hr2) (M.Ind_refl _))).mpr hθ
  · dsimp only [ComesBack, NComesBack]
    rw [interp_mono (Env.agree_extend (env.boxPush ac) (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root e)]
    exact compsBack_compsVal env sb ac cs hcs

include hM in
/-- ⭐**The unit along a returned possible part is sound**, along any leg: the way home lies in
    the possible part's extent, so home is reached along it, where the part's content is the
    value's second component and `sb`'s object comes back along the arrow out. -/
theorem sat_ret_unitDC (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {C X A : VarType}
    (co : List (List Step)) (ho : C.CompOk co)
    {c : Ann (.VTypeProd (C.compsFlat co) X)} (y : Term σ Γ (.VTypeProd (C.compsFlat co) X) c)
    (Ψ : WFF σ (O.view.insert (.bnd 0) (RShape.wit (.box C) X).ty) 1) {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) (cs : List (List Step)) (hcs : A.CompOk cs)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd (C.compsFlat co) X) (.VTypeBox A))) 1)
    (hret : M.sat env (O.retS hS (.wit (.boxC C co ho) X) y Ψ : WFF σ Γ 0))
    (hθ : M.holeSat θ ((interp env y, interp env (Term.boxtm sb)) :
      M.frame.Dom (.VTypeProd (.VTypeProd (C.compsFlat co) X) (.VTypeBox A)) w)) :
    M.sat env (O.retS hS (.wit (.boxC C co ho) X) y
      (WFF.and Ψ (O.lift (WFF.unitBodyDC hS co ho sb cs hcs θ))) : WFF σ Γ 0) := by
  obtain ⟨i, e, hΨ, r, hr⟩ := (OutLeg.sat_retS hS env O (.wit (.boxC C co ho) X) y Ψ).mp hret
  exact (OutLeg.sat_retS hS env O (.wit (.boxC C co ho) X) y _).mpr ⟨i, e,
    ⟨hΨ, (OutLeg.sat_lift env O i e _).mpr
      (sat_unitBodyDC_at env hM hS co ho y sb cs hcs θ _ e r hr hθ)⟩, r, hr⟩

include hM in
/-- ⭐**The doubly witnessed unit is sound**: at the far end of `x`'s arrow `a`, the way home `r`
    lies in the returned possible part's extent; along it `sb`'s object comes back as `sb`, and `x`
    itself is realised along `a` with content `u` (`sat_ret_unitD`, `sat_ret_unitW`). -/
theorem sat_ret_unitWDC (hS : ModalSys.BStrong = true) {x : VarSymb}
    (hx : ∃ X', Γ.ref x = some (.VTypeDia X')) {C Xe A X : VarType}
    (co : List (List Step)) (ho : C.CompOk co)
    {c : Ann (.VTypeProd (C.compsFlat co) Xe)} (y : Term σ Γ (.VTypeProd (C.compsFlat co) Xe) c)
    (Ψ : WFF σ ((Γ.diaIn x).insert (.bnd 0) (RShape.wit (.box C) Xe).ty) 1) {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X} (u : Term σ (Γ.diaIn x) X b₀)
    (cs : List (List Step)) (hcs : A.CompOk cs)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd (C.compsFlat co) Xe) (RShape.wit (.box A) X).ty)) 1)
    (hret : M.sat env (WFF.retxS hS x hx (.wit (.boxC C co ho) Xe) y Ψ : WFF σ Γ 0))
    (hθ : M.holeSat θ ((interp env y, (interp env (Term.boxtm sb),
      interp env (Term.diatm x hx u))) :
        M.frame.Dom (.VTypeProd (.VTypeProd (C.compsFlat co) Xe) (RShape.wit (.box A) X).ty) w)) :
    M.sat env (WFF.retxS hS x hx (.wit (.boxC C co ho) Xe) y
      (WFF.and Ψ (WFF.unitBodyWDC hS co ho sb u cs hcs θ)) :
      WFF σ Γ 0) := by
  obtain ⟨Y, h, a, e, hΨ, r, hr⟩ := hret
  refine ⟨Y, h, a, e, ⟨hΨ, ?_⟩, r, hr⟩
  obtain ⟨hr1, hm, hr2⟩ := hr
  have hu := Ctx.ref_insert_root (Γ.diaIn x) (.bnd 0) (RShape.wit (.box C) Xe).ty
  have hsnd := Ctx.ref_snd_of hu
  let env₁ := (env.diaPush x h a).extend (.bnd 0) e
  have he2 : env₁.ref (.step (.root (.bnd 0)) .snd) hsnd = e.2 := by
    rw [Env.ref_snd _ hu hsnd]
    exact congrArg Prod.snd (Env.extend_root (env.diaPush x h a) (.bnd 0) e hu)
  let bb : (M.posEval (env₁.ref (.step (.root (.bnd 0)) .snd) hsnd)).1 := ⟨⟨w, ⟨r⟩⟩, he2 ▸ hm⟩
  have hcont : (M.posEval (env₁.ref (.step (.root (.bnd 0)) .snd) hsnd)).2 bb =
      (M.posEval (e.2 : M.frame.Pos Xe a.1.1)).2 ⟨_, hm⟩ := by
    have key : ∀ (P : M.frame.Pos Xe a.1.1) (hP : P = e.2)
        (hmP : (⟨w, ⟨r⟩⟩ : M.frame.Acc a.1.1) ∈ (M.posEval P).1),
        (M.posEval P).2 ⟨_, hmP⟩ = (M.posEval (e.2 : M.frame.Pos Xe a.1.1)).2 ⟨_, hm⟩ := by
      intro P hP hmP
      subst hP
      rfl
    exact key _ he2 _
  have he1 : env₁.ref (.root (.bnd 0)) hu = e := Env.extend_root (env.diaPush x h a) (.bnd 0) e hu
  let val : M.frame.Dom (RShape.wit (.boxC A cs hcs) X).ty w :=
    (interp env (Term.boxtm sb), interp env (Term.diatm x hx u))
  refine ⟨Xe, hsnd, bb, val, ?_, a.1.2.down, ?_, ?_⟩
  · rw [sat_holeAt]
    have hag := Env.agree_extend (env₁.diaPush (.step (.root (.bnd 0)) .snd) hsnd bb)
      ((((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert _).diaIn _).root) val
    have hf : (((Γ.diaIn x).insert (.bnd 0) (RShape.wit (.box C) Xe).ty).diaIn
        (.step (.root (.bnd 0)) .snd)).ref (VarSymb.step (.root (.bnd 0)) .fst).inner = some C :=
      (Ctx.le_boxIn_diaIn _ _).ref (Ctx.ref_inner (Ctx.ref_fst_of hu))
    have hd := Ctx.ref_diaIn_of hsnd
    change M.holeSat θ ((interp _ _, interp _ _), interp _ _)
    rw [interp_eta]
    erw [interp_eta]
    rw [← Env.ref_agree hag _ hd,
      show (((env₁.diaPush (.step (.root (.bnd 0)) .snd) hsnd bb).extend
          (T := (RShape.wit (.boxC A cs hcs) X).ty) (.bnd 1) val).ref (.root (.bnd 1))
          (Ctx.ref_insert_root _ _ _)) = val from Env.extend_root _ _ _ _,
      Env.ref_dia env₁ hsnd bb hd, hcont]
    have hr1' : M.compsBack C co (env₁.ref _ (Ctx.ref_fst_of hu)) r (interp env y).1 := by
      rw [Env.ref_fst _ hu, he1]
      exact hr1
    have hslot := compsSlot_ind hM (Ctx.ref_fst_of hu) _ env₁ r _
      ((Env.diaPush_boxIn env₁ hsnd bb).trans hag) co ho _ hr1'
    exact (holeSat_ind hM θ (hM.pair (hM.pair hslot hr2) (M.Ind_refl _))).mpr hθ
  · change M.compsBack A cs (interp env (Term.boxtm sb)) a.1.2.down
      (interp env₁ (Term.mono _ (compsVal sb cs hcs).2))
    rw [← Term.mono_mono (Ctx.le_boxIn_diaIn Γ x)
        (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root _),
      interp_mono (Env.agree_extend (env.diaPush x h a)
        (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root e),
      interp_mono (Env.diaPush_boxIn env h a)]
    exact compsBack_compsVal env sb a.1 cs hcs
  · change ∃ hm : _ ∈ (M.posEval (interp env (Term.diatm x hx u))).1,
      M.Ind ((M.posEval (interp env (Term.diatm x hx u))).2 ⟨_, hm⟩)
        (interp env₁ (Term.mono _ u))
    rw [dia_beta env hx h u]
    refine ⟨a.2, ?_⟩
    rw [interp_mono (Env.agree_extend (env.diaPush x h a)
      (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root e)]
    exact M.Ind_refl _

include hM in
/-- ⭐**The counit of a possible part is sound**: the way home lies in the possible part's extent,
    so what holds along all of its arrows holds along the way home, at the values the object comes
    back as. -/
theorem sat_ret_counitD (hS : ModalSys.BStrong = true) {C X : VarType}
    {c : Ann (.VTypeProd C X)} (y : Term σ Γ (.VTypeProd C X) c)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C X)) 1)
    (h : M.sat env (WFF.retS hS (.wit (.box C) X) y (WFF.counitBodyD ψ) : WFF σ Γ 0)) :
    M.holeSat ψ (interp env y) := by
  obtain ⟨ac, e, hbox, r, hr1, hm, hr2⟩ := h
  have hu := Ctx.ref_insert_root Γ.boxIn (.bnd 0) (RShape.wit (.box C) X).ty
  have hsnd := Ctx.ref_snd_of hu
  let env₁ := (env.boxPush ac).extend (.bnd 0) e
  have he2 : env₁.ref (.step (.root (.bnd 0)) .snd) hsnd = e.2 := by
    rw [Env.ref_snd _ hu hsnd]
    exact congrArg Prod.snd (Env.extend_root (env.boxPush ac) (.bnd 0) e hu)
  let bb : (M.posEval (env₁.ref (.step (.root (.bnd 0)) .snd) hsnd)).1 := ⟨⟨w, ⟨r⟩⟩, he2 ▸ hm⟩
  have hcont : (M.posEval (env₁.ref (.step (.root (.bnd 0)) .snd) hsnd)).2 bb =
      (M.posEval (e.2 : M.frame.Pos X ac.1)).2 ⟨_, hm⟩ := by
    have key : ∀ (P : M.frame.Pos X ac.1) (hP : P = e.2)
        (hmP : (⟨w, ⟨r⟩⟩ : M.frame.Acc ac.1) ∈ (M.posEval P).1),
        (M.posEval P).2 ⟨_, hmP⟩ = (M.posEval (e.2 : M.frame.Pos X ac.1)).2 ⟨_, hm⟩ := by
      intro P hP hmP
      subst hP
      rfl
    exact key _ he2 _
  have he1 : env₁.ref (.root (.bnd 0)) hu = e := Env.extend_root (env.boxPush ac) (.bnd 0) e hu
  have hsat : M.sat (env₁.diaPush (.step (.root (.bnd 0)) .snd) hsnd bb)
      (WFF.holeAt (((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert _).diaIn _)
        (Term.pair
          (Term.eta (VarSymb.step (.root (.bnd 0)) .fst).inner C
            ((Ctx.le_boxIn_diaIn _ _).ref (Ctx.ref_inner (Ctx.ref_fst_of hu))))
          (Term.eta (VarSymb.step (.step (.root (.bnd 0)) .snd) .dia) X (Ctx.ref_diaIn_of hsnd)))
        ψ) := by
    by_contra hn
    exact hbox ⟨X, hsnd, bb, hn⟩
  rw [sat_holeAt] at hsat
  change M.holeSat ψ (interp _ _, interp _ _) at hsat
  rw [interp_eta, interp_eta,
    ← Env.ref_agree (Env.diaPush_boxIn env₁ hsnd bb) _ (Ctx.ref_inner (Ctx.ref_fst_of hu)),
    Env.ref_inner _ _ (Ctx.ref_fst_of hu), Env.ref_fst _ hu, he1,
    Env.ref_dia env₁ hsnd bb (Ctx.ref_diaIn_of hsnd), hcont] at hsat
  exact (holeSat_ind hM ψ (hM.pair hr1 hr2)).mp hsat

end Model
end V12M
