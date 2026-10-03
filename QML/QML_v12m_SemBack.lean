import QML.QML_v12m_SemHere

/-!
# QML v12m — strong B: the semantics of `Back` and the returning possibility

Roadmap milestone 2, step 3 (`docs/v12-modal-extensions.md` §11).  What the rules of step 4 need,
proved at the level of values, once for both rows:

* ⭐`Model.RoundTrip`: `Back`'s truth condition with the out leg a parameter.  A `□□`-carrier's
  body (`backs_nec_boxtm`) and a `◇□`-carrier's (`backs_pos_diatm`) both unfold to it.
* **Hole formulas**, closed apart from the hole (`WFF.holeRead`, `Model.holeSat`): what a round
  trip carries home (§11.2).  `IndInvariant` moves them across `Ind` (`holeSat_ind`).
* ⭐`Model.eq_of_ind`: in a model proper, at a `◇`-free type, an object indistinguishable from a
  named one is that one (test with the slot formula `z = t`).  So at the contents `Back` takes,
  `Ind` costs nothing — β, pairing and the own arrow are equations — and no congruence law is asked
  of `Ind`.
* The rules' semantics: `RoundTrip.ne`, `.elim`, `.intro`, `.of_def` (weak B's arrows home),
  `.map` (β), `.pair` (unique ways home), `.own` (T); for the returning possibility `ret_exists`
  (weak B) and `ret_elim`.
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

/-- The environment of the empty context. -/
def Env.empty (w : M.frame.W) : M.Env Ctx.empty w := fun _ _ h => nomatch h

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
  hM (Ctx.Presented.tame _) (fun _ _ h => by simp [Ctx.empty] at h) (Env.empty w) ψ o o' h

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
  exact (key x).mp ((hM hfin hnp env φ x _ h).mpr ((key _).mpr rfl))

/-! ## The rules, at the level of values -/

namespace RoundTrip

variable {A : VarType} {w : M.frame.W} {ι : Type*} {acc : ι → M.frame.Acc w}
  {val : ∀ i, ∀ b : M.frame.Acc (acc i).1, M.frame.Dom A b.1} {o : M.frame.Dom A w}

/-- The out leg is nonempty (`back_ne`). -/
theorem ne (h : RoundTrip acc val o) : Nonempty ι := h.1

/-- ⭐**Elimination** (`back_elim`): a hole formula true at the end of every way on from some arrow
    of the out leg is true of the round trip's value — along that arrow's way home. -/
theorem elim (hM : M.IndInvariant) (h : RoundTrip acc val o)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) (hψ : ∃ i, ∀ b, M.holeSat ψ (val i b)) :
    M.holeSat ψ o := by
  obtain ⟨i, hi⟩ := hψ
  obtain ⟨r, hr⟩ := h.2 i
  exact (holeSat_ind hM ψ hr).mp (hi _)

/-- ⭐**Introduction** (`back_intro`): what is true of the value is, from every arrow of the out
    leg, true at the end of some way on — the way home. -/
theorem intro (hM : M.IndInvariant) (h : RoundTrip acc val o)
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

/-- ⭐**β** (`back_beta`): mapping every value by one operation maps the return.  The hypothesis
    `hEq` — `Ind` to `o` is equality — is `eq_of_ind` when `o` is named at a `◇`-free type. -/
theorem map (hEq : ∀ x : M.frame.Dom A w, M.Ind x o → x = o) {B : VarType}
    (F : ∀ v : M.frame.W, M.frame.Dom A v → M.frame.Dom B v) (h : RoundTrip acc val o) :
    RoundTrip acc (fun i b => F b.1 (val i b)) (F w o) := by
  refine ⟨h.1, fun i => ?_⟩
  obtain ⟨r, hr⟩ := h.2 i
  refine ⟨r, ?_⟩
  change M.Ind (F w (val i ⟨w, ⟨r⟩⟩)) (F w o)
  rw [hEq _ hr]
  exact M.Ind_refl _

/-- ⭐**Pairing** (`back_pair`, §11.14 check 3): two carriers over one out leg return their pair —
    because each arrow of the leg has only **one** way home (`Frame.homeUnique`), so the two returns
    are read along the same arrow. -/
theorem pair (hS : ModalSys.BStrong = true) (hEq : ∀ x : M.frame.Dom A w, M.Ind x o → x = o)
    {B : VarType} {val' : ∀ i, ∀ b : M.frame.Acc (acc i).1, M.frame.Dom B b.1}
    {o' : M.frame.Dom B w} (hEq' : ∀ x : M.frame.Dom B w, M.Ind x o' → x = o')
    (h : RoundTrip acc val o) (h' : RoundTrip acc val' o') :
    RoundTrip (A := .VTypeProd A B) acc
      (fun i b => ((val i b, val' i b) : M.frame.Dom (.VTypeProd A B) b.1))
      ((o, o') : M.frame.Dom (.VTypeProd A B) w) := by
  refine ⟨h.1, fun i => ?_⟩
  obtain ⟨r, hr⟩ := h.2 i
  obtain ⟨r', hr'⟩ := h'.2 i
  obtain rfl : r' = r := @Subsingleton.elim _ (M.frame.homeUnique hS) r' r
  refine ⟨r', ?_⟩
  change M.Ind (A := .VTypeProd A B) (w := w) (val i ⟨w, ⟨r'⟩⟩, val' i ⟨w, ⟨r'⟩⟩) (o, o')
  rw [hEq _ hr, hEq' _ hr']
  exact M.Ind_refl _

/-- ⭐**The own arrow** (`back_here`, §11.5 (4)): under T the identity is an arrow of the plain
    out leg, and its only way home is the identity again, so the round trip along it is the
    value. -/
theorem own (hT : ModalSys.T = true) (hS : ModalSys.BStrong = true)
    {val : ∀ a : M.frame.Acc w, ∀ b : M.frame.Acc a.1, M.frame.Dom A b.1}
    (hEq : ∀ x : M.frame.Dom A w, M.Ind x o → x = o)
    (h : RoundTrip (fun a : M.frame.Acc w => a) val o) :
    val (M.frame.reflAcc hT w) (M.frame.reflAcc hT w) = o := by
  obtain ⟨r, hr⟩ := h.2 (M.frame.reflAcc hT w)
  obtain rfl : r = M.frame.refl hT w := @Subsingleton.elim _ (M.frame.homeUnique hS) _ _
  exact hEq _ hr

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

/-- ⭐**Elimination** (`ret_elim`, no carriers): what is necessary of the object out there holds of
    its value here — read along the way home. -/
theorem ret_elim (hM : M.IndInvariant) {A : VarType} {w : M.frame.W}
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
    (env : M.Env Γ w) {A : VarType} (hA : A.diaFree = true) (r : Root) (hr : Γ.RootFresh r)
    (c : M.frame.Dom (.VTypeBox (.VTypeBox A)) w) {a : Ann A} (t : Term σ Γ A a) :
    M.sat (env.extend r c) (WFF.back hS .nec hA
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
    {A : VarType} (hA : A.diaFree = true) {a : Ann A} (t : Term σ Γ A a)
    (hr : Γ.RootFresh (.bnd 0)) (hne : Nonempty (M.frame.Acc w)) :
    M.sat env (WFF.ex (.VTypeBox (.VTypeBox A))
      (WFF.back hS .nec hA
        (Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeBox (.VTypeBox A))))
        (Term.weaken hr.root _ t)) : WFF σ Γ 0) := by
  obtain ⟨c₀, hc⟩ := M.backRet_exists hS hA hne (interp env t)
  let c : M.frame.Dom (.VTypeBox (.VTypeBox A)) w := c₀
  exact ⟨c, (sat_back_eta_extend hS env hA (.bnd 0) hr c t).mpr ⟨hne, hc⟩⟩

/-! ## Hole terms and annotations -/

/-- A hole term's value at an object. -/
def holeVal {A B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b)
    {v : M.frame.W} (o : M.frame.Dom A v) : M.frame.Dom B v :=
  interp ((Env.empty v).extend (.bnd 0) o) s

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
    (O : OutLeg Γ) {A : VarType} (hA : A.diaFree = true) {a₀ : Ann A}
    (bd : Term σ O.view.boxIn A a₀) {a : Ann A} (t : Term σ Γ A a) :
    M.sat env (O.back hS hA bd t : WFF σ Γ d) ↔
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
theorem sat_back_elim (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1)
    (hb : M.sat env (O.back hS hA bd t : WFF σ Γ 0))
    (hd : M.sat env (O.dia (WFF.box (WFF.holeRead bd ψ)))) :
    M.sat env (WFF.holeRead t ψ) := by
  rw [sat_holeRead hnp]
  obtain ⟨i, hi⟩ := (OutLeg.sat_dia env O _).mp hd
  exact ((OutLeg.sat_back hS env O hA bd t).mp hb).elim hM ψ
    ⟨i, fun b => (sat_holeRead (Ctx.noProjLast_boxIn _) _ bd ψ).mp (hi b)⟩

include hnp hM in
theorem sat_back_intro (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1)
    (hb : M.sat env (O.back hS hA bd t : WFF σ Γ 0)) (hψ : M.sat env (WFF.holeRead t ψ)) :
    M.sat env (O.box (WFF.box (WFF.holeRead bd ψ).neg).neg) := by
  refine (OutLeg.sat_box env O _).mpr fun i hall => ?_
  obtain ⟨b, hb'⟩ := ((OutLeg.sat_back hS env O hA bd t).mp hb).intro hM ψ
    ((sat_holeRead hnp env t ψ).mp hψ) i
  exact hall b ((sat_holeRead (Ctx.noProjLast_boxIn _) _ bd ψ).mpr hb')

omit [Γ.NoSlots] in
theorem sat_back_ne (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) (hb : M.sat env (O.back hS hA bd t : WFF σ Γ 0)) :
    M.sat env (O.dia (.top : WFF σ O.view 0)) := by
  obtain ⟨i⟩ := ((OutLeg.sat_back hS env O hA bd t).mp hb).ne
  exact (OutLeg.sat_dia env O _).mpr ⟨i, trivial⟩

include hnp hfin hM in
theorem sat_back_beta (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) {B : VarType} (hB : B.diaFree = true) {b : Ann B}
    (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b)
    (hb : M.sat env (O.back hS hA bd t : WFF σ Γ 0)) :
    M.sat env (O.back hS hB (Term.holeRead bd s) (Term.holeRead t s) : WFF σ Γ 0) := by
  rw [OutLeg.sat_back] at hb ⊢
  have hval : (fun i (b : M.frame.Acc (O.acc env i).1) =>
      interp ((O.push env i).boxPush b) (Term.holeRead bd s)) =
      fun i b => M.holeVal s (interp ((O.push env i).boxPush b) bd) := by
    funext i b
    exact interp_holeRead (Ctx.noProjLast_boxIn _) _ bd s
  rw [hval, interp_holeRead hnp env t s]
  exact hb.map (fun x h => eq_of_ind hM hfin hnp env hA t h) _

include hnp hfin hM in
theorem sat_back_pair (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) {B : VarType} (hB : B.diaFree = true) {b₀ : Ann B}
    (bd' : Term σ O.view.boxIn B b₀) {b : Ann B} (t' : Term σ Γ B b)
    (hb : M.sat env (O.back hS hA bd t : WFF σ Γ 0))
    (hb' : M.sat env (O.back hS hB bd' t' : WFF σ Γ 0)) :
    M.sat env (O.back hS (VarType.diaFree_prod hA hB) (Term.pair bd bd') (Term.pair t t') :
      WFF σ Γ 0) := by
  rw [OutLeg.sat_back] at hb hb' ⊢
  exact hb.pair hS (fun x h => eq_of_ind hM hfin hnp env hA t h)
    (fun x h => eq_of_ind hM hfin hnp env hB t' h) hb'

omit [Γ.NoSlots] in
theorem sat_back_eq (hS : ModalSys.BStrong = true) (L : BLeg) {A : VarType}
    (hA : A.diaFree = true) {b : Ann (L.carrier A)} (s : Term σ Γ (L.carrier A) b) {a : Ann A}
    (t t' : Term σ Γ A a) (hb : M.sat env (WFF.back hS L hA s t : WFF σ Γ 0))
    (he : M.sat env (eqRec A t t' : WFF σ Γ 0)) :
    M.sat env (WFF.back hS L hA s t' : WFF σ Γ 0) := by
  change M.Backs L (interp env s) (interp env t')
  rw [← (sat_eqRec env A t t').mp he]
  exact hb

include hnp hfin hM in
theorem sat_back_here (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true) {A : VarType}
    (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ Γ.boxIn.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) (hb : M.sat env ((OutLeg.nec : OutLeg Γ).back hS hA bd t : WFF σ Γ 0)) :
    M.sat env (eqRec A (Term.castAnn hA (Term.collapse (Ctx.collapses_boxIn_self hT Γ)
      (Term.collapse (Ctx.collapses_boxIn_self hT Γ.boxIn) bd))) t : WFF σ Γ 0) := by
  rw [sat_eqRec, interp_castAnn, interp_collapse (Env.collapseAgree_self hT env),
    interp_collapse (Env.collapseAgree_self hT (env.boxPush (M.frame.reflAcc hT w)))]
  exact ((OutLeg.sat_back hS env .nec hA bd t).mp hb).own hT hS
    (fun x h => eq_of_ind hM hfin hnp env hA t h)

theorem sat_back_def (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true) (O : OutLeg Γ)
    {A : VarType} (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀)
    {a : Ann A} (t : Term σ Γ A a) (θ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1)
    (hne : M.sat env (O.dia (.top : WFF σ O.view 0)))
    (hall : M.sat env (O.box (WFF.box (WFF.holeRead bd θ))))
    (hdef : M.sat env (WFF.all A (WFF.imp (WFF.mono ((Ctx.empty_le Γ).insert (.bnd 0) A) θ)
      (eqRec A (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root Γ (.bnd 0) A))
        (Term.castAnn hA (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root A) t))))
      : WFF σ Γ 0)) :
    M.sat env (O.back hS hA bd t : WFF σ Γ 0) := by
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

end V12M
