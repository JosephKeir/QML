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

/-- A **hole formula** — closed apart from its hole (§11.2) — read in `Γ` with `t` in the hole.
    The round trip carries no addresses, so the two ends of a `Back` meet only through the hole. -/
def WFF.holeRead {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) : WFF σ Γ 0 :=
  WFF.instantiate Ctx.NoSlots.slots t (WFF.mono ((Ctx.empty_le Γ).insert (.bnd 0) A) ψ)

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
  refine ⟨c, ?_⟩
  have hag : Env.Agree (Ctx.le_insert hr.root (.VTypeBox (.VTypeBox A))) env
      (env.extend (.bnd 0) c) := by
    intro v U hv
    have hne : v ≠ .root (.bnd 0) := fun hvr => by rw [hvr, hr.root] at hv; cases hv
    simp only [Env.extend, dif_neg hne]
  change M.Backs .nec (interp (env.extend (.bnd 0) c) (Term.eta _ _ _))
    (interp (env.extend (.bnd 0) c) (Term.mono _ t))
  have hslot : (env.extend (.bnd 0) c).ref (.root (.bnd 0))
      (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeBox (.VTypeBox A))) = c :=
    Env.extend_root env (.bnd 0) c (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeBox (.VTypeBox A)))
  rw [interp_eta, interp_mono hag t, hslot]
  exact ⟨hne, hc⟩

end Model

end V12M
