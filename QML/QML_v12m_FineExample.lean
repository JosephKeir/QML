import QML.QML_v12m_GKInterp
import QML.QML_v12m_CubeComplete

/-!
# QML v12m — Fine's counterexample to interpolation, in S5

Fine (1979) shows that interpolation fails for first-order S5.  His valid entailment, without
the Barcan formula, is
  `p ∧ □∀x □(p → F x)  ⊢  q → □∀x ◇(q ∧ F x)`,
and no formula in `F` alone interpolates it: the validity predicates `F`, at the actual world,
of objects of other worlds, and plain first-order modal logic cannot quantify over those here.

In our language an object of one world is read at another only through a modal type, so the
inner `F x` makes `x` a necessary object (`x : □Var`), read at the further world as
`x.keep.here` (under T and 4 the `□` view exposes only `keep`).  Translated so, the entailment
holds whenever T, 4 and B do (so in every S5), and it has an interpolant in `F` alone:
`∀y : □Var. F(y.here)` — **every necessary object, as realised here, is `F`**.

* ⭐`Fine.left`: `φ ⊢ χ` (T twice: what is necessary holds here).
* ⭐`Fine.right`: `χ ⊢ ψ` (B carries `q ∧ χ` to every world and back; there `χ` is read at the
  restriction of the necessary object, `y := x.keep`).
* ⭐`Fine.interpolant`, `Fine.interpolant_S5`: both, with `χ`'s relation symbols (only `F`) in
  `φ` and `ψ`.

Fine's theorem itself (no interpolant in the base language) is untouched: the point is that the
language with typed modal objects has one, of the same kind as Fitting's (propositional
quantifiers) and the hybrid repairs, here built from the language's own means.
-/

namespace V12M

namespace Fine

/-- The relation symbols: `p` and `q` are propositional, `F` unary. -/
inductive Sym
  | p | q | F
  deriving DecidableEq

/-- The signature of the example. -/
def sig : Signature where
  FuncSyms := Empty
  RelSyms := Sym
  funcArity := Empty.elim
  relArity := fun | .F => 1 | _ => 0

variable [ModalSys]

/-- The propositional letters. -/
def P {Γ : Ctx} {d : ℕ} : WFF sig Γ d := .atom (.R ⟨Sym.p, rfl⟩)
def Q {Γ : Ctx} {d : ℕ} : WFF sig Γ d := .atom (.R ⟨Sym.q, rfl⟩)

/-- `F t`. -/
def Fa {Γ : Ctx} {d : ℕ} (t : Term sig Γ .Var .var) : WFF sig Γ d :=
  .atom (.eval (.R ⟨Sym.F, rfl⟩) t)

/-- `◇φ` as `¬□¬φ`. -/
abbrev dia' {Γ : Ctx} {d : ℕ} (φ : WFF sig Γ.boxIn d) : WFF sig Γ d := (WFF.box φ.neg).neg

/-- A necessary object realised here. -/
theorem ref_here (hT : ModalSys.T = true) {Γ : Ctx}
    {u : VarSymb} (hu : Γ.ref u = some (.VTypeBox .Var)) :
    Γ.ref (u.step .here) = some .Var := by
  rw [Ctx.ref_step_proj _ _ (s := .here) rfl, hu]
  simp [VarType.step, hT]

/-- A necessary object, kept one view in, realised there. -/
theorem ref_keep_here (hT : ModalSys.T = true) (hF : ModalSys.Four = true) {Γ : Ctx}
    {u : VarSymb} (hu : Γ.ref u = some (.VTypeBox .Var)) :
    Γ.boxIn.ref ((u.step .keep).step .here) = some .Var :=
  ref_here hT (by rw [Ctx.ref_nonproj _ (v := u.step .keep) rfl, Ctx.boxIn_keep_of hF hu])

/-- The bound variable `x : □Var`. -/
abbrev Γx (Γ : Ctx) : Ctx := Γ.insert (.bnd 0) (.VTypeBox .Var)

abbrev x₀ : VarSymb := .root (.bnd 0)

theorem ref_x₀ (Γ : Ctx) : (Γx Γ).ref x₀ = some (.VTypeBox .Var) := Ctx.ref_insert_root _ _ _

/-- `F(x.keep.here)` one view in. -/
def Fkx (hT : ModalSys.T = true) (hF : ModalSys.Four = true) (Γ : Ctx) : WFF sig (Γx Γ).boxIn 1 :=
  Fa (.var ((x₀.step .keep).step .here) (ref_keep_here hT hF (ref_x₀ Γ)))

/-- ⭐`φ = p ∧ □∀x:□Var. □(p → F(x.keep.here))`. -/
def φ (hT : ModalSys.T = true) (hF : ModalSys.Four = true) : WFF sig Ctx.empty 0 :=
  P.and (.box (.all (.VTypeBox .Var) (.box (P.imp (Fkx hT hF _)))))

/-- ⭐`ψ = q → □∀x:□Var. ◇(q ∧ F(x.keep.here))`. -/
def ψ (hT : ModalSys.T = true) (hF : ModalSys.Four = true) : WFF sig Ctx.empty 0 :=
  Q.imp (.box (.all (.VTypeBox .Var) (dia' (Q.and (Fkx hT hF _)))))

/-- ⭐**The interpolant**, in `F` alone: `∀y:□Var. F(y.here)`. -/
def χ (hT : ModalSys.T = true) : WFF sig Ctx.empty 0 :=
  .all (.VTypeBox .Var) (Fa (.var (x₀.step .here) (ref_here hT (ref_x₀ _))))

theorem left (hT : ModalSys.T = true) (hF : ModalSys.Four = true) :
    Provable [φ hT hF] (χ hT) := by
  have hu : Ctx.empty.RootFresh (.free 0) := Ctx.RootFresh.empty _
  have p₀ : Proof sig Ctx.empty [φ hT hF] _ := .and_elim_r (Proof.lookup List.mem_cons_self)
  have p₁ := Proof.T_box hT p₀
  have p₂ := Proof.weak_ctx 0 (.VTypeBox .Var) hu p₁
  have p₃ := Proof.all_elim (Γ := Ctx.empty.insert (.free 0) (.VTypeBox .Var)) (.VTypeBox .Var)
    (Term.eta (.root (.free 0)) (.VTypeBox .Var) (Ctx.ref_insert_root _ _ _)) p₂
  rw [WFF.instantiate_eta_openFree 0 hu Ctx.NoSlots.slots] at p₃
  have p₄ := Proof.T_box hT p₃
  have hp : Proof sig _ ([φ hT hF].map (WFF.weaken hu.root (.VTypeBox .Var))) P :=
    .and_elim_l (Proof.lookup List.mem_cons_self)
  exact ⟨Proof.all_intro 0 (.VTypeBox .Var) hu (.imp_elim p₄ hp)⟩

theorem toVar_congr {Δ : Ctx} {e e' : SubE sig Δ} (h : e = e') (h₁ : e.OkRef .Var)
    (h₂ : e'.OkRef .Var) : e.toVar h₁ = e'.toVar h₂ := by
  subst h; rfl

theorem right (hT : ModalSys.T = true) (hF : ModalSys.Four = true) (hB : ModalSys.B = true) :
    Provable [χ hT] (ψ hT hF) := by
  -- B carries `q ∧ χ` to every world and back
  have hC : Proof sig Ctx.empty [Q, χ hT] ((Q.and (χ hT)).closed Ctx.empty) :=
    .and_intro (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
  have hb := Proof.imp_elim (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil)
    (Proof.imp_intro (Proof.B_box hB (Q.and (χ hT))))) hC
  -- inside: from `◇(q ∧ χ)`, for every `x : □Var`, `◇(q ∧ F(x.keep.here))`
  have hu : Ctx.empty.boxIn.RootFresh (.free 0) := (Ctx.RootFresh.empty _).boxIn
  have hk : (Ctx.empty.boxIn.insert (.free 0) (.VTypeBox .Var)).boxIn.ref
      (.step (.root (.free 0)) .keep) = some (.VTypeBox .Var) := by
    rw [Ctx.ref_nonproj _ (v := .step (.root (.free 0)) .keep) rfl]
    exact Ctx.boxIn_keep_of hF (Ctx.ref_insert_root _ _ _)
  have inner : Proof sig (Ctx.empty.boxIn.insert (.free 0) (.VTypeBox .Var)).boxIn
      [(Q.and (Fa (.var ((VarSymb.step (.root (.free 0)) .keep).step .here)
        (ref_here hT hk)))).neg]
      ((Q.and (χ hT)).closed _).neg := by
    have h₁ : Proof sig (Ctx.empty.boxIn.insert (.free 0) (.VTypeBox .Var)).boxIn
        [(Q.and (χ hT)).closed _, (Q.and (Fa (.var ((VarSymb.step (.root (.free 0)) .keep).step
          .here) (ref_here hT hk)))).neg]
        ((χ hT).closed _) :=
      .and_elim_r (φ := Q) (Proof.lookup List.mem_cons_self)
    have h₂ := Proof.all_elim (.VTypeBox .Var)
      (φ := WFF.mono ((Ctx.empty_le _).insert (.bnd 0) (.VTypeBox .Var))
        (Fa (.var (x₀.step .here) (ref_here hT (ref_x₀ _)))))
      (Term.eta _ (.VTypeBox .Var) hk) h₁
    have e : WFF.instantiate Ctx.NoSlots.slots (Term.eta _ (.VTypeBox .Var) hk)
        (WFF.mono ((Ctx.empty_le _).insert (.bnd 0) (.VTypeBox .Var))
          (Fa (.var (x₀.step .here) (ref_here hT (ref_x₀ _))))) =
        Fa (.var ((VarSymb.step (.root (.free 0)) .keep).step .here) (ref_here hT hk)) := by
      have e₀ : (Subst.single (σ := sig) (.bnd 0) (.tm (Term.eta _ (.VTypeBox .Var) hk))).at
          (x₀.step .here) = .tm (Term.eta ((VarSymb.step (.root (.free 0)) .keep).step .here)
            .Var (Ctx.ref_here_of hT hk)) := by
        rw [show (Subst.single (σ := sig) (.bnd 0) (.tm (Term.eta _ (.VTypeBox .Var) hk))).at
            (x₀.step .here) = ((Subst.single (σ := sig) (.bnd 0)
              (.tm (Term.eta _ (.VTypeBox .Var) hk))).at x₀).proj .here from if_pos rfl,
          Subst.at_single_root, SubE.proj_here_eta hT hk]
      unfold WFF.instantiate WFF.substRoot
      exact congrArg (fun t => WFF.atom (Rel.eval (.R ⟨Sym.F, rfl⟩) t)) (toVar_congr e₀ _ rfl)
    rw [e] at h₂
    exact .imp_intro (.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (.and_intro (.and_elim_l (ψ := (χ hT).closed _) (Proof.lookup List.mem_cons_self)) h₂))
  -- one view in: refute `□¬(q ∧ F(x.keep.here))` by `◇(q ∧ χ)`
  have step : Proof sig (Ctx.empty.boxIn.insert (.free 0) (.VTypeBox .Var))
      ([dia' ((Q.and (χ hT)).closed Ctx.empty.boxIn.boxIn)].map
        (WFF.weaken hu.root (.VTypeBox .Var)))
      (dia' (Q.and (Fa (.var ((VarSymb.step (.root (.free 0)) .keep).step .here)
        (ref_here hT hk))))) :=
    .imp_intro (.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.ofSubset (fun _ h => by
        rw [List.map_cons, List.map_nil, List.mem_singleton] at h
        rw [h]; exact List.mem_cons_self) (Proof.K_box inner)))
  have all := Proof.all_intro (Γ := Ctx.empty.boxIn) 0 (.VTypeBox .Var) hu step
  have boxed := Proof.K_box all
  exact ⟨.imp_intro (.imp_elim (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil)
    (.imp_intro (Proof.ofSubset (fun _ h => by
      rw [List.map_cons, List.map_nil, List.mem_singleton] at h
      rw [h]; exact List.mem_cons_self) boxed))) hb)⟩

/-- `χ` uses only `F`, which both `φ` and `ψ` use. -/
theorem occ (hT : ModalSys.T = true) (hF : ModalSys.Four = true) (r : sig.RelSyms)
    (h : (χ hT).Occ r) : (φ hT hF).Occ r ∧ (ψ hT hF).Occ r := by
  simp only [χ, φ, ψ, Fkx, Fa, P, Q, WFF.Occ, Rel.sym] at h ⊢
  subst h
  simp

/-- ⭐**Fine's counterexample has an interpolant in our language**, in every system with T, 4 and
    B: `φ ⊢ χ`, `χ ⊢ ψ`, and `χ`'s only relation symbol `F` occurs in both. -/
theorem interpolant (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    (hB : ModalSys.B = true) :
    Provable [φ hT hF] (χ hT) ∧ Provable [χ hT] (ψ hT hF) ∧
      ∀ r, (χ hT).Occ r → (φ hT hF).Occ r ∧ (ψ hT hF).Occ r :=
  ⟨left hT hF, right hT hF hB, occ hT hF⟩

omit [ModalSys] in
/-- In S5. -/
theorem interpolant_S5 :
    letI := ModalSys.S5
    Provable [φ rfl rfl] (χ rfl) ∧ Provable [χ rfl] (ψ rfl rfl) ∧
      ∀ r, (χ rfl).Occ r → (φ rfl rfl).Occ r ∧ (ψ rfl rfl).Occ r :=
  letI := ModalSys.S5
  interpolant rfl rfl rfl

end Fine

end V12M
