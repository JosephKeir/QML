import QML.QML_v12m_CubeComplete

/-!
# QML v12m — admissible rules, semantically

Rules shown admissible through soundness and completeness across the cube
(`provable_iff_validCube`): valid in every model, hence derivable in every system of the cube.
The proof-theoretic counterparts, which would hold for every flag combination (K5 and KD5
included), are on the list in `docs/v12-metatheory-todo.md`; `QML_v12m_ProofAdmissible` holds the
ones done so far.

* ⭐`leibnizCube`: from `t = s` at any type (`eqRec`) and `φ[t]`, `φ[s]`.
* ⭐`usubstCube`: **uniform substitution** of a relation symbol `R` by a formula `ψ` closed apart
  from one hole, the tuple of `R`'s arguments (`WFF.usubst`).  Semantically: the model that reads
  `R` as `ψ` (`Model.relSwap`) satisfies a formula exactly when the original satisfies its
  substitution (`Model.sat_usubst`).
-/

namespace V12M

variable [ModalSys]

/-! ## Tuples of arguments -/

/-- `Var × (Var × ⋯ × 𝟙)`, `n` times: the type of `n` arguments. -/
def VarType.varTup : ℕ → VarType
  | 0 => .VTypeOne
  | n + 1 => .VTypeProd .Var (VarType.varTup n)

/-- Its annotation. -/
def Ann.varTup : (n : ℕ) → Ann (VarType.varTup n)
  | 0 => .one
  | n + 1 => .prod .var (Ann.varTup n)

namespace Spine

variable {σ : Signature} {Γ : Ctx}

/-- The arguments of a spine as one term. -/
def tup : {n : ℕ} → Spine σ Γ n → Term σ Γ (VarType.varTup n) (Ann.varTup n)
  | _, .nil => .unit
  | _, .cons t S => .pair t S.tup

end Spine

/-- A relation applied to all its arguments: its symbol and their spine. -/
def Rel.toSpine {σ : Signature} {Γ : Ctx} :
    {k : ℕ} → Rel σ Γ k → Spine σ Γ k → Σ r : σ.RelSyms, Spine σ Γ (σ.relArity r)
  | _, .R r, S => ⟨r.1, cast (congrArg (Spine σ Γ) r.2.symm) S⟩
  | _, .eval ρ t, S => Rel.toSpine ρ (.cons t S)

/-! ## The substitution -/

section USubst

variable {σ : Signature} (r : σ.RelSyms)
  (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (VarType.varTup (σ.relArity r))) 1)

/-- An atom, with `R(t̄)` replaced by `ψ(t̄)`. -/
def WFF.usubAtom {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) (ρ : Rel σ Γ 0)
    (p : Σ r' : σ.RelSyms, Spine σ Γ (σ.relArity r')) : WFF σ Γ d :=
  if h : p.1 = r then WFF.holeAt hs (cast (by rw [h]) p.2 : Spine σ Γ (σ.relArity r)).tup ψ
  else .atom ρ

/-- ⭐**Uniform substitution**: every atom `R(t̄)` replaced by `ψ(t̄)`. -/
def WFF.usubst : {Γ : Ctx} → {d : ℕ} → Γ.SlotsFrom d → WFF σ Γ d → WFF σ Γ d
  | _, _, hs, .atom ρ => WFF.usubAtom r ψ hs ρ (Rel.toSpine ρ .nil)
  | _, _, _, .eq t s => .eq t s
  | _, _, _, .top => .top
  | _, _, _, .bot => .bot
  | _, _, hs, .and φ χ => .and (WFF.usubst hs φ) (WFF.usubst hs χ)
  | _, _, hs, .or φ χ => .or (WFF.usubst hs φ) (WFF.usubst hs χ)
  | _, _, hs, .imp φ χ => .imp (WFF.usubst hs φ) (WFF.usubst hs χ)
  | _, _, hs, .all T φ => .all T (WFF.usubst (hs.insert T) φ)
  | _, _, hs, .ex T φ => .ex T (WFF.usubst (hs.insert T) φ)
  | _, _, hs, .box φ => .box (WFF.usubst hs.boxIn φ)
  | _, _, hs, .dia x hx φ => .dia x hx (WFF.usubst (hs.diaIn x) φ)
  | _, _, _, .here hT s t => .here hT s t
  | _, _, _, .back hB L s t => .back hB L s t
  | _, _, hs, .retS hB S t Φ => .retS hB S t (WFF.usubst (hs.boxIn.insert _) Φ)
  | _, _, hs, .retxS hB y hy S t Φ => .retxS hB y hy S t (WFF.usubst ((hs.diaIn y).insert _) Φ)
  | _, _, hs, .link hV hF t Φ => .link hV hF t (WFF.usubst (hs.boxIn.insert _) Φ)
  | _, _, hs, .linkx hV hF y hy t Φ => .linkx hV hF y hy t (WFF.usubst ((hs.diaIn y).insert _) Φ)
  | _, _, hs, .optx hO .arrow y hy φ => .optx hO .arrow y hy (WFF.usubst (hs.optIn y) φ)
  | _, _, _, .optx _ .ident _ hyI _ => (hyI.elim fun _ h => Ctx.witT_stage h).elim

end USubst

/-! ## The model that reads `R` as `ψ` -/

namespace Model

variable {σ : Signature} (M : Model.{u, v} σ)

/-- `n` arguments as a tuple. -/
def tupVal {w : M.frame.W} : {n : ℕ} → (Fin n → M.frame.D w) →
    M.frame.Dom (VarType.varTup n) w
  | 0, _ => PUnit.unit
  | _ + 1, f => (f 0, tupVal fun i => f i.succ)

/-- `R` read as `ψ`, every other relation as in `M`. -/
def relSwapRel (r : σ.RelSyms)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (VarType.varTup (σ.relArity r))) 1) :
    (r' : σ.RelSyms) → (w : M.frame.W) → (Fin (σ.relArity r') → M.frame.D w) → Prop :=
  fun r' w args => if h : r' = r then
    M.holeSat ψ (M.tupVal fun i => args (Fin.cast (congrArg σ.relArity h.symm) i))
  else M.relInterp r' w args

/-- ⭐**`M` with `R` read as `ψ`**: the same frame and objects, every other relation as in `M`, and
    `R` inside `ψ` still `M`'s. -/
def relSwap (r : σ.RelSyms)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (VarType.varTup (σ.relArity r))) 1) : Model.{u, v} σ :=
  { M with relInterp := M.relSwapRel r ψ }

variable {M} {r : σ.RelSyms}
  {ψ : WFF σ (Ctx.empty.insert (.bnd 0) (VarType.varTup (σ.relArity r))) 1}

set_option smartUnfolding false in
/-- The swapped model's operations are `M`'s: definitionally, once smart unfolding is off (it
    will not unfold a recursion stuck on a variable, so it never reaches the shared fields). -/
theorem interp_relSwap {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {T : VarType} {a : Ann T}
    (t : Term σ Γ T a) : interp (M := M.relSwap r ψ) env t = interp env t := rfl

/-- A spine's values. -/
def spineVals {N : Model.{u, v} σ} {Γ : Ctx} {w : N.frame.W} (env : N.Env Γ w) :
    {k : ℕ} → Spine σ Γ k → Fin k → N.frame.D w
  | _, .nil => Fin.elim0
  | _, .cons t S => Fin.cons (interp env t) (spineVals env S)

/-- A relation read at a spine is its symbol read at the whole spine. -/
theorem relSat_toSpine {N : Model.{u, v} σ} {Γ : Ctx} {w : N.frame.W} (env : N.Env Γ w) :
    ∀ {k : ℕ} (ρ : Rel σ Γ k) (S : Spine σ Γ k),
      relSat env ρ (spineVals env S) =
        N.relInterp (Rel.toSpine ρ S).1 w (spineVals env (Rel.toSpine ρ S).2)
  | _, .R ⟨_, hr⟩, _ => by subst hr; rfl
  | _, .eval ρ t, S => relSat_toSpine env ρ (.cons t S)

theorem interp_tup {N : Model.{u, v} σ} {Γ : Ctx} {w : N.frame.W} (env : N.Env Γ w) :
    ∀ {k : ℕ} (S : Spine σ Γ k), interp env S.tup = N.tupVal (spineVals env S)
  | _, .nil => rfl
  | _, .cons t S => by
      change (interp env t, interp env S.tup) = _
      rw [interp_tup env S]
      simp only [tupVal, spineVals, Fin.cons_zero, Fin.cons_succ]

set_option maxHeartbeats 800000 in
-- Compiling the recursion re-checks the cases that read the swapped model as `M`, which goes
-- through the shared fields without smart unfolding: slow, not stuck.
/-- ⭐**The model that reads `R` as `ψ` satisfies a formula exactly when `M` satisfies its
    substitution.** -/
theorem sat_usubst : ∀ {Γ : Ctx} {d : ℕ} {w : M.frame.W} (env : M.Env Γ w) (hs : Γ.SlotsFrom d)
    (φ : WFF σ Γ d), (M.relSwap r ψ).sat env φ ↔ M.sat env (WFF.usubst r ψ hs φ)
  | _, _, w, env, hs, .atom ρ => by
      set_option smartUnfolding false in
      have e₁ := relSat_toSpine (N := M.relSwap r ψ) env ρ .nil
      have e₂ := relSat_toSpine (N := M) env ρ .nil
      change relSat (M := M.relSwap r ψ) env ρ (spineVals env .nil) ↔
        M.sat env (WFF.usubAtom r ψ hs ρ (Rel.toSpine ρ .nil))
      refine (iff_of_eq e₁).trans ?_
      generalize Rel.toSpine ρ .nil = p at e₂ ⊢
      rcases p with ⟨r', S⟩
      unfold WFF.usubAtom
      by_cases h : r' = r
      · subst h
        rw [dif_pos rfl, sat_holeAt, interp_tup]
        change M.relSwapRel r' ψ r' w (spineVals env S) ↔ _
        rw [relSwapRel, dif_pos rfl]
        rfl
      · rw [dif_neg h]
        change M.relSwapRel r ψ r' w (spineVals env S) ↔ relSat env ρ (spineVals env .nil)
        rw [e₂, relSwapRel, dif_neg h]
  | _, _, _, _, _, .eq _ _ => by
      set_option smartUnfolding false in
      exact Iff.rfl
  | _, _, _, _, _, .top => by
      set_option smartUnfolding false in
      exact Iff.rfl
  | _, _, _, _, _, .bot => by
      set_option smartUnfolding false in
      exact Iff.rfl
  | _, _, _, env, hs, .and φ χ => and_congr (sat_usubst env hs φ) (sat_usubst env hs χ)
  | _, _, _, env, hs, .or φ χ => or_congr (sat_usubst env hs φ) (sat_usubst env hs χ)
  | _, _, _, env, hs, .imp φ χ => imp_congr (sat_usubst env hs φ) (sat_usubst env hs χ)
  | _, _, _, env, hs, .all T φ => forall_congr' fun o => sat_usubst (env.extend _ o) (hs.insert T) φ
  | _, _, _, env, hs, .ex T φ => exists_congr fun o => sat_usubst (env.extend _ o) (hs.insert T) φ
  | _, _, _, env, hs, .box φ => by
      set_option smartUnfolding false in
      exact forall_congr' fun w' => sat_usubst (env.boxPush w') hs.boxIn φ
  | _, _, _, env, hs, .dia x _ φ => by
      set_option smartUnfolding false in
      exact exists_congr fun _ => exists_congr fun h => exists_congr fun w' =>
        sat_usubst (env.diaPush x h w') (hs.diaIn x) φ
  | _, _, _, _, _, .here _ _ _ => by
      set_option smartUnfolding false in
      exact Iff.rfl
  | _, _, _, _, _, .back _ _ _ _ => by
      set_option smartUnfolding false in
      exact Iff.rfl
  | _, _, _, env, hs, .retS _ _ _ Φ => by
      set_option smartUnfolding false in
      exact exists_congr fun a => exists_congr fun e =>
        and_congr (sat_usubst ((env.boxPush a).extend _ e) (hs.boxIn.insert _) Φ) Iff.rfl
  | _, _, _, env, hs, .retxS _ y _ _ _ Φ => by
      set_option smartUnfolding false in
      exact exists_congr fun _ => exists_congr fun h => exists_congr fun a => exists_congr fun e =>
        and_congr (sat_usubst ((env.diaPush y h a).extend _ e) ((hs.diaIn y).insert _) Φ)
          Iff.rfl
  | _, _, _, env, hs, .link _ _ _ Φ => by
      set_option smartUnfolding false in
      exact forall_congr' fun a => sat_usubst ((env.boxPush a).extend _ _) (hs.boxIn.insert _) Φ
  | _, _, _, env, hs, .linkx _ _ y _ _ Φ => by
      set_option smartUnfolding false in
      exact exists_congr fun _ => exists_congr fun h => exists_congr fun b =>
        sat_usubst ((env.diaPush y h b).extend _ _) ((hs.diaIn y).insert _) Φ
  | _, _, _, env, hs, .optx _ .arrow y _ φ => by
      set_option smartUnfolding false in
      exact exists_congr fun _ => exists_congr fun h => exists_congr fun _ =>
        sat_usubst (env.optPush y h _) (hs.optIn y) φ
  | _, _, _, _, _, .optx _ .ident _ hyI _ => (hyI.elim fun _ h => Ctx.witT_stage h).elim

set_option smartUnfolding false in
/-- The model reading `R` as `ψ` is a model proper when `M` is. -/
theorem indInvariant_relSwap (hM : M.IndInvariant) : (M.relSwap r ψ).IndInvariant where
  toIndCongr := by
    constructor
    · intro A B b s w o o' h; exact hM.map s h
    · intro A B w a a' b b' h h'; exact hM.pair h h'
  inv := by
    intro Γ _ hT hnp w env A φ o o' hi
    have h₁ := sat_usubst (M := M) (r := r) (ψ := ψ) (env.extend _ o)
      (Ctx.NoSlots.slots.insert _) φ
    have h₂ := sat_usubst (M := M) (r := r) (ψ := ψ) (env.extend _ o')
      (Ctx.NoSlots.slots.insert _) φ
    exact h₁.trans ((hM.inv hT hnp env _ o o' hi).trans h₂.symm)
  ret := by
    intro hB
    constructor
    · intro A B b s w ℓ S val o h; exact (hM.ret hB).map s h
    · intro A B w ℓ ℓ' S val val' o o' hl hc hc' h h'
      exact (hM.ret hB).pair hl hc hc' h h'
    · intro hT hF A w ℓ S n hS hc hsh; exact (hM.ret hB).keep hT hF n hS hc hsh
  posSide_side := hM.posSide_side
  posSide_loop := hM.posSide_loop

end Model

/-! ## Across the cube -/

section Cube

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.CubeSys]

/-- ⭐**Leibniz at every type**: from `t = s` (`eqRec`) and `φ[t]`, `φ[s]`, in every system of the
    cube. -/
theorem leibnizCube (e : CtxExpr) (he : e.Wf) {Δ : List (WFF σ e.denote 0)} (T : VarType)
    {a : Ann T} {t s : Term σ e.denote T a} (φ : WFF σ (e.denote.insert (.bnd 0) T) 1)
    (hts : Provable Δ (eqRec T t s)) (hφ : Provable Δ (WFF.instantiate e.slots t φ)) :
    Provable Δ (WFF.instantiate e.slots s φ) := by
  rw [provable_iff_validCube e he] at hts hφ ⊢
  intro M hM w env hnp hΔ
  have h₁ := (Model.sat_eqRec env T t s).mp (hts M hM env hnp hΔ)
  refine (Model.sat_instantiate env hnp e.slots s φ).mpr ?_
  rw [← h₁]
  exact (Model.sat_instantiate env hnp e.slots t φ).mp (hφ M hM env hnp hΔ)

/-- ⭐**Uniform substitution**, in every system of the cube: replacing every atom `R(t̄)` by `ψ(t̄)`
    throughout a provable sequent leaves it provable. -/
theorem usubstCube (e : CtxExpr) (he : e.Wf) (r : σ.RelSyms)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (VarType.varTup (σ.relArity r))) 1)
    {Δ : List (WFF σ e.denote 0)} {φ : WFF σ e.denote 0} (p : Provable Δ φ) :
    Provable (Δ.map (WFF.usubst r ψ e.slots)) (WFF.usubst r ψ e.slots φ) := by
  rw [provable_iff_validCube e he] at p ⊢
  intro M hM w env hnp hΔ
  exact (Model.sat_usubst env e.slots φ).mp
    (p (M.relSwap r ψ) (Model.indInvariant_relSwap hM) env hnp fun χ hχ =>
      (Model.sat_usubst env e.slots χ).mpr (hΔ _ (List.mem_map.mpr ⟨χ, hχ, rfl⟩)))

end Cube

end V12M
