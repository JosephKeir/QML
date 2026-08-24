import QML.TermInterp

/-!
# `interpWFF` on `RModelB` — satisfaction of formulas

Ported from the old `GModel.interpWFF` (`SemanticsGeneral2`).  `interpTerm` = the level-0 box-lift
`termToNecLvl 0` (already the full term interpreter).  Built here: `Env` (+ `extend`), `interpTerm`,
`interpRel`, and the non-modal + quantifier cases of `interpWFF`.  The modal cases (`box`/`dia`, which
need the `necEval` environment-push `boxPush`) and `pair_elim` are stubbed for now.
-/

namespace RModel

variable {σ : Signature}

/-- **Environment**: a value for each context variable at world `w`. -/
abbrev Env (M : RModel σ) (V : VarCtx) (w : M.frame.W) : Type _ :=
  (p : VarSymb × VarType) → p ∈ V.1 → M.frame.interp p.2 w

/-- Extend an environment with a value for a fresh variable `x`. -/
def Env.extend {M : RModel σ} {V : VarCtx} {w : M.frame.W} (env : Env M V w)
    (x : VarSymb × VarType) (hx : x.1 ∉ VarCtx_to_VarSymbs V) (a : M.frame.interp x.2 w) :
    Env M (VarCtx_insert x V hx) w :=
  fun p hp =>
    if hpx : p = x then (congrArg Prod.snd hpx).symm ▸ a
    else env p ((Finset.mem_insert.mp hp).resolve_left hpx)

/-- Push an environment (over a boxed context `W`) to an accessible world `w'`, via `necEval` on each
    box-typed variable — the semantic content of the `□`-elimination environment transfer. -/
noncomputable def Env.boxPush {M : RModel σ} {V W : VarCtx} {w : M.frame.W}
    (hsub : (VarCtx_box V).1 ⊆ W.1) (env : Env M W w)
    (w' : {w' : M.frame.W // M.frame.R w w'}) : Env M V w'.1 :=
  fun p hp => M.necEval (env ⟨p.1, p.2.VTypeBox⟩ (hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩))) w'

/-- Interpret a term (= the level-0 box-lift `termToNecLvl 0`, the full term interpreter). -/
noncomputable def interpTerm (M : RModel σ) {V : VarCtx} {S : VarType} (w : M.frame.W)
    (env : Env M V w) (t : Term σ V S) : M.frame.interp S w :=
  M.termToNecLvl 0 env t

/-- Interpret a (curried) relation application — accumulate its arguments, then `relInterp`. -/
noncomputable def interpRel (M : RModel σ) : {V : VarCtx} → {n : ℕ} →
    Rel σ V n → (w : M.frame.W) → Env M V w → (Fin n → M.frame.D w) → Prop
  | _, _, .R hr,      w, _,   args => M.frame.relInterp hr.1 w (hr.2.symm ▸ args)
  | _, _, .eval R' t, w, env, args => M.interpRel R' w env (Fin.cons (M.interpTerm w env t) args)

/-- **Satisfaction** of a formula at a world under an environment.  Non-modal + quantifier cases;
    `box`/`dia` (need the `necEval` env-push) and `pair_elim` stubbed. -/
noncomputable def interpWFF (M : RModel σ) :
    {V : VarCtx} → WFF σ V → (w : M.frame.W) → Env M V w → Prop
  | _, .atom R,     w, env => M.interpRel R w env Fin.elim0
  | _, .top,        _, _   => True
  | _, .bot,        _, _   => False
  | _, .and φ ψ,    w, env => M.interpWFF φ w env ∧ M.interpWFF ψ w env
  | _, .or φ ψ,     w, env => M.interpWFF φ w env ∨ M.interpWFF ψ w env
  | _, .imp φ ψ,    w, env => M.interpWFF φ w env → M.interpWFF ψ w env
  | _, .eq s t,     w, env => M.interpTerm w env s = M.interpTerm w env t
  | _, @WFF.all _ _ x hx φ, w, env => ∀ a : M.frame.interp x.2 w, M.interpWFF φ w (env.extend x hx a)
  | _, @WFF.ex _ _ x hx φ,  w, env => ∃ a : M.frame.interp x.2 w, M.interpWFF φ w (env.extend x hx a)
  | _, .box φ hsub _, w, env =>
      ∀ w' : {w' : M.frame.W // M.frame.R w w'}, M.interpWFF φ w'.1 (Env.boxPush hsub env w')
  | _, .dia x hx φ hsub _, w, env =>
      -- `◇_x φ` = *some* realization of the ◇-variable makes `φ` hold at its world.
      ∃ dv : Σ' w' : {w' : M.frame.W // M.frame.R w w'}, M.frame.interp x.2 w'.1,
        dv ∈ M.posEval (env ⟨x.1, x.2.VTypeDia⟩ (hsub (Finset.mem_insert_self _ _))) ∧
        M.interpWFF φ dv.1.1
          ((Env.boxPush (fun _ hp => hsub (Finset.mem_insert_of_mem hp)) env dv.1).extend x hx dv.2)
  | _, .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq body, w, env =>
      -- destructure `z` and re-bind `v₁`/`v₂` to its `fst`/`snd` (the `peLookup` env-split)
      M.interpWFF body w
        (peLookup (X := fun T => M.frame.interp T w)
          (fun {A B} x => (x : M.frame.interp A w × M.frame.interp B w).1)
          (fun {A B} x => (x : M.frame.interp A w × M.frame.interp B w).2)
          v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq env)

end RModel
