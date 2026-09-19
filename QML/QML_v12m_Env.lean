import QML.QML_v12m_Model
import QML.QML_v12m_Collapse

/-!
# QML v12m — environments

An environment over a context gives an object of the right type to every VISIBLE address.
Projection components are read from their parent (`Env.ref`, following `Ctx.ref`): product
components by projection, and under T the `here` component of a necessary object by evaluating it
at the current world (reflexivity).  Entering a modality moves the environment into the modal view
of the context:

* `Env.boxPush env w'` — at an accessible world `w'`, the content `u.box` of each necessary
  `u` is its value at `w'`, and under 4 the kept `u.keep` is `u` kept at `w'` (`GFunc.keep`);
* `Env.diaPush env x hx w'` — at a world `w'` of the extent of the possible object `x`, its
  content `x.dia` is its one object there, and the necessary objects are read at `w'` as for `□`.

`Env.extend` declares a root (a quantifier slot or an eigenvariable).
-/

namespace V12M

variable [ModalSys]

theorem Ctx.diaIn_step_dia {Γ : Ctx} {x u : VarSymb} {X T : VarType}
    (hx : Γ.ref x = some (.VTypeDia X)) (h : (Γ.diaIn x) (.step u .dia) = some T) : X = T := by
  change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
    else none) = some T at h
  split_ifs at h
  rw [hx] at h
  exact Option.some.inj h

namespace Model

variable {σ : Signature} (M : Model.{u, v} σ)

/-- An environment: an object for every visible address. -/
abbrev Env (Γ : Ctx) (w : M.frame.W) : Type u := ∀ v T, Γ v = some T → M.frame.Dom T w

/-- The component of an object along a projection step. -/
def stepObj {w : M.frame.W} {U T : VarType} {s : Step} (hs : s.isProj = true)
    (h : U.step s = some T) (a : M.frame.Dom U w) : M.frame.Dom T w := by
  cases U <;> cases s <;> (try cases hs) <;> (try cases h)
  · exact a.1
  · exact a.2
  · exact (VarType.step_here h).2 ▸ M.necEval a ⟨w, ⟨M.frame.refl (VarType.step_here h).1 w⟩⟩

variable {M}

/-- The object at a reachable address: projection components from the parent. -/
def Env.ref {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) :
    (v : VarSymb) → {T : VarType} → Γ.ref v = some T → M.frame.Dom T w
  | .root r, _, h => env (.root r) _ h
  | .step v s, T, h =>
      if hs : s.isProj = true then
        match hU : Γ.ref v with
        | some U =>
            M.stepObj hs (by rw [Ctx.ref_step_proj Γ v hs, hU] at h; exact h)
              (Env.ref env v hU)
        | none => False.elim (by rw [Ctx.ref_step_proj Γ v hs, hU] at h; cases h)
      else env (.step v s) T (by rw [Ctx.ref_step_nonproj Γ v hs] at h; exact h)

/-- Into a `□`, at an accessible world. -/
def Env.boxPush {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (w' : M.frame.Acc w) :
    M.Env Γ.boxIn w'.1
  | .step u .box, _, h => M.necEval (env.ref u (Ctx.boxIn_step_box h)) w'
  | .step u .keep, _, h =>
      M.necEval (GFunc.eval M.ops (GFunc.keep (σ := σ) (Ctx.boxIn_keep h).1 (Ctx.boxIn_keep h).2.2)
        w (env.ref u (Ctx.boxIn_keep h).2.1)) w'
  | .root _, _, h => False.elim (by cases h)
  | .step _ .fst, _, h => False.elim (by cases h)
  | .step _ .snd, _, h => False.elim (by cases h)
  | .step _ .dia, _, h => False.elim (by cases h)
  | .step _ .here, _, h => False.elim (by cases h)

/-- Into a `◇_x`, at a world of the extent of the possible object `x`. -/
def Env.diaPush {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (x : VarSymb) {X : VarType}
    (hx : Γ.ref x = some (.VTypeDia X)) (w' : (M.posEval (env.ref x hx)).1) :
    M.Env (Γ.diaIn x) w'.1.1
  | .step _ .dia, _, h => Ctx.diaIn_step_dia hx h ▸ (M.posEval (env.ref x hx)).2 w'
  | .step u .box, T, h => env.boxPush w'.1 (.step u .box) T h
  | .step u .keep, T, h => env.boxPush w'.1 (.step u .keep) T h
  | .root _, _, h => False.elim (by cases h)
  | .step _ .fst, _, h => False.elim (by cases h)
  | .step _ .snd, _, h => False.elim (by cases h)
  | .step _ .here, _, h => False.elim (by cases h)

/-- Declare a root with an object. -/
def Env.extend {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (r : Root) {T : VarType}
    (o : M.frame.Dom T w) : M.Env (Γ.insert r T) w := fun v U h =>
  if hv : v = .root r then
    (show T = U by rw [hv] at h; simpa [Ctx.insert] using h) ▸ o
  else env v U (by simpa [Ctx.insert, hv] using h)

end Model

end V12M
