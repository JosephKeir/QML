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

omit [ModalSys] in
/-- The only content the view of `y.box` declares is `y`'s, at the type of `y.box`'s value. -/
theorem Ctx.optIn_dia_entry {Γ : Ctx} {y w : VarSymb} {X T : VarType}
    (hy : Γ (.step y .box) = some (.VTypeOpt X)) (h : Γ.optIn y (.step w .dia) = some T) :
    w = y ∧ T = X := by
  by_cases hw : VarSymb.step w .dia = .step y .dia
  · cases hw
    rw [Ctx.optIn_content hy] at h
    exact ⟨rfl, (Option.some.inj h).symm⟩
  · rw [Ctx.optIn_dia hw rfl] at h; cases h

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

/-- ⭐**The value of `u.box` along an arrow**: a necessary object's value there, or (with `Opt` on,
    docs §12.13) a possible object's content there, present exactly when the arrow is in its
    extent. -/
def Env.boxVal {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (u : VarSymb) {T : VarType}
    (h : Γ.boxIn (.step u .box) = some T) (w' : M.frame.Acc w) : M.frame.Dom T w'.1 :=
  if hb : Γ.ref u = some (.VTypeBox T) then M.necEval (env.ref u hb) w'
  else
    match hu : Γ.ref u with
    | some (.VTypeDia A) =>
        have hT : T = .VTypeOpt A := by
          obtain ⟨-, h' | ⟨-, A', hu', hT⟩⟩ := Ctx.boxIn_box' h
          · exact absurd h' hb
          · rw [hu] at hu'; cases hu'; exact hT
        hT ▸ (⟨w' ∈ (M.posEval (env.ref u hu)).1,
          fun hm => (M.posEval (env.ref u hu)).2 ⟨w', hm⟩⟩ : Part (M.frame.Dom A w'.1))
    | some .Var => False.elim (by
        obtain ⟨-, h' | ⟨-, A', hu', -⟩⟩ := Ctx.boxIn_box' h
        · exact hb h'
        · rw [hu'] at hu; cases hu)
    | some .VTypeOne => False.elim (by
        obtain ⟨-, h' | ⟨-, A', hu', -⟩⟩ := Ctx.boxIn_box' h
        · exact hb h'
        · rw [hu'] at hu; cases hu)
    | some (.VTypeProd _ _) => False.elim (by
        obtain ⟨-, h' | ⟨-, A', hu', -⟩⟩ := Ctx.boxIn_box' h
        · exact hb h'
        · rw [hu'] at hu; cases hu)
    | some (.VTypeBox _) => False.elim (by
        obtain ⟨-, h' | ⟨-, A', hu', -⟩⟩ := Ctx.boxIn_box' h
        · exact hb h'
        · rw [hu'] at hu; cases hu)
    | some (.VTypeOpt _) => False.elim (by
        obtain ⟨-, h' | ⟨-, A', hu', -⟩⟩ := Ctx.boxIn_box' h
        · exact hb h'
        · rw [hu'] at hu; cases hu)
    | none => False.elim (by
        obtain ⟨-, h' | ⟨-, A', hu', -⟩⟩ := Ctx.boxIn_box' h
        · exact hb h'
        · rw [hu'] at hu; cases hu)

theorem Env.boxVal_box {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {u : VarSymb} {T : VarType}
    (h : Γ.boxIn (.step u .box) = some T) (hb : Γ.ref u = some (.VTypeBox T))
    (w' : M.frame.Acc w) : env.boxVal u h w' = M.necEval (env.ref u hb) w' := by
  unfold Env.boxVal
  rw [dif_pos hb]

/-- The value of a possible object along an arrow: present exactly when the arrow is in its
    extent, with its content there. -/
theorem Env.boxVal_dia {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {u : VarSymb} {A : VarType}
    (h : Γ.boxIn (.step u .box) = some (.VTypeOpt A)) (hu : Γ.ref u = some (.VTypeDia A))
    (w' : M.frame.Acc w) :
    env.boxVal u h w' = (⟨w' ∈ (M.posEval (env.ref u hu)).1,
      fun hm => (M.posEval (env.ref u hu)).2 ⟨w', hm⟩⟩ : Part (M.frame.Dom A w'.1)) := by
  have hb : ¬ Γ.ref u = some (.VTypeBox (.VTypeOpt A)) := by rw [hu]; simp
  unfold Env.boxVal
  rw [dif_neg hb]
  split
  · rename_i A' hu'
    rw [hu] at hu'
    cases hu'
    rfl
  all_goals (rename_i hne; rw [hu] at hne; cases hne)

/-- Into a `□`, at an accessible world. -/
def Env.boxPush {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w)
    (w' : M.frame.Acc w) : M.Env Γ.boxIn w'.1
  | .step u .box, _, h => env.boxVal u h w'
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

/-- ⭐Into the view of `y.box` (`◇⁰_y`, docs §12.13), at the same world, with `c` its content. -/
def Env.optPush {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (y : VarSymb) {X : VarType}
    (hy : Γ (.step y .box) = some (.VTypeOpt X)) (c : M.frame.Dom X w) :
    M.Env (Γ.optIn y) w := fun v T h =>
  if hv : v = .step y .dia then
    (show X = T by
      subst hv
      rw [Ctx.optIn_content hy] at h
      exact Option.some.inj h) ▸ c
  else env v T (Ctx.optIn_of_ne hv h).2

/-- Declare a root with an object. -/
def Env.extend {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (r : Root) {T : VarType}
    (o : M.frame.Dom T w) : M.Env (Γ.insert r T) w := fun v U h =>
  if hv : v = .root r then
    (show T = U by rw [hv] at h; simpa [Ctx.insert] using h) ▸ o
  else env v U (by simpa [Ctx.insert, hv] using h)

end Model

end V12M
