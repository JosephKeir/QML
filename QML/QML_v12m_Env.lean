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

/-- ⭐An environment: an object for every visible address (`val`), and for every witness in view
    (branch `wip/in-atom`, docs §12.16) its value along the arrow just taken — present exactly when
    the arrow is in its extent, as a `Part` (`wit`).  It needs only the frame, so a model with its
    relations replaced has the same environments (`QML_v12m_SemAdmissible`). -/
structure Frame.Env {σ : Signature} (F : Frame.{u, v} σ) (Γ : Ctx) (w : F.W) : Type u where
  val : ∀ v T, Γ v = some T → F.Dom T w
  wit : ∀ y X, Γ.wit y = some X → Part (F.Dom X w) := fun _ _ _ => Part.none

namespace Model

variable {σ : Signature} (M : Model.{u, v} σ)

/-- An environment of the model: one of its frame. -/
abbrev Env (Γ : Ctx) (w : M.frame.W) : Type u := M.frame.Env Γ w

instance {Γ : Ctx} {w : M.frame.W} :
    CoeFun (M.Env Γ w) (fun _ => ∀ v T, Γ v = some T → M.frame.Dom T w) := ⟨Frame.Env.val⟩

/-- An environment written as a function: no witness is present. -/
instance {Γ : Ctx} {w : M.frame.W} :
    Coe (∀ v T, Γ v = some T → M.frame.Dom T w) (M.Env Γ w) := ⟨fun f => { val := f }⟩

/-- The component of an object along a projection step. -/
def stepObj {w : M.frame.W} {U T : VarType} {s : Step} (hs : s.isProj = true)
    (h : U.step s = some T) (a : M.frame.Dom U w) : M.frame.Dom T w := by
  cases U <;> cases s <;> (try cases hs) <;> (try cases h)
  · exact a.1
  · exact a.2
  · exact (VarType.step_here h).2 ▸ M.necEval a ⟨w, ⟨M.frame.refl (VarType.step_here h).1 w⟩⟩

variable {M}

/-- ⭐A possible object read along an arrow: present exactly when the arrow is in its extent, with
    its content there.  What a witness is worth one view in. -/
def posPart {X : VarType} {w : M.frame.W} (p : M.frame.Dom (.VTypeDia X) w) (w' : M.frame.Acc w) :
    Part (M.frame.Dom X w'.1) :=
  ⟨w' ∈ (M.posEval p).1, fun hm => (M.posEval p).2 ⟨w', hm⟩⟩

/-- Environments are equal when their objects and their witnesses are. -/
theorem Env.ext' {Γ : Ctx} {w : M.frame.W} {e₁ e₂ : M.Env Γ w}
    (hv : ∀ v T (h : Γ v = some T), e₁ v T h = e₂ v T h)
    (hw : ∀ y X (h : Γ.wit y = some X), e₁.wit y X h = e₂.wit y X h) : e₁ = e₂ := by
  cases e₁
  cases e₂
  congr
  · funext v T h
    exact hv v T h
  · funext y X h
    exact hw y X h

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

/-- Into a `□`, at an accessible world: the objects. -/
def Env.boxPushVal {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (w' : M.frame.Acc w) :
    ∀ v T, Γ.boxIn v = some T → M.frame.Dom T w'.1
  | .step u .box, _, h => M.necEval (env.ref u (Ctx.boxIn_step_box h)) w'
  | .step u .keep, _, h =>
      M.necEval (GFunc.eval M.ops (GFunc.keep (σ := σ) (Ctx.boxIn_keep h).1 (Ctx.boxIn_keep h).2.2)
        w (env.ref u (Ctx.boxIn_keep h).2.1)) w'
  | .root _, _, h => False.elim (by cases h)
  | .step _ .fst, _, h => False.elim (by cases h)
  | .step _ .snd, _, h => False.elim (by cases h)
  | .step _ .dia, _, h => False.elim (by cases h)
  | .step _ .here, _, h => False.elim (by cases h)

/-- ⭐Into a `□`, at an accessible world: the objects, and each possible object of `Γ` as a
    witness, present exactly when the arrow is in its extent, with its content there. -/
def Env.boxPush {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (w' : M.frame.Acc w) :
    M.Env Γ.boxIn w'.1 where
  val := env.boxPushVal w'
  wit y _ h := posPart (env.ref y (Ctx.boxIn_wit.mp h).2) w'

/-- Into a `◇_x`, at a world of the extent of the possible object `x`: the objects. -/
def Env.diaPushVal {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (x : VarSymb) {X : VarType}
    (hx : Γ.ref x = some (.VTypeDia X)) (w' : (M.posEval (env.ref x hx)).1) :
    ∀ v T, Γ.diaIn x v = some T → M.frame.Dom T w'.1.1
  | .step _ .dia, _, h => Ctx.diaIn_step_dia hx h ▸ (M.posEval (env.ref x hx)).2 w'
  | .step u .box, T, h => env.boxPush w'.1 (.step u .box) T h
  | .step u .keep, T, h => env.boxPush w'.1 (.step u .keep) T h
  | .root _, _, h => False.elim (by cases h)
  | .step _ .fst, _, h => False.elim (by cases h)
  | .step _ .snd, _, h => False.elim (by cases h)
  | .step _ .here, _, h => False.elim (by cases h)

/-- Into a `◇_x`, at a world of the extent of the possible object `x`; the witnesses as in the
    `□` view. -/
def Env.diaPush {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (x : VarSymb) {X : VarType}
    (hx : Γ.ref x = some (.VTypeDia X)) (w' : (M.posEval (env.ref x hx)).1) :
    M.Env (Γ.diaIn x) w'.1.1 where
  val := env.diaPushVal x hx w'
  wit := (env.boxPush w'.1).wit

/-- Declare a root with an object.  The witnesses stay. -/
def Env.extend {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (r : Root) {T : VarType}
    (o : M.frame.Dom T w) : M.Env (Γ.insert r T) w where
  val v U h :=
    if hv : v = .root r then
      (show T = U by rw [hv] at h; simpa [Ctx.insert] using h) ▸ o
    else env v U (by simpa [Ctx.insert, hv] using h)
  wit := env.wit

/-- ⭐Into the view of the witness `y` (`◇⁰_y`), at the same world, with `c` its content. -/
def Env.optPush {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (y : VarSymb) {X : VarType}
    (hy : Γ.wit y = some X) (c : M.frame.Dom X w) : M.Env (Γ.optIn y) w where
  val v T h :=
    if hv : v = .step y .dia then
      (show X = T by
        subst hv
        rw [Ctx.optIn_content hy] at h
        exact Option.some.inj h) ▸ c
    else env v T (by rwa [Ctx.optIn_ne hv] at h)
  wit := env.wit

end Model

end V12M
