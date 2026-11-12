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

/-- An environment's respect for its opened witnesses, where there is nothing to check: no
    witness, or none whose content is declared (a `□` view).  Later files add rules
    (`ctxOf_wit`). -/
macro_rules | `(tactic| opened_triv) => `(tactic| (intro _ _ h _; cases h))
macro_rules | `(tactic| opened_triv) => `(tactic| (intro _ _ _ h; cases h))

/-- ⭐An environment: an object for every visible address (`val`), and for every witness in view
    (branch `wip/in-atom`, docs §12.16) its value along the arrow just taken — present exactly when
    the arrow is in its extent, as a `Part` (`wit`).  It needs only the frame, so a model with its
    relations replaced has the same environments (`QML_v12m_SemAdmissible`). -/
structure Frame.Env {σ : Signature} (F : Frame.{u, v} σ) (Γ : Ctx) (w : F.W) : Type u where
  val : ∀ v T, Γ v = some T → F.Dom T w
  wit : ∀ y X, Γ.wit y = some X → Part (F.Dom X w) := fun _ _ _ => Part.none
  /-- ⭐It **respects its opened witnesses**: where a witness's content is in view as well
      (inside `◇_x`, or `◇⁰_y`), the witness is present and its content is the object there.  The
      two names for one object agree, so no environment can tell them apart. -/
  opened : ∀ z Z (hz : Γ.wit z = some Z) (hv : Γ (.step z .dia) = some Z),
    ∃ hd : (wit z Z hz).Dom, val (.step z .dia) Z hv = (wit z Z hz).get hd := by opened_triv

/-- An environment given by its objects: a witness whose content is in view is present with it,
    every other one absent. -/
def Frame.Env.ofVal {σ : Signature} {F : Frame.{u, v} σ} {Γ : Ctx} {w : F.W}
    (f : ∀ v T, Γ v = some T → F.Dom T w) : F.Env Γ w where
  val := f
  wit z Z _ := if hv : Γ (.step z .dia) = some Z then Part.some (f _ Z hv) else Part.none
  opened z Z _ hv := by
    split
    · exact ⟨trivial, rfl⟩
    · contradiction

namespace Model

variable {σ : Signature} (M : Model.{u, v} σ)

/-- An environment of the model: one of its frame. -/
abbrev Env (Γ : Ctx) (w : M.frame.W) : Type u := M.frame.Env Γ w

instance {Γ : Ctx} {w : M.frame.W} :
    CoeFun (M.Env Γ w) (fun _ => ∀ v T, Γ v = some T → M.frame.Dom T w) := ⟨Frame.Env.val⟩

/-- An environment written as a function (`Frame.Env.ofVal`). -/
instance {Γ : Ctx} {w : M.frame.W} :
    Coe (∀ v T, Γ v = some T → M.frame.Dom T w) (M.Env Γ w) := ⟨Frame.Env.ofVal⟩

/-- The component of an object along a projection step. -/
def stepObj {w : M.frame.W} {U T : VarType} {s : Step} (hs : s.isStruct = true)
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
  obtain ⟨v₁, w₁, _⟩ := e₁
  obtain ⟨v₂, w₂, _⟩ := e₂
  have h₁ : v₁ = v₂ := funext fun v => funext fun T => funext fun h => hv v T h
  have h₂ : w₁ = w₂ := funext fun y => funext fun X => funext fun h => hw y X h
  subst h₁ h₂
  rfl

/-- An opened witness is present, with its content the object at its content address. -/
theorem Env.wit_opened {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {z : VarSymb} {Z : VarType}
    (hz : Γ.wit z = some Z) (hv : Γ (.step z .dia) = some Z) :
    env.wit z Z hz = Part.some (env (.step z .dia) Z hv) := by
  obtain ⟨hd, he⟩ := env.opened z Z hz hv
  rw [he]
  exact (Part.some_get hd).symm

/-- Environments are equal when their objects are, and their witnesses whose content is not in
    view (an opened witness is its content, `Env.wit_opened`). -/
theorem Env.ext_val {Γ : Ctx} {w : M.frame.W} {e₁ e₂ : M.Env Γ w}
    (hv : ∀ v T (h : Γ v = some T), e₁ v T h = e₂ v T h)
    (hw : ∀ y X (h : Γ.wit y = some X), Γ (.step y .dia) ≠ some X →
      e₁.wit y X h = e₂.wit y X h) : e₁ = e₂ :=
  Env.ext' hv fun y X h => by
    by_cases ho : Γ (.step y .dia) = some X
    · rw [e₁.wit_opened h ho, e₂.wit_opened h ho, hv]
    · exact hw y X h ho

/-- The object at a reachable address: projection components from the parent. -/
def Env.ref {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) :
    (v : VarSymb) → {T : VarType} → Γ.ref v = some T → M.frame.Dom T w
  | .root r, _, h => env (.root r) _ h
  | .step v s, T, h =>
      if hs : s.isStruct = true then
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
  opened z Z _ hv := by
    have hzx : z = x := by
      change (if z = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some Z at hv
      split_ifs at hv with h
      exact h
    subst hzx
    have hXZ := Ctx.diaIn_step_dia hx hv
    subst hXZ
    exact ⟨w'.2, rfl⟩

/-- Declare a root with an object.  The witnesses stay. -/
def Env.extend {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (r : Root) {T : VarType}
    (o : M.frame.Dom T w) : M.Env (Γ.insert r T) w where
  val v U h :=
    if hv : v = .root r then
      (show T = U by rw [hv] at h; simpa [Ctx.insert] using h) ▸ o
    else env v U (by simpa [Ctx.insert, hv] using h)
  wit := env.wit
  opened z Z hz hv := by
    have hne : VarSymb.step z .dia ≠ .root r := fun he => by cases he
    have hv' : Γ (.step z .dia) = some Z := by rwa [Ctx.insert_ne hne] at hv
    obtain ⟨hd, he⟩ := env.opened z Z hz hv'
    refine ⟨hd, ?_⟩
    rw [dif_neg hne]
    exact he

/-- ⭐Into the view of the witness `y` (`◇⁰_y`), at the same world, where it is present: its
    content in view. -/
def Env.optPush {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (y : VarSymb) {X : VarType}
    (hy : Γ.wit y = some X) (hd : (env.wit y X hy).Dom) : M.Env (Γ.optIn y) w where
  val v T h :=
    if hv : v = .step y .dia then
      (show X = T by
        subst hv
        rw [Ctx.optIn_content hy] at h
        exact Option.some.inj h) ▸ (env.wit y X hy).get hd
    else env v T (by rwa [Ctx.optIn_ne hv] at h)
  wit := env.wit
  opened z Z hz hv := by
    by_cases hzy : z = y
    · subst hzy
      have hXZ : X = Z := Option.some.inj (hy.symm.trans hz)
      subst hXZ
      exact ⟨hd, by rw [dif_pos rfl]⟩
    · have hne : VarSymb.step z .dia ≠ .step y .dia := fun he => hzy (by cases he; rfl)
      have hv' : Γ (.step z .dia) = some Z := by rwa [Ctx.optIn_ne hne] at hv
      obtain ⟨hd', he⟩ := env.opened z Z hz hv'
      exact ⟨hd', by rw [dif_neg hne]; exact he⟩

end Model

end V12M
