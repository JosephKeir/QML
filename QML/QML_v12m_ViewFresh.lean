import QML.QML_v12m_Presented

/-!
# QML v12m — an address belongs to one view depth

`Ctx.diaIn x` inherits `Ctx.boxIn` wholesale, so if `x` were *itself* visible in `Γ.boxIn` the view
`Γ.diaIn x` would re-expose `x`, and then the one address `x.dia` would mean two things: the inner
content (the `.dia` branch of `Ctx.diaIn`) and — one level further in — the outer content, inherited
as a `□`-view entry.  That is a **co-naming**, not a co-extension: two addresses may perfectly well
denote the same object, but one address may not stand for two positions.  It is what blocks
abstracting a `◇` view at an arbitrary address (§2d, §9), and only an address of the shape
`VarSymb.inner u` for `u : □◇A` — the value, one view in, of a *necessarily possible*
object — can do it.

The naming discipline already rules it out, and this file says how.  ⭐`Ctx.LevelDepth d Γ`: every
declared address has exactly as many **level** steps as its root's depth `d` prescribes.  A view
adds one to every depth, a fresh declaration starts a root at zero, so a presentation always has one
(`Ctx.Presented.levelDepth`).  ⭐`Ctx.ViewFresh` — nothing the `□` view shows, nor any extension of
it, is visible in the context — then follows by arithmetic: the view's addresses carry `d + 1` level
steps and the context's carry `d`, and an extension only adds more.
-/

namespace V12M

variable [ModalSys]

omit [ModalSys] in
theorem Step.levels_append : ∀ (p q : List Step),
    Step.levels (p ++ q) = Step.levels p + Step.levels q
  | [], q => by simp [Step.levels]
  | s :: p, q => by
      change (if s.isProj then 0 else 1) + Step.levels (p ++ q) =
        ((if s.isProj then 0 else 1) + Step.levels p) + Step.levels q
      rw [Step.levels_append p q]
      omega

omit [ModalSys] in
theorem Step.levels_le_ext : ∀ (v : VarSymb) (p : List Step),
    Step.levels v.path ≤ Step.levels (v.ext p).path
  | _, [] => le_rfl
  | v, s :: p => by
      refine le_trans ?_ (Step.levels_le_ext (.step v s) p)
      change Step.levels v.path ≤ Step.levels (v.path ++ [s])
      rw [Step.levels_append]
      omega

omit [ModalSys] in
theorem Step.levels_step_of_proj {v : VarSymb} {s : Step} (hs : s.isProj = true) :
    Step.levels (VarSymb.step v s).path = Step.levels v.path := by
  change Step.levels (v.path ++ [s]) = _
  rw [Step.levels_append]
  simp [Step.levels, hs]

omit [ModalSys] in
theorem Step.levels_step_of_level {v : VarSymb} {s : Step} (hs : s.isProj = false) :
    Step.levels (VarSymb.step v s).path = Step.levels v.path + 1 := by
  change Step.levels (v.path ++ [s]) = _
  rw [Step.levels_append]
  simp [Step.levels, hs]

namespace Ctx

/-- ⭐**One view depth per address**: a declared address has exactly as many level steps as its
    root's depth prescribes.  A view raises every depth by one and a fresh declaration starts a root
    at zero, so this is what a presentation maintains. -/
def LevelDepth (d : Root → ℕ) (Γ : Ctx) : Prop :=
  ∀ (v : VarSymb) (T : VarType), Γ.ref v = some T → Step.levels v.path = d v.rt

/-- ⭐Nothing the `□` view makes visible, nor any extension of it, is visible in the context. -/
def ViewFresh (Γ : Ctx) : Prop :=
  ∀ (v : VarSymb) (p : List Step), Γ.boxIn.ref v ≠ none → Γ.ref (v.ext p) = none

/-- The box view's addresses carry one more level step than the context's. -/
theorem levelDepth_boxIn {d : Root → ℕ} {Γ : Ctx} (h : LevelDepth d Γ) :
    LevelDepth (fun r => d r + 1) Γ.boxIn := by
  intro v T hv
  match v with
  | .root _ => cases hv
  | .step u .box =>
      obtain ⟨_, hu⟩ := Ctx.boxIn_box hv
      rw [Step.levels_step_of_level (s := Step.box) rfl, h u _ hu]
      rfl
  | .step u .keep =>
      obtain ⟨_, hu, _, rfl⟩ := Ctx.boxIn_keep hv
      rw [Step.levels_step_of_level (s := Step.keep) rfl, h u _ hu]
      rfl
  | .step u .dia => cases hv
  | .step u .fst =>
      change ((Γ.boxIn.ref u).bind (·.step .fst)) = some T at hv
      cases hu : Γ.boxIn.ref u with
      | none => rw [hu] at hv; cases hv
      | some U =>
          rw [Step.levels_step_of_proj (s := Step.fst) rfl]
          exact levelDepth_boxIn h u U hu
  | .step u .snd =>
      change ((Γ.boxIn.ref u).bind (·.step .snd)) = some T at hv
      cases hu : Γ.boxIn.ref u with
      | none => rw [hu] at hv; cases hv
      | some U =>
          rw [Step.levels_step_of_proj (s := Step.snd) rfl]
          exact levelDepth_boxIn h u U hu
  | .step u .here =>
      change ((Γ.boxIn.ref u).bind (·.step .here)) = some T at hv
      cases hu : Γ.boxIn.ref u with
      | none => rw [hu] at hv; cases hv
      | some U =>
          rw [Step.levels_step_of_proj (s := Step.here) rfl]
          exact levelDepth_boxIn h u U hu

/-- ⭐**Nothing below a declared address's level step is declared.**  A level step goes one view in,
    so everything under it carries more level steps than the context allows.  With `s = .dia` this
    is what abstracting a `◇` view needs about the content address; with `s = .box` or `.keep` it is
    `ViewFresh` itself. -/
theorem LevelDepth.not_below {d : Root → ℕ} {Γ : Ctx} (h : LevelDepth d Γ) {x : VarSymb}
    {X : VarType} (hx : Γ.ref x = some X) {s : Step} (hs : s.isProj = false) (p : List Step) :
    Γ.ref ((VarSymb.step x s).ext p) = none := by
  cases hw : Γ.ref ((VarSymb.step x s).ext p) with
  | none => rfl
  | some T =>
      exfalso
      have h₁ : Step.levels x.path = d x.rt := h x X hx
      have h₂ : Step.levels ((VarSymb.step x s).ext p).path =
          d ((VarSymb.step x s).ext p).rt := h _ _ hw
      have h₃ : ((VarSymb.step x s).ext p).rt = x.rt := by
        rw [VarSymb.ext_rt]
        rfl
      have h₄ : Step.levels (VarSymb.step x s).path ≤
          Step.levels ((VarSymb.step x s).ext p).path := Step.levels_le_ext _ p
      rw [Step.levels_step_of_level hs] at h₄
      rw [h₃] at h₂
      omega

/-- ⭐And so nothing is visible at two depths: `ViewFresh`. -/
theorem LevelDepth.viewFresh {d : Root → ℕ} {Γ : Ctx} (h : LevelDepth d Γ) : ViewFresh Γ := by
  intro v p hv
  cases hw : Γ.ref (v.ext p) with
  | none => rfl
  | some T =>
      exfalso
      obtain ⟨U, hU⟩ : ∃ U, Γ.boxIn.ref v = some U := Option.ne_none_iff_exists'.mp hv
      have h₁ : Step.levels v.path = d v.rt + 1 := levelDepth_boxIn h v U hU
      have h₂ : Step.levels (v.ext p).path = d (v.ext p).rt := h _ _ hw
      have h₃ : (v.ext p).rt = v.rt := VarSymb.ext_rt v p
      have h₄ : Step.levels v.path ≤ Step.levels (v.ext p).path := Step.levels_le_ext v p
      rw [h₃] at h₂
      omega


/-- Nothing is visible in the empty context. -/
theorem ref_empty : ∀ v : VarSymb, Ctx.empty.ref v = none
  | .root _ => rfl
  | .step v s => by
      change (if s.isProj then (Ctx.empty.ref v).bind (·.step s) else Ctx.empty (.step v s)) = none
      split_ifs with hs
      · rw [ref_empty v]
        rfl
      · rfl

theorem levelDepth_empty (d : Root → ℕ) : LevelDepth d Ctx.empty := by
  intro v T hv
  rw [ref_empty v] at hv
  cases hv

/-- The `◇_x` view: the content address is one level in, and the rest is the `□` view. -/
theorem levelDepth_diaIn {d : Root → ℕ} {Γ : Ctx} (h : LevelDepth d Γ) (x : VarSymb) :
    LevelDepth (fun r => d r + 1) (Γ.diaIn x) := by
  intro v T hv
  match v with
  | .root _ => cases hv
  | .step u .dia =>
      have hu : u = x := by
        change (if u = x then
          (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none) else none) = some T at hv
        split_ifs at hv with hcon
        exact hcon
      subst hu
      obtain ⟨U, hU⟩ : ∃ U, Γ.ref u = some U := by
        rcases Option.eq_none_or_eq_some (Γ.ref u) with hr | ⟨U, hr⟩
        · exfalso
          change (if u = u then
            (match Γ.ref u with | some (.VTypeDia X) => some X | _ => none)
            else none) = some T at hv
          rw [if_pos rfl, hr] at hv
          cases hv
        · exact ⟨U, hr⟩
      rw [Step.levels_step_of_level (s := Step.dia) rfl, h u U hU]
      rfl
  | .step u .box =>
      obtain ⟨_, hu⟩ := Ctx.boxIn_box (Γ := Γ) hv
      rw [Step.levels_step_of_level (s := Step.box) rfl, h u _ hu]
      rfl
  | .step u .keep =>
      obtain ⟨_, hu, _, rfl⟩ := Ctx.boxIn_keep (Γ := Γ) hv
      rw [Step.levels_step_of_level (s := Step.keep) rfl, h u _ hu]
      rfl
  | .step u .fst =>
      change (((Γ.diaIn x).ref u).bind (·.step .fst)) = some T at hv
      cases hu : (Γ.diaIn x).ref u with
      | none => rw [hu] at hv; cases hv
      | some U =>
          rw [Step.levels_step_of_proj (s := Step.fst) rfl]
          exact levelDepth_diaIn h x u U hu
  | .step u .snd =>
      change (((Γ.diaIn x).ref u).bind (·.step .snd)) = some T at hv
      cases hu : (Γ.diaIn x).ref u with
      | none => rw [hu] at hv; cases hv
      | some U =>
          rw [Step.levels_step_of_proj (s := Step.snd) rfl]
          exact levelDepth_diaIn h x u U hu
  | .step u .here =>
      change (((Γ.diaIn x).ref u).bind (·.step .here)) = some T at hv
      cases hu : (Γ.diaIn x).ref u with
      | none => rw [hu] at hv; cases hv
      | some U =>
          rw [Step.levels_step_of_proj (s := Step.here) rfl]
          exact levelDepth_diaIn h x u U hu


/-- Declaring a root leaves the addresses rooted elsewhere alone. -/
theorem ref_insert_of_rt_ne {Γ : Ctx} {r : Root} {T : VarType} :
    ∀ (v : VarSymb), v.rt ≠ r → (Γ.insert r T).ref v = Γ.ref v
  | .root r', hrt => by
      have hne : (VarSymb.root r') ≠ .root r := fun hcon => hrt (by injection hcon)
      simp only [Ctx.ref, Ctx.insert, if_neg hne]
  | .step u s, hrt => by
      simp only [Ctx.ref]
      split_ifs with hs
      · rw [ref_insert_of_rt_ne u hrt]
      · exact if_neg (fun hcon => by cases hcon)

/-- An address at a fresh root is visible only as the root itself and its projections, so it has no
    level steps. -/
theorem levels_zero_of_insert {Γ : Ctx} {r : Root} {T : VarType} (hr : Γ.RootFresh r) :
    ∀ (v : VarSymb) (S : VarType), (Γ.insert r T).ref v = some S → v.rt = r →
      Step.levels v.path = 0
  | .root _, _, _, _ => rfl
  | .step u s, S, hv, hrt => by
      by_cases hs : s.isProj = true
      · simp only [Ctx.ref, if_pos hs] at hv
        cases hu : (Γ.insert r T).ref u with
        | none => rw [hu] at hv; cases hv
        | some U =>
            rw [Step.levels_step_of_proj hs]
            exact levels_zero_of_insert hr u U hu hrt
      · exfalso
        have hraw : (Γ.insert r T) (.step u s) = some S := by
          simp only [Ctx.ref, if_neg hs] at hv
          exact hv
        rw [show (Γ.insert r T) (.step u s) = Γ (.step u s) from
          if_neg (fun hcon => by cases hcon), hr _ hrt] at hraw
        cases hraw

/-- Declaring a fresh root: that root starts at depth zero and the rest is unchanged. -/
theorem levelDepth_insert {d : Root → ℕ} {Γ : Ctx} (h : LevelDepth d Γ) {r : Root}
    (hr : Γ.RootFresh r) (T : VarType) :
    LevelDepth (Function.update d r 0) (Γ.insert r T) := by
  intro v S hv
  by_cases hrt : v.rt = r
  · rw [hrt, Function.update_self]
    exact levels_zero_of_insert hr v S hv hrt
  · rw [Function.update_of_ne hrt]
    refine h v S ?_
    rwa [ref_insert_of_rt_ne v hrt] at hv

end Ctx

/-- ⭐**A presentation has a depth assignment**, by induction on how it is built: the empty context
    takes any, a fresh declaration starts its root at zero, and a view raises every depth by one.
    This is the whole content of "an address belongs to one view depth" — and it is read off the
    naming discipline the user already owes (`CtxExpr.Fresh`), not assumed. -/
theorem CtxExpr.levelDepth : ∀ (e : CtxExpr), e.Fresh → ∃ d : Root → ℕ, Ctx.LevelDepth d e.denote
  | .empty, _ => ⟨fun _ => 0, Ctx.levelDepth_empty _⟩
  | .insertFree e u T, hf => by
      obtain ⟨d, hd⟩ := CtxExpr.levelDepth e hf.1
      exact ⟨Function.update d (.free u) 0, Ctx.levelDepth_insert hd hf.2 T⟩
  | .boxIn e, hf => by
      obtain ⟨d, hd⟩ := CtxExpr.levelDepth e hf
      exact ⟨fun r => d r + 1, Ctx.levelDepth_boxIn hd⟩
  | .diaIn e x, hf => by
      obtain ⟨d, hd⟩ := CtxExpr.levelDepth e hf
      exact ⟨fun r => d r + 1, Ctx.levelDepth_diaIn hd x⟩

/-- ⭐**So a presented context never names an address at two view depths.**  This is what the
    abstraction of a `◇` view at an arbitrary address needs, and it comes from the presentation
    rather than from a side condition (§2d, §9). -/
theorem Ctx.Presented.viewFresh {Γ : Ctx} (h : Γ.Presented) : Γ.ViewFresh := by
  obtain ⟨d, hd⟩ := h.expr.levelDepth h.fresh
  rw [← h.denote_eq] at *
  exact hd.viewFresh

namespace Ctx

/-- ⭐The same off a presentation: nothing below a declared address's level step is declared. -/
theorem Presented.not_below {Γ : Ctx} (h : Γ.Presented) {x : VarSymb} {X : VarType}
    (hx : Γ.ref x = some X) {s : Step} (hs : s.isProj = false) (p : List Step) :
    Γ.ref ((VarSymb.step x s).ext p) = none := by
  obtain ⟨d, hd⟩ := h.expr.levelDepth h.fresh
  rw [← h.denote_eq] at *
  exact hd.not_below hx hs p

/-- The two readings the generalised abstraction consumes: a declared address is not itself a view
    entry, and no prefix of one is either. -/
theorem ViewFresh.not_boxIn {Γ : Ctx} (h : Γ.ViewFresh) {v : VarSymb} {T : VarType}
    (hv : Γ.ref v = some T) : Γ.boxIn.ref v = none := by
  cases hb : Γ.boxIn.ref v with
  | none => rfl
  | some U =>
      exfalso
      have hnone := h v [] (by rw [hb]; exact fun hcon => by cases hcon)
      rw [show VarSymb.ext v [] = v from rfl, hv] at hnone
      cases hnone

theorem ViewFresh.not_prefix {Γ : Ctx} (h : Γ.ViewFresh) {v w : VarSymb} {T : VarType}
    (p : List Step) (hvw : w = v.ext p) (hw : Γ.ref w = some T) : Γ.boxIn.ref v = none := by
  cases hb : Γ.boxIn.ref v with
  | none => rfl
  | some U =>
      exfalso
      have hnone := h v p (by rw [hb]; exact fun hcon => by cases hcon)
      rw [← hvw, hw] at hnone
      cases hnone

end Ctx

end V12M
