import QML.QML_v12m_ViewRen
import QML.QML_v12m_WorldLang

/-!
# QML v12m — every world language is flat

`Ctx.LevelFlat` — no declared address sits strictly below a declared one along a level step — is
what `Ctx.ViewClean` needs, and so what the view renaming needs (`QML_v12m_ViewRen`).  Here it is
established for the contexts the canonical model uses:

* ⭐`Ctx.LevelFlat.stage`: declaring the own variables of a stage keeps flatness, since their names
  are fresh for the base;
* ⭐`WorldLang.LevelFlat`: a language is flat when its bases are, and then every stage context is
  (`WorldLang.LevelFlat.ctx`), so `Ctx.ViewClean` holds at every `◇`-typed address of every stage
  (`WorldLang.LevelFlat.viewClean`).

The bases of the languages the construction builds are the `□` and `◇_x` views of an outer stage
context, which `Ctx.LevelFlat.boxIn` and `Ctx.LevelFlat.diaIn` cover; the actual world's base is the
context completeness is stated for, and flatness of *that* is the one thing a caller must supply.
-/

namespace V12M

variable [ModalSys]

/-! ## The one non-shadowing condition -/

/-- The empty context is flat: it declares nothing. -/
theorem Ctx.LevelFlat.empty : Ctx.empty.LevelFlat :=
  fun _ _ _ _ hu => absurd (Ctx.ref_empty _) hu

/-- ⭐**A non-shadowing presentation is flat**, one constructor at a time: a declared root by
    `Ctx.LevelFlat.insert` with the presentation's own freshness, and the two views by
    `Ctx.LevelFlat.boxIn` / `.diaIn`, which ask for nothing. -/
theorem CtxExpr.Fresh.levelFlat : ∀ (e : CtxExpr), e.Fresh → e.denote.LevelFlat
  | .empty, _ => Ctx.LevelFlat.empty
  | .insertFree e _ T, h =>
      (CtxExpr.Fresh.levelFlat e h.1).insert h.2 T
  | .boxIn e, h => (CtxExpr.Fresh.levelFlat e h).boxIn
  | .diaIn e x, h => (CtxExpr.Fresh.levelFlat e h).diaIn x

/-- ⭐**Every presented context is flat.**  `CtxExpr.Fresh` — each declaration's name unused in its
    own prefix — is carried by `Ctx.Presented` itself, so flatness is not a side condition anyone
    states: the metatheorems read it off the instance, and so does the canonical model, at every
    stage of every world language (`WorldLang.flatCtx`).  This is what §2d's view renaming needs. -/
theorem Ctx.Presented.levelFlat (Γ : Ctx) [h : Γ.Presented] : Γ.LevelFlat :=
  h.denote_eq ▸ CtxExpr.Fresh.levelFlat h.expr h.fresh

namespace WorldLang

/-- ⭐Every stage context of every world language is flat: its bases are presented, and declaring
    the own variables keeps flatness because their names are fresh for the base. -/
theorem flatCtx (L : WorldLang) (i : ℕ × ℕ) : (L.ctx i).LevelFlat :=
  Ctx.Presented.levelFlat _

/-- ⭐So the view renaming is available at every `◇`-typed address of every stage. -/
theorem viewClean (L : WorldLang) {i : ℕ × ℕ} {x : VarSymb} {A : VarType}
    (hx : (L.ctx i).ref x = some (.VTypeDia A)) : Ctx.ViewClean (L.ctx i) x :=
  (L.flatCtx i).viewClean hx

end WorldLang

end V12M
