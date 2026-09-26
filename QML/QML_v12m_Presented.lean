import QML.QML_v12m_Symbols

/-!
# QML v12m — presented contexts

Contexts are partial functions on addresses, which is what the machinery wants.  But a function
can declare infinitely many roots (no fresh eigenvariables), or make addresses visible that no
declaration produces.  A **presentation** rules both out: an expression built from the empty
context by declaring free variables and taking modal views, whose denotation is the context.

* `Ctx.Presented Γ` carries the expression as data, so fresh names are computed from it
  (`Ctx.Presented.bound`, `Ctx.Presented.fresh_bound`).  It also gives `Ctx.NoSlots`.
* ⭐It also carries `CtxExpr.Fresh`: **each declaration's name is unused in its own prefix**.  That
  is the locally nameless discipline's own obligation on the user, and the only one — so it belongs
  to what "presented" means rather than travelling as a side condition on the metatheorems.  It is
  what `Ctx.LevelFlat` (hence the view renaming of §2d) is read off.
* Instances follow the proof rules: the empty context, declaring a *fresh* free variable, `□` and
  `◇_x` views.  Declaring a name the context may already have is no longer a presentation, so
  `Ctx.Presented.insertFree` asks for the freshness the rule itself asks for.
* `Ctx.ofDecls` builds a context from a finite list of declarations `(u, T)`; the head of the list
  is declared last, so it is presented when the names are distinct (`Ctx.presentedOfDecls`).
-/

namespace V12M

/-- How a proof context is built. -/
inductive CtxExpr where
  | empty
  | insertFree (e : CtxExpr) (u : ℕ) (T : VarType)
  | boxIn (e : CtxExpr)
  | diaIn (e : CtxExpr) (x : VarSymb)

/-- Every free variable from here on is unused. -/
def CtxExpr.freeBound : CtxExpr → ℕ
  | .empty => 0
  | .insertFree e u _ => max e.freeBound (u + 1)
  | .boxIn e => e.freeBound
  | .diaIn e _ => e.freeBound

/-- Declare the free variables of a finite list; the head is declared last. -/
def Ctx.ofDecls : List (ℕ × VarType) → Ctx
  | [] => Ctx.empty
  | (u, T) :: ds => (Ctx.ofDecls ds).insert (.free u) T

def CtxExpr.ofDecls : List (ℕ × VarType) → CtxExpr
  | [] => .empty
  | (u, T) :: ds => .insertFree (CtxExpr.ofDecls ds) u T

variable [ModalSys]

namespace CtxExpr

def denote : CtxExpr → Ctx
  | .empty => Ctx.empty
  | .insertFree e u T => e.denote.insert (.free u) T
  | .boxIn e => e.denote.boxIn
  | .diaIn e x => e.denote.diaIn x

theorem fresh_of_bound : ∀ (e : CtxExpr) (n : ℕ), e.freeBound ≤ n → e.denote.RootFresh (.free n)
  | .empty, _, _ => Ctx.RootFresh.empty _
  | .insertFree e u T, n, hn =>
      (fresh_of_bound e n (Nat.max_le.mp hn).1).insert_ne
        (fun he => by
          cases he
          exact absurd (Nat.max_le.mp hn).2 (Nat.not_succ_le_self _)) T
  | .boxIn e, n, hn => (fresh_of_bound e n hn).boxIn
  | .diaIn e x, n, hn => (fresh_of_bound e n hn).diaIn x

theorem slots : ∀ (e : CtxExpr), e.denote.SlotsFrom 0
  | .empty => fun _ _ _ _ => rfl
  | .insertFree e u T => (slots e).insertFree u T
  | .boxIn e => (slots e).boxIn
  | .diaIn e x => (slots e).diaIn x

/-- ⭐**The one non-shadowing condition**: a presentation **declares no name already in scope** —
    each free variable is fresh for its own prefix.  This is the *only* obligation on the user, the
    locally nameless discipline's own rule, "do not redeclare a free name the context already has",
    read so that a view counts what it exposes (under `□`, a declared `n : □A` is still in scope as
    `n.box`).  It says nothing about bound variables: slots are never declared in a presented
    context (`Ctx.NoSlots`), so every address it quantifies over is rooted at a name the user chose.

    `Ctx.insert` is a function update, so without this a presentation may redeclare a name that a
    view has already made visible below it, and then no address map can serve both (§2d,
    `Ctx.ViewClean`).  It is therefore a field of `Ctx.Presented`: the metatheorems get
    `Ctx.LevelFlat` from the instance (`Ctx.Presented.levelFlat`) instead of asking for it.
    `CtxExpr.fresh_of_bound` turns the decidable arithmetic criterion `e.freeBound ≤ u` into the
    freshness this asks for, which is how the instances discharge it. -/
def Fresh : CtxExpr → Prop
  | .empty => True
  | .insertFree e u _ => e.Fresh ∧ e.denote.RootFresh (.free u)
  | .boxIn e => e.Fresh
  | .diaIn e _ => e.Fresh

/-- Views are taken at declared witnesses: a `◇_x` view needs `x` declared at a `◇`-type.  Not a
    freshness condition — it is the side condition of the `◇`-rule itself — and needed only where a
    presentation is taken apart constructor by constructor (`BArrow.CtxExpr.chain`). -/
def Views : CtxExpr → Prop
  | .empty => True
  | .insertFree e _ _ => e.Views
  | .boxIn e => e.Views
  | .diaIn e x => e.Views ∧ ∃ X, e.denote.ref x = some (.VTypeDia X)

/-- A presentation built the way the proof rules build one: non-shadowing, views at witnesses. -/
def Wf (e : CtxExpr) : Prop := e.Fresh ∧ e.Views

end CtxExpr

/-- ⭐A presentation of the context, declaring no name already in scope: found by instance search. -/
class Ctx.Presented (Γ : Ctx) where
  expr : CtxExpr
  fresh : expr.Fresh
  denote_eq : expr.denote = Γ

namespace Ctx.Presented

/-- The first free variable guaranteed unused. -/
def bound (Γ : Ctx) [h : Γ.Presented] : ℕ := h.expr.freeBound

theorem fresh_bound {Γ : Ctx} [h : Γ.Presented] (n : ℕ) (hn : bound Γ ≤ n) :
    Γ.RootFresh (.free n) :=
  h.denote_eq ▸ h.expr.fresh_of_bound n hn

/-- Declaring a fresh free variable presents the extension.  Not an instance: the rule's own
    freshness side condition has to come from somewhere. -/
def insertFree {Γ : Ctx} (h : Γ.Presented) (u : ℕ) (hu : Γ.RootFresh (.free u)) (T : VarType) :
    (Γ.insert (.free u) T).Presented where
  expr := .insertFree h.expr u T
  fresh := ⟨h.fresh, by rw [h.denote_eq]; exact hu⟩
  denote_eq := congrArg (fun Δ => Ctx.insert Δ (.free u) T) h.denote_eq

end Ctx.Presented

instance : Ctx.empty.Presented := ⟨.empty, trivial, rfl⟩

/-- Declaring the first name the presentation guarantees unused: the eigenvariable of the rules. -/
instance {Γ : Ctx} [h : Γ.Presented] {T : VarType} :
    (Γ.insert (.free (Ctx.Presented.bound Γ)) T).Presented :=
  h.insertFree _ (Ctx.Presented.fresh_bound _ le_rfl) T

instance {Γ : Ctx} [h : Γ.Presented] : Γ.boxIn.Presented :=
  ⟨.boxIn h.expr, h.fresh, congrArg Ctx.boxIn h.denote_eq⟩

instance {Γ : Ctx} [h : Γ.Presented] {x : VarSymb} : (Γ.diaIn x).Presented :=
  ⟨.diaIn h.expr x, h.fresh, congrArg (fun Δ => Ctx.diaIn Δ x) h.denote_eq⟩

instance (priority := low) {Γ : Ctx} [h : Γ.Presented] : Γ.NoSlots :=
  ⟨h.denote_eq ▸ h.expr.slots⟩

/-! ## Contexts from finite declaration lists -/

theorem CtxExpr.denote_ofDecls : ∀ ds, (CtxExpr.ofDecls ds).denote = Ctx.ofDecls ds
  | [] => rfl
  | (u, T) :: ds => congrArg (fun Δ => Ctx.insert Δ (.free u) T) (denote_ofDecls ds)

omit [ModalSys] in
/-- A name none of the declarations uses is fresh for the context they build. -/
theorem Ctx.ofDecls_rootFresh : ∀ (ds : List (ℕ × VarType)) {u : ℕ}, (∀ p ∈ ds, p.1 ≠ u) →
    (Ctx.ofDecls ds).RootFresh (.free u)
  | [], _, _ => Ctx.RootFresh.empty _
  | (v, T) :: ds, _, h =>
      (Ctx.ofDecls_rootFresh ds (fun p hp => h p (List.mem_cons_of_mem _ hp))).insert_ne
        (fun he => h (v, T) List.mem_cons_self (Root.free.inj he)) T

/-- ⭐Declarations with distinct names present their context: the decidable form of the user's
    obligation. -/
theorem CtxExpr.fresh_ofDecls : ∀ (ds : List (ℕ × VarType)), (ds.map Prod.fst).Nodup →
    (CtxExpr.ofDecls ds).Fresh
  | [], _ => trivial
  | (u, T) :: ds, h => by
      rw [List.map_cons, List.nodup_cons] at h
      refine ⟨fresh_ofDecls ds h.2, ?_⟩
      rw [show (CtxExpr.ofDecls ds).denote = Ctx.ofDecls ds from denote_ofDecls ds]
      exact Ctx.ofDecls_rootFresh ds
        (fun p hp he => h.1 (List.mem_map.mpr (Exists.intro p (And.intro hp he))))

/-- A context written as a list of declarations with distinct names. -/
def Ctx.presentedOfDecls (ds : List (ℕ × VarType)) (hnd : (ds.map Prod.fst).Nodup) :
    (Ctx.ofDecls ds).Presented :=
  ⟨CtxExpr.ofDecls ds, CtxExpr.fresh_ofDecls ds hnd, CtxExpr.denote_ofDecls ds⟩

/-! ## Checks -/

example : (Ctx.ofDecls [(3, .Var), (0, .VTypeBox .Var)]).boxIn.NoSlots :=
  letI := Ctx.presentedOfDecls [(3, .Var), (0, .VTypeBox .Var)] (by decide)
  inferInstance

example :
    letI := Ctx.presentedOfDecls [(3, .Var), (0, .VTypeBox .Var)] (by decide)
    Ctx.Presented.bound ((Ctx.ofDecls [(3, .Var), (0, .VTypeBox .Var)]).boxIn) = 4 := rfl

end V12M
