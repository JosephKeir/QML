import QML.QML_v12m_ViewFresh
import Mathlib.Data.Set.Finite.List

/-!
# QML v12m — finite contexts

`Ctx.Fin Γ`: `Γ` declares finitely many addresses.  This is the precondition of
`Model.IndInvariant` (docs §10.38).  In the canonical model an environment over a finite context
can be named address by address at one stage, which is what lets the truth lemma speak about it.
Over an infinite context there may be no common stage.

* Every presented context is finite (`Ctx.Presented.fin`), so nothing usable in a proof is lost.
* Finiteness passes to weakenings (`Ctx.Fin.mono`, needed for `Proof.weak_ctx`, whose premise
  lives in the smaller context), to insertions and to both views.  So soundness can carry it
  through its induction.
* `Ctx.Fin.reach`: a finite context reaches finitely many addresses.  Projections only descend
  into the type, so every reachable address is a declared one followed by a bounded path.
-/

namespace V12M

instance : Finite Step :=
  Finite.of_injective (fun s : Step => (match s with
      | .fst => 0 | .snd => 1 | .box => 2 | .dia => 3 | .here => 4 | .keep => 5 : Fin 6))
    (fun a b h => by cases a <;> cases b <;> first | rfl | exact absurd h (by decide))

/-- The number of constructors of a type. -/
def VarType.sz : VarType → ℕ
  | .Var => 1
  | .VTypeOne => 1
  | .VTypeProd A B => A.sz + B.sz + 1
  | .VTypeBox A => A.sz + 1
  | .VTypeDia A => A.sz + 1

theorem VarSymb.step_ext (v : VarSymb) (s : Step) :
    ∀ p : List Step, (v.ext p).step s = v.ext (p ++ [s]) := by
  intro p
  induction p generalizing v with
  | nil => rfl
  | cons t p ih => exact ih (.step v t)

variable [ModalSys]

/-- A projection step goes to a smaller type. -/
theorem VarType.sz_step {U T : VarType} {s : Step} (h : U.step s = some T) : T.sz < U.sz := by
  cases U <;> cases s <;> simp only [VarType.step, reduceCtorEq, Option.some.injEq] at h
  · subst h; simp only [VarType.sz]; omega
  · subst h; simp only [VarType.sz]; omega
  · subst h; simp only [VarType.sz]; omega
  · rename_i A
    obtain ⟨-, rfl⟩ := VarType.step_here (A := A) (T := T) (by simpa [VarType.step] using h)
    simp only [VarType.sz]; omega
  · subst h; simp only [VarType.sz]; omega

namespace Ctx

/-- ⭐`Γ` declares finitely many addresses. -/
def Fin (Γ : Ctx) : Prop := {v | (Γ v).isSome}.Finite

omit [ModalSys] in
theorem Fin.mono {Γ Γ' : Ctx} (h : Γ.Le Γ') (h' : Γ'.Fin) : Γ.Fin := by
  refine h'.subset fun v hv => ?_
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp hv
  change (Γ' v).isSome
  rw [h v T hT]
  rfl

omit [ModalSys] in
theorem Fin.insert {Γ : Ctx} (h : Γ.Fin) (r : Root) (T : VarType) : (Γ.insert r T).Fin := by
  refine (Set.Finite.insert (VarSymb.root r) h).subset fun v hv => ?_
  change (if v = .root r then some T else Γ v).isSome at hv
  by_cases hvr : v = .root r
  · exact Or.inl hvr
  · rw [if_neg hvr] at hv
    exact Or.inr hv

/-- Every reachable address is a declared one followed by projections, no more of them than the
    declared type has room for. -/
theorem ref_decomp (Γ : Ctx) : ∀ (v : VarSymb) {T : VarType}, Γ.ref v = some T →
    ∃ (d : VarSymb) (U : VarType), Γ d = some U ∧ ∃ π : List Step, v = d.ext π ∧
      π.length + T.sz ≤ U.sz
  | .root r, T, h => ⟨.root r, T, h, [], rfl, by simp⟩
  | .step v s, T, h => by
      by_cases hs : s.isProj = true
      · change (if s.isProj then (Γ.ref v).bind (·.step s) else Γ (.step v s)) = some T at h
        rw [if_pos hs] at h
        cases hv : Γ.ref v with
        | none => rw [hv] at h; cases h
        | some U' =>
            rw [hv] at h
            obtain ⟨d, U, hd, π, rfl, hle⟩ := ref_decomp Γ v hv
            have hlt := VarType.sz_step (s := s) h
            refine ⟨d, U, hd, π ++ [s], VarSymb.step_ext d s π, ?_⟩
            simp only [List.length_append, List.length_singleton]
            omega
      · change (if s.isProj then (Γ.ref v).bind (·.step s) else Γ (.step v s)) = some T at h
        rw [if_neg hs] at h
        exact ⟨.step v s, T, h, [], rfl, by simp⟩

/-- ⭐A finite context reaches finitely many addresses. -/
theorem Fin.reach {Γ : Ctx} (h : Γ.Fin) : {v | (Γ.ref v).isSome}.Finite := by
  refine (h.biUnion fun d _ =>
    ((List.finite_length_le Step (((Γ d).map VarType.sz).getD 0)).image d.ext)).subset ?_
  intro v hv
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp hv
  obtain ⟨d, U, hd, π, rfl, hle⟩ := ref_decomp Γ v hT
  refine Set.mem_biUnion (x := d) (by change (Γ d).isSome; rw [hd]; rfl) ⟨π, ?_, rfl⟩
  change π.length ≤ ((Γ d).map VarType.sz).getD 0
  rw [hd]
  simp only [Option.map_some, Option.getD_some]
  omega

theorem Fin.boxIn {Γ : Ctx} (h : Γ.Fin) : Γ.boxIn.Fin := by
  refine ((h.reach.image fun u => VarSymb.step u .box).union
    (h.reach.image fun u => VarSymb.step u .keep)).subset ?_
  intro v hv
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp hv
  match v, hT with
  | .step u .box, hT =>
      obtain ⟨-, hu⟩ := Ctx.boxIn_box hT
      exact Or.inl ⟨u, by change (Γ.ref u).isSome; rw [hu]; rfl, rfl⟩
  | .step u .keep, hT =>
      obtain ⟨-, hu, -⟩ := Ctx.boxIn_keep hT
      exact Or.inr ⟨u, by change (Γ.ref u).isSome; rw [hu]; rfl, rfl⟩
  | .root _, hT => cases hT
  | .step _ .fst, hT => cases hT
  | .step _ .snd, hT => cases hT
  | .step _ .dia, hT => cases hT
  | .step _ .here, hT => cases hT

theorem Fin.diaIn {Γ : Ctx} (h : Γ.Fin) (x : VarSymb) : (Γ.diaIn x).Fin := by
  refine (Set.Finite.insert (VarSymb.step x .dia) h.boxIn).subset ?_
  intro v hv
  by_cases hvx : v = .step x .dia
  · exact Or.inl hvx
  · right
    match v, hvx, hv with
    | .step u .dia, hvx, hv =>
        change (if u = x then _ else none).isSome at hv
        rw [if_neg (fun h => hvx (by rw [h]))] at hv
        cases hv
    | .step _ .box, _, hv => exact hv
    | .step _ .keep, _, hv => exact hv
    | .root _, _, hv => exact hv
    | .step _ .fst, _, hv => exact hv
    | .step _ .snd, _, hv => exact hv
    | .step _ .here, _, hv => exact hv

omit [ModalSys] in
theorem Fin.empty : Ctx.empty.Fin := by
  refine Set.finite_empty.subset fun v hv => ?_
  cases hv

end Ctx

theorem CtxExpr.fin : ∀ e : CtxExpr, e.denote.Fin
  | .empty => Ctx.Fin.empty
  | .insertFree e u T => (CtxExpr.fin e).insert (.free u) T
  | .boxIn e => (CtxExpr.fin e).boxIn
  | .diaIn e x => (CtxExpr.fin e).diaIn x

/-- ⭐Every presented context is finite. -/
theorem Ctx.Presented.fin (Γ : Ctx) [h : Γ.Presented] : Γ.Fin :=
  h.denote_eq ▸ CtxExpr.fin h.expr

/-! ## Tame contexts -/

namespace Ctx

/-- ⭐A context a proof can live in, as models proper see it: finitely many declared addresses, and
    every address at one view depth (`Ctx.LevelDepth`).  Every presented context is tame
    (`Ctx.Presented.tame`), and tameness passes to weakenings, fresh insertions and both views.
    Finiteness lets the canonical model name an environment at one stage; one view depth makes the
    naming coherent (no declared address extends another). -/
def Tame (Γ : Ctx) : Prop := Γ.Fin ∧ ∃ d, Γ.LevelDepth d

theorem Tame.mono {Γ Γ' : Ctx} (h : Γ.Le Γ') (h' : Γ'.Tame) : Γ.Tame :=
  ⟨h'.1.mono h, h'.2.imp fun _ hd v T hv => hd v T (h.ref hv)⟩

theorem Tame.insert {Γ : Ctx} (h : Γ.Tame) {r : Root} (hr : Γ.RootFresh r) (T : VarType) :
    (Γ.insert r T).Tame :=
  ⟨h.1.insert r T, h.2.elim fun _ hd => ⟨_, Ctx.levelDepth_insert hd hr T⟩⟩

theorem Tame.boxIn {Γ : Ctx} (h : Γ.Tame) : Γ.boxIn.Tame :=
  ⟨h.1.boxIn, h.2.elim fun _ hd => ⟨_, Ctx.levelDepth_boxIn hd⟩⟩

theorem Tame.diaIn {Γ : Ctx} (h : Γ.Tame) (x : VarSymb) : (Γ.diaIn x).Tame :=
  ⟨h.1.diaIn x, h.2.elim fun _ hd => ⟨_, Ctx.levelDepth_diaIn hd x⟩⟩

end Ctx

/-- ⭐Every presented context is tame. -/
theorem Ctx.Presented.tame (Γ : Ctx) [h : Γ.Presented] : Γ.Tame :=
  ⟨Ctx.Presented.fin Γ, h.denote_eq ▸ h.expr.levelDepth h.fresh⟩

end V12M
