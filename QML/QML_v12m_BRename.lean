import QML.QML_v12m_BCompleteness

/-!
# QML v12m — renaming the declared roots of a context

`completenessB` states a world's language as `ctxOf l`, whose roots are named by position.  A
context the user writes declares roots by whatever names they chose (`Ctx.ofDecls`).  The two are
the same context up to a **renaming of roots**, and this file transports provability and validity
along one.

* `RootOnly Γ`: `Γ` declares only free roots — true of every `Ctx.ofDecls`, so of `ctxOf l`.
* Such a context's reachable addresses are a root followed by projections
  (`ppath_of_rootOnly`), so rerooting preserves reachability (`ref_reroot`).
* ⭐`renS`: the substitution renaming roots by `ν`, with `ok_renS`, `coh_renS`, and the round trip
  `subst_renS_renS` when `ν'` inverts `ν` on the declared roots.
* ⭐`completenessB_rename`: completeness for any root-only context that a renaming carries onto
  some `ctxOf l`.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## Contexts of declared roots -/

/-- A context declaring only free roots: every `Ctx.ofDecls`, hence every `ctxOf l`. -/
def RootOnly (Γ : Ctx) : Prop :=
  ∀ {v : VarSymb} {T : VarType}, Γ v = some T → ∃ r, v = .root (.free r)

omit [ModalSys] in
theorem rootOnly_ofDecls (ds : List (ℕ × VarType)) : RootOnly (Ctx.ofDecls ds) := by
  intro v T h
  induction ds with
  | nil => simp [Ctx.ofDecls, Ctx.empty] at h
  | cons d ds ih =>
      obtain ⟨u, U⟩ := d
      simp only [Ctx.ofDecls, Ctx.insert] at h
      split_ifs at h with hv
      · exact ⟨u, hv⟩
      · exact ih h

omit [ModalSys] in
theorem rootOnly_ctxOf (l : List VarType) : RootOnly (ctxOf l) := rootOnly_ofDecls _

variable [ModalSys.NoTFour]

/-- In a context of declared roots, without T and 4, a reachable address is a root followed by
    projections. -/
theorem ppath_of_rootOnly {Γ : Ctx} (hΓ : RootOnly Γ) :
    ∀ {v : VarSymb} {T : VarType}, Γ.ref v = some T → PPath v.path ∧ ∃ r, v.rt = .free r
  | .root _, _, h => by
      obtain ⟨r', hr'⟩ := hΓ h
      cases hr'
      exact ⟨(fun _ hs => nomatch hs), _, rfl⟩
  | .step v s, _, h => by
      simp only [Ctx.ref] at h
      split_ifs at h with hs
      · cases hU : Γ.ref v with
        | none => rw [hU] at h; cases h
        | some U =>
            obtain ⟨hp, hr⟩ := ppath_of_rootOnly hΓ hU
            refine ⟨?_, hr⟩
            change PPath (v.path ++ [s])
            refine hp.append fun s' hs' => ?_
            rw [List.mem_singleton.mp hs']
            rw [hU] at h
            cases s with
            | fst => exact Or.inl rfl
            | snd => exact Or.inr rfl
            | here => cases U <;> simp [VarType.step, ModalSys.NoTFour.noT] at h
            | box => cases hs
            | dia => cases hs
            | keep => cases hs
      · obtain ⟨r, hr⟩ := hΓ h
        cases hr

/-- Rerooting a reachable address at a root of the same type keeps it reachable, at its type. -/
theorem ref_reroot {Γ Δ : Ctx} (hΓ : RootOnly Γ) {z : Root} {R : VarType} :
    ∀ {u : VarSymb} {T : VarType}, Γ.ref u = some T → Γ.ref (.root u.rt) = some R →
      Δ.ref (.root z) = some R → Δ.ref (u.reroot z) = some T
  | .root r, T, h, hR, hz => by
      change Γ.ref (.root r) = some R at hR
      rw [hR] at h
      cases h
      exact hz
  | .step u s, T, h, hR, hz => by
      have hp := (ppath_of_rootOnly hΓ h).1
      have hs : s = .fst ∨ s = .snd := hp s (by simp [VarSymb.path])
      have hproj : s.isProj = true := by rcases hs with rfl | rfl <;> rfl
      simp only [Ctx.ref, if_pos hproj] at h
      cases hU : Γ.ref u with
      | none => rw [hU] at h; cases h
      | some U =>
          rw [hU] at h
          have ih := ref_reroot hΓ hU hR hz
          change Δ.ref (.step (u.reroot z) s) = _
          simp only [Ctx.ref, if_pos hproj, ih, Option.bind_some]
          exact h

/-! ## The renaming -/

/-- ⭐The substitution renaming each root `free r` to `free (ν r)`. -/
def renS (σ : Signature) (Δ : Ctx) (ν : ℕ → ℕ) : Subst σ Δ :=
  fun v => .ren (v.reroot (imgRoot ν v.rt))

/-- Where it sends annotation indices. -/
def renIdx (ν : ℕ → ℕ) (a : VarSymb) : VarSymb := a.reroot (imgRoot ν a.rt)

omit [ModalSys.NoTFour] in
/-- The renaming lands in `Δ` when `Δ` declares every image. -/
theorem ok_renS {Γ Δ : Ctx} (hΓ : RootOnly Γ) {ν : ℕ → ℕ}
    (hν : ∀ r R, Γ (.root (.free r)) = some R → Δ (.root (.free (ν r))) = some R) :
    Subst.Ok Γ (renS σ Δ ν) := by
  intro v T _ hv
  obtain ⟨r, rfl⟩ := hΓ hv
  change Δ.ref (.root (.free (ν r))) = some T
  exact hν r T hv

omit [ModalSys.NoTFour] in
theorem coh_renS {Γ Δ : Ctx} (hΓ : RootOnly Γ) {ν : ℕ → ℕ}
    (hν : ∀ r R, Γ (.root (.free r)) = some R → Δ (.root (.free (ν r))) = some R) :
    Subst.Coh (renIdx ν) Γ (renS σ Δ ν) := by
  refine Subst.coh_of (ok_renS hΓ hν) ?_
  intro v T _ hv p
  obtain ⟨r, rfl⟩ := hΓ hv
  change (VarSymb.root (.free (ν r))).ext p = renIdx ν _
  rw [renIdx, VarSymb.ext_rt, VarSymb.reroot_eq, VarSymb.ext_path]
  rfl


omit [ModalSys.NoTFour] in
/-- ⭐A renaming and the inverse renaming cancel on formulas of the source. -/
theorem subst_renS_renS {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots] (hΓ : RootOnly Γ) (hΔ : RootOnly Δ)
    {ν ν' : ℕ → ℕ}
    (hν : ∀ r R, Γ (.root (.free r)) = some R → Δ (.root (.free (ν r))) = some R)
    (hν' : ∀ r R, Δ (.root (.free r)) = some R → Γ (.root (.free (ν' r))) = some R)
    (hinv : ∀ r R, Γ (.root (.free r)) = some R → ν' (ν r) = r) (φ : WFF σ Γ 0) :
    WFF.subst (renIdx ν') (renS σ Γ ν') (ok_renS hΔ hν') (coh_renS hΔ hν')
        Ctx.NoSlots.slots Ctx.NoSlots.slots
      (WFF.subst (renIdx ν) (renS σ Δ ν) (ok_renS hΓ hν) (coh_renS hΓ hν)
        Ctx.NoSlots.slots Ctx.NoSlots.slots φ) = φ := by
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ Subst.ok_idS Subst.coh_idS _ _ _ ?_ φ).trans
    (WFF.subst_id _ _ _ φ)
  refine Subst.sim_of ?_
  intro v T _ hv
  obtain ⟨r, rfl⟩ := hΓ hv
  change SubE.Sim T (.ren (.root (.free r))) (.ren (.root (.free (ν' (ν r)))))
  rw [hinv r T hv]
  exact .refl _

/-! ## Completeness along a renaming -/

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- ⭐**Completeness for weak B in any context of declared roots** that a renaming carries onto a
    world language `ctxOf l`. -/
theorem completenessB_rename (hB : ModalSys.B = true) {Γ : Ctx} [Γ.Presented] (hΓ : RootOnly Γ)
    {l : List VarType} {ν ν' : ℕ → ℕ}
    (hν : ∀ r R, Γ (.root (.free r)) = some R → ctxOf l (.root (.free (ν r))) = some R)
    (hν' : ∀ r R, ctxOf l (.root (.free r)) = some R → Γ (.root (.free (ν' r))) = some R)
    (hinv : ∀ r R, Γ (.root (.free r)) = some R → ν' (ν r) = r)
    {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0}
    (hval : ∀ (M : Model.{0, 0} σ) {w : M.frame.W} (env : M.Env Γ w), Γ.NoProjLast →
      (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ := by
  set tr : WFF σ Γ 0 → WFF σ (ctxOf l) 0 :=
    WFF.subst (renIdx ν) (renS σ (ctxOf l) ν) (ok_renS hΓ hν) (coh_renS hΓ hν)
      Ctx.NoSlots.slots Ctx.NoSlots.slots with htr
  set tr' : WFF σ (ctxOf l) 0 → WFF σ Γ 0 :=
    WFF.subst (renIdx ν') (renS σ Γ ν') (ok_renS (rootOnly_ctxOf l) hν')
      (coh_renS (rootOnly_ctxOf l) hν') Ctx.NoSlots.slots Ctx.NoSlots.slots with htr'
  have hcancel : ∀ ψ : WFF σ Γ 0, tr' (tr ψ) = ψ := fun ψ =>
    subst_renS_renS hΓ (rootOnly_ctxOf l) hν hν' hinv ψ
  have hvalid : ∀ (M : Model.{0, 0} σ) {w : M.frame.W} (env : M.Env (ctxOf l) w),
      (ctxOf l).NoProjLast → (∀ χ ∈ Δ.map tr, M.sat env χ) → M.sat env (tr φ) := by
    intro M w env _ hΔ
    rw [htr, Model.sat_subst _ _ _ _ _ (Ctx.Presented.noProjLast Γ)]
    refine hval M _ (Ctx.Presented.noProjLast Γ) fun ψ hψ => ?_
    have hs := hΔ (tr ψ) (List.mem_map_of_mem hψ)
    rwa [htr, Model.sat_subst _ _ _ _ _ (Ctx.Presented.noProjLast Γ)] at hs
  obtain ⟨p⟩ := completenessB hB hvalid
  have hq := Proof.subst p (renS σ Γ ν') (ok_renS (rootOnly_ctxOf l) hν')
    (coh_renS (rootOnly_ctxOf l) hν') Ctx.NoSlots.slots
  rw [← htr'] at hq
  have hmap : (Δ.map tr).map tr' = Δ := by
    rw [List.map_map]
    simp only [Function.comp_def, hcancel]
    exact List.map_id _
  rw [hmap, hcancel φ] at hq
  exact ⟨hq⟩


/-! ## A worked example

How a user-written context meets `completenessB`: two variables named `7` and `3` become the world
language's positional `free 1` and `free 0`. -/

namespace RenameExample

/-- A user-written context. -/
abbrev Γ₀ : Ctx := Ctx.ofDecls [(7, VarType.Var), (3, VarType.VTypeOne)]

/-- The matching world language: `free 1 : Var`, `free 0 : 𝟙`. -/
abbrev l₀ : List VarType := [VarType.Var, VarType.VTypeOne]

def ν₀ : ℕ → ℕ := fun r => if r = 7 then 1 else 0
def ν₀' : ℕ → ℕ := fun r => if r = 1 then 7 else 3

omit [ModalSys] [ModalSys.NoTFour] [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem hν₀ : ∀ r R, Γ₀ (.root (.free r)) = some R →
    ctxOf l₀ (.root (.free (ν₀ r))) = some R := by
  intro r R h
  simp only [Ctx.ofDecls, Ctx.insert, VarSymb.root.injEq, Root.free.injEq] at h
  split_ifs at h with h7 h3
  · cases h; subst h7; rfl
  · cases h; subst h3; rfl
  · simp [Ctx.empty] at h

omit [ModalSys] [ModalSys.NoTFour] [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem hν₀' : ∀ r R, ctxOf l₀ (.root (.free r)) = some R →
    Γ₀ (.root (.free (ν₀' r))) = some R := by
  intro r R h
  simp only [ctxOf, decls, Ctx.ofDecls, Ctx.insert, VarSymb.root.injEq, Root.free.injEq] at h
  split_ifs at h with h1 h0
  · cases h; subst h1; rfl
  · cases h; subst h0; rfl
  · simp [Ctx.empty] at h

omit [ModalSys] [ModalSys.NoTFour] [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem hinv₀ : ∀ r R, Γ₀ (.root (.free r)) = some R → ν₀' (ν₀ r) = r := by
  intro r R h
  simp only [Ctx.ofDecls, Ctx.insert, VarSymb.root.injEq, Root.free.injEq] at h
  split_ifs at h with h7 h3
  · subst h7; rfl
  · subst h3; rfl
  · simp [Ctx.empty] at h

/-- ⭐Completeness in the user's own context, names and all. -/
theorem completeness_Γ₀ (hB : ModalSys.B = true) {Δ : List (WFF σ Γ₀ 0)} {φ : WFF σ Γ₀ 0}
    (hval : ∀ (M : Model.{0, 0} σ) {w : M.frame.W} (env : M.Env Γ₀ w), Γ₀.NoProjLast →
      (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ :=
  completenessB_rename hB (rootOnly_ofDecls _) hν₀ hν₀' hinv₀ hval

end RenameExample

end BArrow

end V12M
