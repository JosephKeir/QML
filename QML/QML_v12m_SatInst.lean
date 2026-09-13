import QML.QML_v12m_SatSubst

/-!
# QML v12m — semantics of the substitutions the proof rules use

* `sat_substRoot` / `sat_instantiate`: substituting a term for a root is extending the environment
  by the term's value.
* `sat_renameRoot`: renaming a root to an address of a larger context is extending the restricted
  environment by that address's value.
* `sat_bindFree`: binding a free variable to a slot swaps which root carries the object.
* `sat_weaken`, `sat_weaken_restrict`: weakening changes nothing.
-/

namespace V12M

variable [ModalSys]

omit [ModalSys] in
theorem Ctx.NoProjLast.of_insert {Γ : Ctx} {r : Root} {T : VarType}
    (h : (Γ.insert r T).NoProjLast) (hr : Γ (.root r) = none) : Γ.NoProjLast :=
  fun v U hv => h v U (Ctx.le_insert hr T v U hv)

namespace Model

variable {σ : Signature} {M : Model.{u} σ}

/-- An environment restricted to a smaller context. -/
def Env.restrict {Γ Γ' : Ctx} (h : Γ.Le Γ') {w : M.frame.W} (env : M.Env Γ' w) : M.Env Γ w :=
  fun v T hv => env v T (h v T hv)

theorem Env.agree_restrict {Γ Γ' : Ctx} (h : Γ.Le Γ') {w : M.frame.W} (env : M.Env Γ' w) :
    Env.Agree h (env.restrict h) env :=
  fun _ _ _ => rfl

theorem Env.restrict_extend {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {r : Root}
    (h : Γ (.root r) = none) {T : VarType} (o : M.frame.Dom T w) :
    (env.extend r o).restrict (Ctx.le_insert h T) = env := by
  funext v U hv
  exact Env.extend_ne env r o _ (fun he => by subst he; rw [h] at hv; cases hv) hv

/-! ## Substituting a term for a root -/

theorem substEnv_single_tm {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (hnp : Γ.NoProjLast)
    (r : Root) {T : VarType} {a : Ann T} (s : Term σ Γ T a) :
    substEnv (Subst.single r (.tm s)) (Subst.ok_single (Ctx.Le.refl Γ) rfl) (hnp.insert r T) env =
      env.extend r (interp env s) := by
  funext v U hv
  by_cases hvr : v = .root r
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    exact (entryVal_congr env
      (show Subst.single r (.tm s) (.root r) = .tm s from if_pos rfl) _ rfl).trans
      (Env.extend_root env r _ hv).symm
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    exact (entryVal_congr env (show Subst.single r (.tm s) v = .ren v from if_neg hvr) _
      ((Ctx.ref_nonproj Γ (hnp v U hv')).trans hv')).trans
      ((Env.ref_of_nonproj env (hnp v U hv') _ hv').trans (Env.extend_ne env r _ hv hvr hv').symm)

/-- ⭐Substituting a term for a root. -/
theorem sat_substRoot {Γ : Ctx} {d d' : ℕ} {w : M.frame.W} (env : M.Env Γ w)
    (hnp : Γ.NoProjLast) (r : Root) {T : VarType} (hr : Γ.RootFresh r) (hs : Γ.SlotsFrom d)
    (hs' : (Γ.insert r T).SlotsFrom d') {a : Ann T} (s : Term σ Γ T a)
    (φ : WFF σ (Γ.insert r T) d') :
    M.sat env (WFF.substRoot r hr hs hs' s φ) ↔ M.sat (env.extend r (interp env s)) φ :=
  (sat_subst (Subst.single r (.tm s)) (Subst.ok_single (Ctx.Le.refl Γ) rfl)
    (Subst.coh_single hr (Ctx.Le.refl Γ) rfl) hs' hs (hnp.insert r T) env φ).trans
    (iff_of_eq (congrArg (fun e => M.sat e φ) (substEnv_single_tm env hnp r s)))

/-- ⭐Instantiating the slot. -/
theorem sat_instantiate {Γ : Ctx} {d : ℕ} {w : M.frame.W} (env : M.Env Γ w)
    (hnp : Γ.NoProjLast) (hs : Γ.SlotsFrom d) {T : VarType} {a : Ann T} (t : Term σ Γ T a)
    (φ : WFF σ (Γ.insert (.bnd d) T) (d + 1)) :
    M.sat env (WFF.instantiate hs t φ) ↔ M.sat (env.extend (.bnd d) (interp env t)) φ :=
  sat_substRoot env hnp (.bnd d) (hs.rootFresh le_rfl) hs (hs.insert T) t φ

/-! ## Renaming a root -/

theorem substEnv_single_ren {Γ Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) (hnp : Γ.NoProjLast)
    {r : Root} {T : VarType} (hle : Γ.Le Δ) (x : VarSymb) (hx : Δ.ref x = some T) :
    substEnv (Subst.single (σ := σ) r (.ren x)) (Subst.ok_single hle hx) (hnp.insert r T) env =
      (env.restrict hle).extend r (env.ref x hx) := by
  funext v U hv
  by_cases hvr : v = .root r
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    exact (entryVal_congr env
      (show Subst.single (σ := σ) r (.ren x) (.root r) = .ren x from if_pos rfl) _ hx).trans
      (Env.extend_root (env.restrict hle) r _ hv).symm
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    exact (entryVal_congr env
      (show Subst.single (σ := σ) r (.ren x) v = .ren v from if_neg hvr) _
      ((Ctx.ref_nonproj Δ (hnp v U hv')).trans (hle v U hv'))).trans
      ((Env.ref_of_nonproj env (hnp v U hv') _ (hle v U hv')).trans
        (Env.extend_ne (env.restrict hle) r _ hv hvr hv').symm)

/-- ⭐Renaming a root to an address of a larger context. -/
theorem sat_renameRoot {Γ Δ : Ctx} {d d' : ℕ} {w : M.frame.W} (env : M.Env Δ w)
    (hnp : Γ.NoProjLast) (r : Root) {T : VarType} (hr : Γ.RootFresh r) (hle : Γ.Le Δ)
    (x : VarSymb) (hx : Δ.ref x = some T) (hs : (Γ.insert r T).SlotsFrom d)
    (hs' : Δ.SlotsFrom d') (φ : WFF σ (Γ.insert r T) d) :
    M.sat env (WFF.renameRoot r hr hle x hx hs hs' φ) ↔
      M.sat ((env.restrict hle).extend r (env.ref x hx)) φ :=
  (sat_subst (Subst.single r (.ren x)) (Subst.ok_single hle hx) (Subst.coh_single hr hle hx) hs hs'
    (hnp.insert r T) env φ).trans
    (iff_of_eq (congrArg (fun e => M.sat e φ) (substEnv_single_ren env hnp hle x hx)))

/-- ⭐Binding a free variable to the slot. -/
theorem sat_bindFree {Γ : Ctx} {d : ℕ} {w : M.frame.W} (env : M.Env Γ w) (hnp : Γ.NoProjLast)
    (u : ℕ) (hu : Γ.RootFresh (.free u)) (hs : Γ.SlotsFrom d) (T : VarType)
    (o : M.frame.Dom T w) (φ : WFF σ (Γ.insert (.free u) T) d) :
    M.sat (env.extend (.bnd d) o) (WFF.bindFree u hu hs T φ) ↔
      M.sat (env.extend (.free u) o) φ := by
  refine (sat_renameRoot (env.extend (.bnd d) o) hnp (.free u) hu (Ctx.le_insert hs.root T)
    (.root (.bnd d)) (Ctx.ref_insert_root Γ _ T) (hs.insertFree u T) (hs.insert T) φ).trans ?_
  rw [Env.restrict_extend env hs.root o]
  exact iff_of_eq (congrArg (fun o' => M.sat (env.extend (.free u) o') φ)
    (Env.extend_root env (.bnd d) o (Ctx.ref_insert_root Γ _ T)))

/-! ## Weakening -/

theorem sat_weaken {Γ : Ctx} {d : ℕ} {w : M.frame.W} (env : M.Env Γ w) {r : Root}
    (hr : Γ (.root r) = none) {T : VarType} (o : M.frame.Dom T w) (φ : WFF σ Γ d) :
    M.sat (env.extend r o) (WFF.weaken hr T φ) ↔ M.sat env φ :=
  sat_mono (Env.agree_extend env hr o) φ

theorem sat_weaken_restrict {Γ : Ctx} {d : ℕ} {w : M.frame.W} {r : Root}
    (hr : Γ (.root r) = none) {T : VarType} (env : M.Env (Γ.insert r T) w) (φ : WFF σ Γ d) :
    M.sat env (WFF.weaken hr T φ) ↔ M.sat (env.restrict (Ctx.le_insert hr T)) φ :=
  sat_mono (Env.agree_restrict _ env) φ

end Model

end V12M
