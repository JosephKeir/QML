import QML.QML_v12m_SemBack
import QML.QML_v12m_SemStrongT

/-!
# QML v12m — semantics of strong B with witnessed ways home

`Model.posBack_exists` (rows 3–4, `docs/v12-modal-extensions.md` §11.23): along any arrow, some
possible object at its source has the arrow in its extent, with any given content at its target.
At a returning possibility's way home it is the rule of rows 3–4; at its arrow out it would name
the route, which is derivable (`Proof.ret_route_node`).

* ⭐`sat_ret_realise`: at a returning possibility's way home, a possible part with any content
  here (`Proof.ret_realise`, B's unit `A → □◇A` per arrow).
* `sat_ret_unrealise`, `sat_retx_forget`: the converses the canonical model's truth lemma reads
  rows 3–4 with — a realised part dropped, and a named route forgotten.
-/

namespace V12M

variable [ModalSys]

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

/-- ⭐**Realising along the way home** is sound: the way home of the premise's arrow lies in the
    extent of some possible object at the far end, with the given content
    (`Model.posBack_exists`), and the necessary part's return is unchanged. -/
theorem sat_ret_realise {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W} (env : M.Env Γ w)
    (hS : ModalSys.BStrong = true) (hW : ModalSys.BStrongW = true) (O : OutLeg Γ) (N : NShape)
    {X : VarType} {a : Ann N.flat} (y : Term σ Γ N.flat a) {c₀ : Ann X} (c : Term σ Γ X c₀)
    (Φ : WFF σ (O.view.insert (.bnd 0) N.ty) 1) (h : M.sat env (O.retS hS (.nec N) y Φ)) :
    M.sat env (O.retS hS (.wit N X) (Term.pair y c)
      (WFF.bodyRepl (RShape.realL O.view N X).2 Φ)) := by
  obtain ⟨i, d, hΦ, r, hr⟩ := (OutLeg.sat_retS hS env O (.nec N) y Φ).mp h
  obtain ⟨p, hm, hI⟩ := M.posBack_exists hS hW r (interp env c)
  refine (OutLeg.sat_retS hS env O (.wit N X) _ _).mpr
    ⟨i, ((d, p) : M.frame.Dom (RShape.wit N X).ty (O.acc env i).1), ?_, r, ?_⟩
  · rw [sat_bodyRepl O.noProjLast]
    dsimp only [RShape.realL]
    rw [interp_eta_slot_fst (A := N.ty) (B := .VTypeDia X)]
    exact hΦ
  · change M.NComesBack N d r (interp env y) ∧ _
    exact ⟨hr, hm, hI⟩

/-- **Dropping a realised part**: `◇_O[⟨d, e⟩ ↦ ⟨y, c⟩] Φ(d)` gives `◇_O[d ↦ y] Φ(d)`, the
    converse of `sat_ret_realise`. -/
theorem sat_ret_unrealise {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W} (env : M.Env Γ w)
    (hS : ModalSys.BStrong = true) (O : OutLeg Γ) (N : NShape) {X : VarType}
    {a : Ann N.flat} (y : Term σ Γ N.flat a) {c₀ : Ann X} (c : Term σ Γ X c₀)
    (Φ : WFF σ (O.view.insert (.bnd 0) N.ty) 1)
    (h : M.sat env (O.retS hS (.wit N X) (Term.pair y c)
      (WFF.bodyRepl (RShape.realL O.view N X).2 Φ))) :
    M.sat env (O.retS hS (.nec N) y Φ) := by
  obtain ⟨i, ⟨d, p⟩, hΦ, r, hr⟩ := (OutLeg.sat_retS hS env O (.wit N X) _ _).mp h
  refine (OutLeg.sat_retS hS env O (.nec N) y Φ).mpr ⟨i, d, ?_, r, hr.1⟩
  rw [sat_bodyRepl O.noProjLast] at hΦ
  dsimp only [RShape.realL] at hΦ
  rw [interp_eta_slot_fst (A := N.ty) (B := .VTypeDia X)] at hΦ
  exact hΦ

/-- **Forgetting a named route**: a returning possibility along `κ` whose body is read from the
    `□` view is one along `□` (`Env.diaPush_boxIn`). -/
theorem sat_retx_forget {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w)
    (hS : ModalSys.BStrong = true) {κ : VarSymb} (hκ : ∃ X, Γ.ref κ = some (.VTypeDia X))
    (S : RShape) {a : Ann S.flat} (t : Term σ Γ S.flat a)
    (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) S.ty) 1)
    (h : M.sat env (WFF.retxS hS κ hκ S t
      (WFF.mono ((Ctx.le_boxIn_diaIn Γ κ).insert (.bnd 0) S.ty) Φ))) :
    M.sat env (WFF.retS hS S t Φ) := by
  obtain ⟨Y, hY, a', e, hΦ, r, hr⟩ := h
  exact ⟨a'.1, e, (sat_mono (Env.extend_agree (Env.diaPush_boxIn env hY a') (.bnd 0) e) Φ).mp hΦ,
    r, hr⟩

end Model

end V12M
