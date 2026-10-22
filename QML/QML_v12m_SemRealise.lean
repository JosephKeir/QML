import QML.QML_v12m_SemBack
import QML.QML_v12m_SemStrongT

/-!
# QML v12m — semantics of strong B with witnessed ways home

`Model.posBack_exists` (rows 3–4, `docs/v12-modal-extensions.md` §11.23): along any arrow, some
possible object at its source has the arrow in its extent, with any given content at its target.
Its two readings are the two rules of rows 3–4.

* ⭐`sat_ret_realise`: at a returning possibility's way home, a possible part with any content
  here (`Proof.ret_realise`, B's unit `A → □◇A` per arrow).
* `Env.diaPush_fresh`: pushed into a fresh witness along an arrow of its extent, an environment
  agrees on the `□` part with the one pushed into `□` along the same arrow (`Env.diaPush_ret` at
  any arrow).
* ⭐`sat_ret_route`: at a returning possibility's arrow out, a possible object here naming the
  route (`Proof.ret_route`).
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

/-- Pushed into a fresh witness `c` along an arrow `a` of its extent, an environment agrees on the
    `□` part with the one pushed into `□` along `a`: `Env.diaPush_ret` at any arrow. -/
theorem Env.diaPush_fresh {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {c : ℕ}
    (hc : Γ.RootFresh (.free c)) {A : VarType} (p : M.frame.Dom (.VTypeDia A) w)
    (a : M.frame.Acc w)
    (hr : (Γ.insert (.free c) (.VTypeDia A)).ref (.root (.free c)) = some (.VTypeDia A))
    (hmem : a ∈ (M.posEval ((env.extend (.free c) p).ref (.root (.free c)) hr)).1) :
    Env.Agree ((Ctx.le_insert hc.root (.VTypeDia A)).boxIn.trans
        (Ctx.le_boxIn_diaIn _ (.root (.free c))))
      (env.boxPush a) ((env.extend (.free c) p).diaPush (.root (.free c)) hr ⟨a, hmem⟩) := by
  intro v T hv
  match v with
  | .step u .box =>
      have hu := Ctx.boxIn_step_box hv
      have hu' : (Γ.insert (.free c) (.VTypeDia A)).ref u = some (.VTypeBox T) :=
        (Ctx.ref_insert_ne _ (fun he => by
          rw [Ctx.ref_none_of_rootFresh hc u he] at hu
          cases hu)).trans hu
      change M.necEval (env.ref u hu) a = M.necEval ((env.extend (.free c) p).ref u hu') a
      rw [Env.ref_extend_ne env p hu' hu (fun he => by
        rw [Ctx.ref_none_of_rootFresh hc u he] at hu
        cases hu)]
  | .step u .keep =>
      obtain ⟨hF, hu, B, rfl⟩ := Ctx.boxIn_keep hv
      have hu' : (Γ.insert (.free c) (.VTypeDia A)).ref u = some (.VTypeBox B) :=
        (Ctx.ref_insert_ne _ (fun he => by
          rw [Ctx.ref_none_of_rootFresh hc u he] at hu
          cases hu)).trans hu
      change M.necEval (GFunc.eval M.ops (GFunc.keep (σ := σ) hF ⟨B, rfl⟩) w
          (env.ref u hu)) a =
        M.necEval (GFunc.eval M.ops (GFunc.keep (σ := σ) hF ⟨B, rfl⟩) w
          ((env.extend (.free c) p).ref u hu')) a
      rw [Env.ref_extend_ne env p hu' hu (fun he => by
        rw [Ctx.ref_none_of_rootFresh hc u he] at hu
        cases hu)]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

/-- ⭐**Naming the route** is sound: if the premise's arrow out lies in the extent of a possible
    object here (`Model.posBack_exists` from the far end), that object interprets the fresh root,
    and the returning possibility runs along it, its body read in the root's view
    (`Env.diaPush_fresh`). -/
theorem sat_ret_route {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W} (env : M.Env Γ w)
    (hS : ModalSys.BStrong = true) {S : RShape} {a : Ann S.flat} (t : Term σ Γ S.flat a)
    (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) S.ty) 1) (κ : ℕ) (hκ : Γ.RootFresh (.free κ))
    (p : M.frame.Dom (.VTypeDia .VTypeOne) w) (i : M.frame.Acc w) (hm : i ∈ (M.posEval p).1)
    (e : M.frame.Dom S.ty i.1) (hΦ : M.sat ((env.boxPush i).extend (.bnd 0) e) Φ)
    (r : M.frame.R i.1 w) (hr : M.ComesBack S e r (interp env t)) :
    M.sat (env.extend (.free κ) p)
      (WFF.retxS hS (.root (.free κ)) ⟨.VTypeOne, Ctx.ref_insert_root Γ (.free κ) _⟩ S
        (Term.weaken hκ.root _ t)
        (WFF.mono (((Ctx.le_insert hκ.root _).boxIn.trans
          (Ctx.le_boxIn_diaIn _ (.root (.free κ)))).insert (.bnd 0) S.ty) Φ)) := by
  have hrc := Ctx.ref_insert_root Γ (.free κ) (.VTypeDia .VTypeOne)
  have hpe : (env.extend (.free κ) p).ref (.root (.free κ)) hrc = p :=
    Env.extend_root env (.free κ) p hrc
  have hm' : i ∈ (M.posEval ((env.extend (.free κ) p).ref (.root (.free κ)) hrc)).1 := by
    rw [hpe]
    exact hm
  have hag := Env.diaPush_fresh env hκ p i hrc hm'
  refine ⟨.VTypeOne, hrc, ⟨i, hm'⟩, e, ?_, r, ?_⟩
  · exact (sat_mono (Env.extend_agree hag (.bnd 0) e) Φ).mpr hΦ
  · erw [interp_mono (Env.agree_extend env hκ.root p) t]
    exact hr

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
