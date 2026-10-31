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
* ⭐`sat_ret_keep`: at a returning possibility's way home, a possible object realised here, kept
  (`Proof.ret_keep`, T + 4), by `realised_keep`.
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

/-- ⭐**The way home lies in the kept object's extent**: what is realised here is, kept along an
    arrow out, realised along the way home with the same content, since out and home is the
    identity (`homeUnique`, `posKeep_full`). -/
theorem realised_keep {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w)
    (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType} {b₀ : Ann A}
    (bd : Term σ (Γ.diaIn x) A b₀) (a : M.frame.Acc w) (r : M.frame.R a.1 w)
    {o : M.frame.Dom A w} (h : M.Realised hT (interp env (Term.diatm x hx bd)) o) :
    ∃ hm : (⟨w, ⟨r⟩⟩ : M.frame.Acc a.1) ∈
        (M.posEval (interp (env.boxPush a) (Term.keptDia hF hx bd).2)).1,
      M.Ind ((M.posEval (interp (env.boxPush a) (Term.keptDia hF hx bd).2)).2 ⟨_, hm⟩) o := by
  obtain ⟨Y, hr⟩ := id hx
  have hk : Γ.boxIn.ref (.step x .keep) = some (.VTypeDia Y) :=
    Ctx.ref_keep_of' hF hr VarType.keepable_dia
  unfold Realised at h
  rw [dia_beta env hx hr] at h
  dsimp only [Term.keptDia]
  rw [dia_beta (env.boxPush a) (Ctx.exists_keep_dia hF hx) hk]
  obtain ⟨hm₁, hi⟩ := h
  have key : ∀ (s : M.frame.R w w)
      (hs : (⟨w, ⟨s⟩⟩ : M.frame.Acc w) ∈ (M.posEval (env.ref x hr)).1),
      M.Ind (interp (env.diaPush x hr ⟨⟨w, ⟨s⟩⟩, hs⟩) bd) o := fun s hs => by
    obtain rfl : s = M.frame.refl hT w := @Subsingleton.elim _ (M.frame.homeUnique hS) _ _
    exact hi
  have hm₀ : (⟨w, ⟨M.frame.trans hF a.2.down r⟩⟩ : M.frame.Acc w) ∈
      (M.posEval (env.ref x hr)).1 := by
    rw [@Subsingleton.elim _ (M.frame.homeUnique hS) (M.frame.trans hF a.2.down r)
      (M.frame.refl hT w)]
    exact hm₁
  have H := congrArg Prod.fst (M.posKeep_full hF (env.ref x hr) a)
  have hm : (⟨w, ⟨r⟩⟩ : M.frame.Acc a.1) ∈
      (M.posEval ((env.boxPush a).ref (.step x .keep) hk)).1 :=
    (congrArg (fun S : M.frame.PosSec _ _ => (⟨w, ⟨r⟩⟩ : M.frame.Acc a.1) ∈ S.1) H).mpr hm₀
  refine ⟨hm, ?_⟩
  change M.Ind (interp ((env.boxPush a).diaPush (.step x .keep) hk ⟨_, hm⟩)
    (Term.shift (Ctx.shifts_diaIn_keep hF Γ x) bd)) _
  rw [interp_shift (Env.shiftAgree_diaKeep hF env hr a ⟨w, ⟨r⟩⟩ hm₀ hk hm) bd]
  exact key _ hm₀

/-- ⭐**A kept possible object comes back as its own content** is sound (`realised_keep`), and the
    necessary part's return is unchanged. -/
theorem sat_ret_keep {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W} (env : M.Env Γ w)
    (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    (O : OutLeg Γ) (N : NShape) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    {A : VarType} {b₀ : Ann A} (bd : Term σ (Γ.diaIn x) A b₀) {c₀ : Ann A} (c : Term σ Γ A c₀)
    {a : Ann N.flat} (y : Term σ Γ N.flat a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit N A).ty) 1)
    (hh : M.sat env (WFF.here hT (Term.diatm x hx bd) c : WFF σ Γ 0))
    (h : M.sat env (O.retS hS (.nec N) y (WFF.bodyRepl (RShape.keepL hF O N hx bd).2 Φ))) :
    M.sat env (O.retS hS (.wit N A) (Term.pair y c) Φ) := by
  obtain ⟨i, d, hΦ, r, hr⟩ := (OutLeg.sat_retS hS env O (.nec N) y _).mp h
  obtain ⟨hm, hI⟩ := realised_keep env hS hT hF hx bd (O.acc env i) r (o := interp env c) hh
  rw [sat_bodyRepl O.noProjLast] at hΦ
  have hv : interp ((O.push env i).extend (.bnd 0) d) (RShape.keepL hF O N hx bd).2 =
      ((d, interp (env.boxPush (O.acc env i)) (Term.keptDia hF hx bd).2) :
        M.frame.Dom (RShape.wit N A).ty (O.acc env i).1) := by
    have e₁ := interp_eta_slot (σ := σ) (T := N.ty) (O.push env i) d
      (Ctx.ref_insert_root O.view (.bnd 0) N.ty)
    have e₂ := (interp_mono (Env.agree_extend (O.push env i)
      (Ctx.NoSlots.slots (Γ := O.view)).root d) (Term.mono O.le_view
        (Term.keptDia hF hx bd).2)).trans (interp_mono (OutLeg.agree_push env O i) _)
    exact congrArg₂ (fun u v => ((u, v) : M.frame.Dom (RShape.wit N A).ty (O.acc env i).1)) e₁ e₂
  rw [hv] at hΦ
  refine (OutLeg.sat_retS hS env O (.wit N A) _ _).mpr ⟨i, _, hΦ, r, ?_⟩
  change M.NComesBack N d r (interp env y) ∧ _
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
