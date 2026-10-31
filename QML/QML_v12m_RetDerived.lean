import QML.QML_v12m_BSyntax

/-!
# QML v12m — strong B: the returning possibility's derived rules

The primitive rules extend a returning possibility by a companion at any shape (`ret_extS`) and
move it along a map of shapes (`ret_map`).  The `□`-shaped forms used by the network are derived
here: extension with repacking (`Proof.ret_ext`, `ret_extS` then `ret_map` at `pack`) and β for a
hole term on the item (`Proof.ret_beta`, `ret_map` at `hole`).
-/

namespace V12M

variable [ModalSys] {σ : Signature}

/-- The entry of a necessary object's term, one view in: its body. -/
theorem Subst.box_at_inner_boxtm {Δ : Ctx} (θ : Subst σ Δ) {v : VarSymb} {A : VarType}
    {a : Ann A} {t : Term σ Δ.boxIn A a} (hs : θ.at v = .tm (.boxtm t)) :
    θ.box.at v.inner = .tm t := by
  by_cases hk : ModalSys.keepOnly = true
  · have hTF := ModalSys.keepOnly_flags hk
    rw [VarSymb.inner_keepOnly hk]
    change (((θ.at v).keepE).proj .here) = _
    rw [hs, SubE.keepE_tm t hTF.2, SubE.proj_boxtm_here _ hTF.1]
    exact SubE.tm_sigma ((Term.collapse_shift_same (Ctx.shifts_boxIn_boxIn hTF.2 Δ)
      (Ctx.collapses_boxIn_self hTF.1 Δ.boxIn) (Ctx.Le.refl _)
      (Ctx.shiftCollapseId_keepOnly hk Δ) t).trans (congrArg (Sigma.mk _) (Term.mono_refl _ t)))
  · rw [VarSymb.inner_box (Bool.eq_false_iff.mpr hk)]
    change (θ.at v).unbox = _
    rw [hs]
    rfl

/-- Terms equal as dependent pairs are similar entries. -/
theorem SubE.sim_tm_sigma {Δ : Ctx} {T : VarType} {a b : Ann T} {s : Term σ Δ T a}
    {t : Term σ Δ T b} (h : (⟨a, s⟩ : Σ c, Term σ Δ T c) = ⟨b, t⟩) :
    SubE.Sim T (.tm s) (.tm t) := by
  cases h
  exact .refl _


/-! ## Repacking a split body -/

section Body

variable {V : Ctx} [V.NoSlots]

/-- ⭐Packing two necessary objects into one, then splitting it, is splitting along the pair:
    `pack ⟨d₀, d₁⟩`'s first component is `d₀` and its second `d₁` (`ret_ext` from `ret_extS`). -/
theorem WFF.bodyRepl_pack_bodySplit {A B : VarType}
    (Φ : WFF σ ((V.insert (.bnd 0) (.VTypeBox A)).insert (.bnd 1) (.VTypeBox B)) 2) :
    WFF.bodyRepl (Term.mono ((Ctx.empty_le V).insert (.bnd 0) _)
        (ShapeMap.pack (σ := σ) A B).obj.2)
        (WFF.bodySplit (Term.boxFst (Ctx.ref_insert_root V (.bnd 0) (.VTypeBox (.VTypeProd A B))))
          (Term.boxSnd (Ctx.ref_insert_root V (.bnd 0) (.VTypeBox (.VTypeProd A B)))) Φ) =
      WFF.bodySplit
        (Term.eta (.step (.root (.bnd 0)) .fst) (NShape.box A).ty
          (Ctx.ref_fst_of (Ctx.ref_insert_root V (.bnd 0) (NShape.prod (.box A) (.box B)).ty)))
        (Term.eta (.step (.root (.bnd 0)) .snd) (.VTypeBox B)
          (Ctx.ref_snd_of (Ctx.ref_insert_root V (.bnd 0) (NShape.prod (.box A) (.box B)).ty)))
        Φ := by
  unfold WFF.bodyRepl WFF.bodySplit
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  have hpk : ((Subst.idS σ (V.insert (.bnd 0) (NShape.prod (.box A) (.box B)).ty)).set (.bnd 0)
      (.tm (Term.mono ((Ctx.empty_le V).insert (.bnd 0) _) (ShapeMap.pack (σ := σ) A B).obj.2))).at
        (.root (.bnd 0)) = .tm (Term.mono ((Ctx.empty_le V).insert (.bnd 0) _)
          (ShapeMap.pack (σ := σ) A B).obj.2) := Subst.set_root _ _ _
  refine Subst.sim_of fun v T _ hv => ?_
  by_cases h1 : v = .root (.bnd 1)
  · subst h1
    obtain rfl : T = .VTypeBox B := by simpa [Ctx.insert] using hv.symm
    dsimp only [Subst.comp]
    rw [Subst.set_root, Subst.set_root]
    dsimp only [SubE.comp]
    refine SubE.sim_tm_sigma (sig_boxtm ?_)
    refine ((Term.subst_eta_tm _ _ _ _ _ _ (Term.mono
      (((Ctx.empty_le V).insert (.bnd 0) (NShape.prod (.box A) (.box B)).ty).boxIn)
      (Term.eta (σ := σ) (VarSymb.step (.root (.bnd 0)) .snd).inner B
        (Ctx.ref_inner (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))) ?_).trans ?_).symm
    · rw [Subst.at_proj _ _ rfl, Subst.box_at_inner_boxtm _ hpk]
      rfl
    · rw [Term.mono_eta]
  · by_cases h0 : v = .root (.bnd 0)
    · subst h0
      obtain rfl : T = .VTypeBox A := by simpa [Ctx.insert] using hv.symm
      dsimp only [Subst.comp]
      rw [Subst.set_ne _ _ (fun h => by cases h), Subst.set_root,
        Subst.set_ne _ _ (fun h => by cases h), Subst.set_root]
      dsimp only [SubE.comp]
      refine SubE.sim_tm_sigma (sig_boxtm ?_)
      refine ((Term.subst_eta_tm _ _ _ _ _ _ (Term.mono
        (((Ctx.empty_le V).insert (.bnd 0) (NShape.prod (.box A) (.box B)).ty).boxIn)
        (Term.eta (σ := σ) (VarSymb.step (.root (.bnd 0)) .fst).inner A
          (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))) ?_).trans ?_).symm
      · rw [Subst.at_proj _ _ rfl, Subst.box_at_inner_boxtm _ hpk]
        rfl
      · rw [Term.mono_eta]
    · dsimp only [Subst.comp]
      rw [Subst.set_ne _ _ h1, Subst.set_ne _ _ h0, Subst.set_ne _ _ h1, Subst.set_ne _ _ h0]
      change SubE.Sim T (.ren v) (Subst.at _ v)
      rw [Subst.at_nonproj _ (by assumption), Subst.set_ne _ _ h0]
      exact .refl _

/-- Weakening commutes with replacing the bound item. -/
theorem WFF.mono_bodyRepl {V' : Ctx} [V'.NoSlots] (h : V.Le V') {A B : VarType} {b : Ann B}
    (X : Term σ (V.insert (.bnd 0) A) B b) (Ψ : WFF σ (V.insert (.bnd 0) B) 1) :
    WFF.mono (h.insert (.bnd 0) A) (WFF.bodyRepl X Ψ) =
      WFF.bodyRepl (Term.mono (h.insert (.bnd 0) A) X) (WFF.mono (h.insert (.bnd 0) B) Ψ) := by
  unfold WFF.bodyRepl
  rw [WFF.mono_subst, WFF.subst_mono]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) Ψ
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    change SubE.Sim T (SubE.mono _ (Subst.set _ _ _ (.root (.bnd 0))))
      (Subst.set _ _ _ (.root (.bnd 0)))
    rw [Subst.set_root, Subst.set_root]
    exact .refl _
  · change SubE.Sim T (SubE.mono _ (Subst.set _ _ _ v)) (Subst.set _ _ _ v)
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    exact .refl _

end Body

/-- A hole read at the hole's own η-expansion is the term in it. -/
theorem Term.holeRead_eta_root {Γ : Ctx} [Γ.NoSlots] {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) :
    (⟨_, Term.holeRead t (Term.eta (σ := σ) (.root (.bnd 0)) A (Ctx.ref_insert_root _ _ _))⟩ :
      Σ b, Term σ Γ A b) = ⟨a, t⟩ := by
  unfold Term.holeRead
  rw [Term.mono_eta]
  exact Term.subst_eta_tm _ _ _ _ _ _ t (by
    change Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm t) (.root (.bnd 0)) = _
    exact if_pos rfl)

/-! ## The `□` forms, derived -/

/-- ⭐**β for a hole term on the item** is `ret_map` at `ShapeMap.hole`. -/
def Proof.ret_beta {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
    (O : OutLeg Γ) {A B : VarType} {a : Ann A}
    (y : Term σ Γ A a) {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b)
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox B)) 1)
    (p : Proof σ Γ Δ (O.ret hS y (WFF.bodyRepl
      (Term.boxtm (Term.holeAt (Term.eta (VarSymb.root (.bnd 0)).inner A
        (Ctx.ref_inner (Ctx.ref_insert_root O.view (.bnd 0) (.VTypeBox A)))) s)) Φ))) :
    Proof σ Γ Δ (O.ret hS (Term.holeRead y s) Φ) :=
  Proof.ret_map hS O (.hole s) y Φ (Proof.conv (OutLeg.retS_congr' hS O (.box A) rfl
    (WFF.bodyRepl_congr (sig_boxtm ((Term.holeAt_congr_sig
      (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)).symm s).trans
      (Term.mono_holeAt_sig _ _ s).symm)) Φ)) p)

/-- ⭐**One more item, packed** is `ret_extS` followed by `ret_map` at `ShapeMap.pack`: the pair
    of necessary objects is repacked as one necessary object of the pair type. -/
def Proof.ret_ext {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) (O : OutLeg Γ)
    {A B : VarType} {a : Ann A} (t : Term σ Γ A a)
    (Φ : WFF σ ((O.view.insert (.bnd 0) (.VTypeBox A)).insert (.bnd 1) (.VTypeBox B)) 2)
    (c : ℕ) (hc : Γ.RootFresh (.free c)) {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0}
    (p : Proof σ Γ Δ (O.ret hS t (WFF.ex (.VTypeBox B) Φ)))
    (q : Proof σ (Γ.insert (.free c) B)
      ((O.mono (Ctx.le_insert hc.root B)).ret hS
          (Term.pair (Term.weaken hc.root B t)
            (Term.eta (.root (.free c)) B (Ctx.ref_insert_root Γ (.free c) B)))
          (WFF.mono ((O.le_view_mono (Ctx.le_insert hc.root B)).insert (.bnd 0) _) (WFF.bodySplit
            (Term.boxFst (Ctx.ref_insert_root O.view (.bnd 0) (.VTypeBox (.VTypeProd A B))))
            (Term.boxSnd (Ctx.ref_insert_root O.view (.bnd 0) (.VTypeBox (.VTypeProd A B))))
            Φ)) ::
        Δ.map (WFF.weaken hc.root B))
      (φ.weaken hc.root B)) : Proof σ Γ Δ φ :=
  have hle := O.le_view_mono (Ctx.le_insert hc.root B)
  Proof.ret_extS hS O (S := .box A) t Φ c hc p
    (Proof.imp_elim (Proof.ofSubset (fun _ hx => List.mem_cons_of_mem _ hx) (Proof.imp_intro q))
      (Proof.conv (OutLeg.retS_congr hS _ (.box (.VTypeProd A B))
          (Term.holeRead_eta_root _) rfl)
        (Proof.ret_map hS _ (S := .nec (.prod (.box A) (.box B))) (.pack A B) _ _
          (Proof.conv (OutLeg.retS_congr' hS _ _ rfl (by
            dsimp only [RShape.extL, RShape.extR, ShapeMap.liftObj]
            rw [← WFF.bodyRepl_pack_bodySplit, WFF.mono_bodyRepl hle, Term.mono_mono]))
          (Proof.lookup List.mem_cons_self)))))

end V12M
