import QML.QML_v12m_GCanonModel

/-!
# QML v12m — the growing tree's canonical model: strong 4's lift, and the model

* ⭐`gkeep_edge`: along one edge, every definable object of a liftable type at the child is a
  kept object of the parent.  The chain lifted its term `u` to a root `r` (`gllift`); the root's
  η-expansion, kept (`applyG_keep_eta`), translates along the edge to `u`'s entry
  (`Term.subst_eta_tm`).
* ⭐`graw_keepLift`: along any arrow, by induction on its path, keeping composing along paths
  (`grawEval_keep_comp`).
* ⭐`gmodel`: the canonical model.  `necDup_eval` and `posKeep_full` hold by definition; `Ind` is
  equality (nothing reads it with T and strong B off).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- Keeping an η-expanded address is the η-expansion of its kept item, inside `□`. -/
theorem applyG_keep_eta {Γ : Ctx} : ∀ {T : VarType} (hk : T.keepable = true) (r : VarSymb)
    (h : Γ.ref r = some T),
    Canon.applyG (GFunc.keep (σ := σ) hF hk) (Term.eta r T h) =
      ⟨_, .boxtm (Term.eta (.step r .keep) T (Ctx.ref_keep_of' hF h hk))⟩
  | .VTypeBox B, _, r, h =>
      sig_boxtm (sig_boxtm ((Term.shift_eta (Ctx.shifts_boxIn_boxIn hF Γ) r.inner B
        (Ctx.ref_inner h)).trans (Term.eta_congr (VarSymb.inner_shift_zero r) B _ _)))
  | .VTypeDia B, _, r, h =>
      sig_boxtm (sig_diatm ((Term.shift_eta (Ctx.shifts_diaIn_keep hF Γ r) (.step r .dia) B
        (Ctx.ref_diaIn_of h)).trans
          (Term.eta_congr (VarSymb.shift_level_zero (s := .dia) rfl) B _ _)))
  | .Var, hk, _, _ => (Bool.false_ne_true hk).elim
  | .VTypeOne, hk, _, _ => (Bool.false_ne_true hk).elim
  | .VTypeProd _ _, hk, _, _ => (Bool.false_ne_true hk).elim

variable [ModalSys.NoT] {hM₀ : Theory.IsMCS M₀}

/-- Keeping along a composite arrow is keeping twice. -/
theorem grawEval_keep_comp : ∀ {T : VarType} (hk : T.keepable = true) {s u t : GW hF M₀}
    (e : GR s u) (q : GR u t) (m : GRDom hM₀ T s),
    grawEval hM₀ (GFunc.keep hF hk) s m ⟨t, ⟨gtrans e q⟩⟩ =
      grawEval hM₀ (GFunc.keep hF hk) u (grawEval hM₀ (GFunc.keep hF hk) s m ⟨u, ⟨e⟩⟩)
        ⟨t, ⟨q⟩⟩
  | .VTypeBox _, _, _, _, _, _, _, _ => rfl
  | .VTypeDia _, _, _, _, _, _, _, _ => rfl
  | .Var, hk, _, _, _, _, _, _ => (Bool.false_ne_true hk).elim
  | .VTypeOne, hk, _, _, _, _, _, _ => (Bool.false_ne_true hk).elim
  | .VTypeProd _ _, hk, _, _, _, _, _, _ => (Bool.false_ne_true hk).elim

/-- ⭐**Strong 4 along an edge**: every definable object of a liftable type at a child is a kept
    object of its parent — the kept root the chain lifted its term to. -/
theorem gkeep_edge {T : VarType} (hl : T.liftable = true) {s t : GW hF M₀} (c : ℕ)
    (hc : t.1 = c :: s.1) (o : GRDom hM₀ T t) (ho : GDefinable hM₀ T t o) :
    ∃ m, GDefinable hM₀ T s m ∧
      grawEval hM₀ (GFunc.keep hF (VarType.keepable_of_liftable hl)) s m
        ⟨t, ⟨⟨[c], pathOk_cons, hc⟩⟩⟩ = o := by
  obtain ⟨j, a, u, rfl⟩ := ho
  obtain ⟨i, r, hr, hroot, L, hL, hfm, hLsuf⟩ := gllift hM₀ ⟨c, hc⟩ j u hl
  have hR : (ctxOf (glat s i)).ref (.root (.free r)) = some T := by
    rw [Ctx.ref_nonproj _ rfl, ctxOf_root_lt hr, hroot]
  refine ⟨grden hM₀ s i (Ctx.Le.refl _) (Term.eta _ T hR), gdefinable_rden _ _, ?_⟩
  rw [← grden_applyG]
  refine (congrFun (grden_sigma (Ctx.Le.refl _)
    (applyG_keep_eta (VarType.keepable_of_liftable hl) _ hR)) _).trans ?_
  rw [grden_boxtm_path (Ctx.Le.refl _) _ t _ [c] hc (pathOk_cons), Term.mono_refl]
  have hat : (eS σ (ctxOf (glat t (glstg s t i))) (fmapL hF M₀ t.1)).at
      (.step (.root (.free r)) .keep) =
        .tm (Term.mono (ctxOf_le_of_suffix hLsuf) (Term.mono (ctxOf_le_of_suffix hL) u)) := by
    rw [Subst.at_nonproj _ rfl, eS_item _ rfl, hfm, entOf_tm (ctxOf_le_of_suffix hLsuf)]
  refine (grden_sigma (Ctx.Le.refl _) (Term.subst_eta_tm _ _ _ T _ _ _ hat)).trans ?_
  rw [Term.mono_mono, grden_mono]
  exact grden_congr _ _ _ _ _ _

/-- Strong 4 along a path. -/
theorem gkeepLift_path {T : VarType} (hl : T.liftable = true) : ∀ (P : List ℕ) (s t : GW hF M₀)
    (_ : t.1 = nodeOf s.1 P) (_ : PathOk P) (o : GRDom hM₀ T t) (_ : GDefinable hM₀ T t o)
    (hR : GR s t),
    ∃ m, GDefinable hM₀ T s m ∧
      grawEval hM₀ (GFunc.keep hF (VarType.keepable_of_liftable hl)) s m ⟨t, ⟨hR⟩⟩ = o
  | [], _, _, _, hP, _, _, _ => (absT hP.T_of_nil).elim
  | [c], _, _, h, _, o, ho, _ => gkeep_edge hl c h o ho
  | c :: c' :: P, s, t, h, _, o, ho, _ => by
      have hb := born_step h
      have q : GR (stepW s c hb) t := ⟨c' :: P, pathOk_cons, h⟩
      obtain ⟨m', hm', e'⟩ :=
        gkeepLift_path hl (c' :: P) (stepW s c hb) t h (pathOk_cons) o ho q
      obtain ⟨m, hm, e⟩ := gkeep_edge hl (s := s) (t := stepW s c hb) c rfl m' hm'
      refine ⟨m, hm, ?_⟩
      subst e' e
      exact grawEval_keep_comp _ ⟨[c], pathOk_cons, rfl⟩ q m

/-- ⭐**Strong 4 on raw objects**: along any arrow, every definable object of a liftable type at its
    target is a kept definable object of its source. -/
theorem graw_keepLift {T : VarType} (hl : T.liftable = true) (s : GW hF M₀) (a : GAcc hF M₀ s)
    (o : GRDom hM₀ T a.1) (ho : GDefinable hM₀ T a.1 o) :
    ∃ m, GDefinable hM₀ T s m ∧
      grawEval hM₀ (GFunc.keep hF (VarType.keepable_of_liftable hl)) s m a = o := by
  obtain ⟨t, ⟨hR⟩⟩ := a
  exact gkeepLift_path hl (pathOf hR) s t (pathOf_eq hR) (pathOf_ok hR) o ho hR

/-! ## The model -/

variable [ModalSys.NoSym]

omit [ModalSys.NoT] in
theorem absBS (h : ModalSys.BStrong = true) : False := by
  rw [ModalSys.NoSym.noBStrong] at h
  cases h

variable (hF hM₀) in
/-- ⭐**The canonical model on the growing tree** (4 without T or B, every strong form of 4 and
    D). -/
noncomputable def gmodel : Model.{0, 0} σ where
  frame := gframe hF hM₀
  necEval := gnecEval hM₀
  nec_inj := fun h => gnecEval_injective hM₀ h
  RootPoss _ := PUnit
  rootKeep := fun _ _ _ _ => PUnit.unit
  rootKeep_trans := fun _ _ _ _ _ => rfl
  rootKeep_refl := fun hT => (absT hT).elim
  posFull p := (gposEval hM₀ p, fun hSh => (absShaped hSh).elim)
  posFull_inj := fun h => gposEval_injective hM₀ (congrArg Prod.fst h)
  posShape_wf := fun hSh => (absShaped hSh).elim
  ops := gops hF hM₀
  necMap_eval g _ a := (geval_toDom hM₀ g a.1 _ _).symm
  necPair_eval _ _ _ := rfl
  posMap_full g _ := Prod.ext
    (congrArg (Sigma.mk _) (funext fun a => (geval_toDom hM₀ g a.1.1 _ _).symm))
    (funext fun hSh => (absShaped hSh).elim)
  posStrength_full _ _ := Prod.ext rfl (funext fun hSh => (absShaped hSh).elim)
  necExtract_eval hT := (absT hT).elim
  necDup_eval _ _ _ _ := rfl
  keepLift := by
    intro _ T hl w a o
    obtain ⟨m, hm, e⟩ := graw_keepLift hl w a _ (gdefinable_fromDom hM₀ T a.1 o)
    refine ⟨gtoDom hM₀ T w m hm, ?_⟩
    rw [geval_toDom]
    exact (gtoDom_congr e _ _).trans (gtoDom_fromDom hM₀ T a.1 o)
  posKeep_full _ _ _ := Prod.ext rfl (funext fun hSh => (absShaped hSh).elim)
  posSerial hDS s := gposSerial_canon hM₀ hDS s
  Ind o o' := o = o'
  Ind_refl _ := rfl
  posRet_exists hT := (absT hT).elim
  Ret _ _ _ := False
  Ret_fwd hS := (absBS hS).elim
  Ret_conv hS := (absBS hS).elim
  backRet_exists hS := (absBS hS).elim
  posBack_exists hS := (absBS hS).elim

end GArrow

end V12M
