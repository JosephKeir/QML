import QML.QML_v12m_Open

/-!
# QML v12m — Leibniz at `◇`-type, and symmetry and transitivity of the defined equality

Since `eqRec`'s `◇` clause is now the primitive `WFF.diaEq` (§2d), symmetry and transitivity at that
type are derived from reflexivity and Leibniz, exactly as at base type.  The one wrinkle is that a
`◇`-typed slot can only be *mentioned* as its own η-expansion, so using `Proof.diaEq_elim` needs to
know what instantiating that η-expansion does:

* ⭐`WFF.instantiate_diaEq_slot`, `WFF.instantiate_diaEq_slot'`: filling the slot gives the term
  substituted in (`Term.subst_eta_tm`), while the other side, weakened past the slot, comes back
  unchanged (`Term.subst_ren` at the identity inclusion).
* ⭐`Proof.eqRec_symm`, ⭐`Proof.eqRec_trans`: annotation-free, as `eqRec` now is.

They live here rather than in `QML_v12m_Eq` only because `Term.subst_ren` and `Subst.at_single_root`
do.
-/

namespace V12M

variable [ModalSys]

theorem WFF.instantiate_diaEq_slot {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {A : VarType}
    {b b' : Ann (.VTypeDia A)} (u : Term σ Γ (.VTypeDia A) b) (t : Term σ Γ (.VTypeDia A) b') :
    WFF.instantiate (d := 0) Ctx.NoSlots.slots u
        (WFF.diaEq (Term.eta (.root (.bnd 0)) (.VTypeDia A)
            (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A)))
          (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root (.VTypeDia A)) t)) =
      WFF.diaEq u t := by
  refine WFF.diaEq_congr (Term.subst_eta_tm _ _ _ (.VTypeDia A) (.root (.bnd 0)) _ u
    (Subst.at_single_root _ _)) ?_
  refine (congrArg (Sigma.mk _) (Term.subst_mono _ _ _ _ t)).trans ?_
  refine (Term.subst_ren (Ctx.Le.refl Γ) _ _ _ ?_ t).trans
    (congrArg (Sigma.mk _) (Term.mono_refl _ t))
  intro v T hv
  exact Subst.single_at_ne
    (Ctx.ref_rt_ne ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) hv)

theorem WFF.instantiate_diaEq_slot' {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {A : VarType}
    {b b' : Ann (.VTypeDia A)} (u : Term σ Γ (.VTypeDia A) b) (t : Term σ Γ (.VTypeDia A) b') :
    WFF.instantiate (d := 0) Ctx.NoSlots.slots u
        (WFF.diaEq (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root (.VTypeDia A)) t)
          (Term.eta (.root (.bnd 0)) (.VTypeDia A)
            (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A)))) =
      WFF.diaEq t u := by
  refine WFF.diaEq_congr ?_ (Term.subst_eta_tm _ _ _ (.VTypeDia A) (.root (.bnd 0)) _ u
    (Subst.at_single_root _ _))
  refine (congrArg (Sigma.mk _) (Term.subst_mono _ _ _ _ t)).trans ?_
  refine (Term.subst_ren (Ctx.Le.refl Γ) _ _ _ ?_ t).trans
    (congrArg (Sigma.mk _) (Term.mono_refl _ t))
  intro v T hv
  exact Subst.single_at_ne
    (Ctx.ref_rt_ne ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) hv)

/-- ⭐Filling the `◇`-slot of a `Here` formula: the slot's η-expansion becomes the term, and the
    value, weakened past the slot, comes back unchanged.  The `Here`-shaped hole formula is what
    Leibniz for `≐` needs in order to transfer a realisation, so this is
    `instantiate_diaEq_slot`'s partner for the other atom that mentions a `◇`-term. -/
theorem WFF.instantiate_here_slot {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true)
    {A : VarType} {b : Ann (.VTypeDia A)} {a : Ann A} (u : Term σ Γ (.VTypeDia A) b)
    (t : Term σ Γ A a) :
    WFF.instantiate (d := 0) Ctx.NoSlots.slots u
        (WFF.here (d := 1) hT (Term.eta (.root (.bnd 0)) (.VTypeDia A)
            (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A)))
          (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root (.VTypeDia A)) t)) =
      WFF.here hT u t := by
  refine WFF.here_congr hT (Term.subst_eta_tm _ _ _ (.VTypeDia A) (.root (.bnd 0)) _ u
    (Subst.at_single_root _ _)) ?_
  refine (congrArg (Sigma.mk _) (Term.subst_mono _ _ _ _ t)).trans ?_
  refine (Term.subst_ren (Ctx.Le.refl Γ) _ _ _ ?_ t).trans
    (congrArg (Sigma.mk _) (Term.mono_refl _ t))
  intro v T hv
  exact Subst.single_at_ne
    (Ctx.ref_rt_ne ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) hv)

namespace Proof

/-- ⭐Symmetry, at any two annotations. -/
def eqRec_symm {σ : Signature} : {Γ : Ctx} → [Γ.NoSlots] → {Δ : List (WFF σ Γ 0)} →
    (T : VarType) → {a a' : Ann T} → {t : Term σ Γ T a} → {s : Term σ Γ T a'} →
    Proof σ Γ Δ (eqRec T t s) → Proof σ Γ Δ (eqRec T s t)
  | _, _, _, .Var, .var, .var, _, _, p =>
      Proof.conv (eqRec_Var _ _).symm (Proof.eq_symm_base (Proof.conv (eqRec_Var _ _) p))
  | _, _, _, .VTypeOne, .one, .one, .unit, .unit, _ => .top_intro
  | _, _, _, .VTypeProd A B, .prod _ _, .prod _ _, .pair _ _, .pair _ _, p =>
      .and_intro (eqRec_symm A (.and_elim_l p)) (eqRec_symm B (.and_elim_r p))
  | _, _, Δ, .VTypeBox A, .box _, .box _, .boxtm t, .boxtm s, p =>
      Proof.cut (Proof.weakenTail Δ
        (Proof.K_box (Δ := [eqRec A t s]) (eqRec_symm A (.ax _)))) p
  | _, _, _, .VTypeDia A, _, _, t, s, p =>
      Proof.conv ((WFF.instantiate_diaEq_slot s t).trans (eqRec_dia s t).symm)
        (Proof.diaEq_elim
          (φ := WFF.diaEq (Term.eta (.root (.bnd 0)) (.VTypeDia A)
              (Ctx.ref_insert_root _ (.bnd 0) (.VTypeDia A)))
            (Term.mono (Ctx.le_insert Ctx.NoSlots.slots.root (.VTypeDia A)) t))
          t s (Proof.conv (eqRec_dia t s) p)
          (Proof.conv (WFF.instantiate_diaEq_slot t t).symm (Proof.diaEq_intro t)))

/-- ⭐Transitivity, at any three annotations. -/
def eqRec_trans {σ : Signature} : {Γ : Ctx} → [Γ.NoSlots] → {Δ : List (WFF σ Γ 0)} →
    (T : VarType) → {a a' a'' : Ann T} → {t : Term σ Γ T a} → {s : Term σ Γ T a'} →
    {r : Term σ Γ T a''} →
    Proof σ Γ Δ (eqRec T t s) → Proof σ Γ Δ (eqRec T s r) → Proof σ Γ Δ (eqRec T t r)
  | _, _, _, .Var, .var, .var, .var, _, _, _, p, q =>
      Proof.conv (eqRec_Var _ _).symm
        (Proof.eq_trans_base (Proof.conv (eqRec_Var _ _) p) (Proof.conv (eqRec_Var _ _) q))
  | _, _, _, .VTypeOne, .one, .one, .one, .unit, .unit, .unit, _, _ => .top_intro
  | _, _, _, .VTypeProd A B, .prod _ _, .prod _ _, .prod _ _, .pair _ _, .pair _ _, .pair _ _,
      p, q =>
      .and_intro (eqRec_trans A (.and_elim_l p) (.and_elim_l q))
        (eqRec_trans B (.and_elim_r p) (.and_elim_r q))
  | Γ, _, Δ, .VTypeBox A, .box _, .box _, .box _, .boxtm t, .boxtm s, .boxtm r, p, q =>
      have h₁ : Proof σ Γ (WFF.box (eqRec A t s) :: WFF.box (eqRec A s r) :: Δ)
          (.box (eqRec A t r)) :=
        Proof.weakenTail Δ (Proof.K_box (Δ := [eqRec A t s, eqRec A s r])
          (eqRec_trans A (Proof.lookup (x := eqRec A t s) List.mem_cons_self)
            (Proof.lookup (x := eqRec A s r) (List.mem_cons_of_mem _ List.mem_cons_self))))
      Proof.cut (Proof.cut h₁ (.weak _ p)) q
  | _, _, _, .VTypeDia A, _, _, _, t, s, r, p, q =>
      Proof.conv ((WFF.instantiate_diaEq_slot' r t).trans (eqRec_dia t r).symm)
        (Proof.diaEq_elim
          (φ := WFF.diaEq (Term.mono (Ctx.le_insert Ctx.NoSlots.slots.root (.VTypeDia A)) t)
            (Term.eta (.root (.bnd 0)) (.VTypeDia A)
              (Ctx.ref_insert_root _ (.bnd 0) (.VTypeDia A))))
          s r (Proof.conv (eqRec_dia s r) q)
          (Proof.conv (WFF.instantiate_diaEq_slot' s t).symm (Proof.conv (eqRec_dia t s) p)))


/-- ⭐**Realisation transfers along `≐`**: if the theory identifies two possible objects and one of
    them is realised by `t` here, so is the other.  Leibniz (`diaEq_elim`) with the hole formula
    `Here □ t` — the atom takes an arbitrary `◇`-term as its subject, so this hole needs no view
    renaming, unlike `boxx_reView`'s.  This is the `≐`-invariance that realisedness read off the
    theory has by construction. -/
def here_diaEq {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)}
    (hT : ModalSys.T = true) {A : VarType} {b b' : Ann (.VTypeDia A)} {a : Ann A}
    (s : Term σ Γ (.VTypeDia A) b) (s' : Term σ Γ (.VTypeDia A) b') (t : Term σ Γ A a) :
    Proof σ Γ (WFF.diaEq s s' :: WFF.here hT s t :: Δ) (WFF.here hT s' t) :=
  Proof.conv (WFF.instantiate_here_slot hT s' t)
    (Proof.diaEq_elim
      (φ := WFF.here hT (Term.eta (.root (.bnd 0)) (.VTypeDia A)
          (Ctx.ref_insert_root _ (.bnd 0) (.VTypeDia A)))
        (Term.mono (Ctx.le_insert Ctx.NoSlots.slots.root (.VTypeDia A)) t))
      s s' (Proof.lookup List.mem_cons_self)
      (Proof.conv (WFF.instantiate_here_slot hT s t).symm
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))))
end Proof

end V12M
