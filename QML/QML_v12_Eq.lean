import QML.QML_v12_Proof

/-!
# QML v12 — equality at every type

`eqRec T t s` defines equality by extensionality.  Here: reflexivity, symmetry and transitivity at
every type, by induction on the type.  The base cases come from `eq_intro` / `eq_elim`; the `□`
case goes through `K_box`, the `◇` case through `K_dia` and `dia_bot` (`□_x E` is `¬◇_x¬E`).
-/

namespace V12

/-! ## Proof helpers -/

namespace Proof

variable {σ : Signature} {Γ : Ctx}

def conv {Δ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (h : φ = ψ) (p : Proof σ Γ Δ φ) :
    Proof σ Γ Δ ψ :=
  h ▸ p

/-- Cut, via implication. -/
def cut {Δ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (p : Proof σ Γ (φ :: Δ) ψ)
    (q : Proof σ Γ Δ φ) : Proof σ Γ Δ ψ :=
  .imp_elim (.imp_intro p) q

/-- Weaken by a whole list at the back. -/
def weakenTail {Δ₀ : List (WFF σ Γ 0)} (Δ : List (WFF σ Γ 0)) {φ : WFF σ Γ 0}
    (p : Proof σ Γ Δ₀ φ) : Proof σ Γ (Δ₀ ++ Δ) φ :=
  Proof.ofSubset (fun _ h => List.mem_append_left _ h) p

end Proof

/-! ## Substituting into a weakened base term changes nothing -/

theorem SubE.toVar_tm {σ : Signature} {Δ : Ctx} :
    ∀ (s : Term σ Δ .Var .var) (h : (SubE.tm s).OkRef .Var), (SubE.tm s).toVar h = s
  | .var _ _, _ => rfl
  | .func _, _ => rfl

theorem SubE.toVar_of_eq_ren {σ : Signature} {Δ : Ctx} {e : SubE σ Δ} {w : VarSymb}
    (he : e = .ren w) (h : e.OkRef .Var) : e.toVar h = .var w (by subst he; exact h) := by
  subst he
  rfl

theorem Subst.single_at_ne {σ : Signature} {Δ : Ctx} {r : Root} {e : SubE σ Δ} :
    ∀ {v : VarSymb}, v.rt ≠ r → (Subst.single r e).at v = .ren v
  | .root r', h => by
      have h' : r' ≠ r := h
      change (if VarSymb.root r' = .root r then e else .ren (.root r')) = _
      rw [if_neg (fun he => h' (VarSymb.root.inj he))]
  | .step v s, h => by
      have ih := Subst.single_at_ne (r := r) (e := e) (v := v) h
      change (if s.isProd then ((Subst.single r e).at v).proj s
        else (if VarSymb.step v s = .root r then e else .ren (.step v s))) = _
      rw [ih]
      split_ifs with h₁ h₂
      · rfl
      · cases h₂
      · rfl

mutual
  theorem Func.subst_mono_id {σ : Signature} (ι : VarSymb → VarSymb) {Γ Γ' : Ctx}
      (hle : Γ.Le Γ') (θ : Subst σ Γ) (hθ : Subst.Ok Γ' θ) (hc : Subst.Coh ι Γ' θ)
      (hid : ∀ v, Γ.ref v = some .Var → θ.at v = .ren v) :
      {n : ℕ} → (f : Func σ Γ n) → Func.subst ι θ hθ hc (Func.mono hle f) = f
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.subst ι θ hθ hc (Func.mono hle g))
          (Term.subst ι θ hθ hc (Term.mono hle t)) = _
        rw [Func.subst_mono_id ι hle θ hθ hc hid g,
          eq_of_heq (Term.subst_mono_id_heq ι hle θ hθ hc hid t rfl)]
    termination_by structural _ f => f

  /-- Stated at arbitrary indices (so the recursion is structural); only `Var` terms qualify. -/
  theorem Term.subst_mono_id_heq {σ : Signature} (ι : VarSymb → VarSymb) {Γ Γ' : Ctx}
      (hle : Γ.Le Γ') (θ : Subst σ Γ) (hθ : Subst.Ok Γ' θ) (hc : Subst.Coh ι Γ' θ)
      (hid : ∀ v, Γ.ref v = some .Var → θ.at v = .ren v) :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ T a) → T = .Var →
      HEq (Term.subst ι θ hθ hc (Term.mono hle t)) t
    | _, _, .var v hv, _ => heq_of_eq (SubE.toVar_of_eq_ren (hid v hv) _)
    | _, _, .func f, _ => heq_of_eq (by
        change Term.func (Func.subst ι θ hθ hc (Func.mono hle f)) = _
        rw [Func.subst_mono_id ι hle θ hθ hc hid f])
    | _, _, .unit, h => nomatch h
    | _, _, .pair _ _, h => nomatch h
    | _, _, .boxtm _, h => nomatch h
    | _, _, .diatm _ _ _, h => nomatch h
    termination_by structural _ _ t => t
end

theorem Term.subst_mono_id {σ : Signature} (ι : VarSymb → VarSymb) {Γ Γ' : Ctx}
    (hle : Γ.Le Γ') (θ : Subst σ Γ) (hθ : Subst.Ok Γ' θ) (hc : Subst.Coh ι Γ' θ)
    (hid : ∀ v, Γ.ref v = some .Var → θ.at v = .ren v) (t : Term σ Γ .Var .var) :
    Term.subst ι θ hθ hc (Term.mono hle t) = t :=
  eq_of_heq (Term.subst_mono_id_heq ι hle θ hθ hc hid t rfl)

/-! ## Base equality -/

section Base

variable {σ : Signature} {Γ : Ctx} [Γ.NoSlots]

theorem Ctx.NoSlots.ref_bnd0 {v : VarSymb} {T : VarType} (hv : Γ.ref v = some T) :
    v.rt ≠ .bnd 0 := fun he => by
  rw [Ctx.ref_none_of_rootFresh (Ctx.NoSlots.slots.rootFresh le_rfl) v he] at hv
  cases hv

/-- `□ = t`, the hole at the slot. -/
def eqHoleL (t : Term σ Γ .Var .var) : WFF σ (Γ.insert (.bnd 0) .Var) 1 :=
  .eq (.var (.root (.bnd 0)) (Ctx.ref_insert_root Γ _ _))
    (Term.mono (Ctx.le_insert Ctx.NoSlots.slots.root .Var) t)

/-- `t = □`, the hole at the slot. -/
def eqHoleR (t : Term σ Γ .Var .var) : WFF σ (Γ.insert (.bnd 0) .Var) 1 :=
  .eq (Term.mono (Ctx.le_insert Ctx.NoSlots.slots.root .Var) t)
    (.var (.root (.bnd 0)) (Ctx.ref_insert_root Γ _ _))

theorem instantiate_eqHoleL (s t : Term σ Γ .Var .var) :
    WFF.instantiate Ctx.NoSlots.slots s (eqHoleL t) = .eq s t := by
  change WFF.eq (Term.subst _ _ _ _ (Term.var _ _)) (Term.subst _ _ _ _ (Term.mono _ t)) = _
  congr 1
  · exact SubE.toVar_tm s _
  · exact Term.subst_mono_id _ _ _ _ _
      (fun v hv => Subst.single_at_ne (Ctx.NoSlots.ref_bnd0 hv)) t

theorem instantiate_eqHoleR (s t : Term σ Γ .Var .var) :
    WFF.instantiate Ctx.NoSlots.slots s (eqHoleR t) = .eq t s := by
  change WFF.eq (Term.subst _ _ _ _ (Term.mono _ t)) (Term.subst _ _ _ _ (Term.var _ _)) = _
  congr 1
  · exact Term.subst_mono_id _ _ _ _ _
      (fun v hv => Subst.single_at_ne (Ctx.NoSlots.ref_bnd0 hv)) t
  · exact SubE.toVar_tm s _

def Proof.eq_symm_base {Δ : List (WFF σ Γ 0)} {t s : Term σ Γ .Var .var}
    (p : Proof σ Γ Δ (.eq t s)) : Proof σ Γ Δ (.eq s t) :=
  Proof.conv (instantiate_eqHoleL s t)
    (Proof.eq_elim (φ := eqHoleL t) t s p
      (Proof.conv (instantiate_eqHoleL t t).symm (Proof.eq_intro t)))

def Proof.eq_trans_base {Δ : List (WFF σ Γ 0)} {t s r : Term σ Γ .Var .var}
    (p : Proof σ Γ Δ (.eq t s)) (q : Proof σ Γ Δ (.eq s r)) : Proof σ Γ Δ (.eq t r) :=
  Proof.conv (instantiate_eqHoleR r t)
    (Proof.eq_elim (φ := eqHoleR t) s r q (Proof.conv (instantiate_eqHoleR s t).symm p))

end Base

/-! ## Every type -/

theorem eqRec_Var {σ : Signature} {Γ : Ctx} {d : ℕ} (t s : Term σ Γ .Var .var) :
    (eqRec .Var t s : WFF σ Γ d) = .eq t s := by
  cases t <;> cases s <;> rfl

namespace Proof

/-- ⭐Reflexivity. -/
def eqRec_refl {σ : Signature} : {Γ : Ctx} → [Γ.NoSlots] → {Δ : List (WFF σ Γ 0)} →
    (T : VarType) → {a : Ann T} → (t : Term σ Γ T a) → Proof σ Γ Δ (eqRec T t t)
  | _, _, _, .Var, .var, t => Proof.conv (eqRec_Var t t).symm (.eq_intro t)
  | _, _, _, .VTypeOne, .one, .unit => .top_intro
  | _, _, _, .VTypeProd A B, .prod _ _, .pair t₁ t₂ =>
      .and_intro (eqRec_refl A t₁) (eqRec_refl B t₂)
  | _, _, _, .VTypeBox A, .box _, .boxtm t =>
      Proof.ofSubset (fun _ h => absurd h List.not_mem_nil)
        (Proof.K_box (Δ := []) (eqRec_refl A t))
  | _, _, Δ, .VTypeDia A, .dia x _, .diatm _ hx t =>
      .imp_intro (Proof.weakenTail Δ
        (.dia_bot x hx (Proof.K_dia (Δ₁ := []) (Δ₂ := []) (φ := .bot) x hx
          (.imp_elim (.ax _) (eqRec_refl A t)))))

/-- ⭐Symmetry. -/
def eqRec_symm {σ : Signature} : {Γ : Ctx} → [Γ.NoSlots] → {Δ : List (WFF σ Γ 0)} →
    (T : VarType) → {a : Ann T} → {t s : Term σ Γ T a} →
    Proof σ Γ Δ (eqRec T t s) → Proof σ Γ Δ (eqRec T s t)
  | _, _, _, .Var, .var, _, _, p =>
      Proof.conv (eqRec_Var _ _).symm (Proof.eq_symm_base (Proof.conv (eqRec_Var _ _) p))
  | _, _, _, .VTypeOne, .one, .unit, .unit, _ => .top_intro
  | _, _, _, .VTypeProd A B, .prod _ _, .pair _ _, .pair _ _, p =>
      .and_intro (eqRec_symm A (.and_elim_l p)) (eqRec_symm B (.and_elim_r p))
  | _, _, Δ, .VTypeBox A, .box _, .boxtm t, .boxtm s, p =>
      Proof.cut (Proof.weakenTail Δ
        (Proof.K_box (Δ := [eqRec A t s]) (eqRec_symm A (.ax _)))) p
  | _, _, Δ, .VTypeDia A, .dia x _, .diatm _ hx t, .diatm _ _ s, p =>
      .imp_intro (.imp_elim (.weak _ p)
        (Proof.weakenTail Δ
          (Proof.K_dia (Δ₁ := []) (Δ₂ := []) (ψ := (eqRec A s t).neg)
            (φ := (eqRec A t s).neg) x hx
            (.imp_intro (.imp_elim
              (Proof.lookup (x := (eqRec A s t).neg) (List.mem_cons_of_mem _ List.mem_cons_self))
              (eqRec_symm A (Proof.lookup (x := eqRec A t s) List.mem_cons_self)))))))

/-- ⭐Transitivity. -/
def eqRec_trans {σ : Signature} : {Γ : Ctx} → [Γ.NoSlots] → {Δ : List (WFF σ Γ 0)} →
    (T : VarType) → {a : Ann T} → {t s r : Term σ Γ T a} →
    Proof σ Γ Δ (eqRec T t s) → Proof σ Γ Δ (eqRec T s r) → Proof σ Γ Δ (eqRec T t r)
  | _, _, _, .Var, .var, _, _, _, p, q =>
      Proof.conv (eqRec_Var _ _).symm
        (Proof.eq_trans_base (Proof.conv (eqRec_Var _ _) p) (Proof.conv (eqRec_Var _ _) q))
  | _, _, _, .VTypeOne, .one, .unit, .unit, .unit, _, _ => .top_intro
  | _, _, _, .VTypeProd A B, .prod _ _, .pair _ _, .pair _ _, .pair _ _, p, q =>
      .and_intro (eqRec_trans A (.and_elim_l p) (.and_elim_l q))
        (eqRec_trans B (.and_elim_r p) (.and_elim_r q))
  | Γ, _, Δ, .VTypeBox A, .box _, .boxtm t, .boxtm s, .boxtm r, p, q =>
      have h₁ : Proof σ Γ (WFF.box (eqRec A t s) :: WFF.box (eqRec A s r) :: Δ)
          (.box (eqRec A t r)) :=
        Proof.weakenTail Δ (Proof.K_box (Δ := [eqRec A t s, eqRec A s r])
          (eqRec_trans A (Proof.lookup (x := eqRec A t s) List.mem_cons_self)
            (Proof.lookup (x := eqRec A s r) (List.mem_cons_of_mem _ List.mem_cons_self))))
      Proof.cut (Proof.cut h₁ (.weak _ p)) q
  | Γ, _, Δ, .VTypeDia A, .dia x _, .diatm _ hx t, .diatm _ _ s, .diatm _ _ r, p, q =>
      have inner : Proof σ Γ [.dia x hx (eqRec A t r).neg, WFF.boxx x hx (eqRec A t s),
          WFF.boxx x hx (eqRec A s r)] .bot :=
        .dia_bot x hx (Proof.K_dia (Δ₁ := []) (Δ₂ := [eqRec A t s, eqRec A s r])
          (ψ := (eqRec A t r).neg) (φ := .bot) x hx
          (.imp_elim (Proof.lookup (x := (eqRec A t r).neg) List.mem_cons_self)
            (eqRec_trans A (Proof.lookup (x := eqRec A t s) (List.mem_cons_of_mem _ List.mem_cons_self))
              (Proof.lookup (x := eqRec A s r)
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))
      have h₁ : Proof σ Γ (.dia x hx (eqRec A t r).neg :: WFF.boxx x hx (eqRec A t s) ::
          WFF.boxx x hx (eqRec A s r) :: Δ) .bot :=
        Proof.weakenTail Δ inner
      have h₂ : Proof σ Γ (WFF.boxx x hx (eqRec A t s) :: .dia x hx (eqRec A t r).neg ::
          WFF.boxx x hx (eqRec A s r) :: Δ) .bot :=
        Proof.exch [] _ h₁
      have h₃ : Proof σ Γ (.dia x hx (eqRec A t r).neg :: WFF.boxx x hx (eqRec A s r) :: Δ)
          .bot :=
        Proof.cut h₂ (.weak _ (.weak _ p))
      have h₄ : Proof σ Γ (WFF.boxx x hx (eqRec A s r) :: .dia x hx (eqRec A t r).neg :: Δ)
          .bot :=
        Proof.exch [] _ h₃
      .imp_intro (Proof.cut h₄ (.weak _ q))

end Proof

end V12
