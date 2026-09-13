import QML.QML_v12m_Eq

/-!
# QML v12m — argument spines and holes

The part of the Leibniz development the canonical model needs: argument spines (`Spine`), holes in
argument position (`instantiate_funcHole`, `instantiate_relHole`), lists of proofs and
discharging them.

The general Leibniz principle of K (provably equal substitutions, `SubE.EqE`) tracks equalities by
membership among the hypotheses, which is what lets them pass under `□` and `◇_x`.  Under T the
`here` component of a necessary entry needs the collapsed equality, which T proves but which is
not a hypothesis, so that bookkeeping does not carry over as it stands.  It is not needed for
completeness, and completeness gives the principle back.
-/

namespace V12M

variable [ModalSys]

/-! ## Argument spines -/

/-- The arguments still to be supplied to a function or relation symbol, outermost first. -/
inductive Spine (σ : Signature) (Δ : Ctx) : ℕ → Type where
  | nil : Spine σ Δ 0
  | cons {n : ℕ} : Term σ Δ .Var .var → Spine σ Δ n → Spine σ Δ (n + 1)

namespace Spine

variable {σ : Signature}

def fill {Δ : Ctx} : {n : ℕ} → Spine σ Δ n → Func σ Δ n → Func σ Δ 0
  | _, .nil, f => f
  | _, .cons t S, f => S.fill (.eval f t)

def fillR {Δ : Ctx} : {n : ℕ} → Spine σ Δ n → Rel σ Δ n → Rel σ Δ 0
  | _, .nil, ρ => ρ
  | _, .cons t S, ρ => S.fillR (.eval ρ t)

def mono {Δ Δ' : Ctx} (h : Δ.Le Δ') : {n : ℕ} → Spine σ Δ n → Spine σ Δ' n
  | _, .nil => .nil
  | _, .cons t S => .cons (Term.mono h t) (S.mono h)

def subst {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) : {n : ℕ} → Spine σ Γ n → Spine σ Δ n
  | _, .nil => .nil
  | _, .cons t S => .cons (Term.subst ι θ hθ hc t) (S.subst θ hθ hc)

theorem subst_fill {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) : ∀ {n : ℕ} (S : Spine σ Γ n) (f : Func σ Γ n),
    Func.subst ι θ hθ hc (S.fill f) = (S.subst θ hθ hc).fill (Func.subst ι θ hθ hc f)
  | _, .nil, _ => rfl
  | _, .cons t S, f => subst_fill θ hθ hc S (.eval f t)

theorem subst_fillR {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) : ∀ {n : ℕ} (S : Spine σ Γ n) (ρ : Rel σ Γ n),
    Rel.subst ι θ hθ hc (S.fillR ρ) = (S.subst θ hθ hc).fillR (Rel.subst ι θ hθ hc ρ)
  | _, .nil, _ => rfl
  | _, .cons t S, ρ => subst_fillR θ hθ hc S (.eval ρ t)

theorem subst_mono_id {ι : VarSymb → VarSymb} {Γ Γ' : Ctx} (hle : Γ.Le Γ') (θ : Subst σ Γ)
    (hθ : Subst.Ok Γ' θ) (hc : Subst.Coh ι Γ' θ)
    (hid : ∀ v, Γ.ref v = some .Var → θ.at v = .ren v) :
    ∀ {n : ℕ} (S : Spine σ Γ n), (S.mono hle).subst θ hθ hc = S
  | _, .nil => rfl
  | _, .cons t S => by
      change Spine.cons (Term.subst ι θ hθ hc (Term.mono hle t)) ((S.mono hle).subst θ hθ hc) = _
      rw [Term.subst_mono_id ι hle θ hθ hc hid t, subst_mono_id hle θ hθ hc hid S]

end Spine

theorem Rel.subst_mono_id {σ : Signature} {ι : VarSymb → VarSymb} {Γ Γ' : Ctx} (hle : Γ.Le Γ')
    (θ : Subst σ Γ) (hθ : Subst.Ok Γ' θ) (hc : Subst.Coh ι Γ' θ)
    (hid : ∀ v, Γ.ref v = some .Var → θ.at v = .ren v) :
    ∀ {n : ℕ} (ρ : Rel σ Γ n), Rel.subst ι θ hθ hc (Rel.mono hle ρ) = ρ
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.subst ι θ hθ hc (Rel.mono hle ρ))
        (Term.subst ι θ hθ hc (Term.mono hle t)) = _
      rw [Rel.subst_mono_id hle θ hθ hc hid ρ, Term.subst_mono_id ι hle θ hθ hc hid t]

/-! ## Holes in argument position -/

section Holes

variable {σ : Signature} {Δ : Ctx} [Δ.NoSlots]

abbrev holeLe : Δ.Le (Δ.insert (.bnd 0) .Var) := Ctx.le_insert Ctx.NoSlots.slots.root .Var

/-- The hole: the slot `bnd 0`. -/
def hole : Term σ (Δ.insert (.bnd 0) .Var) .Var .var :=
  .var (.root (.bnd 0)) (Ctx.ref_insert_root Δ _ _)

theorem single_hid (b : Term σ Δ .Var .var) :
    ∀ v, Δ.ref v = some .Var → (Subst.single (σ := σ) (.bnd 0) (.tm b)).at v = .ren v :=
  fun _ hv => Subst.single_at_ne (Ctx.NoSlots.ref_bnd0 hv)

theorem instantiate_funcHole (L : Term σ Δ .Var .var) {n : ℕ} (S : Spine σ Δ n)
    (G : Func σ Δ (n + 1)) (b : Term σ Δ .Var .var) :
    WFF.instantiate Ctx.NoSlots.slots b (WFF.eq (Term.mono holeLe L)
        (Term.func ((Spine.cons hole (S.mono holeLe)).fill (Func.mono holeLe G)))) =
      WFF.eq L (Term.func ((Spine.cons b S).fill G)) := by
  change WFF.eq (Term.subst _ _ _ _ (Term.mono holeLe L))
    (Term.func (Func.subst _ _ _ _ ((Spine.cons hole (S.mono holeLe)).fill (Func.mono holeLe G))))
    = _
  rw [Term.subst_mono_id _ _ _ _ _ (single_hid b), Spine.subst_fill]
  change WFF.eq L (Term.func (Spine.fill (Spine.cons (SubE.toVar (.tm b) rfl)
    (Spine.subst _ _ _ (S.mono holeLe))) (Func.subst _ _ _ _ (Func.mono holeLe G)))) = _
  rw [SubE.toVar_tm, Spine.subst_mono_id _ _ _ _ (single_hid b),
    Func.subst_mono_id _ _ _ _ _ (single_hid b)]

theorem instantiate_relHole {n : ℕ} (S : Spine σ Δ n) (ρ : Rel σ Δ (n + 1))
    (b : Term σ Δ .Var .var) :
    WFF.instantiate Ctx.NoSlots.slots b
        (WFF.atom ((Spine.cons hole (S.mono holeLe)).fillR (Rel.mono holeLe ρ))) =
      WFF.atom ((Spine.cons b S).fillR ρ) := by
  change WFF.atom (Rel.subst _ _ _ _ ((Spine.cons hole (S.mono holeLe)).fillR (Rel.mono holeLe ρ)))
    = _
  rw [Spine.subst_fillR]
  change WFF.atom (Spine.fillR (Spine.cons (SubE.toVar (.tm b) rfl)
    (Spine.subst _ _ _ (S.mono holeLe))) (Rel.subst _ _ _ _ (Rel.mono holeLe ρ))) = _
  rw [SubE.toVar_tm, Spine.subst_mono_id _ _ _ _ (single_hid b),
    Rel.subst_mono_id _ _ _ _ (single_hid b)]

end Holes

/-! ## Lists of proofs -/

/-- A proof of every formula of a list, from the hypotheses `M`. -/
inductive Proofs (σ : Signature) (Γ : Ctx) (M : List (WFF σ Γ 0)) : List (WFF σ Γ 0) → Type where
  | nil : Proofs σ Γ M []
  | cons {ℓ : WFF σ Γ 0} {L : List (WFF σ Γ 0)} :
      Proof σ Γ M ℓ → Proofs σ Γ M L → Proofs σ Γ M (ℓ :: L)

namespace Proofs

variable {σ : Signature} {Γ : Ctx} {M : List (WFF σ Γ 0)}

def append : {L₁ L₂ : List (WFF σ Γ 0)} → Proofs σ Γ M L₁ → Proofs σ Γ M L₂ →
    Proofs σ Γ M (L₁ ++ L₂)
  | _, _, .nil, q => q
  | _, _, .cons p ps, q => .cons p (append ps q)

def ofMap {Γ' : Ctx} (f : WFF σ Γ' 0 → WFF σ Γ 0) :
    (L : List (WFF σ Γ' 0)) → (∀ c ∈ L, Proof σ Γ M (f c)) → Proofs σ Γ M (L.map f)
  | [], _ => .nil
  | c :: L, h =>
      .cons (h c List.mem_cons_self) (ofMap f L fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

def ofMem : (L : List (WFF σ Γ 0)) → (∀ c ∈ L, Proof σ Γ M c) → Proofs σ Γ M L
  | [], _ => .nil
  | c :: L, h =>
      .cons (h c List.mem_cons_self) (ofMem L fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

end Proofs

/-- ⭐Discharge a list of hypotheses by proofs of them. -/
def Proof.dischargeAll {σ : Signature} {Γ : Ctx} {M : List (WFF σ Γ 0)} :
    {L : List (WFF σ Γ 0)} → {χ : WFF σ Γ 0} → Proof σ Γ L χ → Proofs σ Γ M L → Proof σ Γ M χ
  | [], _, p, .nil => Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) p
  | _ :: _, _, p, .cons q qs => Proof.imp_elim (dischargeAll (Proof.imp_intro p) qs) q

omit [ModalSys] in
theorem List.sub_cons_cons {α : Type} (a b : α) (l : List α) : ∀ x ∈ a :: l, x ∈ a :: b :: l :=
  fun x hx => (List.mem_cons.mp hx).elim (fun h => by subst h; exact List.mem_cons_self)
    (fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))

end V12M
