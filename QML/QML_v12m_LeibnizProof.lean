import QML.QML_v12m_Leibniz

/-!
# QML v12m — Leibniz: hypothesis bookkeeping

* `Proof.discharge`: drop hypotheses that are provable.
* `Proof.box_mono`, `Proof.boxx_mono`: monotonicity of `□` and `□_x` (from K).
* `WFF.conjuncts` and `Proof.conjunct`: a conjunction proves each conjunct (found by search, so
  the proof is computed from a membership proof).
* `eqRec_mono`: weakening commutes with equality at every type.
-/

namespace V12M

variable [ModalSys]

namespace Proof

variable {σ : Signature} {Γ : Ctx}

/-- Discharge hypotheses that are provable. -/
def discharge : {L M : List (WFF σ Γ 0)} → {χ : WFF σ Γ 0} → Proof σ Γ L χ →
    (∀ ℓ ∈ L, Proof σ Γ M ℓ) → Proof σ Γ M χ
  | [], _, _, p, _ => Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) p
  | _ :: _, _, _, p, h =>
      Proof.imp_elim (discharge (Proof.imp_intro p) fun x hx => h x (List.mem_cons_of_mem _ hx))
        (h _ List.mem_cons_self)

/-- `□` is monotone. -/
def box_mono {ψ c : WFF σ Γ.boxIn 0} (p : Proof σ Γ.boxIn [ψ] c) :
    Proof σ Γ [.box ψ] (.box c) :=
  Proof.K_box (Δ := [ψ]) p

/-- `□_x` is monotone. -/
def boxx_mono (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    {ψ c : WFF σ (Γ.diaIn x) 0} (p : Proof σ (Γ.diaIn x) [ψ] c) :
    Proof σ Γ [WFF.boxx x hx ψ] (WFF.boxx x hx c) :=
  .imp_intro (.dia_bot x hx (Proof.K_dia (Δ₁ := []) (Δ₂ := [ψ]) (ψ := c.neg) (φ := .bot) x hx
    (.imp_elim (Proof.lookup (x := c.neg) List.mem_cons_self) (.weak _ p))))

end Proof

/-- The conjuncts of a formula, nested conjunctions flattened. -/
def WFF.conjuncts {σ : Signature} {Γ : Ctx} {d : ℕ} : WFF σ Γ d → List (WFF σ Γ d)
  | .and φ ψ => φ.conjuncts ++ ψ.conjuncts
  | φ => [φ]

/-- Where a conjunct sits in a nest of conjunctions. -/
inductive WFF.ConjPath {σ : Signature} {Γ : Ctx} {d : ℕ} : WFF σ Γ d → WFF σ Γ d → Type where
  | self (φ : WFF σ Γ d) : ConjPath φ φ
  | left {φ₁ φ₂ c : WFF σ Γ d} : ConjPath φ₁ c → ConjPath (.and φ₁ φ₂) c
  | right {φ₁ φ₂ c : WFF σ Γ d} : ConjPath φ₂ c → ConjPath (.and φ₁ φ₂) c

/-- Find the conjunct.  At any depth, so that the recursion is structural. -/
def WFF.conjPath {σ : Signature} {Γ : Ctx} : {d : ℕ} → (ψ : WFF σ Γ d) → {c : WFF σ Γ d} →
    c ∈ ψ.conjuncts → WFF.ConjPath ψ c
  | _, .and φ₁ φ₂, c, h =>
      if h₁ : c ∈ φ₁.conjuncts then .left (WFF.conjPath φ₁ h₁)
      else .right (WFF.conjPath φ₂ ((List.mem_append.mp h).resolve_left h₁))
  | _, .atom _, _, h | _, .eq _ _, _, h | _, .top, _, h | _, .bot, _, h | _, .or _ _, _, h
  | _, .imp _ _, _, h | _, .all _ _, _, h | _, .ex _ _, _, h | _, .box _, _, h
  | _, .dia _ _ _, _, h | _, .here _ _ _, _, h | _, .back _ _ _ _, _, h
  | _, .ret _ _ _, _, h => (List.mem_singleton.mp h).symm ▸ .self _

def Proof.ofConjPath {σ : Signature} {Γ : Ctx} :
    {ψ c : WFF σ Γ 0} → WFF.ConjPath ψ c → Proof σ Γ [ψ] c
  | _, _, .self _ => Proof.ax _
  | .and φ₁ φ₂, _, .left p =>
      Proof.cut (Proof.weakenTail [WFF.and φ₁ φ₂] (Proof.ofConjPath p)) (.and_elim_l (.ax _))
  | .and φ₁ φ₂, _, .right p =>
      Proof.cut (Proof.weakenTail [WFF.and φ₁ φ₂] (Proof.ofConjPath p)) (.and_elim_r (.ax _))

/-- A formula proves each of its conjuncts. -/
def Proof.conjunct {σ : Signature} {Γ : Ctx} {c : WFF σ Γ 0} (ψ : WFF σ Γ 0)
    (h : c ∈ ψ.conjuncts) : Proof σ Γ [ψ] c :=
  Proof.ofConjPath (ψ.conjPath h)

end V12M
