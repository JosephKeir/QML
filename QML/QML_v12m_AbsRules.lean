import QML.QML_v12m_Abs
import QML.QML_v12m_ProofSubst

/-!
# QML v12m — the realisation rules pinned at an arbitrary address (strong T)

`Proof.here_elim` and `Proof.here_intro` are stated at an arbitrary `◇`-typed address already, but
about a formula *presented as a hole formula read in the view*.  To use them at a given view formula
one has to abstract it, which `QML_v12m_Abs` now does at any declared address — so the **pinned**
forms generalise from a root to an address with no change of content:

* ⭐`Proof.here_elimAtA`: `Here x t, □_x χ ⊢ χ(t)`, the rule the canonical model states as
  `RealDatum.spec`;
* ⭐`Proof.here_introAtA`: `Here x t, χ(t) ⊢ ◇_x χ`, its converse.

Both read the view formula through `WFF.viewReadAtA_diaAbsA` (the round trip) and
`WFF.viewReadTm_eta`, which was already general in the address.  The only hypothesis beyond the
declaration is that the context is presented — the naming discipline that keeps an address to one
view depth (`Ctx.ViewFresh`, §2d and §9).
-/

namespace V12M

variable [ModalSys] {σ : Signature}

/-- ⭐**Elimination, pinned at an arbitrary address**: `Here x t, □_x χ ⊢ χ(t)`. -/
def Proof.here_elimAtA {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)} (hT : ModalSys.T = true)
    (x : VarSymb) {A : VarType}
    (hxA : Γ.ref x = some (.VTypeDia A)) {a : Ann A} (t : Term σ Γ A a)
    (χ : WFF σ (Γ.diaIn x) 0)
    (ph : Proof σ Γ Δ (WFF.hereAt hT x hxA t))
    (pb : Proof σ Γ Δ (WFF.boxx x ⟨A, hxA⟩ χ)) :
    Proof σ Γ Δ (WFF.realiseAtA hT x hxA t χ) :=
  Proof.here_elim hT x ⟨A, hxA⟩ t
    (Term.eta (.step x .dia) A (Ctx.ref_diaIn_of hxA))
    (WFF.diaAbsA x hxA χ) ph
    (Proof.conv (congrArg (WFF.boxx x ⟨A, hxA⟩)
      ((WFF.viewReadAtA_diaAbsA x hxA χ).symm.trans
        (WFF.viewReadTm_eta hxA (WFF.diaAbsA x hxA χ)).symm)) pb)

/-- ⭐**Introduction, pinned at an arbitrary address**: `Here x t, χ(t) ⊢ ◇_x χ`. -/
def Proof.here_introAtA {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)} (hT : ModalSys.T = true)
    (x : VarSymb) {A : VarType}
    (hxA : Γ.ref x = some (.VTypeDia A)) {a : Ann A} (t : Term σ Γ A a)
    (χ : WFF σ (Γ.diaIn x) 0)
    (ph : Proof σ Γ Δ (WFF.hereAt hT x hxA t))
    (pr : Proof σ Γ Δ (WFF.realiseAtA hT x hxA t χ)) :
    Proof σ Γ Δ (WFF.dia x ⟨A, hxA⟩ χ) :=
  Proof.conv (congrArg (WFF.dia x ⟨A, hxA⟩)
      ((WFF.viewReadTm_eta hxA (WFF.diaAbsA x hxA χ)).trans
        (WFF.viewReadAtA_diaAbsA x hxA χ)))
    (Proof.here_intro hT x ⟨A, hxA⟩ t
      (Term.eta (.step x .dia) A (Ctx.ref_diaIn_of hxA))
      (WFF.diaAbsA x hxA χ) ph pr)

end V12M
