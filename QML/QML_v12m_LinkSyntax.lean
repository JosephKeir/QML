import QML.QML_v12m_BackSyntax

/-!
# QML v12m — links: the hole, and the statements of weak 5 without 4

Without 4 a possible object moved across is named only by a link, `□[d ↦ t] Φ(d)` (`WFF.link`),
and what a rule says of it is said by a formula **closed apart from one hole**, the link's slot:
the side view (`docs/v12-modal-extensions.md`, "K5 and KD5: the substitution check, F2").  The
origin's `□`-parameters have no image along an arrow across, so they are not in it; generality
comes by pairing, the hole's term carrying them where they are in scope.

* The hole is `WFF.holeAt`, as for the returning possibility (`QML_v12m_BackSyntax`).
* `WFF.linkHole`: `□[d ↦ t] χ(d)`; `WFF.sideDia`: `◇_d χ(d.dia)` for the slot `d`.
-/

namespace V12M

variable [ModalSys]

variable {σ : Signature}

variable (hV : ModalSys.Five = true) (hN : ModalSys.Four = false)

/-- ⭐`□[d ↦ t] χ(d)` at depth `d` of `Γ`: the link with its body `χ` closed apart from the slot. -/
def WFF.linkHole {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {D : DShape} {a : Ann D.ty}
    (t : Term σ Γ D.ty a) (χ : WFF σ (Ctx.empty.insert (.bnd 0) D.ty) 1) : WFF σ Γ d :=
  .link hV hN t (WFF.holeAt (hs.boxIn.insert _)
    (Term.eta (.root (.bnd d)) D.ty (Ctx.ref_insert_root _ _ _)) χ)

/-- ⭐`◇_d χ(d.dia)` for the slot `d : ◇A` of a link at depth `d`. -/
def WFF.sideDia {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {A : VarType}
    (χ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) :
    WFF σ (Γ.boxIn.insert (.bnd d) (.VTypeDia A)) (d + 1) :=
  .dia (.root (.bnd d)) ⟨A, Ctx.ref_insert_root _ _ _⟩
    (WFF.holeAt ((hs.boxIn.insert _).diaIn _)
      (Term.eta (.step (.root (.bnd d)) .dia) A (Ctx.ref_diaIn_of (Ctx.ref_insert_root _ _ _)))
      χ)

end V12M
