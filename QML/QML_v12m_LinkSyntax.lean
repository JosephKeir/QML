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

/-- ⭐`□[d ↦ t] χ(⟨n.box, d⟩)` at depth `d` of `Γ`: the link, with the values of a necessary
    object `n : □B` of `Γ` beside the slot in the hole.  What the gather speaks of. -/
def WFF.linkHoleN {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {B : VarType} (n : VarSymb)
    (hn : Γ.ref n = some (.VTypeBox B)) {D : DShape} {a : Ann D.ty} (t : Term σ Γ D.ty a)
    (χ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd B D.ty)) 1) : WFF σ Γ d :=
  .link hV hN t (WFF.holeAt (hs.boxIn.insert _)
    (.pair (Term.mono (Ctx.le_insert hs.boxIn.root _) (Term.eta n.inner B (Ctx.ref_inner hn)))
      (Term.eta (.root (.bnd d)) D.ty (Ctx.ref_insert_root _ _ _))) χ)

/-- ⭐**U with objects, without 4** (docs, "K5 and KD5: U and the gather without 4"), closed:
    `□∀k:□B. ∀q:D.ty. (□[d ↦ q] χ(⟨k.box, d⟩) → ∃c:B. χ(⟨c, q⟩))`.  Every world an arrow reaches
    has a loop, `side a a`, which a necessary object's value along it names, and which moves the
    possible objects there to themselves (`Frame.side_loop`): T's collapse under a `□`, with `∃`
    in place of `here`. -/
def WFF.fiveReflL {B : VarType} {D : DShape}
    (χ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd B D.ty)) 1) : WFF σ Ctx.empty 0 :=
  have h₁ := (Ctx.NoSlots.slots (Γ := Ctx.empty.boxIn)).insert (.VTypeBox B)
  have h₂ := h₁.insert D.ty
  .box (.all (.VTypeBox B) (.all D.ty (.imp
    (WFF.linkHoleN hV hN h₂ (.root (.bnd 0))
      ((Ctx.le_insert h₁.root D.ty).ref (Ctx.ref_insert_root _ _ _))
      (Term.eta (.root (.bnd 1)) D.ty (Ctx.ref_insert_root _ _ _)) χ)
    (.ex B (WFF.holeAt (h₂.insert B)
      (.pair (Term.eta (.root (.bnd 2)) B (Ctx.ref_insert_root _ _ _))
        (Term.eta (.root (.bnd 1)) D.ty
          ((Ctx.le_insert h₂.root B).ref (Ctx.ref_insert_root _ _ _)))) χ)))))

namespace OutLeg

variable {Γ : Ctx}

/-- ⭐**A link along the leg**, existentially: `◇[d ↦ t] Φ` from some arrow, or `◇_y[d ↦ t] Φ`
    from an arrow of `y`'s extent, with `Φ` read in the leg's view (as `OutLeg.retS`). -/
def linkDia {d : ℕ} : (O : OutLeg Γ) → {D : DShape} → {a : Ann D.ty} → Term σ Γ D.ty a →
    WFF σ (O.view.insert (.bnd d) D.ty) (d + 1) → WFF σ Γ d
  | .nec, _, _, t, Φ => WFF.neg (.link hV hN t (WFF.neg Φ))
  | .pos y hy, _, _, t, Φ => .linkx hV hN y hy t Φ

end OutLeg

end V12M
