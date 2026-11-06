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

/-- ⭐**The link along the leg**: `□[d ↦ t] Φ` along every arrow, or `◇_y[d ↦ t] Φ` along some
    arrow of `y`'s extent; the leg's primitive modality (`OutLeg.prim`) with the slot carried. -/
def linkL {d : ℕ} : (O : OutLeg Γ) → {D : DShape} → {a : Ann D.ty} → Term σ Γ D.ty a →
    WFF σ (O.view.insert (.bnd d) D.ty) (d + 1) → WFF σ Γ d
  | .nec, _, _, t, Φ => .link hV hN t Φ
  | .pos y hy, _, _, t, Φ => .linkx hV hN y hy t Φ

/-- The leg's primitive modality: `□`, or `◇_y`. -/
def prim {d : ℕ} : (O : OutLeg Γ) → WFF σ O.view d → WFF σ Γ d
  | .nec, φ => .box φ
  | .pos y hy, φ => .dia y hy φ

end OutLeg

/-- `□_y[d ↦ t] Φ`, the dual of `◇_y[d ↦ t]`: along every arrow of `y`'s extent.  What `K_dia`'s
    `□_x` hypotheses are for `linkx_K`. -/
def WFF.linkxBox {Γ : Ctx} {d : ℕ} (y : VarSymb) (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y))
    {D : DShape} {a : Ann D.ty} (t : Term σ Γ D.ty a)
    (Φ : WFF σ ((Γ.diaIn y).insert (.bnd d) D.ty) (d + 1)) : WFF σ Γ d :=
  WFF.neg (.linkx hV hN y hy t (WFF.neg Φ))

omit [ModalSys] in
theorem Ctx.RootFresh.of_le {Γ Γ' : Ctx} {r : Root} (hle : Γ.Le Γ') (h : Γ'.RootFresh r) :
    Γ.RootFresh r := by
  intro v hv
  cases hΓ : Γ v with
  | none => rfl
  | some T =>
      have := hle v T hΓ
      rw [h v hv] at this
      cases this

/-! ## Maps of tuples

A link's tuple is rearranged by projections, pairing and unit; moving across commutes with that
(`Model.sideOf` is componentwise), which is `Proof.link_map`.  `ret_map`'s `ShapeMap` is the
precedent; here no item has a value to come back as, so a map is just where each possible object
of the target is found in the source. -/

/-- A **place of a tuple shape** holding a possible object `◇A`. -/
inductive DShape.Pos : DShape → VarType → Type where
  | here (A : VarType) : DShape.Pos (.dia A) A
  | fst {D : DShape} (E : DShape) {A : VarType} : DShape.Pos D A → DShape.Pos (.prod D E) A
  | snd (D : DShape) {E : DShape} {A : VarType} : DShape.Pos E A → DShape.Pos (.prod D E) A

/-- ⭐A **map of tuple shapes** `D → E`: for each possible object of `E`, its place in `D`. -/
def DShape.Map (D : DShape) : DShape → Type
  | .one => Unit
  | .dia A => D.Pos A
  | .prod E₁ E₂ => D.Map E₁ × D.Map E₂

/-- The object at a place of the tuple at address `v`, as an η-term. -/
def DShape.Pos.tm {Γ : Ctx} : {D : DShape} → {A : VarType} → D.Pos A → (v : VarSymb) →
    Γ.ref v = some D.ty → Σ b, Term σ Γ (.VTypeDia A) b
  | _, _, .here A, v, h => ⟨_, Term.eta v (.VTypeDia A) h⟩
  | _, _, .fst _ p, v, h => p.tm (.step v .fst) (Ctx.ref_fst_of h)
  | _, _, .snd _ p, v, h => p.tm (.step v .snd) (Ctx.ref_snd_of h)

/-- The tuple at address `v`, rearranged by a map. -/
def DShape.Map.tm {Γ : Ctx} {D : DShape} (v : VarSymb) (h : Γ.ref v = some D.ty) :
    (E : DShape) → D.Map E → Σ b, Term σ Γ E.ty b
  | .one, _ => ⟨_, .unit⟩
  | .dia _, p => DShape.Pos.tm (σ := σ) (D := D) p v h
  | .prod E₁ E₂, f => ⟨_, .pair (DShape.Map.tm v h E₁ f.1).2 (DShape.Map.tm v h E₂ f.2).2⟩

/-- ⭐A map as a **hole term**: the hole's tuple rearranged. -/
def DShape.Map.hole {D E : DShape} (f : D.Map E) :
    Σ b, Term σ (Ctx.empty.insert (.bnd 0) D.ty) E.ty b :=
  DShape.Map.tm (.root (.bnd 0)) (Ctx.ref_insert_root _ _ _) E f

end V12M
