import QML.QML_v12m_OCanonChild
import QML.QML_v12m_HereOpt

/-!
# QML v12m — the KT tree with `Opt` on: identity presence and identity names

Under T a world is one of its own successors, along the identity arrow (docs §12.36).  A possible
address `x` of a stage is in its own identity view (`Ctx.witT_of`), so the world's theory decides
whether the identity arrow is in `x`'s extent: **identity presence**, `◇⁰ᵀ_x ⊤`.  No second pass
is needed for it, unlike the children's arrow witnesses (`OCanonChild`).

The content there cannot be declared in the world's language (a `◇`-typed Henkin root appears at a
later stage than its presence could be decided at), so it is **named**: `Proof.opt_nameT` gives
`∃e. ◇⁰ᵀ_x (x.at ≡ e)`, and the world's `∃`-witness property a Henkin root for `e`.

* `IdName w x`: such a name — stages, the root, and the sentence.
* ⭐`exists_idName`: identity presence gives a name.
* `IdPres w x`, `IdPres.name`: presence, and the name chosen for it.  The choice is immaterial: two
  names are `≡` (`Proof.hereO_fun`).
-/

namespace V12M

variable [ModalSys]

namespace TCanon

open Canon

variable {σ : Signature} {N₀ : ℕ} (hT : ModalSys.T = true) (hO : ModalSys.Opt = true)

/-- `◇⁰ᵀ_x ⊤` at a stage where `x` is a possible address: the identity arrow is in `x`'s
    extent. -/
abbrev idPresent {Γ : Ctx} {x : VarSymb} {A : VarType} (hx : Γ.ref x = some (.VTypeDia A)) :
    WFF σ Γ 0 :=
  .optx hO .ident x ⟨A, Ctx.witT_of hT hO hx⟩ .top

/-- ⭐**An identity name** for the possible address `x` at the world `w`: at a stage `i` where `x`
    is a possible address, and a later stage `i₀` with a Henkin root `c`, the theory says
    `◇⁰ᵀ_x (x.at ≡ c)` — `x` is realised at the world itself, its content named by `c`. -/
structure IdName (w : World σ N₀) (x : VarSymb) where
  i : ℕ × ℕ
  A : VarType
  hx : (w.L.ctx i).ref x = some (.VTypeDia A)
  i₀ : ℕ × ℕ
  hi : i ≤ i₀
  c : ℕ
  hc : (w.L.ctx i₀).ref (.root (.free c)) = some A
  hname : (⟨i₀, WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free c)) A hc)
      (WFF.mono ((w.L.ctx_le hi).insert (.bnd 0) A)
        (WFF.optNameT hO (Ctx.witT_of hT hO hx)))⟩ : w.L.sys.Sentence σ) ∈ w.T

/-- ⭐**Identity presence gives a name**: `opt_nameT`, then the world's `∃`-witness property. -/
theorem exists_idName (w : World σ N₀) {i : ℕ × ℕ} {x : VarSymb} {A : VarType}
    (hx : (w.L.ctx i).ref x = some (.VTypeDia A))
    (hp : (⟨i, idPresent hT hO hx⟩ : w.L.sys.Sentence σ) ∈ w.T) :
    Nonempty (IdName hT hO w x) := by
  have hex : (⟨i, .ex A (WFF.optNameT hO (Ctx.witT_of hT hO hx))⟩ :
      w.L.sys.Sentence σ) ∈ w.T :=
    World.mem_of_provable (Δ := [_]) (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hp)
      ⟨Proof.opt_nameT hO (Ctx.witT_of hT hO hx)⟩
  obtain ⟨i₀, hi, c, hc, hmem⟩ := w.exW hex
  exact ⟨⟨i, A, hx, i₀, hi, c, hc, hmem⟩⟩

/-- ⭐**Identity presence**: at some stage where `x` is a possible address, the theory has
    `◇⁰ᵀ_x ⊤`. -/
def IdPres (w : World σ N₀) (x : VarSymb) : Prop :=
  ∃ (i : ℕ × ℕ) (A : VarType) (hx : (w.L.ctx i).ref x = some (.VTypeDia A)),
    (⟨i, idPresent hT hO hx⟩ : w.L.sys.Sentence σ) ∈ w.T

variable {hT hO}

/-- The name chosen for a present address. -/
noncomputable def IdPres.name {w : World σ N₀} {x : VarSymb} (h : IdPres hT hO w x) :
    IdName hT hO w x :=
  (h.elim fun _ h => h.elim fun _ h => h.elim fun hx hp => exists_idName hT hO w hx hp).some

/-- Presence read at a later stage. -/
theorem idPresent_lift (w : World σ N₀) {i j : ℕ × ℕ} (hij : i ≤ j) {x : VarSymb} {A : VarType}
    (hx : (w.L.ctx i).ref x = some (.VTypeDia A))
    (hp : (⟨i, idPresent hT hO hx⟩ : w.L.sys.Sentence σ) ∈ w.T) :
    (⟨j, idPresent hT hO ((w.L.ctx_le hij).ref hx)⟩ : w.L.sys.Sentence σ) ∈ w.T :=
  (World.mem_lift (w := w) hij).mp hp

end TCanon

end V12M
