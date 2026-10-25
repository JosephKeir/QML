import QML.QML_v12m_GTemplate

/-!
# QML v12m — the growing tree: leaves of shapes

Predicates on the leaves of shapes: `Shp.AllL`, families (`IsFam`), and that below a `□` at the
top every leaf of a well-formed shape is a family (`allL_isFam_of_wf`).  And where an edge keeps a
witness whose kept item is an address (`wit_of_inl`).
-/

namespace V12M

universe uL

/-- Every leaf of a shape satisfies `Q`. -/
def Shp.AllL {L : Type*} (Q : L → Prop) : {A : VarType} → Shp L A → Prop
  | _, .var => True
  | _, .one => True
  | _, .prod a b => Shp.AllL Q a ∧ Shp.AllL Q b
  | _, .box a => Shp.AllL Q a
  | _, .dia ℓ a => Q ℓ ∧ Shp.AllL Q a

namespace Shp

variable {L L' : Type uL} {Q : L → Prop}

theorem allL_map {Q' : L' → Prop} {g : L → L'} (hg : ∀ ℓ, Q ℓ → Q' (g ℓ)) :
    ∀ {A : VarType} (a : Shp L A), a.AllL Q → (a.map g).AllL Q'
  | _, .var, _ => trivial
  | _, .one, _ => trivial
  | _, .prod a b, h => ⟨allL_map hg a h.1, allL_map hg b h.2⟩
  | _, .box a, h => allL_map hg a h
  | _, .dia ℓ a, h => ⟨hg ℓ h.1, allL_map hg a h.2⟩

theorem allL_map_all {Q' : L' → Prop} {g : L → L'} (hg : ∀ ℓ, Q' (g ℓ)) :
    ∀ {A : VarType} (a : Shp L A), (a.map g).AllL Q'
  | _, .var => trivial
  | _, .one => trivial
  | _, .prod a b => ⟨allL_map_all hg a, allL_map_all hg b⟩
  | _, .box a => allL_map_all hg a
  | _, .dia ℓ a => ⟨hg ℓ, allL_map_all hg a⟩

theorem allL_mono {Q' : L → Prop} (hq : ∀ ℓ, Q ℓ → Q' ℓ) :
    ∀ {A : VarType} (a : Shp L A), a.AllL Q → a.AllL Q'
  | _, .var, _ => trivial
  | _, .one, _ => trivial
  | _, .prod a b, h => ⟨allL_mono hq a h.1, allL_mono hq b h.2⟩
  | _, .box a, h => allL_mono hq a h
  | _, .dia _ a, h => ⟨hq _ h.1, allL_mono hq a h.2⟩

end Shp

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-! ## Leaves -/

/-- A family. -/
def IsFam {s : GW hF M₀} : GLeaf hF M₀ s → Prop
  | .root _ _ => False
  | .fam _ => True

/-- Below a `□` at the top, every leaf of a well-formed shape is a family. -/
theorem allL_isFam_of_wf {s : GW hF M₀} :
    ∀ (lw : List Bool) {T : VarType} (S : GShape hF M₀ s T),
      Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) (true :: lw) S → S.AllL IsFam
  | _, _, .var, _ => trivial
  | _, _, .one, _ => trivial
  | lw, _, .prod a b, h => ⟨allL_isFam_of_wf lw a h.1, allL_isFam_of_wf lw b h.2⟩
  | lw, _, .box a, h => allL_isFam_of_wf (lw ++ [true]) a h
  | lw, _, .dia ℓ a, h => by
      refine ⟨?_, allL_isFam_of_wf (lw ++ [false]) a h.2⟩
      match ℓ, h.1 with
      | .root _ _, h₁ => exact absurd ((Arrows.Leaf.wf_root _ _).mp h₁).2 (by simp)
      | .fam _, _ => trivial

omit [ModalSys] in
theorem ctxOf_step : ∀ (l : List VarType) (v : VarSymb) (st : Step), ctxOf l (.step v st) = none
  | [], _, _ => rfl
  | A :: l, v, st => by
      rw [ctxOf_cons]
      change (if VarSymb.step v st = .root (.free l.length) then some A else ctxOf l _) = none
      rw [if_neg (by simp)]
      exact ctxOf_step l v st

/-- The kept witness of an address whose kept item is an address is that address. -/
theorem wit_of_inl {t : GW hF M₀} {x y : VarSymb} (hx : PPath x.path)
    (h : fmapL hF M₀ t.1 (.step x .keep) = .inl y) : wit t x = y := by
  have e := eIdx_item (fmapL hF M₀ t.1) hx (s := .keep) rfl []
  change eIdx _ ((VarSymb.step x .keep).ext []) = _
  rw [e, h]
  rfl

end GArrow

end V12M
