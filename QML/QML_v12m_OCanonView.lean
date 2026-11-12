import QML.QML_v12m_LeibnizH

/-!
# QML v12m — the canonical tree with `Opt` on: views with opened witnesses

Under `Opt` a child's language is the `□` view of its parent's with the witnesses **present at the
child** opened (docs §12.22, "Revised: children open their present witnesses").  This file has the
syntax of that:

* `Ctx.optIns Γ L`: `Γ` with the witnesses of the list `L` opened, one `◇⁰` view after another.
  Opening keeps the witnesses, declares each one's content (`Ctx.optIns_content`), and depends on
  `L` only as a set (`Ctx.optIns_le`); the result is presented when `Γ` is.
* ⭐`Proof.unopen`, `Proof.unopens`: **opening a present witness is conservative** — a contradiction
  in the opened language, from hypotheses of the outer one, is a contradiction outside once the
  witnesses are known present (`K_opt`, then `opt_bot`).
-/

namespace V12M

variable [ModalSys]

namespace Ctx

/-- `Γ` with the witnesses of `L` opened, the head opened last. -/
def optIns (Γ : Ctx) : List VarSymb → Ctx
  | [] => Γ
  | y :: L => (Γ.optIns L).optIn y

omit [ModalSys] in
theorem optIns_wit (Γ : Ctx) : ∀ (L : List VarSymb) (y : VarSymb),
    (Γ.optIns L).wit y = Γ.wit y
  | [], _ => rfl
  | _ :: L, y => optIns_wit Γ L y

omit [ModalSys] in
theorem le_optIns (Γ : Ctx) : ∀ L : List VarSymb, Γ.Le (Γ.optIns L)
  | [] => Le.refl Γ
  | y :: L => (le_optIns Γ L).trans (le_optIn _ y)

omit [ModalSys] in
theorem Le.optIns {Γ Γ' : Ctx} (h : Γ.Le Γ') : ∀ L : List VarSymb, (Γ.optIns L).Le (Γ'.optIns L)
  | [] => h
  | y :: L => (Le.optIns h L).optIn y

omit [ModalSys] in
/-- ⭐An opened witness has its content declared. -/
theorem optIns_content {Γ : Ctx} : ∀ {L : List VarSymb} {y : VarSymb} {X : VarType},
    y ∈ L → Γ.wit y = some X → Γ.optIns L (.step y .dia) = some X
  | z :: L, y, X, hy, hw => by
      by_cases hz : y = z
      · subst hz
        change (Γ.optIns L).optIn y (.step y .dia) = some X
        exact optIn_content ((optIns_wit Γ L y).trans hw)
      · have hne : VarSymb.step y .dia ≠ .step z .dia := fun h => hz (by cases h; rfl)
        change (Γ.optIns L).optIn z (.step y .dia) = some X
        rw [optIn_ne hne]
        exact optIns_content ((List.mem_cons.mp hy).resolve_left hz) hw

omit [ModalSys] in
/-- Opening a list stays inside any context that keeps the witnesses and declares the contents of
    those it opens. -/
theorem optIns_le_of {Γ Δ : Ctx} (h : Γ.Le Δ) :
    ∀ {L : List VarSymb}, (∀ y ∈ L, ∀ X, Γ.wit y = some X → Δ (.step y .dia) = some X) →
      (Γ.optIns L).Le Δ
  | [], _ => h
  | y :: L, hL => by
      have ih := optIns_le_of h (L := L) fun z hz => hL z (List.mem_cons_of_mem _ hz)
      refine ⟨fun v T hv => ?_, fun z X hz => h.wit z X ((optIns_wit Γ (y :: L) z).symm.trans hz)⟩
      change (Γ.optIns L).optIn y v = some T at hv
      by_cases hc : v = .step y .dia
      · subst hc
        rcases hw : (Γ.optIns L).wit y with _ | X
        · rw [optIn_content_none hw] at hv
          exact ih _ _ hv
        · rw [optIn_content hw] at hv
          cases hv
          exact hL y List.mem_cons_self _ ((optIns_wit Γ L y).symm.trans hw)
      · rw [optIn_ne hc] at hv
        exact ih _ _ hv

omit [ModalSys] in
/-- ⭐Opening depends on the list only as a set: more witnesses opened, in a larger context, is
    larger. -/
theorem optIns_le {Γ Γ' : Ctx} (h : Γ.Le Γ') {L L' : List VarSymb} (hL : ∀ y ∈ L, y ∈ L') :
    (Γ.optIns L).Le (Γ'.optIns L') :=
  optIns_le_of (h.trans (le_optIns Γ' L')) fun y hy X hw =>
    optIns_content (hL y hy) (h.wit y X hw)

omit [ModalSys] in
theorem RootFresh.optIns {Γ : Ctx} {r : Root} (h : Γ.RootFresh r) :
    ∀ L : List VarSymb, (Γ.optIns L).RootFresh r
  | [] => h
  | y :: L => (RootFresh.optIns h L).optIn y

/-- Opening keeps a presentation. -/
instance presentedOptIns {Γ : Ctx} [h : Γ.Presented] : ∀ L : List VarSymb, (Γ.optIns L).Presented
  | [] => h
  | y :: L =>
      haveI := presentedOptIns (Γ := Γ) L
      inferInstanceAs ((Γ.optIns L).optIn y).Presented

end Ctx

/-! ## Opening is conservative -/

namespace Proof

variable {σ : Signature} (hO : ModalSys.Opt = true)

/-- ⭐**Opening a present witness is conservative**: a contradiction in the view of `y` from
    hypotheses of `Γ` is one in `Γ`, given `◇⁰_y ⊤` (`K_opt` gives `◇⁰_y ⊥`, `opt_bot` the
    rest). -/
def unopen {Γ : Ctx} {y : VarSymb} (hy : ∃ X, Γ.wit y = some X) {Δ : List (WFF σ Γ 0)}
    (p : Proof σ (Γ.optIn y) (Δ.map (WFF.mono (Ctx.le_optIn Γ y))) .bot) :
    Proof σ Γ (.optx hO y hy .top :: Δ) .bot :=
  .opt_bot hO y hy (Proof.K_opt hO y hy (Δ₂ := []) (Δ₁ := Δ) (ψ := .top) (Proof.weak _ p))

/-- `◇⁰_y ⊤` where `y` is a witness, `⊤` otherwise: the presence of `y`. -/
def presence {Γ : Ctx} (y : VarSymb) : WFF σ Γ 0 :=
  match hw : Γ.wit y with
  | some X => .optx hO y ⟨X, hw⟩ .top
  | none => .top

theorem presence_eq {Γ : Ctx} {y : VarSymb} {X : VarType} (hw : Γ.wit y = some X) :
    presence (σ := σ) hO (Γ := Γ) y = .optx hO y ⟨X, hw⟩ .top := by
  unfold presence
  split
  · rfl
  · rename_i hw'
    rw [hw] at hw'
    cases hw'

/-- ⭐Opening a list of present witnesses is conservative. -/
def unopens {Γ : Ctx} {Δ : List (WFF σ Γ 0)} :
    (L : List VarSymb) → (∀ y ∈ L, ∃ X, Γ.wit y = some X) →
    Proof σ (Γ.optIns L) (Δ.map (WFF.mono (Ctx.le_optIns Γ L))) .bot →
    Proof σ Γ (L.map (presence hO (Γ := Γ)) ++ Δ) .bot
  | [], _, p => Proof.castHyps
      ((List.map_congr_left fun φ _ => WFF.mono_refl _ φ).trans (List.map_id Δ)) p
  | y :: L, hL, p =>
      have hy : ∃ X, (Γ.optIns L).wit y = some X := (hL y List.mem_cons_self).imp
        fun _ h => (Ctx.optIns_wit Γ L y).trans h
      have p' : Proof σ (Γ.optIns L) (.optx hO y hy .top ::
          Δ.map (WFF.mono (Ctx.le_optIns Γ L))) .bot :=
        unopen hO hy (Proof.castHyps (by
          rw [List.map_map]
          exact List.map_congr_left fun φ _ => (WFF.mono_mono _ _ φ).symm) p)
      have hpres : WFF.mono (Ctx.le_optIns Γ L) (presence (σ := σ) hO (Γ := Γ) y) =
          .optx hO y hy .top := by
        obtain ⟨X, hX⟩ := hL y List.mem_cons_self
        rw [presence_eq hO hX]
        rfl
      have ih := unopens L (fun z hz => hL z (List.mem_cons_of_mem _ hz))
        (Δ := presence hO y :: Δ) (Proof.castHyps (by rw [List.map_cons, hpres]) p')
      Proof.ofSubset (fun φ hφ => by
        rcases List.mem_append.mp hφ with h | h
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)
        · rcases List.mem_cons.mp h with h | h
          · rw [h]
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ h)) ih

end Proof

end V12M
