import QML.QML_v12m_GLimit

/-!
# QML v12m — the growing tree: term entries are admissible lifts

Every term entry of every edge is an admissible lifted term (`LiftAdm`: the `□` view tuple, the
η-expansion of a possible address, or — only when the `□`-lift is off — a view tuple), weakened to
the child's language at the lift (`docs/v12-modal-extensions.md` §3 4, D-H3).  Term entries are
made only by the lift (`gliftG`); the other operations make address entries (`gextF`, `ofRen`).

* `AdmEnt`, `LiftEntOk`, `liftEntOk_gnet`, and in the limit ⭐`fmapL_adm`.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature}

/-- An entry is an admissible lifted term of a liftable type, weakened to a later language. -/
def AdmEnt (hF : ModalSys.Four = true) (e : LTerm σ) : Prop :=
  ∃ (e₀ : LTerm σ) (h : e₀.1 <:+ e.1), LiftAdm hF e₀ ∧ e₀.2.1.liftable = true ∧
    e = ⟨e.1, e₀.2.1, e₀.2.2.1, Term.mono (ctxOf_le_of_suffix h) e₀.2.2.2⟩

namespace GNetSt

/-- Every term entry of every edge is an admissible lifted term. -/
def LiftEntOk (hF : ModalSys.Four = true) (N : GNetSt σ) : Prop :=
  ∀ k v e, N.fmap k v = .inr e → AdmEnt hF e

variable {hF : ModalSys.Four = true} {N : GNetSt σ}

theorem LiftEntOk.setSt (hL : N.LiftEntOk hF) (s : Node) (t : NodeSt σ) :
    (N.setSt s t).LiftEntOk hF := hL

theorem LiftEntOk.setFwd (hL : N.LiftEntOk hF) (k : Node) (cl : List VarType)
    {f : VarSymb → LEnt σ} (hf : ∀ v e, f v = .inr e → AdmEnt hF e) :
    (N.setFwd k cl f).LiftEntOk hF := by
  intro k' v e he
  change Function.update N.fmap k f k' v = .inr e at he
  by_cases hk : k' = k
  · subst hk
    rw [Function.update_self] at he
    exact hf v e he
  · rw [Function.update_of_ne hk] at he
    exact hL k' v e he

theorem LiftEntOk.newChild (hL : N.LiftEntOk hF) (s : Node) (kd : Option VarSymb)
    (t : NodeSt σ) (g : VarSymb → VarSymb) : (N.newChild s kd t (ofRen g)).LiftEntOk hF := by
  intro k' v e he
  change Function.update N.fmap (N.nch s :: s) (ofRen g) k' v = .inr e at he
  by_cases hk : k' = N.nch s :: s
  · subst hk
    rw [Function.update_self] at he
    cases he
  · rw [Function.update_of_ne hk] at he
    exact hL k' v e he

theorem LiftEntOk.realF (hL : N.LiftEntOk hF) (k : Node) : (N.realF hF k).LiftEntOk hF := by
  match k with
  | [] => exact hL
  | c :: p =>
      simp only [GNetSt.realF]
      split_ifs
      · refine (hL.setSt _ _).setFwd _ _ fun v e he => ?_
        match v, he with
        | .root _, he => exact hL _ _ e he
        | .step u s, he =>
            simp only [gextF] at he
            split_ifs at he
            · exact hL _ _ e he
      · exact hL

theorem LiftEntOk.iterate_realF (k : Node) :
    ∀ (j : ℕ) {N : GNetSt σ}, N.LiftEntOk hF → ((fun N' => N'.realF hF k)^[j] N).LiftEntOk hF
  | 0, _, hL => hL
  | j + 1, _, hL => by
      rw [Function.iterate_succ_apply]
      exact LiftEntOk.iterate_realF k j (hL.realF k)

theorem LiftEntOk.catchUp (hL : N.LiftEntOk hF) (k : Node) : (N.catchUp hF k).LiftEntOk hF := by
  match k with
  | [] => exact hL
  | c :: p => exact LiftEntOk.iterate_realF (c :: p) _ hL

theorem LiftEntOk.lift (hL : N.LiftEntOk hF) (k : Node) (o : LTerm σ) :
    (N.lift hF k o).LiftEntOk hF := by
  match k, o with
  | [], _ => exact hL
  | c :: p, ⟨l, T, a, t⟩ =>
      simp only [GNetSt.lift]
      split_ifs with hcl h hl hv
      · refine ((hL.setSt _ _).setSt _ _).setFwd _ _ fun v e he => ?_
        match v, he with
        | .root _, he => exact hL _ _ e he
        | .step u s, he =>
            simp only [gliftG] at he
            split_ifs at he with h₁ h₂
            · cases he
              exact ⟨⟨l, T, a, t⟩, h, hv.1, hl, rfl⟩
            · exact hL _ _ e he
      all_goals exact hL

theorem LiftEntOk.henk (hL : N.LiftEntOk hF) (s : Node)
    (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : (N.henk s o).LiftEntOk hF := by
  obtain ⟨l, φ⟩ := o
  simp only [GNetSt.henk]
  split_ifs
  · split
    · split_ifs
      · exact hL.setSt _ _
      · exact hL
    · split_ifs
      · exact hL.setSt _ _
      · exact hL
    · exact hL
  · exact hL

theorem LiftEntOk.mkChild (hL : N.LiftEntOk hF) (s : Node)
    (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : (N.mkChild hF s o).LiftEntOk hF := by
  obtain ⟨l, φ⟩ := o
  simp only [GNetSt.mkChild]
  split_ifs
  · split
    · split_ifs
      · exact hL
      · exact hL.newChild _ _ _ _
    · split_ifs
      · split
        · exact hL.newChild _ _ _ _
        · exact hL
      · exact hL
    · exact hL
  · exact hL

theorem LiftEntOk.applyOp (hL : N.LiftEntOk hF) (o : GOp σ) : (N.applyOp hF o).LiftEntOk hF := by
  rcases o with ⟨s, o⟩ | ⟨s, o⟩ | k | ⟨k, n⟩
  · simp only [GNetSt.applyOp]
    split_ifs
    · exact hL.henk s o
    · exact hL
  · simp only [GNetSt.applyOp]
    split_ifs
    · exact hL.mkChild s o
    · exact hL
  · simp only [GNetSt.applyOp]
    split_ifs
    · exact hL.realF k
    · exact hL
  · simp only [GNetSt.applyOp]
    split_ifs
    · exact (hL.catchUp k).lift k n
    · exact hL

theorem liftEntOk_init {l₀ : List VarType} (M₀ : Set (WFF σ (ctxOf l₀) 0)) :
    (init M₀).LiftEntOk hF :=
  fun _ _ _ he => nomatch he

end GNetSt

/-- ⭐Every network of the chain has admissible term entries. -/
theorem liftEntOk_gnet [Countable σ.FuncSyms] [Countable σ.RelSyms] (hF : ModalSys.Four = true)
    {l₀ : List VarType} (M₀ : Set (WFF σ (ctxOf l₀) 0)) : ∀ n, (gnet hF M₀ n).LiftEntOk hF
  | 0 => GNetSt.liftEntOk_init M₀
  | n + 1 => (liftEntOk_gnet hF M₀ n).applyOp (gsched n)

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-- ⭐**In the limit, every term entry is an admissible lifted term**, weakened. -/
theorem fmapL_adm {k : Node} {v : VarSymb} {e : LTerm σ} (h : fmapL hF M₀ k v = .inr e) :
    AdmEnt hF e := by
  unfold fmapL at h
  split_ifs at h
  exact liftEntOk_gnet hF M₀ _ k v e h

end GArrow

end V12M
