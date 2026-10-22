import QML.QML_v12m_BNetS

/-!
# QML v12m — strong B's rows 3–4 on the network: every edge is labelled both ways

Under rows 3–4 (`BStrongW`) the network makes only doubly witnessed children (`mkRetXDC`), so
every live child has a kind (the witness its arrow lies in the extent of) and a back kind (the
witness its way home lies in the extent of): ⭐`NetSt.Labelled`, kept by every operation
(`Labelled.applyOpT`), and so by the strong chain (`labelled_netS`).  It is what the canonical
model reads to meet `Model.posBack_exists` (docs §11.23, paper check 2).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

namespace NetSt

/-- ⭐Every live child has a kind and a back kind. -/
def Labelled (N : NetSt σ) : Prop :=
  ∀ c p, N.Live (c :: p) → N.kind (c :: p) ≠ none ∧ N.bkind (c :: p) ≠ none

theorem Labelled.init {l₀ : List VarType} (M₀ : Set (WFF σ (ctxOf l₀) 0)) :
    (init M₀).Labelled :=
  fun _ _ h => absurd (init_live h) (by simp)

/-- An operation that makes no child and changes no kind keeps the labels. -/
theorem Labelled.of_same {N N' : NetSt σ} (h : N.Labelled) (hn : N'.nch = N.nch)
    (hk : N'.kind = N.kind) (hb : N'.bkind = N.bkind) : N'.Labelled := fun c p hl => by
  rw [hk, hb]
  exact h c p ((live_of_nch hn _).mp hl)

/-- A child born with a kind and a back kind keeps the labels. -/
theorem Labelled.newChild {N : NetSt σ} (h : N.Labelled) {s : Node} (hs : N.Live s)
    {kd : Option (VarSymb × VarType)} {cx : ℕ} {t : NodeSt σ} {fimg₀ : ℕ → ℕ}
    {bcl₀ : List VarType} {bimg₀ : ℕ → ℕ} {bkd₀ : Option (VarSymb × VarType)} {bcx₀ : ℕ}
    (hkd : kd ≠ none) (hbk : bkd₀ ≠ none) :
    (N.newChild s kd cx t fimg₀ bcl₀ bimg₀ bkd₀ bcx₀).Labelled := fun c p hl => by
  rcases (live_newChild hs kd cx t _).mp hl with hl | he
  · have hne : (c :: p : Node) ≠ N.nch s :: s := fun e => not_live_new s (e ▸ hl)
    change Function.update N.kind _ kd (c :: p) ≠ none ∧
      Function.update N.bkind _ bkd₀ (c :: p) ≠ none
    rw [Function.update_of_ne hne, Function.update_of_ne hne]
    exact h c p hl
  · change Function.update N.kind _ kd (c :: p) ≠ none ∧
      Function.update N.bkind _ bkd₀ (c :: p) ≠ none
    rw [he, Function.update_self, Function.update_self]
    exact ⟨hkd, hbk⟩

variable [ModalSys.NoFour]

theorem Labelled.henk {N : NetSt σ} (h : N.Labelled) (s : Node)
    (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : (N.henk s o).Labelled := by
  obtain ⟨l, φ⟩ := o
  simp only [NetSt.henk]
  split_ifs
  all_goals first
    | exact h
    | (split <;> (try split_ifs) <;> first | exact h | exact h.of_same rfl rfl rfl)

omit [ModalSys.NoFour] in
theorem Labelled.mkAlias {N : NetSt σ} (h : N.Labelled) (s : Node) (o : AliasObl σ) :
    (N.mkAlias s o).Labelled := by
  obtain ⟨l, A, a, tm⟩ := o
  simp only [NetSt.mkAlias]
  split_ifs
  · exact h.of_same rfl rfl rfl
  · exact h

omit [ModalSys.NoFour] in
theorem Labelled.mkRoute {hS : ModalSys.BStrong = true} {N : NetSt σ} (h : N.Labelled)
    (s : Node) (o : RouteObl σ) : (N.mkRoute hS s o).Labelled := by
  obtain ⟨l, S, a, y, Φ⟩ := o
  simp only [NetSt.mkRoute]
  split_ifs
  · exact h.of_same rfl rfl rfl
  all_goals exact h

theorem Labelled.realFS {hS : ModalSys.BStrong = true} {N : NetSt σ} (h : N.Labelled)
    (k : Node) : (N.realFS hS k).Labelled := by
  match k with
  | [] => exact h
  | c :: p =>
      simp only [NetSt.realFS]
      split_ifs
      · exact h.of_same rfl rfl rfl
      · exact h

theorem Labelled.realBS {hS : ModalSys.BStrong = true} {N : NetSt σ} (h : N.Labelled)
    (k : Node) : (N.realBS hS k).Labelled := by
  match k with
  | [] => exact h
  | c :: p =>
      simp only [NetSt.realBS]
      split_ifs
      · exact h.of_same rfl rfl rfl
      · exact h

theorem Labelled.mkRetXDC {hS : ModalSys.BStrong = true} {N : NetSt σ} (h : N.Labelled)
    {s : Node} (hs : N.Live s) (o : RetOblXDC σ) : (N.mkRetXDC hS s o).Labelled := by
  obtain ⟨l, A, Xe, x, ⟨y, o, z⟩, Ξ⟩ := o
  simp only [NetSt.mkRetXDC]
  split_ifs
  · split
    · split_ifs
      · exact h.newChild hs (by simp) (by simp)
      · exact h
    · exact h
  all_goals exact h

/-- ⭐**Under rows 3–4 every operation keeps the labels**: the others make no child. -/
theorem Labelled.applyOpT {hS : ModalSys.BStrong = true} (hW : ModalSys.BStrongW = true)
    {N : NetSt σ} (h : N.Labelled) (o : OpS σ) : (N.applyOpT hS o).Labelled := by
  rcases o with ((⟨s, o⟩ | ⟨s, o⟩ | k | k) | ⟨s, o⟩ | ⟨s, o⟩ | ⟨s, o⟩ | ⟨s, o⟩ | ⟨s, o⟩ |
    ⟨s, o⟩)
  · simp only [NetSt.applyOpT, NetSt.applyOpS]
    split_ifs
    · exact h.henk s o
    · exact h
  · simp only [NetSt.applyOpT, NetSt.applyOpS, hW, ↓reduceIte, ite_self]
    exact h
  · simp only [NetSt.applyOpT, NetSt.applyOpS]
    split_ifs
    · exact h.realFS k
    · exact h
  · simp only [NetSt.applyOpT, NetSt.applyOpS]
    split_ifs
    · exact h.realBS k
    · exact h
  · simp only [NetSt.applyOpT]
    split_ifs
    · exact h.mkAlias s o
    · exact h
  all_goals
    simp only [NetSt.applyOpT, hW, ↓reduceIte, ite_self]
    try split_ifs with hl
    all_goals first
      | exact h
      | exact h.mkRetXDC hl o
      | exact h.mkRoute s o

end NetSt

variable [ModalSys.NoFour] [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- ⭐**Under rows 3–4 every network of the strong chain is labelled.** -/
theorem labelled_netS (hS : ModalSys.BStrong = true) (hW : ModalSys.BStrongW = true)
    {l₀ : List VarType} (M₀ : Set (WFF σ (ctxOf l₀) 0)) : ∀ n, (netS hS M₀ n).Labelled
  | 0 => NetSt.Labelled.init M₀
  | n + 1 => (labelled_netS hS hW M₀ n).applyOpT hW (schedS n)

end BArrow

end V12M
