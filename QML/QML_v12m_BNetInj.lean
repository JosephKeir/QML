import QML.QML_v12m_BNetMono

/-!
# QML v12m — B's networks: injective images

Every arrow of a network sends distinct variables to distinct variables (`NetSt.InjOk`): what the
T-free decoder needs (`BData.ImgInj`, docs §11.20).  A child is born with injective images (the
identity, a shift, or one variable back), and a realisation step commits the next variable to
the target's **next** variable, which no older image is: the older images are declared at the
target (`ImgOk`), so below its length (`InjOn.extImg`).

* `InjOn`, ⭐`InjOn.extImg`;
* `NetSt.InjOk`, kept by every operation of weak B (⭐`InjOk.applyOp`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-- An index map injective on a list's variables. -/
def InjOn (cl : List VarType) (img : ℕ → ℕ) : Prop :=
  ∀ r r', r < cl.length → r' < cl.length → img r = img r' → r = r'

omit [ModalSys] in
theorem InjOn.nil (img : ℕ → ℕ) : InjOn [] img :=
  fun r _ hr => absurd hr (Nat.not_lt_zero r)

omit [ModalSys] in
theorem InjOn.of_injective {cl : List VarType} {img : ℕ → ℕ} (h : Function.Injective img) :
    InjOn cl img :=
  fun _ _ _ _ e => h e

omit [ModalSys] in
/-- One variable back is injective. -/
theorem InjOn.single (A : VarType) (y : ℕ) : InjOn [A] (fun _ => y) := by
  intro r r' hr hr' _
  simp only [List.length_cons, List.length_nil] at hr hr'
  omega

omit [ModalSys] in
/-- ⭐Committing the next variable to a value above every older image keeps the map injective. -/
theorem InjOn.ext {A : VarType} {cl : List VarType} {img : ℕ → ℕ} {n : ℕ} (h : InjOn cl img)
    (hb : ∀ r < cl.length, img r < n) : InjOn (A :: cl) (BArrow.extImg img cl.length n) := by
  intro r r' hr hr' e
  simp only [List.length_cons] at hr hr'
  unfold BArrow.extImg at e
  by_cases h₁ : r = cl.length <;> by_cases h₂ : r' = cl.length
  · rw [h₁, h₂]
  · rw [if_pos h₁, if_neg h₂] at e
    exact absurd e (Nat.ne_of_gt (hb r' (by omega)))
  · rw [if_neg h₁, if_pos h₂] at e
    exact absurd e (Nat.ne_of_lt (hb r (by omega)))
  · rw [if_neg h₁, if_neg h₂] at e
    exact h r r' (by omega) (by omega) e

/-- Images declared in a world's language are below its length. -/
theorem ImgOk.lt {cl l : List VarType} {img : ℕ → ℕ} (h : ImgOk cl (ctxOf l) img) :
    ∀ r < cl.length, img r < l.length := by
  intro r hr
  have h' : ctxOf l (.root (.free (img r))) = some (rootTy cl r).bc := h r hr
  rw [ctxOf_root] at h'
  by_contra hn
  rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hn)] at h'
  cases h'

namespace NetSt

/-- ⭐**Every arrow's images are injective** on the variables it commits. -/
def InjOk (N : NetSt σ) : Prop :=
  ∀ c p, N.Live (c :: p) →
    InjOn (N.fcl (c :: p)) (N.fimg (c :: p)) ∧ InjOn (N.bcl (c :: p)) (N.bimg (c :: p))

theorem InjOk.init {l₀ : List VarType} (M₀ : Set (WFF σ (ctxOf l₀) 0)) : (init M₀).InjOk :=
  fun _ _ hk => absurd (init_live hk) (List.cons_ne_nil _ _)

theorem InjOk.setSt {N : NetSt σ} (h : N.InjOk) (s : Node) (t : NodeSt σ) :
    (N.setSt s t).InjOk := fun c p hk => h c p ((live_setSt N s t _).mp hk)

theorem InjOk.setFwd {N : NetSt σ} (h : N.InjOk) {k : Node} {cl : List VarType} {img : ℕ → ℕ}
    (hi : InjOn cl img) : (N.setFwd k cl img).InjOk := by
  intro c p hk
  rw [live_setFwd] at hk
  by_cases he : (c :: p : Node) = k
  · subst he
    change InjOn (Function.update N.fcl (c :: p) cl (c :: p))
      (Function.update N.fimg (c :: p) img (c :: p)) ∧ _
    rw [Function.update_self, Function.update_self]
    exact ⟨hi, (h c p hk).2⟩
  · change InjOn (Function.update N.fcl k cl (c :: p))
      (Function.update N.fimg k img (c :: p)) ∧ _
    rw [Function.update_of_ne he, Function.update_of_ne he]
    exact h c p hk

theorem InjOk.setBack {N : NetSt σ} (h : N.InjOk) {k : Node} {cl : List VarType} {img : ℕ → ℕ}
    (hi : InjOn cl img) : (N.setBack k cl img).InjOk := by
  intro c p hk
  rw [live_setBack] at hk
  by_cases he : (c :: p : Node) = k
  · subst he
    change _ ∧ InjOn (Function.update N.bcl (c :: p) cl (c :: p))
      (Function.update N.bimg (c :: p) img (c :: p))
    rw [Function.update_self, Function.update_self]
    exact ⟨(h c p hk).1, hi⟩
  · change _ ∧ InjOn (Function.update N.bcl k cl (c :: p))
      (Function.update N.bimg k img (c :: p))
    rw [Function.update_of_ne he, Function.update_of_ne he]
    exact h c p hk

theorem InjOk.newChild {N : NetSt σ} (h : N.InjOk) {s : Node} (hs : N.Live s)
    {kd : Option (VarSymb × VarType)} {cx : ℕ} {t : NodeSt σ} {fimg₀ : ℕ → ℕ}
    {bcl₀ : List VarType} {bimg₀ : ℕ → ℕ} {bkd₀ : Option (VarSymb × VarType)}
    (h₁ : InjOn (N.st s).l fimg₀) (h₂ : InjOn bcl₀ bimg₀) :
    (N.newChild s kd cx t fimg₀ bcl₀ bimg₀ bkd₀).InjOk := by
  intro c p hk
  rw [live_newChild hs] at hk
  by_cases he : (c :: p : Node) = N.nch s :: s
  · rw [he]
    change InjOn (Function.update N.fcl (N.nch s :: s) (N.st s).l (N.nch s :: s))
      (Function.update N.fimg (N.nch s :: s) fimg₀ (N.nch s :: s)) ∧
      InjOn (Function.update N.bcl (N.nch s :: s) bcl₀ (N.nch s :: s))
        (Function.update N.bimg (N.nch s :: s) bimg₀ (N.nch s :: s))
    rw [Function.update_self, Function.update_self, Function.update_self, Function.update_self]
    exact ⟨h₁, h₂⟩
  · rcases hk with hk | hk
    · change InjOn (Function.update N.fcl (N.nch s :: s) (N.st s).l (c :: p))
        (Function.update N.fimg (N.nch s :: s) fimg₀ (c :: p)) ∧
        InjOn (Function.update N.bcl (N.nch s :: s) bcl₀ (c :: p))
          (Function.update N.bimg (N.nch s :: s) bimg₀ (c :: p))
      rw [Function.update_of_ne he, Function.update_of_ne he, Function.update_of_ne he,
        Function.update_of_ne he]
      exact h c p hk
    · exact absurd hk he

variable [ModalSys.NoFour]

theorem InjOk.realF {N : NetSt σ} (hN : N.Good) (h : N.InjOk) (k : Node) (hk : N.Live k) :
    (N.realF k).InjOk := by
  match k, hk with
  | [], _ => exact h
  | c :: p, hk =>
      simp only [NetSt.realF]
      split_ifs
      · obtain ⟨_, himg, _⟩ := hN.fwd c p hk
        exact (h.setSt _ _).setFwd ((h c p hk).1.ext himg.lt)
      · exact h

theorem InjOk.realB {N : NetSt σ} (hN : N.Good) (h : N.InjOk) (k : Node) (hk : N.Live k) :
    (N.realB k).InjOk := by
  match k, hk with
  | [], _ => exact h
  | c :: p, hk =>
      simp only [NetSt.realB]
      split_ifs
      · obtain ⟨_, himg, _⟩ := hN.back c p hk
        exact (h.setSt _ _).setBack ((h c p hk).2.ext himg.lt)
      · exact h

theorem InjOk.henk {N : NetSt σ} (h : N.InjOk) (s : Node)
    (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : (N.henk s o).InjOk := by
  obtain ⟨l, φ⟩ := o
  simp only [NetSt.henk]
  split_ifs
  · split
    · split_ifs
      · exact h.setSt _ _
      · exact h
    · split_ifs
      · exact h.setSt _ _
      · exact h
    · exact h
  · exact h

theorem InjOk.mkChild {N : NetSt σ} (h : N.InjOk) {s : Node} (hs : N.Live s)
    (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : (N.mkChild s o).InjOk := by
  obtain ⟨l, φ⟩ := o
  simp only [NetSt.mkChild]
  split_ifs
  · split
    · split_ifs
      · exact h
      · exact h.newChild hs (InjOn.of_injective Function.injective_id) (InjOn.nil _)
    · split_ifs
      · split
        · exact h.newChild hs (InjOn.of_injective Function.injective_id) (InjOn.nil _)
        · exact h
      · exact h
    · exact h
  · exact h

/-- ⭐Every operation of weak B keeps the images injective. -/
theorem InjOk.applyOp {N : NetSt σ} (hN : N.Good) (h : N.InjOk) (o : Op σ) :
    (N.applyOp o).InjOk := by
  rcases o with ⟨s, o⟩ | ⟨s, o⟩ | k | k
  all_goals
    simp only [NetSt.applyOp]
    split_ifs with hl
    · first
        | exact h.henk s o
        | exact h.mkChild hl o
        | exact h.realF hN k hl
        | exact h.realB hN k hl
    · exact h

end NetSt

end BArrow

end V12M
