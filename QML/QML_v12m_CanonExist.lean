import QML.QML_v12m_CanonDom
import QML.QML_v12m_HenkinRet

/-!
# QML v12m — the canonical model: existence of successors

* `World.ofHenkin`: the Henkin construction over a starting theory gives a world.
* ⭐`exists_box_fail`: if `□χ` fails at a world, `χ` fails at some proper successor — the Henkin
  construction over everything necessary at the world together with `¬χ`, consistent by `K`.
* ⭐`exists_dia`: if `◇_x χ` holds at a world, `χ` holds at some successor in the extent of `x` —
  the Henkin construction over everything necessary and `□_x`-necessary at the world together with
  `χ`, consistent by `K◇`.

The starting sentences record an inclusion of OUTER stage contexts, so all the hypotheses of a
derivation live at one stage `(m, m)` of the world, where their necessitations hold.  The worlds
built are one level deeper.
-/

namespace V12M

variable [ModalSys]

namespace Canon

variable {σ : Signature} {N₀ : ℕ}

namespace World

/-- Membership moves along inclusions of stage contexts. -/
theorem mem_mono (w : World σ N₀) {j j' : ℕ × ℕ} (h : (w.L.ctx j').Le (w.L.ctx j))
    {φ : WFF σ (w.L.ctx j') 0} (hm : (⟨j', φ⟩ : w.L.sys.Sentence σ) ∈ w.T) :
    (⟨j, WFF.mono h φ⟩ : w.L.sys.Sentence σ) ∈ w.T := by
  have h₁ := (mem_lift (w := w) (le_sup_right : j' ≤ j ⊔ j')).mp hm
  refine (mem_lift (w := w) (le_sup_left : j ≤ j ⊔ j')).mpr ?_
  rw [WFF.mono_mono]
  exact h₁

/-- Membership of a weakened formula does not depend on the stage or the inclusion. -/
theorem mem_mono_congr (w : World σ N₀) {Γ : Ctx} {j j' : ℕ × ℕ} (h : Γ.Le (w.L.ctx j))
    (h' : Γ.Le (w.L.ctx j')) {ψ : WFF σ Γ 0}
    (hm : (⟨j', WFF.mono h' ψ⟩ : w.L.sys.Sentence σ) ∈ w.T) :
    (⟨j, WFF.mono h ψ⟩ : w.L.sys.Sentence σ) ∈ w.T := by
  have h₁ := (mem_lift (w := w) (le_sup_right : j' ≤ j ⊔ j')).mp hm
  refine (mem_lift (w := w) (le_sup_left : j ≤ j ⊔ j')).mpr ?_
  rw [WFF.mono_mono] at h₁ ⊢
  exact h₁

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- The Henkin construction over a consistent starting theory gives a world. -/
noncomputable def ofHenkin (d : ℕ) (L₀ : WorldLang) (hρ : ∀ n, L₀.ρ n = names N₀ d n)
    (hfresh : ∀ m d' n, d ≤ d' → (L₀.base m).RootFresh (.free (names N₀ d' n)))
    (S₀ : Set ((L₀.pre []).Sentence σ)) (hS₀ : StageSys.Consistent S₀) : World σ N₀ where
  depth := d
  L := L₀.final S₀
  hρ := hρ
  hfresh := hfresh
  T := L₀.finalT S₀
  mcs := WorldLang.finalT_isMCS hS₀
  exW := WorldLang.finalT_ex_witness hS₀
  allW := WorldLang.finalT_all_witness
  real := L₀.chainReal hS₀
  realW := by
    intro hTb hTS i A a t
    obtain ⟨m, j⟩ := i
    obtain ⟨n, hret, hm, hj, hlt, hterm⟩ := WorldLang.exists_isRet_term (L := L₀) (S₀ := S₀) m j
      (Term.mono (Ctx.le_of_eq (WorldLang.ctxL_eq_final S₀ m j).symm) t)
    obtain ⟨d, hsome, hf⟩ := WorldLang.chainReal_ret hTb hTS hS₀ hret
    refine ⟨L₀.ρ n, (WorldLang.decM n, n), ⟨le_of_eq hm.symm, ?_⟩, d, hsome, ?_⟩
    · rw [← hj]
      exact WorldLang.decJ_le n
    refine hf.trans ((congrArg
      (fun z : Σ A : VarType, Σ a : Ann A,
          Term σ (L₀.ctxL (WorldLang.decM n) (L₀.chain S₀ n).l) A a =>
        (⟨z.1, (WorldLang.decM n, n), z.2.1,
            Term.mono (Ctx.le_of_eq (WorldLang.ctxL_eq_final S₀ (WorldLang.decM n) n)) z.2.2⟩ :
          Σ (A : VarType) (i : ℕ × ℕ) (a : Ann A), Term σ ((L₀.final S₀).ctx i) A a))
      hterm).trans ?_)
    rw [Term.mono_mono, Term.mono_mono]

end World

theorem childNames_fresh (w : World σ N₀) (m n : ℕ) :
    (w.L.ctx (m, m)).RootFresh (.free (names N₀ (w.depth + 1) n)) :=
  w.fresh_deeper (Nat.lt_succ_self _) n (m, m)

/-- The language of a `□`-successor. -/
def boxLang (w : World σ N₀) : WorldLang :=
  w.L.boxChild (fun _ => .VTypeOne) (names N₀ (w.depth + 1)) (names_injective _ _)
    (childNames_fresh w)

/-- The language of a `◇_x`-successor. -/
def diaLang (w : World σ N₀) (x : VarSymb) : WorldLang :=
  w.L.diaChild x (fun _ => .VTypeOne) (names N₀ (w.depth + 1)) (names_injective _ _)
    (childNames_fresh w)

/-- A necessitated formula at some stage, with an inclusion into stage `(m, m)`. -/
abbrev BoxItem (w : World σ N₀) (m : ℕ) : Type :=
  Σ' (i' : ℕ × ℕ) (_ : WFF σ (w.L.ctx i').boxIn 0), (w.L.ctx i').Le (w.L.ctx (m, m))

/-- A `□_x`-necessitated formula at some stage, with an inclusion into stage `(m, m)`. -/
abbrev BoxxItem (w : World σ N₀) (x : VarSymb) (m : ℕ) : Type :=
  Σ' (i' : ℕ × ℕ) (_ : ∃ X, (w.L.ctx i').ref x = some (.VTypeDia X))
    (_ : WFF σ ((w.L.ctx i').diaIn x) 0), (w.L.ctx i').Le (w.L.ctx (m, m))

theorem le_diag_max (w : World σ N₀) (i : ℕ × ℕ) :
    (w.L.ctx i).Le (w.L.ctx (max i.1 i.2, max i.1 i.2)) :=
  w.L.le_diag (le_max_left _ _) (le_max_right _ _)

/-! ## `□`-successors -/

/-- Everything necessary at `w`, and `¬χ`. -/
def boxStart (w : World σ N₀) {i : ℕ × ℕ} (χ : WFF σ (w.L.ctx i).boxIn 0) :
    Set (((boxLang w).pre []).Sentence σ) :=
  {s | ∃ (i' : ℕ × ℕ) (ψ : WFF σ (w.L.ctx i').boxIn 0)
      (h : (w.L.ctx i').Le (w.L.ctx (s.1, s.1))),
      (⟨i', .box ψ⟩ : w.L.sys.Sentence σ) ∈ w.T ∧ s.2 = WFF.mono h.boxIn ψ} ∪
  {⟨max i.1 i.2, WFF.mono (le_diag_max w i).boxIn χ.neg⟩}

theorem boxStart_consistent (w : World σ N₀) {i : ℕ × ℕ} (χ : WFF σ (w.L.ctx i).boxIn 0)
    (hχ : (⟨i, .box χ⟩ : w.L.sys.Sentence σ) ∉ w.T) : StageSys.Consistent (boxStart w χ) := by
  have key : ∀ m, max i.1 i.2 ≤ m → Theory.Consistent (StageSys.atStage (boxStart w χ) m) := by
    rintro m hm ⟨Δ, hΔ, p⟩
    have hi : i ≤ (m, m) := ⟨(le_max_left _ _).trans hm, (le_max_right _ _).trans hm⟩
    have hcases : ∀ δ ∈ Δ, δ = (WFF.mono (w.L.ctx_le hi).boxIn χ).neg ∨
        ∃ b : BoxItem w m, (⟨b.1, .box b.2.1⟩ : w.L.sys.Sentence σ) ∈ w.T ∧
          WFF.mono b.2.2.boxIn b.2.1 = δ := by
      intro δ hδ
      obtain ⟨s, hs, hle, rfl⟩ := hΔ δ hδ
      rcases hs with ⟨i', ψ, h, hmem, hφ⟩ | hs
      · rw [hφ]
        exact Or.inr ⟨⟨i', ψ, h.trans (w.L.le_diag hle hle)⟩, hmem,
          (WFF.mono_mono _ _ ψ).symm⟩
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        exact Or.inl (congrArg (fun x => WFF.neg x) (WFF.mono_mono _ _ χ))
    obtain ⟨Δ₀, h₀, h₁⟩ := exists_hyps_cons_map
      (P := fun b : BoxItem w m => (⟨b.1, .box b.2.1⟩ : w.L.sys.Sentence σ) ∈ w.T)
      (fun b => WFF.mono b.2.2.boxIn b.2.1) _ Δ hcases
    obtain ⟨q⟩ := Provable.byContra (Provable.mono h₁ p)
    have hmem : (⟨(m, m), .box (WFF.mono (w.L.ctx_le hi).boxIn χ)⟩ :
        w.L.sys.Sentence σ) ∈ w.T :=
      World.mem_of_provable (Δ := (Δ₀.map fun b => WFF.mono b.2.2.boxIn b.2.1).map
          fun ψ => WFF.box (Γ := w.L.ctx (m, m)) ψ)
        (fun ψ hψ => by
          obtain ⟨ψ₀, hψ₀, rfl⟩ := List.mem_map.mp hψ
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hψ₀
          exact World.mem_mono w b.2.2 (h₀ b hb))
        ⟨Proof.K_box q⟩
    exact hχ ((World.mem_lift hi).mpr hmem)
  intro m
  rcases le_total (max i.1 i.2) m with h | h
  · exact key m h
  · exact StageSys.consistent_of_le (key _ le_rfl) h

section

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- The `□`-successor refuting `χ`. -/
noncomputable def boxWorld (w : World σ N₀) {i : ℕ × ℕ} (χ : WFF σ (w.L.ctx i).boxIn 0)
    (hχ : (⟨i, .box χ⟩ : w.L.sys.Sentence σ) ∉ w.T) : World σ N₀ :=
  World.ofHenkin (w.depth + 1) (boxLang w) (fun _ => rfl)
    (fun m _ n hd => (w.fresh_deeper hd n (m, m)).boxIn) (boxStart w χ)
    (boxStart_consistent w χ hχ)

theorem boxWorld_acc (w : World σ N₀) {i : ℕ × ℕ} (χ : WFF σ (w.L.ctx i).boxIn 0)
    (hχ : (⟨i, .box χ⟩ : w.L.sys.Sentence σ) ∉ w.T) : Acc' w (boxWorld w χ hχ) := by
  refine ⟨rfl, Or.inl fun _ => rfl, ?_⟩
  intro i' ψ j h hmem
  have hk : (⟨max i'.1 i'.2, WFF.mono (le_diag_max w i').boxIn ψ⟩ :
      ((boxLang w).pre []).Sentence σ) ∈ boxStart w χ :=
    Or.inl ⟨i', ψ, le_diag_max w i', hmem, rfl⟩
  exact World.mem_mono_congr (boxWorld w χ hχ) h _ (WorldLang.subset_finalT _ hk)

/-- ⭐A non-necessary formula fails at some proper successor. -/
theorem exists_box_fail (w : World σ N₀) {i : ℕ × ℕ} (χ : WFF σ (w.L.ctx i).boxIn 0)
    (hχ : (⟨i, .box χ⟩ : w.L.sys.Sentence σ) ∉ w.T) :
    ∃ (w' : World σ N₀) (ha : Acc' w w'),
      (⟨childStage i, WFF.mono (ha.boxIn_le i) χ⟩ : w'.L.sys.Sentence σ) ∉ w'.T := by
  refine ⟨boxWorld w χ hχ, boxWorld_acc w χ hχ, fun hin => ?_⟩
  have hneg := WorldLang.subset_finalT (boxStart w χ)
    (Or.inr rfl : (⟨max i.1 i.2, WFF.mono (le_diag_max w i).boxIn χ.neg⟩ :
      ((boxLang w).pre []).Sentence σ) ∈ boxStart w χ)
  exact ((boxWorld w χ hχ).mcs.neg_mem_iff (φ := WFF.mono (le_diag_max w i).boxIn χ)).mp hneg hin

/-- ⭐Under D every world has a proper successor: the rule `D_box` refutes `□⊥`, so `□⊥` is not in
    the theory, and a `□` that fails has a successor (`exists_box_fail`).  This is the canonical
    frame's seriality. -/
theorem exists_succ (hD : ModalSys.D = true) (w : World σ N₀) : ∃ w' : World σ N₀, Acc' w w' := by
  have hnot : (⟨(0, 0), .box .bot⟩ : w.L.sys.Sentence σ) ∉ w.T := fun h =>
    w.mcs.bot_not_mem (World.mem_of_provable (Δ := [.box .bot])
      (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact h)
      ⟨Proof.D_box hD (Proof.lookup List.mem_cons_self)⟩)
  obtain ⟨w', ha, -⟩ := exists_box_fail w (i := (0, 0)) .bot hnot
  exact ⟨w', ha⟩

end

/-! ## `◇_x`-successors -/

/-- Everything necessary and `□_x`-necessary at `w`, and `χ`. -/
def diaStart (w : World σ N₀) (x : VarSymb) {i : ℕ × ℕ} (χ : WFF σ ((w.L.ctx i).diaIn x) 0) :
    Set (((diaLang w x).pre []).Sentence σ) :=
  ({s | ∃ (i' : ℕ × ℕ) (ψ : WFF σ (w.L.ctx i').boxIn 0)
      (h : (w.L.ctx i').Le (w.L.ctx (s.1, s.1))),
      (⟨i', .box ψ⟩ : w.L.sys.Sentence σ) ∈ w.T ∧
        s.2 = WFF.mono (h.boxIn.trans (Ctx.le_boxIn_diaIn _ x)) ψ} ∪
    {s | ∃ (i' : ℕ × ℕ) (hx : ∃ X, (w.L.ctx i').ref x = some (.VTypeDia X))
      (ψ : WFF σ ((w.L.ctx i').diaIn x) 0) (h : (w.L.ctx i').Le (w.L.ctx (s.1, s.1))),
      (⟨i', WFF.boxx x hx ψ⟩ : w.L.sys.Sentence σ) ∈ w.T ∧ s.2 = WFF.mono (h.diaIn x) ψ}) ∪
  {⟨max i.1 i.2, WFF.mono ((le_diag_max w i).diaIn x) χ⟩}

/-- The formula of a necessitated item, in the `◇_x` view of stage `(m, m)`. -/
def itemF (w : World σ N₀) (x : VarSymb) (m : ℕ) :
    BoxItem w m ⊕ BoxxItem w x m → WFF σ ((w.L.ctx (m, m)).diaIn x) 0
  | .inl b => WFF.mono (b.2.2.boxIn.trans (Ctx.le_boxIn_diaIn _ x)) b.2.1
  | .inr c => WFF.mono (c.2.2.2.diaIn x) c.2.2.1

/-- An item is necessitated at `w`. -/
def itemP (w : World σ N₀) (x : VarSymb) (m : ℕ) : BoxItem w m ⊕ BoxxItem w x m → Prop
  | .inl b => (⟨b.1, .box b.2.1⟩ : w.L.sys.Sentence σ) ∈ w.T
  | .inr c => (⟨c.1, WFF.boxx x c.2.1 c.2.2.1⟩ : w.L.sys.Sentence σ) ∈ w.T

/-- The `□`-items, in the `□` view of stage `(m, m)`. -/
def boxPart (w : World σ N₀) (x : VarSymb) (m : ℕ) :
    BoxItem w m ⊕ BoxxItem w x m → Option (WFF σ (w.L.ctx (m, m)).boxIn 0)
  | .inl b => some (WFF.mono b.2.2.boxIn b.2.1)
  | .inr _ => none

/-- The `□_x`-items, in the `◇_x` view of stage `(m, m)`. -/
def boxxPart (w : World σ N₀) (x : VarSymb) (m : ℕ) :
    BoxItem w m ⊕ BoxxItem w x m → Option (WFF σ ((w.L.ctx (m, m)).diaIn x) 0)
  | .inl _ => none
  | .inr c => some (WFF.mono (c.2.2.2.diaIn x) c.2.2.1)

theorem diaStart_consistent (w : World σ N₀) (x : VarSymb) {i : ℕ × ℕ}
    (hx : ∃ X, (w.L.ctx i).ref x = some (.VTypeDia X)) (χ : WFF σ ((w.L.ctx i).diaIn x) 0)
    (hχ : (⟨i, .dia x hx χ⟩ : w.L.sys.Sentence σ) ∈ w.T) :
    StageSys.Consistent (diaStart w x χ) := by
  have key : ∀ m, max i.1 i.2 ≤ m →
      Theory.Consistent (StageSys.atStage (diaStart w x χ) m) := by
    rintro m hm ⟨Δ, hΔ, p⟩
    have hi : i ≤ (m, m) := ⟨(le_max_left _ _).trans hm, (le_max_right _ _).trans hm⟩
    have hcases : ∀ δ ∈ Δ, δ = WFF.mono ((w.L.ctx_le hi).diaIn x) χ ∨
        ∃ a, itemP w x m a ∧ itemF w x m a = δ := by
      intro δ hδ
      obtain ⟨s, hs, hle, rfl⟩ := hΔ δ hδ
      rcases hs with (⟨i', ψ, h, hmem, hφ⟩ | ⟨i', hx', ψ, h, hmem, hφ⟩) | hs
      · rw [hφ]
        exact Or.inr ⟨.inl ⟨i', ψ, h.trans (w.L.le_diag hle hle)⟩, hmem,
          (WFF.mono_mono _ _ ψ).symm⟩
      · rw [hφ]
        exact Or.inr ⟨.inr ⟨i', hx', ψ, h.trans (w.L.le_diag hle hle)⟩, hmem,
          (WFF.mono_mono _ _ ψ).symm⟩
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        exact Or.inl (WFF.mono_mono _ _ χ)
    obtain ⟨Δ₀, h₀, h₁⟩ := exists_hyps_cons_map (P := itemP w x m) (itemF w x m) _ Δ hcases
    have hxm : ∃ X, (w.L.ctx (m, m)).ref x = some (.VTypeDia X) :=
      hx.imp fun _ h => (w.L.ctx_le hi).ref h
    have q₀ := Provable.mono h₁ p
    obtain ⟨q⟩ := Provable.mono (Δ' := WFF.mono ((w.L.ctx_le hi).diaIn x) χ ::
        (Δ₀.filterMap (boxxPart w x m) ++
          (Δ₀.filterMap (boxPart w x m)).map (WFF.mono (Ctx.le_boxIn_diaIn _ x))))
      (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact List.mem_cons_self
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
          refine List.mem_cons_of_mem _ ?_
          cases a with
          | inl b =>
              exact List.mem_append_right _ (List.mem_map.mpr
                ⟨WFF.mono b.2.2.boxIn b.2.1, List.mem_filterMap.mpr ⟨.inl b, ha, rfl⟩,
                  WFF.mono_mono _ _ _⟩)
          | inr c =>
              exact List.mem_append_left _ (List.mem_filterMap.mpr ⟨.inr c, ha, rfl⟩))
      q₀
    refine w.mcs.bot_not_mem (i := (m, m)) (World.mem_of_provable (fun ψ hψ => ?_)
      ⟨Proof.dia_bot x hxm (Proof.K_dia (Γ := w.L.ctx (m, m)) x hxm q)⟩)
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact (World.mem_lift hi).mp hχ
    · rcases List.mem_append.mp hψ with hψ | hψ
      · obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hψ
        obtain ⟨a, ha, hsome⟩ := List.mem_filterMap.mp hφ
        cases a with
        | inl _ => cases hsome
        | inr c =>
            cases hsome
            exact World.mem_mono w c.2.2.2
              (h₀ (.inr c) ha : (⟨c.1, WFF.boxx x c.2.1 c.2.2.1⟩ : w.L.sys.Sentence σ) ∈ w.T)
      · obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hψ
        obtain ⟨a, ha, hsome⟩ := List.mem_filterMap.mp hφ
        cases a with
        | inl b =>
            cases hsome
            exact World.mem_mono w b.2.2
              (h₀ (.inl b) ha : (⟨b.1, .box b.2.1⟩ : w.L.sys.Sentence σ) ∈ w.T)
        | inr _ => cases hsome
  intro m
  rcases le_total (max i.1 i.2) m with h | h
  · exact key m h
  · exact StageSys.consistent_of_le (key _ le_rfl) h

section

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- The `◇_x`-successor verifying `χ`. -/
noncomputable def diaWorld (w : World σ N₀) (x : VarSymb) {i : ℕ × ℕ}
    (hx : ∃ X, (w.L.ctx i).ref x = some (.VTypeDia X)) (χ : WFF σ ((w.L.ctx i).diaIn x) 0)
    (hχ : (⟨i, .dia x hx χ⟩ : w.L.sys.Sentence σ) ∈ w.T) : World σ N₀ :=
  World.ofHenkin (w.depth + 1) (diaLang w x) (fun _ => rfl)
    (fun m _ n hd => (w.fresh_deeper hd n (m, m)).diaIn x) (diaStart w x χ)
    (diaStart_consistent w x hx χ hχ)

theorem diaWorld_acc (w : World σ N₀) (x : VarSymb) {i : ℕ × ℕ}
    (hx : ∃ X, (w.L.ctx i).ref x = some (.VTypeDia X)) (χ : WFF σ ((w.L.ctx i).diaIn x) 0)
    (hχ : (⟨i, .dia x hx χ⟩ : w.L.sys.Sentence σ) ∈ w.T) : Acc' w (diaWorld w x hx χ hχ) := by
  refine ⟨rfl, Or.inr ⟨x, fun _ => rfl⟩, ?_⟩
  intro i' ψ j h hmem
  have hk : (⟨max i'.1 i'.2, WFF.mono ((le_diag_max w i').boxIn.trans
      (Ctx.le_boxIn_diaIn _ x)) ψ⟩ : ((diaLang w x).pre []).Sentence σ) ∈ diaStart w x χ :=
    Or.inl (Or.inl ⟨i', ψ, le_diag_max w i', hmem, rfl⟩)
  exact World.mem_mono_congr (diaWorld w x hx χ hχ) h _ (WorldLang.subset_finalT _ hk)

/-- ⭐A possible formula holds at some successor in the extent of its witness. -/
theorem exists_dia (w : World σ N₀) (x : VarSymb) {i : ℕ × ℕ}
    (hx : ∃ X, (w.L.ctx i).ref x = some (.VTypeDia X)) (χ : WFF σ ((w.L.ctx i).diaIn x) 0)
    (hχ : (⟨i, .dia x hx χ⟩ : w.L.sys.Sentence σ) ∈ w.T) :
    ∃ (w' : Succ w) (hw' : w' ∈ extent w x) (hd : w'.1.depth - w.depth ≠ 0),
      (⟨childStage i, WFF.mono (extent_le hw' hd i) χ⟩ : w'.1.L.sys.Sentence σ) ∈ w'.1.T := by
  have hext : (⟨diaWorld w x hx χ hχ, R.of_acc (diaWorld_acc w x hx χ hχ)⟩ : Succ w) ∈
      extent w x := by
    refine Or.inl ⟨rfl, fun _ => rfl, ?_⟩
    intro i' hx' ψ j h hmem
    have hk : (⟨max i'.1 i'.2, WFF.mono ((le_diag_max w i').diaIn x) ψ⟩ :
        ((diaLang w x).pre []).Sentence σ) ∈ diaStart w x χ :=
      Or.inl (Or.inr ⟨i', hx', ψ, le_diag_max w i', hmem, rfl⟩)
    exact World.mem_mono_congr (diaWorld w x hx χ hχ) h _ (WorldLang.subset_finalT _ hk)
  have hdd : ((⟨diaWorld w x hx χ hχ, R.of_acc (diaWorld_acc w x hx χ hχ)⟩ : Succ w)).1.depth -
      w.depth ≠ 0 := by
    have h1 : (diaWorld w x hx χ hχ).depth = w.depth + 1 := (diaWorld_acc w x hx χ hχ).1
    change (diaWorld w x hx χ hχ).depth - w.depth ≠ 0
    omega
  refine ⟨_, hext, hdd, ?_⟩
  have hk : (⟨max i.1 i.2, WFF.mono ((le_diag_max w i).diaIn x) χ⟩ :
      ((diaLang w x).pre []).Sentence σ) ∈ diaStart w x χ :=
    Or.inr rfl
  exact World.mem_mono_congr (diaWorld w x hx χ hχ) _ _ (WorldLang.subset_finalT _ hk)

/-- A possible formula in the theory has a successor in its witness's extent — stated for any
    formula that *is* a `◇_z`, so that callers need not name the witness a substitution produced. -/
theorem exists_extent_of_mem (w : World σ N₀) {i : ℕ × ℕ} (φ : WFF σ (w.L.ctx i) 0)
    (hφ : (⟨i, φ⟩ : w.L.sys.Sentence σ) ∈ w.T) (hdia : ∃ z hz χ, φ = .dia z hz χ) :
    ∃ (z : VarSymb) (_ : ∃ X, (w.L.ctx i).ref z = some (.VTypeDia X)) (w' : Succ w),
      w' ∈ extent w z := by
  obtain ⟨z, hz, χ, rfl⟩ := hdia
  obtain ⟨w', hw', -, -⟩ := exists_dia w z hz χ hφ
  exact ⟨z, hz, w', hw'⟩

/-- ⭐Under strong D every world has a witness with a successor in its extent: the axiom
    `∃x:◇𝟙. ◇_x ⊤` is in the theory, its Henkin witness gives a `◇_z ⊤`, and that has a
    successor (`exists_dia`).  This is the canonical model's `posSerial`. -/
theorem exists_extent (hDS : ModalSys.DStrong = true) (w : World σ N₀) :
    ∃ (i : ℕ × ℕ) (z : VarSymb) (_ : ∃ X, (w.L.ctx i).ref z = some (.VTypeDia X)) (w' : Succ w),
      w' ∈ extent w z := by
  have hax : (⟨(0, 0), WFF.somePoss⟩ : w.L.sys.Sentence σ) ∈ w.T :=
    World.mem_of_provable (Δ := []) (fun _ h => by simp at h) ⟨Proof.D_ex hDS⟩
  obtain ⟨i', _, _, _, hmem⟩ := w.exW hax
  exact ⟨i', exists_extent_of_mem w _ hmem ⟨_, _, _, rfl⟩⟩

end

end Canon

end V12M
