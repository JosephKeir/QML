import QML.QML_v12m_GKEq

/-!
# QML v12m — natural deduction into GK: K, KD, K4, KD4, and K, KD with `Opt` on

⭐`GK.Der.ofProof`: every sequent provable in natural deduction over a presented context has a
**cut-free** GK derivation (`docs/v12-metatheory-todo.md`, item 4).  The proof translates the ND
proof rule by rule, using GK's admissible cut (`GK.cut`) for the elimination rules, identity
(`GK.ident`) and replacement (`GK.replace`).

Two ND rules have premises over a context that need not be presented even when the conclusion's
is (`weak_ctx`, `pair_elim`), and GK's cut needs presented contexts.  So the translation is
stated, as `Proof.subst` is, for **every substitution into a presented context** (`GK.ofProof`):
there `weak_ctx` becomes a restriction and `pair_elim` the substitution `θ.pairSplit`, and every
context met is presented.  Weak D and weak 4 go to `serial` and to `□R` with copies
(`Der.D_box`, `Der.four_box`, `Der.four_dia`).  With `Opt` on, `K⁰` opens the witness on the left
and re-opens the conclusion (`Der.K_opt`), and the bridge goes to `◇_uL` and `□R` with the fold
(`Der.dia_opt`, `Der.opt_dia`).  The other rules are excluded by their flags
(`ModalSys.GKBase`).
-/

namespace V12M

variable [ModalSys] {σ : Signature}

namespace GK

/-- `Δ ⇒ φ` has a cut-free GK derivation. -/
def Der (σ : Signature) (Γ : Ctx) (Δ : List (WFF σ Γ 0)) (φ : WFF σ Γ 0) : Prop :=
  ∃ n, GK σ n Γ Δ [φ]

/-! ## The ND rules, derived in GK -/

namespace Der

variable {Γ : Ctx} {Δ : List (WFF σ Γ 0)}

theorem castHyps {Δ' : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (e : Δ = Δ') (h : Der σ Γ Δ φ) :
    Der σ Γ Δ' φ := e ▸ h

theorem conv {φ φ' : WFF σ Γ 0} (e : φ = φ') (h : Der σ Γ Δ φ) : Der σ Γ Δ φ' := e ▸ h

theorem weaken {Δ' : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (h : Der σ Γ Δ φ) (hs : Δ ⊆ Δ') :
    Der σ Γ Δ' φ :=
  let ⟨n, p⟩ := h; ⟨n, p.weaken hs (fun _ h => h)⟩

theorem cut [ModalSys.TOpt] [Γ.Presented] {A φ : WFF σ Γ 0} (h₁ : Der σ Γ Δ A)
    (h₂ : Der σ Γ (A :: Δ) φ) :
    Der σ Γ Δ φ := by
  obtain ⟨n, p⟩ := h₁
  obtain ⟨m, q⟩ := h₂
  exact GK.cut A (p.weaken (fun _ h => h) (by lsub)) q

theorem ax [ModalSys.GKBase] [Γ.Presented] {φ : WFF σ Γ 0} (h : φ ∈ Δ) : Der σ Γ Δ φ :=
  GK.ident φ h List.mem_cons_self

theorem and_intro {φ ψ : WFF σ Γ 0} (h₁ : Der σ Γ Δ φ) (h₂ : Der σ Γ Δ ψ) :
    Der σ Γ Δ (φ.and ψ) := by
  obtain ⟨n, p⟩ := h₁
  obtain ⟨m, q⟩ := h₂
  have hp := p.weaken (fun _ h => h) (Θ' := [φ, φ.and ψ]) (by lsub)
  have hq := q.weaken (fun _ h => h) (Θ' := [ψ, φ.and ψ]) (by lsub)
  exact ⟨_, .andR List.mem_cons_self (both hp hq).1 (both hp hq).2⟩

theorem and_elim_l [ModalSys.GKBase] [Γ.Presented] {φ ψ : WFF σ Γ 0} (h : Der σ Γ Δ (φ.and ψ)) :
    Der σ Γ Δ φ := by
  refine cut h ?_
  obtain ⟨n, e⟩ := GK.ident φ (Δ := φ :: ψ :: φ.and ψ :: Δ) (Θ := [φ]) List.mem_cons_self
    List.mem_cons_self
  exact ⟨_, .andL List.mem_cons_self e⟩

theorem and_elim_r [ModalSys.GKBase] [Γ.Presented] {φ ψ : WFF σ Γ 0} (h : Der σ Γ Δ (φ.and ψ)) :
    Der σ Γ Δ ψ := by
  refine cut h ?_
  obtain ⟨n, e⟩ := GK.ident ψ (Δ := φ :: ψ :: φ.and ψ :: Δ) (Θ := [ψ])
    (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self
  exact ⟨_, .andL List.mem_cons_self e⟩

theorem or_intro_l {φ : WFF σ Γ 0} (ψ : WFF σ Γ 0) (h : Der σ Γ Δ φ) : Der σ Γ Δ (φ.or ψ) := by
  obtain ⟨n, p⟩ := h
  exact ⟨_, .orR List.mem_cons_self (p.weaken (fun _ h => h) (by lsub))⟩

theorem or_intro_r (φ : WFF σ Γ 0) {ψ : WFF σ Γ 0} (h : Der σ Γ Δ ψ) : Der σ Γ Δ (φ.or ψ) := by
  obtain ⟨n, p⟩ := h
  exact ⟨_, .orR List.mem_cons_self (p.weaken (fun _ h => h) (by lsub))⟩

theorem or_elim [ModalSys.TOpt] [Γ.Presented] {φ ψ χ : WFF σ Γ 0} (h : Der σ Γ Δ (φ.or ψ))
    (h₁ : Der σ Γ (φ :: Δ) χ) (h₂ : Der σ Γ (ψ :: Δ) χ) : Der σ Γ Δ χ := by
  refine cut h ?_
  obtain ⟨n, p⟩ := h₁
  obtain ⟨m, q⟩ := h₂
  have hp := p.weaken (Δ' := φ :: φ.or ψ :: Δ) (by lsub) (fun _ h => h)
  have hq := q.weaken (Δ' := ψ :: φ.or ψ :: Δ) (by lsub) (fun _ h => h)
  exact ⟨_, .orL List.mem_cons_self (both hp hq).1 (both hp hq).2⟩

theorem imp_intro {φ ψ : WFF σ Γ 0} (h : Der σ Γ (φ :: Δ) ψ) : Der σ Γ Δ (φ.imp ψ) := by
  obtain ⟨n, p⟩ := h
  exact ⟨_, .impR List.mem_cons_self (p.weaken (fun _ h => h) (by lsub))⟩

theorem imp_elim [ModalSys.GKBase] [Γ.Presented] {φ ψ : WFF σ Γ 0} (h : Der σ Γ Δ (φ.imp ψ))
    (h' : Der σ Γ Δ φ) : Der σ Γ Δ ψ := by
  refine cut h ?_
  obtain ⟨n, p⟩ := h'
  have hp := p.weaken (Δ' := φ.imp ψ :: Δ) (Θ' := [φ, ψ]) (by lsub) (by lsub)
  obtain ⟨m, q⟩ := GK.ident ψ (Δ := ψ :: φ.imp ψ :: Δ) (Θ := [ψ]) List.mem_cons_self
    List.mem_cons_self
  exact ⟨_, .impL List.mem_cons_self (both hp q).1 (both hp q).2⟩

theorem top_intro : Der σ Γ Δ .top := ⟨0, .topR List.mem_cons_self⟩

theorem bot_elim [ModalSys.TOpt] [Γ.Presented] (φ : WFF σ Γ 0) (h : Der σ Γ Δ .bot) : Der σ Γ Δ φ :=
  cut h ⟨0, .botL List.mem_cons_self⟩

theorem lem [ModalSys.GKBase] [Γ.Presented] (φ : WFF σ Γ 0) : Der σ Γ Δ (φ.or φ.neg) := by
  obtain ⟨n, e⟩ := GK.ident φ (Δ := φ :: Δ) (Θ := [WFF.bot, φ, φ.neg, φ.or φ.neg])
    List.mem_cons_self (by simp)
  exact ⟨_, .orR List.mem_cons_self (.impR (by simp) e)⟩

theorem all_intro [Γ.NoSlots] (u : ℕ) (T : VarType) (hu : Γ.RootFresh (.free u))
    {φ : WFF σ (Γ.insert (.free u) T) 0}
    (h : Der σ (Γ.insert (.free u) T) (Δ.map (WFF.weaken hu.root T)) φ) :
    Der σ Γ Δ (.all T (WFF.bindFree u hu Ctx.NoSlots.slots T φ)) := by
  obtain ⟨n, p⟩ := h
  exact ⟨_, .allR u T hu List.mem_cons_self (p.weaken (fun _ h => h) (by lsub))⟩

theorem all_elim [ModalSys.GKBase] [Γ.Presented] (T : VarType)
    {φ : WFF σ (Γ.insert (.bnd 0) T) 1} {a : Ann T} (t : Term σ Γ T a)
    (h : Der σ Γ Δ (.all T φ)) : Der σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ) := by
  refine cut h ?_
  obtain ⟨n, e⟩ := GK.ident (WFF.instantiate Ctx.NoSlots.slots t φ)
    (Δ := WFF.instantiate Ctx.NoSlots.slots t φ :: .all T φ :: Δ)
    (Θ := [WFF.instantiate Ctx.NoSlots.slots t φ]) List.mem_cons_self List.mem_cons_self
  exact ⟨_, .allL T t List.mem_cons_self e⟩

theorem ex_intro [Γ.NoSlots] (T : VarType) {φ : WFF σ (Γ.insert (.bnd 0) T) 1} {a : Ann T}
    (t : Term σ Γ T a) (h : Der σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ)) :
    Der σ Γ Δ (.ex T φ) := by
  obtain ⟨n, p⟩ := h
  exact ⟨_, .exR T t List.mem_cons_self (p.weaken (fun _ h => h) (by lsub))⟩

theorem ex_elim [ModalSys.TOpt] [Γ.Presented] (u : ℕ) (T : VarType) (hu : Γ.RootFresh (.free u))
    {φ : WFF σ (Γ.insert (.free u) T) 0} {ψ : WFF σ Γ 0}
    (h : Der σ Γ Δ (.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T φ)))
    (h' : Der σ (Γ.insert (.free u) T) (φ :: Δ.map (WFF.weaken hu.root T))
      (WFF.weaken hu.root T ψ)) : Der σ Γ Δ ψ := by
  refine cut h ?_
  obtain ⟨n, p⟩ := h'
  exact ⟨_, .exL u T hu List.mem_cons_self (p.weaken (by lsub) (fun _ h => h))⟩

theorem eq_intro (t : Term σ Γ .Var .var) : Der σ Γ Δ (.eq t t) :=
  ⟨_, .ref t (.ax (n := 0) (.eq t t) trivial List.mem_cons_self List.mem_cons_self)⟩

theorem eq_elim [ModalSys.GKBase] [Γ.Presented] (φ : WFF σ (Γ.insert (.bnd 0) .Var) 1)
    (t s : Term σ Γ .Var .var) (h : Der σ Γ Δ (.eq t s))
    (h' : Der σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ)) :
    Der σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots s φ) := by
  refine cut h' (cut (h.weaken (by lsub))
    (cut (A := .eq s t) (GK.eq_symm t s List.mem_cons_self List.mem_cons_self) ?_))
  exact GK.replace φ t s (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) List.mem_cons_self

theorem K_box [Γ.NoSlots] {Δ₁ : List (WFF σ Γ.boxIn 0)} {φ : WFF σ Γ.boxIn 0}
    (h : Der σ Γ.boxIn Δ₁ φ) :
    Der σ Γ (Δ₁.map fun ψ => WFF.box (Γ := Γ) ψ) (.box φ) := by
  obtain ⟨n, p⟩ := h
  exact ⟨_, .boxR (L := []) List.mem_cons_self (fun χ hχ => List.mem_map_of_mem hχ)
    (List.nil_subset _) (p.weaken (fun _ h => List.mem_append_left _ h)
      (fun a ha => by rw [kp4_nil]; exact ha))⟩

theorem dia_bot [ModalSys.TOpt] (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) [Γ.Presented]
    (h : Der σ Γ Δ (.dia x hx .bot)) : Der σ Γ Δ .bot :=
  cut h ⟨_, .diaL x hx (ψ := .bot) (Δ₁ := []) (Θ₁ := []) (L := []) List.mem_cons_self
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
    (List.nil_subset _) (.botL (n := 0) List.mem_cons_self)⟩

/-- Weak D: `□⊥ ⇒` by `serial`. -/
theorem D_box [ModalSys.TOpt] [Γ.Presented] (hD : ModalSys.D = true) (h : Der σ Γ Δ (.box .bot)) :
    Der σ Γ Δ .bot :=
  cut h ⟨_, .serial hD (Δ₁ := [.bot]) (L := [])
    (fun χ hχ => by rw [List.mem_singleton.mp hχ]; exact List.mem_cons_self) (List.nil_subset _)
    (.botL (n := 0) (List.mem_append_left _ List.mem_cons_self))⟩

/-- Weak T, `T_box`: `TL` and identity. -/
theorem T_box [ModalSys.TOpt] [ModalSys.GKBase] [Γ.Presented] (hT : ModalSys.T = true)
    {φ : WFF σ Γ.boxIn 0} (h : Der σ Γ Δ (.box φ)) :
    Der σ Γ Δ (WFF.collapse (Ctx.collapses_boxIn_self hT Γ) Ctx.NoSlots.slots φ) := by
  refine cut h ?_
  obtain ⟨n, e⟩ := GK.ident (WFF.collapse (Ctx.collapses_boxIn_self hT Γ) Ctx.NoSlots.slots φ)
    (Δ := WFF.collapse (Ctx.collapses_boxIn_self hT Γ) Ctx.NoSlots.slots φ :: WFF.box φ :: Δ)
    (Θ := [WFF.collapse (Ctx.collapses_boxIn_self hT Γ) Ctx.NoSlots.slots φ])
    List.mem_cons_self List.mem_cons_self
  exact ⟨_, .TL hT List.mem_cons_self e⟩

/-- Weak 4, `four_box`: `□R` with the boxed hypothesis' copy. -/
theorem four_box [ModalSys.GKBase] [Γ.Presented] (hF : ModalSys.Four = true)
    {φ : WFF σ Γ.boxIn 0} (h : Der σ Γ Δ (.box φ)) :
    Der σ Γ Δ (.box (.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots φ))) := by
  refine cut h ?_
  obtain ⟨k, q⟩ := GK.ident (WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots φ))
    (Δ := [φ] ++ cp4 [φ]) (Θ := WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ)
      Ctx.NoSlots.slots φ) :: kp4 []) (List.mem_append_right _ (mem_cp4 hF List.mem_cons_self))
    List.mem_cons_self
  exact ⟨_, .boxR (Δ₁ := [φ]) (L := []) List.mem_cons_self
    (fun χ hχ => by rw [List.mem_singleton.mp hχ]; exact List.mem_cons_self)
    (List.nil_subset _) q⟩

/-- Weak 4, `four_dia`: `□_x φ` is `¬◇_x¬φ`, and `□R` takes `◇_x¬φ`'s copy. -/
theorem four_dia [ModalSys.GKBase] [Γ.Presented] (hF : ModalSys.Four = true) (x : VarSymb)
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {φ : WFF σ (Γ.diaIn x) 0}
    (h : Der σ Γ Δ (WFF.boxx x hx φ)) :
    Der σ Γ Δ (.box (WFF.boxx (.step x .keep) (Ctx.exists_keep_dia hF hx)
      (WFF.shift (Ctx.shifts_diaIn_keep hF Γ x) Ctx.NoSlots.slots φ))) := by
  refine cut h ?_
  have hC : WFF.dia (.step x .keep) (Ctx.exists_keep_dia hF hx)
      (WFF.shift (Ctx.shifts_diaIn_keep hF Γ x) Ctx.NoSlots.slots φ).neg ∈
        kp4 [WFF.dia x hx φ.neg] := mem_kp4 hF List.mem_cons_self
  obtain ⟨k, q⟩ := GK.ident (WFF.dia (.step x .keep) (Ctx.exists_keep_dia hF hx)
      (WFF.shift (Ctx.shifts_diaIn_keep hF Γ x) Ctx.NoSlots.slots φ).neg)
    (Δ := WFF.dia (.step x .keep) (Ctx.exists_keep_dia hF hx)
      (WFF.shift (Ctx.shifts_diaIn_keep hF Γ x) Ctx.NoSlots.slots φ).neg :: ([] ++ cp4 []))
    (Θ := WFF.bot :: (WFF.dia (.step x .keep) (Ctx.exists_keep_dia hF hx)
      (WFF.shift (Ctx.shifts_diaIn_keep hF Γ x) Ctx.NoSlots.slots φ).neg).neg ::
        kp4 [WFF.dia x hx φ.neg])
    List.mem_cons_self (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))
  exact ⟨_, .impL (φ := WFF.dia x hx φ.neg) (ψ := .bot) List.mem_cons_self
    (.boxR (Δ₁ := []) (L := [WFF.dia x hx φ.neg]) (List.mem_cons_of_mem _ List.mem_cons_self)
      (fun _ h => absurd h List.not_mem_nil)
      (fun _ h => by rw [List.mem_singleton.mp h]; exact List.mem_cons_self)
      (.impR List.mem_cons_self q))
    (.botL List.mem_cons_self)⟩

end Der

/-- Hypotheses moved to the right, negated. -/
theorem negRight {Γ : Ctx} : ∀ (L : List (WFF σ Γ 0)) {n : ℕ} {M Θ : List (WFF σ Γ 0)},
    GK σ n Γ (L ++ M) Θ → ∃ k, GK σ k Γ M (Θ ++ L.map WFF.neg)
  | [], _, _, _, p => ⟨_, p.weaken (by lsub) (by simp)⟩
  | a :: L, _, M, Θ, p => by
      obtain ⟨k, e⟩ := negRight L (M := a :: M) (Θ := Θ) (p.weaken (by lsub) (fun _ h => h))
      refine ⟨_, .impR (φ := a) (ψ := .bot) (by simp)
        (e.weaken (fun _ h => h) (fun b hb => ?_))⟩
      simp only [List.mem_append, List.mem_map, List.map_cons, List.mem_cons] at hb ⊢
      tauto

/-- Conclusions whose negations are hypotheses dropped. -/
theorem dropNeg {Γ : Ctx} : ∀ (L : List (WFF σ Γ 0)) {n : ℕ} {A Θ : List (WFF σ Γ 0)},
    (∀ χ ∈ L, χ.neg ∈ A) → GK σ n Γ A (L ++ Θ) → ∃ k, GK σ k Γ A Θ
  | [], _, _, _, _, p => ⟨_, p⟩
  | a :: L, _, A, Θ, hL, p => by
      obtain ⟨k, e⟩ := dropNeg L (A := A) (Θ := a :: Θ)
        (fun χ hχ => hL χ (List.mem_cons_of_mem _ hχ)) (p.weaken (fun _ h => h) (by lsub))
      exact ⟨_, .impL (hL a List.mem_cons_self) (e.mono_height (Nat.le_succ_of_le le_rfl))
        (.botL (n := k + 1) List.mem_cons_self)⟩

namespace Der

variable {Γ : Ctx} {Δ : List (WFF σ Γ 0)}

theorem K_dia [Γ.NoSlots] (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    {Δ₁ : List (WFF σ Γ.boxIn 0)} {Δ₂ : List (WFF σ (Γ.diaIn x) 0)} {φ ψ : WFF σ (Γ.diaIn x) 0}
    (h : Der σ (Γ.diaIn x) (ψ :: (Δ₂ ++ Δ₁.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))) φ) :
    Der σ Γ (.dia x hx ψ :: (Δ₂.map (WFF.boxx x hx) ++ Δ₁.map fun χ => WFF.box (Γ := Γ) χ))
      (.dia x hx φ) := by
  obtain ⟨n, p⟩ := h
  obtain ⟨k, e⟩ := negRight Δ₂ (M := ψ :: Δ₁.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))
    (p.weaken (by lsub) (fun _ h => h))
  have d : GK σ (k + 1) Γ
      (.dia x hx ψ :: (Δ₂.map (WFF.boxx x hx) ++ Δ₁.map fun χ => WFF.box (Γ := Γ) χ))
      (Δ₂.map (fun δ => WFF.dia x hx δ.neg) ++ [.dia x hx φ]) := by
    refine .diaL x hx (Δ₁ := Δ₁) (Θ₁ := [φ] ++ Δ₂.map WFF.neg) (L := []) List.mem_cons_self
      (fun χ hχ => ?_) (fun χ hχ => ?_) (List.nil_subset _)
      (e.weaken (by lsub4) (fun _ h => List.mem_append_left _ h))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map_of_mem hχ))
    · rcases List.mem_append.mp hχ with hχ | hχ
      · rw [List.mem_singleton.mp hχ]; exact List.mem_append_right _ List.mem_cons_self
      · obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hχ
        exact List.mem_append_left _ (List.mem_map_of_mem (f := fun δ => WFF.dia x hx δ.neg) hδ)
  refine dropNeg _ (fun χ hχ => ?_) d
  obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hχ
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem hδ))

/-! ### The witness views (`Opt`) -/

/-- In the view of the witness `y`, hypotheses `□⁰_y δ` moved in give their bodies `δ`: re-open
    `◇⁰_y ¬δ` on the right (`reopenR`). -/
theorem optBoxIn (hO : ModalSys.Opt = true) (κ : WitKind) (y : VarSymb)
    (hy : ∃ X, Γ.witK κ y = some X) :
    ∀ (L : List (WFF σ (Γ.optInK κ y) 0)) {n : ℕ} {M Θ : List (WFF σ (Γ.optInK κ y) 0)},
      GK σ n (Γ.optInK κ y) (L ++ M) Θ →
      ∃ k, GK σ k (Γ.optInK κ y)
        ((L.map (WFF.optBox hO κ y hy)).map (WFF.mono (Ctx.le_optInK Γ κ y)) ++ M) Θ
  | [], _, _, _, p => ⟨_, p⟩
  | δ :: L, _, M, Θ, p => by
      obtain ⟨k, e⟩ := optBoxIn hO κ y hy L (M := δ :: M) (Θ := Θ)
        (p.weaken (by lsub) (fun _ h => h))
      refine ⟨_, .impL (ψ := .bot) (φ := WFF.optx hO κ y
          ((Ctx.opened_optInK hy).imp fun _ h => h.1)
          (WFF.mono (Ctx.le_optInK (Γ.optInK κ y) κ y) δ.neg)) List.mem_cons_self
        (.reopenR hO κ y (Ctx.opened_optInK hy) (χ := δ.neg) List.mem_cons_self
          (.impR (φ := δ) (ψ := .bot) List.mem_cons_self (e.weaken (by lsub) (by lsub))))
        (.botL List.mem_cons_self)⟩

/-- `K⁰`: open the witness on the left, re-open the conclusion on the right. -/
theorem K_opt (hO : ModalSys.Opt = true) (κ : WitKind) (y : VarSymb)
    (hy : ∃ X, Γ.witK κ y = some X) {Δ₁ : List (WFF σ Γ 0)}
    {Δ₂ : List (WFF σ (Γ.optInK κ y) 0)} {φ ψ : WFF σ (Γ.optInK κ y) 0}
    (h : Der σ (Γ.optInK κ y) (ψ :: (Δ₂ ++ Δ₁.map (WFF.mono (Ctx.le_optInK Γ κ y)))) φ) :
    Der σ Γ (.optx hO κ y hy ψ :: (Δ₂.map (WFF.optBox hO κ y hy) ++ Δ₁))
      (.optx hO κ y hy φ) := by
  obtain ⟨n, p⟩ := h
  obtain ⟨k, e⟩ := optBoxIn hO κ y hy Δ₂ (M := ψ :: Δ₁.map (WFF.mono (Ctx.le_optInK Γ κ y)))
    (Θ := [φ]) (p.weaken (by lsub) (fun _ h => h))
  exact ⟨_, .optL hO κ y hy List.mem_cons_self (.reopenR hO κ y (Ctx.opened_optInK hy)
    (χ := φ) List.mem_cons_self (e.weaken (fun a ha => by
      simp only [List.map_cons, List.map_append, List.mem_cons, List.mem_append] at ha ⊢
      tauto) (by lsub)))⟩

theorem opt_bot [ModalSys.TOpt] [Γ.Presented] (hO : ModalSys.Opt = true) (κ : WitKind) (y : VarSymb)
    (hy : ∃ X, Γ.witK κ y = some X) (h : Der σ Γ Δ (.optx hO κ y hy .bot)) :
    Der σ Γ Δ .bot :=
  cut h ⟨_, .optL hO κ y hy List.mem_cons_self (.botL (n := 0) List.mem_cons_self)⟩

/-- Reopening is `reopenR`. -/
theorem opt_reopen (hO : ModalSys.Opt = true) (κ : WitKind) (y : VarSymb)
    (hy : ∃ X, Γ.witK κ y = some X ∧ Γ (.step y κ.step) = some X) {ψ : WFF σ Γ 0}
    (h : Der σ Γ Δ ψ) :
    Der σ Γ Δ (.optx hO κ y (hy.imp fun _ h => h.1) (WFF.mono (Ctx.le_optInK Γ κ y) ψ)) := by
  obtain ⟨n, p⟩ := h
  exact ⟨_, .reopenR hO κ y hy List.mem_cons_self (p.weaken (fun _ h => h) (by lsub))⟩

/-- The bridge `◇ ◇⁰_u φ ⊢ ◇_u φ`: `□R` with the conclusion's fold. -/
theorem opt_dia [ModalSys.GKBase] [Γ.Presented] (hO : ModalSys.Opt = true) (u : VarSymb)
    (hu : ∃ X, Γ.ref u = some (.VTypeDia X)) {φ : WFF σ (Γ.diaIn u) 0}
    (h : Der σ Γ Δ (WFF.diaOpt hO u hu φ)) : Der σ Γ Δ (.dia u hu φ) := by
  refine cut h ?_
  have hm : WFF.optx hO .arrow u (hu.imp fun _ h => Ctx.boxIn_wit.mpr ⟨hO, h⟩)
      (WFF.mono (hu.elim fun _ h => Ctx.le_diaIn_boxIn_optIn hO h) φ) ∈
        kp4 [WFF.dia u hu φ] := by
    rw [kp4_of_opt hO]
    exact List.mem_flatMap.mpr ⟨_, List.mem_cons_self, List.mem_cons_self⟩
  obtain ⟨k, e⟩ := GK.ident (WFF.optx hO .arrow u (hu.imp fun _ h => Ctx.boxIn_wit.mpr ⟨hO, h⟩)
      (WFF.mono (hu.elim fun _ h => Ctx.le_diaIn_boxIn_optIn hO h) φ))
    (Δ := WFF.optx hO .arrow u (hu.imp fun _ h => Ctx.boxIn_wit.mpr ⟨hO, h⟩)
      (WFF.mono (hu.elim fun _ h => Ctx.le_diaIn_boxIn_optIn hO h) φ) :: ([] ++ cp4 []))
    (Θ := WFF.bot :: (WFF.optx hO .arrow u (hu.imp fun _ h => Ctx.boxIn_wit.mpr ⟨hO, h⟩)
      (WFF.mono (hu.elim fun _ h => Ctx.le_diaIn_boxIn_optIn hO h) φ)).neg ::
        kp4 [WFF.dia u hu φ])
    List.mem_cons_self (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
  exact ⟨_, .impL List.mem_cons_self
    (.boxR (Δ₁ := []) (L := [WFF.dia u hu φ]) List.mem_cons_self
      (fun _ h => absurd h List.not_mem_nil)
      (fun _ h => by rw [List.mem_singleton.mp h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      (.impR List.mem_cons_self e))
    (.botL List.mem_cons_self)⟩

/-- The bridge `◇_u φ ⊢ ◇ ◇⁰_u φ`: `◇_uL` with the hypothesis `□¬◇⁰_u φ` moved in, where `u` is
    opened, and `reopenR`. -/
theorem dia_opt [ModalSys.GKBase] [Γ.Presented] (hO : ModalSys.Opt = true) (u : VarSymb)
    (hu : ∃ X, Γ.ref u = some (.VTypeDia X)) {φ : WFF σ (Γ.diaIn u) 0}
    (h : Der σ Γ Δ (.dia u hu φ)) : Der σ Γ Δ (WFF.diaOpt hO u hu φ) := by
  have hyo : ∃ X, (Γ.diaIn u).witK .arrow u = some X ∧ (Γ.diaIn u) (.step u .dia) = some X :=
    hu.imp fun X hX => ⟨Ctx.boxIn_wit.mpr ⟨hO, hX⟩, by
      change (if u = u then (match Γ.ref u with | some (.VTypeDia X) => some X | _ => none)
        else none) = some X
      rw [if_pos rfl, hX]⟩
  set χ := WFF.optx hO .arrow u (hu.imp fun _ h => Ctx.boxIn_wit.mpr ⟨hO, h⟩)
    (WFF.mono (hu.elim fun _ h => Ctx.le_diaIn_boxIn_optIn hO h) φ)
  have he : WFF.mono (Ctx.le_boxIn_diaIn Γ u) χ = WFF.optx hO .arrow u
      (hyo.imp fun _ h => h.1) (WFF.mono (Ctx.le_optInK (Γ.diaIn u) .arrow u) φ) :=
    congrArg (WFF.optx hO .arrow u _) (WFF.mono_mono _ _ φ)
  obtain ⟨k, e⟩ := GK.ident φ (Δ := φ :: ([χ.neg] ++ cp4 [χ.neg]).map
      (WFF.mono (Ctx.le_boxIn_diaIn Γ u)))
    (Θ := φ :: WFF.optx hO .arrow u (hyo.imp fun _ h => h.1)
      (WFF.mono (Ctx.le_optInK (Γ.diaIn u) .arrow u) φ) :: [])
    List.mem_cons_self List.mem_cons_self
  have hp : GK σ (k + 2) (Γ.diaIn u)
      (φ :: ([χ.neg] ++ cp4 [χ.neg]).map (WFF.mono (Ctx.le_boxIn_diaIn Γ u)))
      ([] ++ (kp4 []).map (WFF.mono (Ctx.le_boxIn_diaIn Γ u))) := by
    rw [kp4_nil]
    refine .impL (φ := WFF.mono (Ctx.le_boxIn_diaIn Γ u) χ) (ψ := .bot)
      (List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_append_left _ List.mem_cons_self)))
      ?_ (.botL List.mem_cons_self)
    rw [he]
    exact .reopenR hO .arrow u hyo List.mem_cons_self e
  obtain ⟨n, p⟩ := h
  refine cut ⟨n, p⟩ ⟨_, .impR List.mem_cons_self (.diaL u hu (ψ := φ) (Δ₁ := [χ.neg])
    (Θ₁ := []) (L := []) (List.mem_cons_of_mem _ List.mem_cons_self)
    (fun c hc => by rw [List.mem_singleton.mp hc]; exact List.mem_cons_self)
    (fun _ h => absurd h List.not_mem_nil) (List.nil_subset _) hp)⟩

end Der

/-! ## The translation -/

/-- Strong 4 is off: no type has 4's lift. -/
theorem ModalSys.GKBase.liftableR [ModalSys.GKBase] (T : VarType) : T.liftableR = false := by
  cases T <;> simp [VarType.liftableR, ModalSys.GKBase.noFourStrong, ModalSys.GKBase.noFourStrongW]

/-- The rules outside K, KD, K4 and KD4, excluded by their flags. -/
macro "kflag" : tactic => `(tactic| first
  | exact absurd (ModalSys.GKBase.tOpt ‹ModalSys.T = true›) (by rw [‹ModalSys.Opt = false›]; decide)
  | exact absurd (ModalSys.GKBase.tOpt ‹ModalSys.T = true›)
      (by rw [ModalSys.noOpt_of_Four ‹ModalSys.Four = true›]; decide)
  | exact absurd ‹ModalSys.TStrong = true› (by simp [ModalSys.GKBase.noTStrong])
  | exact absurd ‹ModalSys.DStrong = true› (by simp [ModalSys.GKBase.noDStrong])
  | exact absurd ‹ModalSys.B = true› (by simp [ModalSys.GKBase.noB])
  | exact absurd ‹ModalSys.BStrong = true› (by simp [ModalSys.GKBase.noBStrong])
  | exact absurd ‹ModalSys.BStrongW = true› (by simp [ModalSys.GKBase.noBStrongW])
  | exact absurd ‹ModalSys.FourStrong = true› (by simp [ModalSys.GKBase.noFourStrong])
  | exact absurd ‹ModalSys.FourStrongW = true› (by simp [ModalSys.GKBase.noFourStrongW])
  | exact absurd ‹ModalSys.Five = true› (by simp [ModalSys.GKBase.noFive])
  | exact absurd ‹ModalSys.FiveStrong = true› (by simp [ModalSys.GKBase.noFiveStrong])
  | exact absurd ‹VarType.liftableR _ = true› (by rw [ModalSys.GKBase.liftableR]; decide))

/-- ⭐**Natural deduction into GK**, along any substitution into a presented context. -/
theorem ofProof [ModalSys.GKBase] {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0}
    (p : Proof σ Γ Δ φ) : ∀ {Γ' : Ctx} [Γ'.Presented] {ι : VarSymb → VarSymb} (θ : Subst σ Γ')
      (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0),
      Der σ Γ' (Δ.map (WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots))
        (WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots φ) := by
  induction p
  case ax Γ φ =>
    intro Γ' _ ι θ hθ hc hΓ
    exact Der.ax List.mem_cons_self
  case weak Γ Δ φ ψ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    exact (ih θ hθ hc hΓ).weaken (by lsub)
  case contr Γ Δ φ ψ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    exact (ih θ hθ hc hΓ).weaken (by lsub)
  case exch Γ Δ₁ Δ₂ φ ψ χ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    refine (ih θ hθ hc hΓ).weaken (fun a ha => ?_)
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at ha ⊢
    tauto
  case weak_ctx Γ Δ φ u T hu p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    have hle := Ctx.le_insert hu.root T
    have hΓ₀ := hΓ.of_le hle
    have key : ∀ ψ : WFF σ Γ 0, WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots
        (WFF.weaken hu.root T ψ) = WFF.subst ι θ (hθ.restrict hle) (hc.restrict hle) hΓ₀
          Ctx.NoSlots.slots ψ :=
      fun ψ => WFF.subst_mono hle θ hθ hc hΓ₀ hΓ Ctx.NoSlots.slots ψ
    rw [List.map_map, show (WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots ∘ WFF.weaken hu.root T) =
      WFF.subst ι θ (hθ.restrict hle) (hc.restrict hle) hΓ₀ Ctx.NoSlots.slots from funext key,
      key]
    exact ih θ (hθ.restrict hle) (hc.restrict hle) hΓ₀
  case and_intro Γ Δ φ ψ p q ihp ihq =>
    intro Γ' _ ι θ hθ hc hΓ
    exact Der.and_intro (ihp θ hθ hc hΓ) (ihq θ hθ hc hΓ)
  case and_elim_l Γ Δ φ ψ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    exact Der.and_elim_l (ih θ hθ hc hΓ)
  case and_elim_r Γ Δ φ ψ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    exact Der.and_elim_r (ih θ hθ hc hΓ)
  case or_intro_l Γ Δ φ ψ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    exact Der.or_intro_l _ (ih θ hθ hc hΓ)
  case or_intro_r Γ Δ φ ψ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    exact Der.or_intro_r _ (ih θ hθ hc hΓ)
  case or_elim Γ Δ φ ψ χ p q r ihp ihq ihr =>
    intro Γ' _ ι θ hθ hc hΓ
    exact Der.or_elim (ihp θ hθ hc hΓ) (ihq θ hθ hc hΓ) (ihr θ hθ hc hΓ)
  case imp_intro Γ Δ φ ψ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    exact Der.imp_intro (ih θ hθ hc hΓ)
  case imp_elim Γ Δ φ ψ p q ihp ihq =>
    intro Γ' _ ι θ hθ hc hΓ
    exact Der.imp_elim (ihp θ hθ hc hΓ) (ihq θ hθ hc hΓ)
  case top_intro =>
    intro Γ' _ ι θ hθ hc hΓ
    exact Der.top_intro
  case bot_elim Γ Δ φ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    exact Der.bot_elim _ (ih θ hθ hc hΓ)
  case lem =>
    intro Γ' _ ι θ hθ hc hΓ
    exact Der.lem _
  case all_intro Γ _ Δ u T hu φ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
    have hu' : Γ'.RootFresh (.free (Ctx.Presented.bound Γ')) := Ctx.Presented.fresh_bound _ le_rfl
    have ih' := ih (Γ' := Γ'.insert (.free (Ctx.Presented.bound Γ')) T)
      (θ.rename u _ T hu'.root) (Subst.ok_rename hθ T hu'.root)
      (Subst.coh_rename hθ hc hu T hu'.root) (hΓ.insertFree u T)
    have hf : (_ ∘ WFF.weaken hu.root T) =
        WFF.weaken hu'.root T ∘ WFF.subst ι θ hθ hc hΓ hΓ' :=
      funext fun ψ => WFF.subst_weaken_rename θ hθ hc hΓ hΓ' hu hu' T ψ
    rw [List.map_map, hf, ← List.map_map] at ih'
    have := Der.all_intro _ T hu' ih'
    rw [← WFF.subst_bindFree θ hθ hc hΓ hΓ' hu hu' T φ] at this
    exact this
  case all_elim Γ _ Δ T φ a t p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    rw [WFF.subst_instantiate θ hθ hc hΓ Ctx.NoSlots.slots t φ]
    exact Der.all_elim T _ (ih θ hθ hc hΓ)
  case ex_intro Γ _ Δ T φ a t p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    have ih' := ih θ hθ hc hΓ
    rw [WFF.subst_instantiate θ hθ hc hΓ Ctx.NoSlots.slots t φ] at ih'
    exact Der.ex_intro T _ ih'
  case ex_elim Γ _ Δ u T hu φ ψ p q ihp ihq =>
    intro Γ' _ ι θ hθ hc hΓ
    have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
    have hu' : Γ'.RootFresh (.free (Ctx.Presented.bound Γ')) := Ctx.Presented.fresh_bound _ le_rfl
    have ihp' := ihp θ hθ hc hΓ
    have ihq' := ihq (Γ' := Γ'.insert (.free (Ctx.Presented.bound Γ')) T)
      (θ.rename u _ T hu'.root) (Subst.ok_rename hθ T hu'.root)
      (Subst.coh_rename hθ hc hu T hu'.root) (hΓ.insertFree u T)
    have hf : (_ ∘ WFF.weaken hu.root T) =
        WFF.weaken hu'.root T ∘ WFF.subst ι θ hθ hc hΓ hΓ' :=
      funext fun ψ => WFF.subst_weaken_rename θ hθ hc hΓ hΓ' hu hu' T ψ
    rw [List.map_cons, List.map_map, hf, ← List.map_map,
      WFF.subst_weaken_rename θ hθ hc hΓ hΓ' hu hu' T ψ] at ihq'
    change Der σ Γ' _ (WFF.ex T (WFF.subst _ _ _ _ _ _ (WFF.bindFree u hu _ T φ))) at ihp'
    rw [WFF.subst_bindFree θ hθ hc hΓ hΓ' hu hu' T φ] at ihp'
    exact Der.ex_elim _ T hu' ihp' ihq'
  case eq_intro Γ Δ t =>
    intro Γ' _ ι θ hθ hc hΓ
    exact Der.eq_intro _
  case eq_elim Γ _ Δ φ t s p q ihp ihq =>
    intro Γ' _ ι θ hθ hc hΓ
    have ihq' := ihq θ hθ hc hΓ
    rw [WFF.subst_instantiate θ hθ hc hΓ Ctx.NoSlots.slots t φ] at ihq'
    rw [WFF.subst_instantiate θ hθ hc hΓ Ctx.NoSlots.slots s φ]
    exact Der.eq_elim _ _ _ (ihp θ hθ hc hΓ) ihq'
  case pair_elim Γ₀ _ A B u₁ u₂ z hu hz₁ hu₁ hu₂ hzf Δ φ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    have hΓ₀ : Γ₀.SlotsFrom 0 := Ctx.NoSlots.slots
    have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
    have key := fun χ => WFF.subst_bindPair u₁ u₂ z hu hz₁ hu₁ hu₂ hzf hΓ₀ hΓ' A B θ hθ hc χ
    rw [List.map_map, show (WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots ∘
      WFF.bindPair u₁ u₂ z hu hz₁ hu₁ hu₂ hzf Ctx.NoSlots.slots A B) = _ from funext key, key]
    exact ih (θ.pairSplit u₁ u₂ z) (Subst.ok_pairSplit hzf hθ)
      (Subst.coh_pairSplit hu hz₁ hu₁ hu₂ hzf hθ hc) ((hΓ₀.insertFree u₁ A).insertFree u₂ B)
  case K_box Γ Δ φ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    have e : (Δ.map fun ψ => WFF.box (Γ := Γ) ψ).map (WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots) =
        (Δ.map (WFF.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn
          Ctx.NoSlots.slots)).map fun ψ => WFF.box (Γ := Γ') ψ := by
      rw [List.map_map, List.map_map]
      rfl
    rw [e]
    exact Der.K_box (ih θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn)
  case K_dia Γ x hx Δ₁ Δ₂ φ ψ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
    have hwx : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
      hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
    have ih' := ih (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
      (hΓ.diaIn x)
    have hf : (_ ∘ WFF.mono (Ctx.le_boxIn_diaIn Γ x)) =
        WFF.mono (Ctx.le_boxIn_diaIn Γ' (ι x)) ∘
          WFF.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn Ctx.NoSlots.slots :=
      funext fun χ => WFF.subst_diaIn_mono θ hθ hc hx hw hΓ Ctx.NoSlots.slots
        Ctx.NoSlots.slots χ
    rw [List.map_cons, List.map_append, List.map_map, hf, ← List.map_map] at ih'
    have e : (WFF.dia x hx ψ :: (Δ₂.map (WFF.boxx x hx) ++ Δ₁.map fun χ => WFF.box (Γ := Γ) χ)).map
        (WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots) =
        WFF.dia (ι x) hwx (WFF.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw)
          (Subst.coh_dia hθ hc hx) (hΓ.diaIn x) Ctx.NoSlots.slots ψ) ::
        ((Δ₂.map (WFF.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
          (hΓ.diaIn x) Ctx.NoSlots.slots)).map (WFF.boxx (ι x) hwx) ++
          (Δ₁.map (WFF.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn
            Ctx.NoSlots.slots)).map fun χ => WFF.box (Γ := Γ') χ) := by
      simp only [List.map_cons, List.map_append, List.map_map]
      rfl
    rw [e]
    exact Der.K_dia (ι x) hwx ih'
  case D_box Γ Δ hD p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    exact Der.D_box hD (ih θ hθ hc hΓ)
  case four_box Γ _ hF Δ φ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    have e := subst_cp4 θ hθ hc hΓ [φ]
    simp only [cp4, dif_pos hF, List.map_cons, List.map_nil, List.cons.injEq, and_true] at e
    have e' : WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots
        (.box (.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots φ))) =
        .box (.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ') Ctx.NoSlots.slots
          (WFF.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn Ctx.NoSlots.slots
            φ))) := congrArg WFF.box e
    rw [e']
    exact Der.four_box hF (ih θ hθ hc hΓ)
  case four_dia Γ _ hF Δ x hx φ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
    have hwx : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
      hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
    have e := subst_keepDia θ hθ hc hΓ hF (WFF.dia x hx φ.neg)
    simp only [WFF.keepDia, List.map_cons, List.map_nil] at e
    have e' : WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots
        (.box (WFF.boxx (.step x .keep) (Ctx.exists_keep_dia hF hx)
          (WFF.shift (Ctx.shifts_diaIn_keep hF Γ x) Ctx.NoSlots.slots φ))) =
        .box (WFF.boxx (.step (ι x) .keep) (Ctx.exists_keep_dia hF hwx)
          (WFF.shift (Ctx.shifts_diaIn_keep hF Γ' (ι x)) Ctx.NoSlots.slots
            (WFF.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
              (hΓ.diaIn x) Ctx.NoSlots.slots φ))) :=
      congrArg (fun χ => WFF.box (WFF.neg χ)) (List.cons.inj e).1
    rw [e']
    exact Der.four_dia hF (ι x) hwx (ih θ hθ hc hΓ)
  case T_box Γ _ hT Δ φ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    rw [← WFF.collapse_subst (Ctx.collapses_boxIn_self hT _) (Ctx.collapses_boxIn_self hT Γ')
      θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) θ hθ hc hΓ.boxIn hΓ Ctx.NoSlots.slots
      Ctx.NoSlots.slots (Subst.corr_box_self hT hθ) φ fun _ => Subst.corrW_box_self hT hθ]
    exact Der.T_box hT (ih θ hθ hc hΓ)
  case dia_bot Γ Δ x hx p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
    have hwx : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
      hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
    exact Der.dia_bot (ι x) hwx (ih θ hθ hc hΓ)
  case K_opt Γ hO κ y hy Δ₁ Δ₂ φ ψ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    cases κ with
    | ident =>
        have hwy : ∃ X, Γ'.witT (ι y) = some X :=
          hy.elim fun X hX => by
            obtain ⟨hT, hO', hr⟩ := Ctx.witT_spec hX
            obtain ⟨Y, hY⟩ := SubE.ref_witness (Subst.okRef_at hθ hr) (hc y _ hr [])
            exact ⟨Y, Ctx.witT_of hT hO' hY⟩
        obtain ⟨X, hX⟩ := hy
        have hθy := Subst.ok_optInT hθ hX (hc y _ (Ctx.witT_spec hX).2.2 [])
        have hcy := Subst.coh_optInT hθ hc hX
        have ih' := ih (θ.optInT y (ι y)) hθy hcy (hΓ.optInT y)
        exact Der.castHyps (by simp only [List.map_cons, List.map_append, List.map_map]; rfl)
          (Der.K_opt (Γ := Γ') hO .ident (ι y) hwy
            (Δ₁ := Δ₁.map (WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots))
            (Δ₂ := Δ₂.map (WFF.subst ι (θ.optInT y (ι y)) hθy hcy (hΓ.optInT y)
              Ctx.NoSlots.slots))
            (Der.castHyps
              (by
                simp only [List.map_cons, List.map_append, List.map_map]
                congr 2
                exact List.map_congr_left fun χ _ =>
                  WFF.subst_optInT_mono θ hθ hc hX hΓ Ctx.NoSlots.slots Ctx.NoSlots.slots χ)
              ih'))
    | arrow =>
        have hwy : ∃ X, Γ'.wit (ι y) = some X :=
          hy.elim fun X hX => WitE.wit_of (hθ.wit hO y X hX) (hc.wit hO y X hX [])
        obtain ⟨X, hX⟩ := hy
        have hθy := Subst.ok_optIn hθ hO hX (hc.wit hO y X hX [])
        have hcy := Subst.coh_optIn hθ hc hO hX
        have ih' := ih (θ.optIn y (ι y)) hθy hcy (hΓ.optIn y)
        exact Der.castHyps (by simp only [List.map_cons, List.map_append, List.map_map]; rfl)
          (Der.K_opt (Γ := Γ') hO .arrow (ι y) hwy
            (Δ₁ := Δ₁.map (WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots))
            (Δ₂ := Δ₂.map (WFF.subst ι (θ.optIn y (ι y)) hθy hcy (hΓ.optIn y) Ctx.NoSlots.slots))
            (Der.castHyps
              (by
                simp only [List.map_cons, List.map_append, List.map_map]
                congr 2
                exact List.map_congr_left fun χ _ =>
                  WFF.subst_optIn_mono θ hθ hc hO hX hΓ Ctx.NoSlots.slots Ctx.NoSlots.slots χ)
              ih'))
  case opt_bot Γ Δ hO κ y hy p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    cases κ with
    | ident =>
        exact Der.opt_bot hO .ident (ι y)
          (hy.elim fun X hX => by
            obtain ⟨hT, hO', hr⟩ := Ctx.witT_spec hX
            obtain ⟨Y, hY⟩ := SubE.ref_witness (Subst.okRef_at hθ hr) (hc y _ hr [])
            exact ⟨Y, Ctx.witT_of hT hO' hY⟩)
          (ih θ hθ hc hΓ)
    | arrow =>
        exact Der.opt_bot hO .arrow (ι y)
          (hy.elim fun X hX => WitE.wit_of (hθ.wit hO y X hX) (hc.wit hO y X hX []))
          (ih θ hθ hc hΓ)
  case opt_reopen Γ Δ hO κ y hy ψ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    cases κ with
    | ident =>
        exact Der.conv
          (by
            obtain ⟨X, hX, hXd⟩ := hy
            exact congrArg (WFF.optx hO .ident (ι y) _)
              (WFF.subst_optInT_mono θ hθ hc hX hΓ Ctx.NoSlots.slots Ctx.NoSlots.slots ψ).symm)
          (Der.opt_reopen hO .ident (ι y)
            (hy.elim fun X h =>
              hc.openedToT y X (ι y) h.1 h.2 (hc y _ (Ctx.witT_spec h.1).2.2 []))
            (ih θ hθ hc hΓ))
    | arrow =>
        exact Der.conv
          (by
            obtain ⟨X, hX, hXd⟩ := hy
            exact congrArg (WFF.optx hO .arrow (ι y) _)
              (WFF.subst_optIn_mono θ hθ hc hO hX hΓ Ctx.NoSlots.slots Ctx.NoSlots.slots
                ψ).symm)
          (Der.opt_reopen hO .arrow (ι y)
            (hy.elim fun X h => hc.openedTo hO y X (ι y) h.1 h.2 (hc.wit hO y X h.1 []))
            (ih θ hθ hc hΓ))
  case dia_opt Γ Δ hO u hu φ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    have hw : (θ.at u).idxAlong [] = ι u := hu.elim fun _ hX => hc u _ hX []
    have hwu : ∃ X, Γ'.ref (ι u) = some (.VTypeDia X) :=
      hu.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
    exact Der.conv
      (by
        obtain ⟨X, hX⟩ := hu
        obtain ⟨Y, hY⟩ := hwu
        exact congrArg (fun χ => (WFF.box (WFF.optx hO .arrow (ι u) _ χ).neg).neg)
          (WFF.subst_diaOpt_mono θ hθ hc hO hX hw hY hΓ Ctx.NoSlots.slots Ctx.NoSlots.slots
            φ).symm)
      (Der.dia_opt hO (ι u) hwu (ih θ hθ hc hΓ))
  case opt_dia Γ Δ hO u hu φ p ih =>
    intro Γ' _ ι θ hθ hc hΓ
    have hw : (θ.at u).idxAlong [] = ι u := hu.elim fun _ hX => hc u _ hX []
    have hwu : ∃ X, Γ'.ref (ι u) = some (.VTypeDia X) :=
      hu.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
    exact Der.opt_dia hO (ι u) hwu (Der.conv
      (by
        obtain ⟨X, hX⟩ := hu
        obtain ⟨Y, hY⟩ := hwu
        exact congrArg (fun χ => (WFF.box (WFF.optx hO .arrow (ι u) _ χ).neg).neg)
          (WFF.subst_diaOpt_mono θ hθ hc hO hX hw hY hΓ Ctx.NoSlots.slots Ctx.NoSlots.slots φ))
      (ih θ hθ hc hΓ))
  all_goals kflag

/-- ⭐**Cut-free derivability of every ND-provable sequent**, over a presented context, in K, KD,
    K4 and KD4. -/
theorem Der.ofProof [ModalSys.GKBase] {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)}
    {φ : WFF σ Γ 0} (p : Proof σ Γ Δ φ) : Der σ Γ Δ φ := by
  have hΓ : Γ.SlotsFrom 0 := Ctx.NoSlots.slots
  have key : ∀ ψ : WFF σ Γ 0, WFF.subst id (Subst.idRen Γ) Subst.ok_idRen Subst.coh_idRen hΓ
      Ctx.NoSlots.slots ψ = ψ := fun ψ =>
    (WFF.subst_ren (Ctx.Le.refl Γ) _ _ _ hΓ _ (fun v _ _ => Subst.at_idRen v) ψ
      (fun _ _ _ _ => rfl)).trans
      (WFF.mono_refl _ ψ)
  have := GK.ofProof p (Subst.idRen Γ) Subst.ok_idRen Subst.coh_idRen hΓ
  rwa [show (WFF.subst id (Subst.idRen Γ) Subst.ok_idRen Subst.coh_idRen hΓ
    Ctx.NoSlots.slots) = id from funext key, List.map_id, id] at this

end GK

end V12M
