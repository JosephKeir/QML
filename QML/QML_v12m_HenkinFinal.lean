import QML.QML_v12m_Henkin

/-!
# QML v12m — the Henkin construction: the finished language and theory

The chain fixes the type of the `i`-th own variable at step `i` (`finalτ`).  With those types the
base data is a world language (`final`), whose stages are the contexts of the chain
(`final_ctx`).  Its theory `finalT` holds a sentence when some step of the chain holds it:

* ⭐`subset_finalT`: it contains the starting theory;
* ⭐`finalT_isMCS`: it is maximal consistent;
* ⭐`finalT_ex_witness`: an existential it holds has an instance it holds, at a term;
* ⭐`finalT_all_witness`: a universal it lacks has an instance it lacks, at a term.
-/

namespace V12M

variable [ModalSys]

theorem WFF.instantiate_eta_congr {σ : Signature} {Γ : Ctx} (hs : Γ.SlotsFrom 0) {A : VarType}
    {w w' : VarSymb} (e : w = w') (h : Γ.ref w = some A) (h' : Γ.ref w' = some A)
    (F : WFF σ (Γ.insert (.bnd 0) A) 1) :
    WFF.instantiate hs (Term.eta w A h) F = WFF.instantiate hs (Term.eta w' A h') F := by
  subst e
  rfl

namespace WorldLang

variable {L : WorldLang} {σ : Signature}

omit [ModalSys] in
theorem decJ_le (n : ℕ) : decJ n ≤ n := Nat.unpair_left_le n

omit [ModalSys] in
/-- Every formula index at every stage is read at some step. -/
theorem exists_decF (m j k : ℕ) : ∃ n, decJ n = j ∧ decM n = m ∧ decKF n = k :=
  ⟨Nat.pair j (Nat.pair m (Nat.pair k 0)), by simp [decJ, decM, decK, decKF, Nat.unpair_pair]⟩

omit [ModalSys] in
/-- Every term index at every stage is read at some step, with any chosen formula index. -/
theorem exists_decFT (m j k k' : ℕ) :
    ∃ n, decJ n = j ∧ decM n = m ∧ decKF n = k ∧ decKT n = k' :=
  ⟨Nat.pair j (Nat.pair m (Nat.pair k k')),
    by simp [decJ, decM, decK, decKF, decKT, Nat.unpair_pair]⟩

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-! ## Witness sentences of one step -/

/-- After adding `∃x:A. ψ`, the step holds `ψ` at the new variable. -/
theorem step_wit_ex (n : ℕ) (st : HState L σ) {A : VarType}
    {ψ : WFF σ ((L.ctxL (decM n) st.l).insert (.bnd 0) A) 1}
    (hχ : L.choice n st = .ex A ψ)
    (href : (L.ctxL (decM n) (L.step n st).l).ref (.root (.free (L.ρ st.l.length))) = some A)
    (hle : ((L.ctxL (decM n) st.l).insert (.bnd 0) A).Le
      ((L.ctxL (decM n) (L.step n st).l).insert (.bnd 0) A)) :
    (⟨decM n, WFF.instantiate Ctx.NoSlots.slots (Term.eta _ A href) (WFF.mono hle ψ)⟩ :
      (L.pre (L.step n st).l).Sentence σ) ∈ (L.step n st).S := by
  have key : ∀ (χ : WFF σ (L.ctxL (decM n) st.l) 0), χ = .ex A ψ →
      ∀ (href : (L.ctxL (decM n) ((L.witStep (decM n) st.l (L.termQ n) χ).1 :: st.l)).ref
          (.root (.free (L.ρ st.l.length))) = some A)
        (hle : ((L.ctxL (decM n) st.l).insert (.bnd 0) A).Le
          ((L.ctxL (decM n) ((L.witStep (decM n) st.l (L.termQ n) χ).1 :: st.l)).insert
            (.bnd 0) A)),
      (⟨decM n, WFF.instantiate Ctx.NoSlots.slots (Term.eta _ A href) (WFF.mono hle ψ)⟩ :
        (L.pre ((L.witStep (decM n) st.l (L.termQ n) χ).1 :: st.l)).Sentence σ) ∈
        (L.witStep (decM n) st.l (L.termQ n) χ).2 := by
    rintro χ rfl href hle
    exact congrArg (Sigma.mk (decM n))
      (WFF.instantiate_eta_openFree _ (L.ctxL_fresh le_rfl) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ)
  exact Or.inr (key _ hχ href hle)

/-- After adding `¬∀x:A. ψ`, the step holds `¬ψ` at the new variable. -/
theorem step_wit_negAll (n : ℕ) (st : HState L σ) {A : VarType}
    {ψ : WFF σ ((L.ctxL (decM n) st.l).insert (.bnd 0) A) 1}
    (hχ : L.choice n st = (WFF.all A ψ).neg)
    (href : (L.ctxL (decM n) (L.step n st).l).ref (.root (.free (L.ρ st.l.length))) = some A)
    (hle : ((L.ctxL (decM n) st.l).insert (.bnd 0) A).Le
      ((L.ctxL (decM n) (L.step n st).l).insert (.bnd 0) A)) :
    (⟨decM n, (WFF.instantiate Ctx.NoSlots.slots (Term.eta _ A href) (WFF.mono hle ψ)).neg⟩ :
      (L.pre (L.step n st).l).Sentence σ) ∈ (L.step n st).S := by
  have key : ∀ (χ : WFF σ (L.ctxL (decM n) st.l) 0), χ = (WFF.all A ψ).neg →
      ∀ (href : (L.ctxL (decM n) ((L.witStep (decM n) st.l (L.termQ n) χ).1 :: st.l)).ref
          (.root (.free (L.ρ st.l.length))) = some A)
        (hle : ((L.ctxL (decM n) st.l).insert (.bnd 0) A).Le
          ((L.ctxL (decM n) ((L.witStep (decM n) st.l (L.termQ n) χ).1 :: st.l)).insert
            (.bnd 0) A)),
      (⟨decM n, (WFF.instantiate Ctx.NoSlots.slots (Term.eta _ A href) (WFF.mono hle ψ)).neg⟩ :
        (L.pre ((L.witStep (decM n) st.l (L.termQ n) χ).1 :: st.l)).Sentence σ) ∈
        (L.witStep (decM n) st.l (L.termQ n) χ).2 := by
    rintro χ rfl href hle
    exact congrArg (Sigma.mk (decM n))
      (WFF.instantiate_eta_openFree _ (L.ctxL_fresh le_rfl) Ctx.NoSlots.slots Ctx.NoSlots.slots
        ψ.neg)
  exact Or.inr (key _ hχ href hle)

/-- The choice at step `n`, with its type stated through the chain. -/
theorem choice_mem' (S₀ : Set ((L.pre []).Sentence σ)) (n : ℕ) :
    (⟨decM n, WFF.mono (chain_le S₀ (Nat.le_succ n) (decM n)) (L.choice n (L.chain S₀ n))⟩ :
      (L.pre (L.chain S₀ (n + 1)).l).Sentence σ) ∈ (L.chain S₀ (n + 1)).S :=
  choice_mem S₀ n

theorem enumF_mono_congr (m k : ℕ) {X : Ctx} :
    ∀ {l l' : List VarType} (_ : l = l') (h : (L.ctxL m l).Le X) (h' : (L.ctxL m l').Le X),
      WFF.mono h (enumF (σ := σ) (L.ctxL m l) k) = WFF.mono h' (enumF (σ := σ) (L.ctxL m l') k)
  | _, _, rfl, _, _ => rfl

/-- The query at step `n` is the enumerated formula at its own stage, lifted. -/
theorem query_chain (S₀ : Set ((L.pre []).Sentence σ)) (n : ℕ)
    (h₀ : (L.ctxL (decM n) (L.chain S₀ (decJ n)).l).Le (L.ctxL (decM n) (L.chain S₀ n).l)) :
    L.query (σ := σ) n (L.chain S₀ n).l =
      WFF.mono h₀ (enumF (σ := σ) (L.ctxL (decM n) (L.chain S₀ (decJ n)).l) (decKF n)) :=
  enumF_mono_congr (decM n) (decKF n) (drop_chain S₀ (decJ_le n)) _ _

/-! ## The finished language -/

variable (L) in
/-- The type chosen at step `i`. -/
noncomputable def finalτ (S₀ : Set ((L.pre []).Sentence σ)) (i : ℕ) : VarType :=
  (L.witStep (decM i) (L.chain S₀ i).l (L.termQ i) (L.choice i (L.chain S₀ i))).1

variable (L) in
/-- The finished language. -/
noncomputable def final (S₀ : Set ((L.pre []).Sentence σ)) : WorldLang :=
  L.withTypes (L.finalτ S₀)

theorem final_ctx (S₀ : Set ((L.pre []).Sentence σ)) (m : ℕ) :
    ∀ j, (L.final S₀).ctx (m, j) = L.ctxL m (L.chain S₀ j).l
  | 0 => rfl
  | j + 1 => by
      change ((L.final S₀).ctx (m, j)).insert (.free (L.ρ j)) (L.finalτ S₀ j) =
        (L.ctxL m (L.chain S₀ j).l).insert (.free (L.ρ (L.chain S₀ j).l.length)) (L.finalτ S₀ j)
      rw [final_ctx S₀ m j, length_chain]

theorem final_le_ctxL (S₀ : Set ((L.pre []).Sentence σ)) (m j : ℕ) :
    ((L.final S₀).ctx (m, j)).Le (L.ctxL m (L.chain S₀ j).l) := by
  rw [final_ctx]
  exact Ctx.Le.refl _

/-- A stage of the finished language inside a later step of the chain. -/
theorem toChain (S₀ : Set ((L.pre []).Sentence σ)) {m j n : ℕ} (h : j ≤ n) :
    ((L.final S₀).ctx (m, j)).Le (L.ctxL m (L.chain S₀ n).l) :=
  (L.final_le_ctxL S₀ m j).trans (chain_le S₀ h m)

/-! ## The finished theory -/

variable (L) in
/-- The sentences held at some step of the chain. -/
def finalT (S₀ : Set ((L.pre []).Sentence σ)) : Set ((L.final S₀).sys.Sentence σ) :=
  {s | ∃ n, ∃ h : s.1.2 ≤ n,
    (⟨s.1.1, WFF.mono (L.toChain S₀ (m := s.1.1) h) s.2⟩ : (L.pre (L.chain S₀ n).l).Sentence σ) ∈
      (L.chain S₀ n).S}

/-- ⭐The finished theory contains the starting theory. -/
theorem subset_finalT (S₀ : Set ((L.pre []).Sentence σ)) {m : ℕ} {φ : WFF σ (L.base m) 0}
    (h : (⟨m, φ⟩ : (L.pre []).Sentence σ) ∈ S₀) :
    (⟨(m, 0), φ⟩ : (L.final S₀).sys.Sentence σ) ∈ L.finalT S₀ := by
  refine ⟨0, le_rfl, ?_⟩
  have e : WFF.mono (L.toChain S₀ (m := m) (le_refl 0)) φ = φ := WFF.mono_refl _ φ
  rw [e]
  exact h

theorem atStage_chain_mono (S₀ : Set ((L.pre []).Sentence σ)) {n N : ℕ} (hN : n ≤ N) {m : ℕ}
    {ψ : WFF σ (L.ctxL m (L.chain S₀ n).l) 0} (h : ψ ∈ StageSys.atStage (L.chain S₀ n).S m) :
    WFF.mono (chain_le S₀ hN m) ψ ∈ StageSys.atStage (L.chain S₀ N).S m := by
  obtain ⟨⟨m₀, φ₀⟩, hs, hle, rfl⟩ := h
  exact ⟨⟨m₀, WFF.mono (chain_le S₀ hN m₀) φ₀⟩, mem_chain_mono S₀ hN hs, hle,
    (WFF.mono_mono _ _ _).trans (WFF.mono_mono _ _ _).symm⟩

/-- Finitely many members of the finished theory are all held, lifted, at one step. -/
theorem finalT_bound (S₀ : Set ((L.pre []).Sentence σ)) {m j : ℕ} :
    ∀ Δ : List (WFF σ ((L.final S₀).ctx (m, j)) 0),
      (∀ δ ∈ Δ, δ ∈ StageSys.atStage (L.finalT S₀) (m, j)) →
      ∃ N, ∃ hN : j ≤ N, ∀ δ ∈ Δ,
        WFF.mono (L.toChain S₀ hN) δ ∈ StageSys.atStage (L.chain S₀ N).S m
  | [], _ => ⟨j, le_rfl, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: Δ, h => by
      obtain ⟨N₁, hN₁, h₁⟩ := finalT_bound S₀ Δ (fun d hd => h d (List.mem_cons_of_mem _ hd))
      obtain ⟨⟨⟨m₀, j₀⟩, φ₀⟩, ⟨n₀, hn₀, hφ₀⟩, ⟨hm₀, hj₀⟩, hδ⟩ := h δ List.mem_cons_self
      have hN : j ≤ max N₁ n₀ := le_trans hN₁ (le_max_left _ _)
      refine ⟨max N₁ n₀, hN, fun d hd => ?_⟩
      rcases List.mem_cons.mp hd with rfl | hd
      · subst hδ
        exact ⟨⟨m₀, WFF.mono (chain_le S₀ (le_max_right N₁ n₀) m₀)
            (WFF.mono (L.toChain S₀ hn₀) φ₀)⟩,
          mem_chain_mono S₀ (le_max_right N₁ n₀) hφ₀, hm₀,
          by simp only [StageSys.lift, WFF.mono_mono]⟩
      · have e : WFF.mono (L.toChain S₀ hN) d =
            WFF.mono (chain_le S₀ (le_max_left N₁ n₀) m) (WFF.mono (L.toChain S₀ hN₁) d) :=
          (WFF.mono_mono _ _ d).symm
        rw [e]
        exact atStage_chain_mono S₀ (le_max_left N₁ n₀) (h₁ d hd)

/-- The finished theory is consistent. -/
theorem finalT_consistent {S₀ : Set ((L.pre []).Sentence σ)} (hS₀ : StageSys.Consistent S₀) :
    StageSys.Consistent (L.finalT S₀) := by
  rintro ⟨m, j⟩ ⟨Δ, hΔ, p⟩
  obtain ⟨N, hN, hmem⟩ := finalT_bound S₀ Δ hΔ
  exact consistent_chain hS₀ N m ⟨Δ.map (WFF.mono (L.toChain S₀ hN)), fun ψ hψ => by
      obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hψ
      exact hmem δ hδ,
    Provable.monoCtx (L.toChain S₀ hN) p⟩

theorem finalT_not_both {S₀ : Set ((L.pre []).Sentence σ)} (hS₀ : StageSys.Consistent S₀)
    {i : ℕ × ℕ} {φ : WFF σ ((L.final S₀).sys.ctx i) 0}
    (h₁ : (⟨i, φ⟩ : (L.final S₀).sys.Sentence σ) ∈ L.finalT S₀)
    (h₂ : (⟨i, φ.neg⟩ : (L.final S₀).sys.Sentence σ) ∈ L.finalT S₀) : False :=
  finalT_consistent hS₀ i ⟨[φ, φ.neg], fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact StageSys.mem_atStage_self h₁
      · rw [List.mem_singleton.mp hx]
        exact StageSys.mem_atStage_self h₂,
    Provable.mp (Provable.of_mem (List.mem_cons_of_mem _ List.mem_cons_self))
      (Provable.of_mem List.mem_cons_self)⟩

/-- The step reading a formula of the finished language decides it. -/
theorem finalT_decides (S₀ : Set ((L.pre []).Sentence σ)) (n : ℕ)
    {φ : WFF σ ((L.final S₀).ctx (decM n, decJ n)) 0}
    (hq : enumF (L.ctxL (decM n) (L.chain S₀ (decJ n)).l) (decKF n) =
      WFF.mono (L.final_le_ctxL S₀ _ _) φ) :
    (L.choice n (L.chain S₀ n) = WFF.mono (L.toChain S₀ (decJ_le n)) φ ∧
        (⟨(decM n, decJ n), φ⟩ : (L.final S₀).sys.Sentence σ) ∈ L.finalT S₀) ∨
      (L.choice n (L.chain S₀ n) = (WFF.mono (L.toChain S₀ (decJ_le n)) φ).neg ∧
        (⟨(decM n, decJ n), φ.neg⟩ : (L.final S₀).sys.Sentence σ) ∈ L.finalT S₀) := by
  have hquery : L.query (σ := σ) n (L.chain S₀ n).l = WFF.mono (L.toChain S₀ (decJ_le n)) φ := by
    rw [query_chain S₀ n (chain_le S₀ (decJ_le n) _), hq, WFF.mono_mono]
  have hm := choice_mem' S₀ n
  rcases choice_cases n (L.chain S₀ n) with hc | hc
  · refine Or.inl ⟨hc.trans hquery, n + 1, (decJ_le n).trans (Nat.le_succ n), ?_⟩
    rw [hc, hquery, WFF.mono_mono] at hm
    exact hm
  · refine Or.inr ⟨hc.trans (congrArg (fun x => WFF.neg x) hquery), n + 1,
      (decJ_le n).trans (Nat.le_succ n), ?_⟩
    rw [hc, hquery] at hm
    have e : WFF.mono (chain_le S₀ (Nat.le_succ n) (decM n))
          (WFF.mono (L.toChain S₀ (decJ_le n)) φ).neg =
        WFF.mono (L.toChain S₀ (m := decM n) ((decJ_le n).trans (Nat.le_succ n))) φ.neg :=
      congrArg (fun x => WFF.neg x) (WFF.mono_mono _ _ φ)
    rw [e] at hm
    exact hm

/-- The finished theory decides every sentence. -/
theorem finalT_complete (S₀ : Set ((L.pre []).Sentence σ)) {i : ℕ × ℕ}
    (φ : WFF σ ((L.final S₀).sys.ctx i) 0) :
    (⟨i, φ⟩ : (L.final S₀).sys.Sentence σ) ∈ L.finalT S₀ ∨
      (⟨i, φ.neg⟩ : (L.final S₀).sys.Sentence σ) ∈ L.finalT S₀ := by
  obtain ⟨m, j⟩ := i
  obtain ⟨k, hk⟩ := enumF_surjective (σ := σ) (L.ctxL m (L.chain S₀ j).l)
    (WFF.mono (L.final_le_ctxL S₀ m j) φ)
  obtain ⟨n, rfl, rfl, rfl⟩ := exists_decF m j k
  rcases finalT_decides S₀ n hk with ⟨_, h⟩ | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr h

/-- ⭐The finished theory is maximal consistent. -/
theorem finalT_isMCS {S₀ : Set ((L.pre []).Sentence σ)} (hS₀ : StageSys.Consistent S₀) :
    StageSys.IsMCS (L.finalT S₀) := by
  refine ⟨finalT_consistent hS₀, fun s hs => ?_⟩
  rcases finalT_complete S₀ s.2 with h | h
  · exact h
  · exfalso
    exact hs s.1 ⟨[s.2, s.2.neg], fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact StageSys.mem_atStage_self (Set.mem_insert _ _)
        · rw [List.mem_singleton.mp hx]
          exact StageSys.mem_atStage_self (Set.mem_insert_of_mem _ h),
      Provable.mp (Provable.of_mem (List.mem_cons_of_mem _ List.mem_cons_self))
        (Provable.of_mem List.mem_cons_self)⟩

/-- ⭐An existential in the finished theory has an instance there, at a term. -/
theorem finalT_ex_witness {S₀ : Set ((L.pre []).Sentence σ)} (hS₀ : StageSys.Consistent S₀)
    {i : ℕ × ℕ} {A : VarType} {ψ : WFF σ (((L.final S₀).ctx i).insert (.bnd 0) A) 1}
    (h : (⟨i, .ex A ψ⟩ : (L.final S₀).sys.Sentence σ) ∈ L.finalT S₀) :
    ∃ (i' : ℕ × ℕ) (hi : i ≤ i') (c : ℕ)
      (hc : ((L.final S₀).ctx i').ref (.root (.free c)) = some A),
      (⟨i', WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free c)) A hc)
          (WFF.mono (((L.final S₀).ctx_le hi).insert (.bnd 0) A) ψ)⟩ :
        (L.final S₀).sys.Sentence σ) ∈ L.finalT S₀ := by
  obtain ⟨m, j⟩ := i
  obtain ⟨k, hk⟩ := enumF_surjective (σ := σ) (L.ctxL m (L.chain S₀ j).l)
    (WFF.mono (L.final_le_ctxL S₀ m j) (.ex A ψ))
  obtain ⟨n, rfl, rfl, rfl⟩ := exists_decF m j k
  rcases finalT_decides S₀ n hk with ⟨hc, _⟩ | ⟨_, hneg⟩
  swap
  · exact (finalT_not_both hS₀ h hneg).elim
  have hτ : L.finalτ S₀ n = A := by
    unfold finalτ
    rw [hc]
    rfl
  have hle_c : ((L.ctxL (decM n) (L.chain S₀ n).l).insert (.bnd 0) A).Le
      ((L.ctxL (decM n) (L.chain S₀ (n + 1)).l).insert (.bnd 0) A) :=
    (chain_le S₀ (Nat.le_succ n) _).insert _ A
  have href_c : (L.ctxL (decM n) (L.chain S₀ (n + 1)).l).ref
      (.root (.free (L.ρ (L.chain S₀ n).l.length))) = some A := by
    change ((L.ctxL (decM n) (L.chain S₀ n).l).insert (.free (L.ρ (L.chain S₀ n).l.length))
      (L.finalτ S₀ n)).ref _ = _
    rw [Ctx.ref_insert_root, hτ]
  have hmem := step_wit_ex n (L.chain S₀ n) (A := A)
    (ψ := WFF.mono ((L.toChain S₀ (decJ_le n)).insert (.bnd 0) A) ψ) hc href_c hle_c
  have href_f : ((L.final S₀).ctx (decM n, n + 1)).ref (.root (.free (L.ρ n))) = some A := by
    change (((L.final S₀).ctx (decM n, n)).insert (.free (L.ρ n)) (L.finalτ S₀ n)).ref _ = _
    rw [Ctx.ref_insert_root, hτ]
  have hi : (decM n, decJ n) ≤ (decM n, n + 1) := ⟨le_rfl, (decJ_le n).trans (Nat.le_succ n)⟩
  refine ⟨(decM n, n + 1), hi, L.ρ n, href_f, n + 1, le_rfl, ?_⟩
  have e : WFF.mono (L.toChain S₀ (m := decM n) (le_refl (n + 1)))
      (WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free (L.ρ n))) A href_f)
        (WFF.mono (((L.final S₀).ctx_le hi).insert (.bnd 0) A) ψ)) =
      WFF.instantiate Ctx.NoSlots.slots
        (Term.eta (.root (.free (L.ρ (L.chain S₀ n).l.length))) A href_c)
        (WFF.mono hle_c (WFF.mono ((L.toChain S₀ (decJ_le n)).insert (.bnd 0) A) ψ)) := by
    rw [WFF.mono_instantiate _ Ctx.NoSlots.slots Ctx.NoSlots.slots, Term.mono_eta]
    simp only [WFF.mono_mono]
    exact WFF.instantiate_eta_congr _ (by rw [length_chain]) _ _ _
  change (⟨decM n, WFF.mono (L.toChain S₀ (m := decM n) (le_refl (n + 1))) _⟩ :
    (L.pre (L.chain S₀ (n + 1)).l).Sentence σ) ∈ _
  rw [e]
  exact hmem

/-- ⭐A universal missing from the finished theory has an instance missing there, at a term. -/
theorem finalT_all_witness {S₀ : Set ((L.pre []).Sentence σ)} {i : ℕ × ℕ} {A : VarType}
    {ψ : WFF σ (((L.final S₀).ctx i).insert (.bnd 0) A) 1}
    (h : (⟨i, .all A ψ⟩ : (L.final S₀).sys.Sentence σ) ∉ L.finalT S₀) :
    ∃ (i' : ℕ × ℕ) (hi : i ≤ i') (a : Ann A) (t : Term σ ((L.final S₀).ctx i') A a),
      (⟨i', (WFF.instantiate Ctx.NoSlots.slots t
          (WFF.mono (((L.final S₀).ctx_le hi).insert (.bnd 0) A) ψ)).neg⟩ :
        (L.final S₀).sys.Sentence σ) ∈ L.finalT S₀ := by
  obtain ⟨m, j⟩ := i
  obtain ⟨k, hk⟩ := enumF_surjective (σ := σ) (L.ctxL m (L.chain S₀ j).l)
    (WFF.mono (L.final_le_ctxL S₀ m j) (.all A ψ))
  obtain ⟨n, rfl, rfl, rfl⟩ := exists_decF m j k
  rcases finalT_decides S₀ n hk with ⟨_, hpos⟩ | ⟨hc, _⟩
  · exact (h hpos).elim
  have hτ : L.finalτ S₀ n = A := by
    unfold finalτ
    rw [hc]
    rfl
  have hle_c : ((L.ctxL (decM n) (L.chain S₀ n).l).insert (.bnd 0) A).Le
      ((L.ctxL (decM n) (L.chain S₀ (n + 1)).l).insert (.bnd 0) A) :=
    (chain_le S₀ (Nat.le_succ n) _).insert _ A
  have href_c : (L.ctxL (decM n) (L.chain S₀ (n + 1)).l).ref
      (.root (.free (L.ρ (L.chain S₀ n).l.length))) = some A := by
    change ((L.ctxL (decM n) (L.chain S₀ n).l).insert (.free (L.ρ (L.chain S₀ n).l.length))
      (L.finalτ S₀ n)).ref _ = _
    rw [Ctx.ref_insert_root, hτ]
  have hmem := step_wit_negAll n (L.chain S₀ n) (A := A)
    (ψ := WFF.mono ((L.toChain S₀ (decJ_le n)).insert (.bnd 0) A) ψ) hc href_c hle_c
  have href_f : ((L.final S₀).ctx (decM n, n + 1)).ref (.root (.free (L.ρ n))) = some A := by
    change (((L.final S₀).ctx (decM n, n)).insert (.free (L.ρ n)) (L.finalτ S₀ n)).ref _ = _
    rw [Ctx.ref_insert_root, hτ]
  have hi : (decM n, decJ n) ≤ (decM n, n + 1) := ⟨le_rfl, (decJ_le n).trans (Nat.le_succ n)⟩
  refine ⟨(decM n, n + 1), hi, _, Term.eta (.root (.free (L.ρ n))) A href_f, n + 1, le_rfl, ?_⟩
  have e : WFF.mono (L.toChain S₀ (m := decM n) (le_refl (n + 1)))
      (WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free (L.ρ n))) A href_f)
        (WFF.mono (((L.final S₀).ctx_le hi).insert (.bnd 0) A) ψ)) =
      WFF.instantiate Ctx.NoSlots.slots
        (Term.eta (.root (.free (L.ρ (L.chain S₀ n).l.length))) A href_c)
        (WFF.mono hle_c (WFF.mono ((L.toChain S₀ (decJ_le n)).insert (.bnd 0) A) ψ)) := by
    rw [WFF.mono_instantiate _ Ctx.NoSlots.slots Ctx.NoSlots.slots, Term.mono_eta]
    simp only [WFF.mono_mono]
    exact WFF.instantiate_eta_congr _ (by rw [length_chain]) _ _ _
  change (⟨decM n, WFF.mono (L.toChain S₀ (m := decM n) (le_refl (n + 1))) (WFF.neg _)⟩ :
    (L.pre (L.chain S₀ (n + 1)).l).Sentence σ) ∈ _
  have e' := congrArg (fun x => WFF.neg x) e
  simp only at e'
  rw [show ∀ (X : WFF σ ((L.final S₀).ctx (decM n, n + 1)) 0),
      WFF.mono (L.toChain S₀ (m := decM n) (le_refl (n + 1))) X.neg =
        (WFF.mono (L.toChain S₀ (m := decM n) (le_refl (n + 1))) X).neg from fun _ => rfl, e']
  exact hmem

end WorldLang

end V12M
