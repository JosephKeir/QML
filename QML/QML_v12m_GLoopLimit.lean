import QML.QML_v12m_GCanonModel

/-!
# QML v12m — the root's loop in the limit

The root's self-edge (`docs/v12-modal-extensions.md`, "KB5 and KDB5: the step in Lean") in the
chain: every variable of the root is eventually committed (`loop_total`), so a stage of the root
has a later stage where it is (`glstg`, `gloop_at`), and the limit's entries type its view, fix
kept items and transfer necessity (`gloopOk`, `gloopFix`, `gltr_loop`).  As `fwd_total`, `gfwd_at`,
`gentOk_box` and `gltr` for a child's edge.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-- The flag is fixed along the chain. -/
theorem lp_gnet (hM₀ : Theory.IsMCS M₀) (n : ℕ) : (gnet hF M₀ n).lp = GNetSt.LoopOn M₀ :=
  (ext_gnet hF hM₀ (Nat.zero_le n)).lp

open Classical in
omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem GNetSt.realF_fcl_root (hF : ModalSys.Four = true) (N : GNetSt σ) :
    (N.realF hF []).fcl [] =
      if N.lp ∧ (N.fcl []).length < (N.st []).l.length then
        nextTy (N.st []).l (N.fcl []) :: N.fcl []
      else N.fcl [] := by
  simp only [GNetSt.realF]
  split_ifs
  · simp only [GNetSt.setFwd, Function.update_self]
  · rfl

/-- ⭐Every variable of the root is eventually committed along its self-edge. -/
theorem loop_total (hM₀ : Theory.IsMCS M₀) (hl : GNetSt.LoopOn M₀) {n r : ℕ}
    (hr : r < ((gnet hF M₀ n).st []).l.length) :
    ∃ m, n ≤ m ∧ r < ((gnet hF M₀ m).fcl []).length := by
  have key : ∀ j, ∃ m, n ≤ m ∧ min j (r + 1) ≤ ((gnet hF M₀ m).fcl []).length := by
    intro j
    induction j with
    | zero => exact ⟨n, le_rfl, by simp⟩
    | succ j ih =>
        obtain ⟨m, hnm, hm⟩ := ih
        by_cases hdone : r + 1 ≤ ((gnet hF M₀ m).fcl []).length
        · exact ⟨m, hnm, (min_le_right _ _).trans hdone⟩
        obtain ⟨m', hm'm, hs⟩ := gsched_after (σ := σ) (.inr (.inr (.inl []))) m
        have hmono : ((gnet hF M₀ m).fcl []).length ≤ ((gnet hF M₀ m').fcl []).length :=
          ((ext_gnet hF hM₀ hm'm).fcl [] trivial).length_le
        by_cases hdone' : r + 1 ≤ ((gnet hF M₀ m').fcl []).length
        · exact ⟨m', hnm.trans hm'm, (min_le_right _ _).trans hdone'⟩
        have hlp : ((gnet hF M₀ n).st []).l.length ≤ ((gnet hF M₀ m').st []).l.length :=
          (gnet_lang_suffix hF hM₀ (hnm.trans hm'm) (k := []) trivial).length_le
        have hlt : ((gnet hF M₀ m').fcl []).length < ((gnet hF M₀ m').st []).l.length := by
          omega
        have hlpm : (gnet hF M₀ m').lp := by
          rw [lp_gnet hM₀]
          exact hl
        refine ⟨m' + 1, by omega, ?_⟩
        rw [gnet_succ_of hF hs]
        simp only [GNetSt.applyOp]
        rw [if_pos (show (gnet hF M₀ m').Live [] from trivial), GNetSt.realF_fcl_root,
          if_pos ⟨hlpm, hlt⟩, List.length_cons]
        omega
  obtain ⟨m, hnm, hm⟩ := key (r + 1)
  exact ⟨m, hnm, by simp at hm; omega⟩

theorem gstg_exists_loop (hM₀ : Theory.IsMCS M₀) (hl : GNetSt.LoopOn M₀) (i : ℕ) :
    ∃ j, GStgP (groot hF M₀) (groot hF M₀) i j := by
  rcases hlen : (glat (groot hF M₀) i).length with _ | L
  · exact ⟨i, le_rfl, by rw [hlen]; exact Nat.zero_le _⟩
  · have hL : L < ((gnet hF M₀ (gbirth hF M₀ (groot hF M₀).2 + i)).st []).l.length := by
      change L < (glat (groot hF M₀) i).length
      omega
    obtain ⟨m, hnm, hm⟩ := loop_total hM₀ hl hL
    refine ⟨m - gbirth hF M₀ (groot hF M₀).2, ?_, ?_⟩ <;>
      rw [show gbirth hF M₀ (groot hF M₀).2 + (m - gbirth hF M₀ (groot hF M₀).2) = m by omega]
    · exact hnm
    · rw [hlen]
      exact hm

/-- The stage of the root where its stage `i` is committed along the self-edge. -/
noncomputable abbrev lstg (hF : ModalSys.Four = true) (M₀ : Set (WFF σ (ctxOf l₀) 0)) (i : ℕ) :
    ℕ := glstg (groot hF M₀) (groot hF M₀) i

open Classical in
theorem lstg_spec (hM₀ : Theory.IsMCS M₀) (hl : GNetSt.LoopOn M₀) (i : ℕ) :
    GStgP (groot hF M₀) (groot hF M₀) i (lstg hF M₀ i) := by
  have he := gstg_exists_loop (hF := hF) hM₀ hl i
  rw [lstg, glstg, dif_pos he]
  exact Nat.find_spec he

/-- ⭐Along the self-edge, stage `i` of the root is committed at its stage, with the limit's
    entries. -/
theorem gloop_at (hM₀ : Theory.IsMCS M₀) (hl : GNetSt.LoopOn M₀) (i : ℕ) :
    glat (groot hF M₀) i <:+
        (gnet hF M₀ (grnd (groot hF M₀) (groot hF M₀) i)).fcl [] ∧
      (∀ v T, (ctxOf (glat (groot hF M₀) i)).kView none v = some T →
        (gnet hF M₀ (grnd (groot hF M₀) (groot hF M₀) i)).fmap [] v = fmapL hF M₀ [] v) ∧
      LoopData ((gnet hF M₀ (grnd (groot hF M₀) (groot hF M₀) i)).st [])
        ((gnet hF M₀ (grnd (groot hF M₀) (groot hF M₀) i)).fcl [])
        ((gnet hF M₀ (grnd (groot hF M₀) (groot hF M₀) i)).fmap []) := by
  obtain ⟨hle, hlen⟩ := lstg_spec (hF := hF) hM₀ hl i
  have hG := good_gnet hF hM₀ (grnd (groot hF M₀) (groot hF M₀) i)
  have hld := hG.loop (by rw [lp_gnet hM₀]; exact hl)
  have hls : glat (groot hF M₀) i <:+
      ((gnet hF M₀ (grnd (groot hF M₀) (groot hF M₀) i)).st []).l :=
    gnet_lang_suffix hF hM₀ hle (k := []) trivial
  obtain ⟨hsuf₀, -⟩ := id hld.1
  have hsuf' := List.suffix_of_suffix_length_le hls hsuf₀ hlen
  refine ⟨hsuf', fun v T hv => ?_, hld⟩
  refine (fmapL_eq hM₀ (k := []) trivial (T := T) ?_).symm
  rw [hG.kindRoot]
  exact ((ctxOf_le_of_suffix hsuf').kView _) v T hv

/-- ⭐The limit's entries type a stage's `□` view, at the later stage. -/
theorem gloopOk (hM₀ : Theory.IsMCS M₀) (hl : GNetSt.LoopOn M₀) (i : ℕ) :
    EntOk ((ctxOf (glat (groot hF M₀) i)).kView none) (ctxOf (glat (groot hF M₀) (lstg hF M₀ i)))
      (fmapL hF M₀ []) := by
  obtain ⟨hsuf, hag, ⟨⟨_, _, hf, _⟩, _⟩⟩ := gloop_at (hF := hF) hM₀ hl i
  exact (hf.restrict ((ctxOf_le_of_suffix hsuf).kView _)).congr hag

/-- ⭐The limit's entries fix a stage's kept items. -/
theorem gloopFix (hM₀ : Theory.IsMCS M₀) (hl : GNetSt.LoopOn M₀) (i : ℕ) :
    KeepFix (glat (groot hF M₀) i) (fmapL hF M₀ []) := by
  obtain ⟨hsuf, hag, ⟨-, hfix⟩⟩ := gloop_at (hF := hF) hM₀ hl i
  intro v U hv
  rw [← hag _ U (show (ctxOf (glat (groot hF M₀) i)).kView none (.step v .keep) = some U from hv)]
  exact hfix v U (((ctxOf_le_of_suffix hsuf).boxIn) _ _ hv)

/-- ⭐**Necessity transfer along the self-edge.** -/
theorem gltr_loop (hM₀ : Theory.IsMCS M₀) (hl : GNetSt.LoopOn M₀) (i : ℕ)
    (ψ : WFF σ ((ctxOf (glat (groot hF M₀) i)).kView none) 0)
    (hψ : .box ψ ∈ ((gnet hF M₀ (gbirth hF M₀ (groot hF M₀).2 + i)).st []).M) :
    WFF.subst (eIdx (fmapL hF M₀ [])) (eS σ _ (fmapL hF M₀ []))
      (ok_eS_kView (gloopOk hM₀ hl i)) (coh_eS_kView (gloopOk hM₀ hl i))
      Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈
        ((gnet hF M₀ (grnd (groot hF M₀) (groot hF M₀) i)).st []).M := by
  have hle := (lstg_spec (hF := hF) hM₀ hl i).1
  have hψ' := (ggrow_stage hM₀ (groot hF M₀) i hle).sub _ hψ
  obtain ⟨hsuf, hag, ⟨⟨hsuf', hk, hf, htr⟩, -⟩⟩ := gloop_at (hF := hF) hM₀ hl i
  have h₁ := htr (WFF.mono (ctxOf_le_of_suffix hsuf).boxIn ψ) (by
    convert hψ' using 1
    simp only [kBox, WFF.mono, WFF.mono_mono])
  rw [WFF.subst_mono _ _ _ _ Ctx.NoSlots.slots] at h₁
  change WFF.subst _ (eS σ (ctxOf (glat (groot hF M₀) (lstg hF M₀ i))) _) _ _ _ _ ψ ∈ _ at h₁
  rwa [WFF.subst_congr _ _ _ (ok_eS_kView (gloopOk hM₀ hl i)) _
    (coh_eS_kView (gloopOk hM₀ hl i)) _ _
    (sim_eS_congr fun v T _ hv => (hag v T hv).symm) ψ] at h₁

theorem lstg_monotone (hM₀ : Theory.IsMCS M₀) (hl : GNetSt.LoopOn M₀) {i i' : ℕ} (hii : i ≤ i') :
    lstg hF M₀ i ≤ lstg hF M₀ i' := by
  have hP := lstg_spec (hF := hF) hM₀ hl i'
  have hP' : GStgP (groot hF M₀) (groot hF M₀) i (lstg hF M₀ i') :=
    ⟨by have := hP.1; omega, le_trans (gnet_lang_suffix hF hM₀ (by omega)
      (live_gbirth hF hM₀ (groot hF M₀).2 (Nat.le_add_right _ i))).length_le hP.2⟩
  classical
  rw [lstg, glstg, dif_pos ⟨_, hP'⟩]
  exact Nat.find_min' _ hP'

/-- ⭐**A root's `□`-view term translated along the self-edge.** -/
noncomputable def loopTm (hM₀ : Theory.IsMCS M₀) (hl : GNetSt.LoopOn M₀) (i : ℕ) {A : VarType}
    {a : Ann A} (b : Term σ ((ctxOf (glat (groot hF M₀) i)).kView none) A a) :
    Σ c : Ann A, Term σ (ctxOf (glat (groot hF M₀) (lstg hF M₀ i))) A c :=
  ⟨_, Term.subst (eIdx (fmapL hF M₀ [])) (eS σ _ (fmapL hF M₀ []))
    (ok_eS_kView (gloopOk hM₀ hl i)) (coh_eS_kView (gloopOk hM₀ hl i)) b⟩

theorem loopTm_sigma (hM₀ : Theory.IsMCS M₀) (hl : GNetSt.LoopOn M₀) (i : ℕ) {A : VarType}
    {a a' : Ann A} {u : Term σ ((ctxOf (glat (groot hF M₀) i)).kView none) A a}
    {u' : Term σ ((ctxOf (glat (groot hF M₀) i)).kView none) A a'}
    (e : (⟨a, u⟩ : Σ b : Ann A, Term σ ((ctxOf (glat (groot hF M₀) i)).kView none) A b) =
      ⟨a', u'⟩) :
    loopTm hM₀ hl i u = loopTm hM₀ hl i u' := by
  cases e
  rfl

/-- Translating a later stage is weakening the translation. -/
theorem loopTm_mono (hM₀ : Theory.IsMCS M₀) (hl : GNetSt.LoopOn M₀) {i i' : ℕ} (hii : i ≤ i')
    {A : VarType} {a : Ann A} (b : Term σ ((ctxOf (glat (groot hF M₀) i)).kView none) A a) :
    (⟨_, Term.mono (gle hM₀ (groot hF M₀) (lstg_monotone hM₀ hl hii)) (loopTm hM₀ hl i b).2⟩ :
      Σ c, Term σ (ctxOf (glat (groot hF M₀) (lstg hF M₀ i'))) A c) =
      loopTm hM₀ hl i' (Term.mono ((gle hM₀ (groot hF M₀) hii).kView none) b) := by
  change (⟨_, Term.mono _ (Term.subst _ _ _ _ b)⟩ : Σ c, Term σ _ _ c) =
    ⟨_, Term.subst _ _ _ _ (Term.mono _ b)⟩
  rw [Term.mono_subst, Term.subst_mono]
  exact Term.subst_congr _ _ _ _ _ _ (sim_eS_mono _ (gloopOk hM₀ hl i)) b

end GArrow

end V12M
