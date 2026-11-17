import QML.QML_v12m_GKNTrans

/-!
# QML v12m — `GKN` into natural deduction

⭐`GKN.toND`: a `GKN` derivation of a tree sequent gives an ND refutation of its reading at the
root (`Pc … []`), for K and KD (docs §12.49).  By induction on the derivation: each rule's premise
reading is entailed by its conclusion's at the rule's node (the **hole**), and the path lemmas of
`QML_v12m_GKNTrans` carry that to the root — `claim_path` (across a grown tree), `or_path` (two
premises), `bot_path` (axioms).
-/

namespace V12M

set_option linter.unusedSectionVars false

variable [ModalSys]

namespace GKN

open NDP

variable {σ : Signature} {Γ₀ : Ctx}

/-! ## Holes -/

theorem hole_tr {D' : Tree} {Δ' Θ' : Seq σ Γ₀ D'} {τ : Lab} {f : ℕ}
    {H : List (WFF σ (D'.ctxAt Γ₀ τ) 0)}
    (hcont : ∀ φ ∈ Δ'.at τ ++ (Θ'.at τ).map WFF.neg, Provable H φ)
    (hpk : ∀ j ∈ D'.children τ,
      Provable H (pack D' (D'.ctxAt Γ₀ τ) (j :: τ) (Pc D' Δ' Θ' f (j :: τ)))) :
    Provable H (tr D' Δ' Θ' (f + 1) τ) := by
  rw [tr_succ]
  exact andI (conj_intro hcont) (conj_intro fun z hz => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
    exact hpk j hj)

section Hole

variable {D D' : Tree} {Δ Θ : Seq σ Γ₀ D} {Δ' Θ' : Seq σ Γ₀ D'}
  {hk : ∀ ρ, (D.ctxAt Γ₀ ρ).Le (D'.ctxAt Γ₀ ρ)} {hV : ∀ ρ, (Vw D Γ₀ ρ).Le (Vw D' Γ₀ ρ)}

/-- A formula of the node, weakened, from the node's reading. -/
theorem of_content {τ : Lab} {f : ℕ} {H : List (WFF σ (D'.ctxAt Γ₀ τ) 0)}
    (hH : WFF.mono (hk τ) (tr D Δ Θ f τ) ∈ H) {c : WFF σ (D.ctxAt Γ₀ τ) 0}
    (hc : c ∈ Δ.at τ ++ (Θ.at τ).map WFF.neg) : Provable H (WFF.mono (hk τ) c) := by
  have h₁ : Provable H (WFF.mono (hk τ) (conj (Δ.at τ ++ (Θ.at τ).map WFF.neg))) := by
    cases f <;> exact (lk hH).map .and_elim_l
  rw [mono_conj] at h₁
  exact conj_elim h₁ _ (List.mem_map_of_mem hc)

/-- A child's reading behind its edge, from the node's reading and the child's claim. -/
theorem pack_of_claim (hW : D.WitOK Γ₀) {τ : Lab} {j f : ℕ} (hj : j ∈ D.children τ)
    (he : D'.edge (j :: τ) = D.edge (j :: τ)) (hcl : Claim Δ Θ Δ' Θ' hV f (j :: τ))
    {H : List (WFF σ (D'.ctxAt Γ₀ τ) 0)} (hH : WFF.mono (hk τ) (tr D Δ Θ (f + 1) τ) ∈ H) :
    Provable H (pack D' (D'.ctxAt Γ₀ τ) (j :: τ) (Pc D' Δ' Θ' f (j :: τ))) := by
  have h₁ : Provable H (WFF.mono (hk τ) (conj ((D.children τ).map fun k =>
      pack D (D.ctxAt Γ₀ τ) (k :: τ) (Pc D Δ Θ f (k :: τ))))) := (lk hH).map .and_elim_r
  rw [mono_conj, List.map_map] at h₁
  have h₂ := conj_elim h₁ _ (List.mem_map_of_mem (f := WFF.mono (hk τ) ∘ fun k =>
    pack D (D.ctxAt Γ₀ τ) (k :: τ) (Pc D Δ Θ f (k :: τ))) hj)
  simp only [Function.comp] at h₂
  rw [mono_pack (hk τ) he (hV (j :: τ)) (fun x he' => hW j τ x he')] at h₂
  refine chain h₂ (sub (fun _ h => by rw [List.mem_singleton.mp h]; exact List.mem_cons_self) ?_)
  refine pack_mono (fun x he' => ?_) hcl
  rw [he] at he'
  exact (hW j τ x he').imp fun _ hX => (hk τ).ref hX

end Hole

/-- Closing a node whose births gain the eigenvariable at the head: the `∃` taken out of the
    node's openings (`closeO_ex`). -/
theorem closed_cons_of {V V' : Ctx} (hVV : V.Le V') {L L' : List (Root × VarType)}
    {O O' : List (WitKind × VarSymb)} {v : ℕ} {T : VarType} (hL : L' = (.free v, T) :: L)
    (hO : O' = O) (hb : NOK V L O) (hb' : NOK V' L' O') (hbO : (V'.inserts L).OptsEff O)
    {A : WFF σ ((V.inserts L).optInsK O) 0} {B : WFF σ ((V'.inserts L').optInsK O') 0}
    (hA : ((V.inserts L).optInsK O).Le ((V'.inserts L).optInsK O))
    (hfr₁ : ((V'.inserts L).optInsK O).RootFresh (.free v)) (hs : (V'.inserts L).SlotsFrom 0)
    (hcast : ((V'.inserts L').optInsK O').Le (((V'.inserts L).optInsK O).insert (.free v) T))
    (p : Provable [WFF.mono hA A]
      (.ex T (WFF.bindFree v hfr₁ (hs.optInsK O) T (WFF.mono hcast B)))) :
    Provable [WFF.mono hVV (closeN L O A)] (closeN L' O' B) := by
  subst hL
  subst O'
  have hfr : (V'.inserts L).RootFresh (.free v) := Ctx.RootFresh.of_le (Ctx.le_optInsK _ _) hfr₁
  have hbL' : BOK V' L := hb'.1.2.2
  rw [mono_closeN hVV hb ⟨hbL', hbO⟩ A]
  unfold closeN
  rw [closeB_cons hfr hs]
  refine or_cases (closeB_or hbL' (H := []) (orl _ ?_)) (lk List.mem_cons_self)
    (lk List.mem_cons_self)
  have s₁ : Provable [closeO O (WFF.mono ((hVV.inserts L).optInsK O) A)]
      (closeO O (.ex T (WFF.bindFree v hfr₁ (hs.optInsK O) T (WFF.mono hcast B)))) :=
    or_cases (closeO_or hbO (H := []) (orl _ p)) (lk List.mem_cons_self) (lk List.mem_cons_self)
  have s₂ := closeO_ex hbO T hs hfr hfr₁ hb'.2 (Ctx.insert_optInsK_le hfr T O) (WFF.mono hcast B)
  rw [WFF.mono_mono, WFF.mono_refl] at s₂
  exact chain s₁ (sub (by lsub) s₂)

/-- `¬∀ ⊢ ∃¬`. -/
theorem not_all {Γ : Ctx} [Γ.NoSlots] {v : ℕ} (hv : Γ.RootFresh (.free v)) (T : VarType)
    {φ : WFF σ (Γ.insert (.free v) T) 0} {H : List (WFF σ Γ 0)}
    (h : (WFF.all T (WFF.bindFree v hv Ctx.NoSlots.slots T φ)).neg ∈ H) :
    Provable H (.ex T (WFF.bindFree v hv Ctx.NoSlots.slots T φ.neg)) := by
  refine byContra ?_
  have q : Provable (((WFF.ex T (WFF.bindFree v hv Ctx.NoSlots.slots T φ.neg)).neg :: H).map
      (WFF.weaken hv.root T)) φ :=
    byContra (contra (List.mem_cons_of_mem _ List.mem_cons_self)
      (ex_self hv T (lk List.mem_cons_self)))
  obtain ⟨q⟩ := q
  exact contra (List.mem_cons_of_mem _ h) ⟨.all_intro v T hv q⟩

/-! ## Rules over the same tree -/

section Same

variable {D : Tree}

theorem ag_same {Δ Θ Δ' Θ' : Seq σ Γ₀ D} {σ' : Lab} (hΔ : Δ'.at σ' = Δ.at σ')
    (hΘ : Θ'.at σ' = Θ.at σ') : Ag Δ Θ Δ' Θ' (fun _ => Ctx.Le.refl _) σ' where
  left := by rw [hΔ, List.map_congr_left fun ψ _ => WFF.mono_refl _ ψ, List.map_id']
  right := by rw [hΘ, List.map_congr_left fun ψ _ => WFF.mono_refl _ ψ, List.map_id']
  children := rfl
  edge _ := rfl
  births := rfl
  opens := rfl

theorem of_tr {Δ Θ : Seq σ Γ₀ D} {τ : Lab} {f : ℕ} {c : WFF σ (D.ctxAt Γ₀ τ) 0}
    (hc : c ∈ Δ.at τ ++ (Θ.at τ).map WFF.neg) : Provable [tr D Δ Θ f τ] c := by
  cases f <;> exact conj_elim ((lk List.mem_cons_self).map .and_elim_l) c hc

theorem not_sub_child {j : ℕ} {τ σ' : Lab} (h : (j :: τ) <:+ σ') : σ' ≠ τ := fun e => by
  subst e
  have := h.length_le
  simp at this

/-- A premise over the same tree, its reading at the hole entailed. -/
theorem same_hole' (h0 : Γ₀.SlotsFrom 0) (hok : D.OK Γ₀) (hW : D.WitOK Γ₀)
    {Δ Θ Δ' Θ' : Seq σ Γ₀ D} {τ : Lab} {d : ℕ} (hd : τ.length ≤ d)
    (hagree : ∀ σ', ¬ τ <:+ σ' → Δ'.at σ' = Δ.at σ' ∧ Θ'.at σ' = Θ.at σ')
    (hole : ∀ f, Provable [tr D Δ Θ f τ] (tr D Δ' Θ' f τ))
    (q : Provable [Pc D Δ' Θ' d []] .bot) : Provable [Pc D Δ Θ d []] .bot := by
  have hc := claim_path (hk := fun _ => Ctx.Le.refl _) (hV := fun _ => Ctx.Le.refl _) h0 hok hok
    hW τ hd (fun σ' hσ => ag_same (hagree σ' hσ).1 (hagree σ' hσ).2)
      (claim_of_tr (hk := fun _ => Ctx.Le.refl _) h0 hok hok rfl rfl
        (by rw [WFF.mono_refl]; exact hole _))
  unfold Claim at hc
  rw [WFF.mono_refl] at hc
  exact chain hc (sub (by lsub) q)

/-- ⭐**A premise adding formulas at the rule's node.** -/
theorem same_hole (h0 : Γ₀.SlotsFrom 0) (hok : D.OK Γ₀) (hW : D.WitOK Γ₀)
    {Δ Θ Δ' Θ' : Seq σ Γ₀ D} {τ : Lab} {d : ℕ} (hd : τ.length ≤ d)
    (hagree : ∀ σ', σ' ≠ τ → Δ'.at σ' = Δ.at σ' ∧ Θ'.at σ' = Θ.at σ')
    (hcont : ∀ f, ∀ φ ∈ Δ'.at τ ++ (Θ'.at τ).map WFF.neg, Provable [tr D Δ Θ f τ] φ)
    (q : Provable [Pc D Δ' Θ' d []] .bot) : Provable [Pc D Δ Θ d []] .bot :=
  same_hole' h0 hok hW hd (fun σ' hσ => hagree σ' fun h => hσ (h ▸ List.suffix_refl _))
    (fun f => match f with
    | 0 => by rw [tr_zero, tr_zero]; exact andI (conj_intro (hcont 0)) ⟨.top_intro⟩
    | f + 1 => hole_tr (hcont (f + 1)) fun j hj => by
      rw [Pc_congr fun σ' hσ => hagree σ' (not_sub_child hσ)]
      exact conj_elim ((lk List.mem_cons_self).map .and_elim_r) _
        (List.mem_map_of_mem (f := fun k => pack D (D.ctxAt Γ₀ τ) (k :: τ)
          (Pc D Δ Θ f (k :: τ))) hj)) q

theorem or_and_right {Γ : Ctx} {C C₁ C₂ X : WFF σ Γ 0} (p : Provable [C] (C₁.or C₂)) :
    Provable [C.and X] ((C₁.and X).or (C₂.and X)) :=
  or_cases (chain ((lk List.mem_cons_self).map .and_elim_l) (sub (by lsub) p))
    (orl _ (andI (lk List.mem_cons_self)
      ((lk (List.mem_cons_of_mem _ List.mem_cons_self)).map .and_elim_r)))
    (orr _ (andI (lk List.mem_cons_self)
      ((lk (List.mem_cons_of_mem _ List.mem_cons_self)).map .and_elim_r)))

/-- ⭐**Two premises over the same tree**, their readings at the hole a disjunction. -/
theorem same_hole2 (h0 : Γ₀.SlotsFrom 0) (hok : D.OK Γ₀) (hW : D.WitOK Γ₀)
    {Δ Θ Δ₁ Θ₁ Δ₂ Θ₂ : Seq σ Γ₀ D} {τ : Lab} {d : ℕ} (hd : τ.length < d)
    (hagree : ∀ σ', σ' ≠ τ →
      (Δ₁.at σ' = Δ.at σ' ∧ Θ₁.at σ' = Θ.at σ') ∧ (Δ₂.at σ' = Δ.at σ' ∧ Θ₂.at σ' = Θ.at σ'))
    (hcont : Provable [conj (Δ.at τ ++ (Θ.at τ).map WFF.neg)]
      ((conj (Δ₁.at τ ++ (Θ₁.at τ).map WFF.neg)).or (conj (Δ₂.at τ ++ (Θ₂.at τ).map WFF.neg))))
    (q₁ : Provable [Pc D Δ₁ Θ₁ d []] .bot) (q₂ : Provable [Pc D Δ₂ Θ₂ d []] .bot) :
    Provable [Pc D Δ Θ d []] .bot := by
  obtain ⟨f, hf⟩ : ∃ f, d - τ.length = f + 1 := ⟨d - τ.length - 1, by omega⟩
  have hc := or_path h0 hok hW τ hd.le
    (fun σ' hσ => hagree σ' fun h => hσ (h ▸ List.suffix_refl _)) (by
      rw [hf]
      refine closed_or_tr h0 hok ?_
      rw [tr_succ, tr_succ, tr_succ]
      have e₁ : (D.children τ).map (fun k => pack D (D.ctxAt Γ₀ τ) (k :: τ)
          (Pc D Δ₁ Θ₁ f (k :: τ))) = (D.children τ).map (fun k => pack D (D.ctxAt Γ₀ τ) (k :: τ)
          (Pc D Δ Θ f (k :: τ))) := List.map_congr_left fun j _ => by
        rw [Pc_congr fun σ' hσ => (hagree σ' (not_sub_child hσ)).1]
      have e₂ : (D.children τ).map (fun k => pack D (D.ctxAt Γ₀ τ) (k :: τ)
          (Pc D Δ₂ Θ₂ f (k :: τ))) = (D.children τ).map (fun k => pack D (D.ctxAt Γ₀ τ) (k :: τ)
          (Pc D Δ Θ f (k :: τ))) := List.map_congr_left fun j _ => by
        rw [Pc_congr fun σ' hσ => (hagree σ' (not_sub_child hσ)).2]
      rw [e₁, e₂]
      exact or_and_right hcont)
  exact or_cases hc (sub (by lsub) q₁) (sub (by lsub) q₂)

/-- ⭐**An axiom**: the node's formulas refuted. -/
theorem bot_hole (h0 : Γ₀.SlotsFrom 0) (hok : D.OK Γ₀) (hW : D.WitOK Γ₀)
    {Δ Θ : Seq σ Γ₀ D} {τ : Lab} {d : ℕ} (hd : τ.length < d) (hr : D.Reach τ)
    (hc : Provable [conj (Δ.at τ ++ (Θ.at τ).map WFF.neg)] .bot) :
    Provable [Pc D Δ Θ d []] .bot := by
  obtain ⟨f, hf⟩ : ∃ f, d - τ.length = f + 1 := ⟨d - τ.length - 1, by omega⟩
  refine bot_path h0 hok hW τ hd.le hr ?_
  rw [hf]
  exact closed_bot_tr h0 hok (chain ((lk List.mem_cons_self).map .and_elim_l) (sub (by lsub) hc))

end Same

/-! ## A child's formulas, from the parent's modal ones -/

/-- `pack` with `□`-hypotheses of the parent moved into the child. -/
theorem pack_side {D : Tree} {Γ : Ctx} {c : Lab}
    (hw : ∀ x, D.edge c = some (.dia x) → ∃ X, Γ.ref x = some (.VTypeDia X))
    {χs : List (WFF σ Γ.boxIn 0)} {A B : WFF σ (D.view c Γ) 0}
    (p : Provable (A :: χs.map (WFF.mono (Tree.boxIn_le_view c Γ))) B) :
    Provable (pack D Γ c A :: χs.map fun χ => WFF.box (Γ := Γ) χ) (pack D Γ c B) := by
  have key : ∀ (W : Ctx) (e : D.view c Γ = W) (h' : Γ.boxIn.Le W),
      Provable (WFF.mono (Ctx.le_of_eq e) A :: χs.map (WFF.mono h'))
        (WFF.mono (Ctx.le_of_eq e) B) := fun W e h' => by
    have q := prov_cast e p
    rw [List.map_cons, List.map_map] at q
    refine (congrArg (fun L => Provable (WFF.mono (Ctx.le_of_eq e) A :: L) _) ?_).mp q
    exact List.map_congr_left fun ψ _ => by simp only [Function.comp, WFF.mono_mono]
  cases he : D.edge c with
  | none =>
      have q := key _ (Tree.view_box (Or.inl he)) (Ctx.Le.refl _)
      rw [List.map_congr_left fun ψ _ => WFF.mono_refl _ ψ, List.map_id'] at q
      simp only [pack_box (Or.inl he)]
      exact or_cases (dpk_or (orl _ q)) (lk List.mem_cons_self) (lk List.mem_cons_self)
  | some e =>
      cases e with
      | box =>
          have q := key _ (Tree.view_box (Or.inr he)) (Ctx.Le.refl _)
          rw [List.map_congr_left fun ψ _ => WFF.mono_refl _ ψ, List.map_id'] at q
          simp only [pack_box (Or.inr he)]
          exact or_cases (dpk_or (orl _ q)) (lk List.mem_cons_self) (lk List.mem_cons_self)
      | dia x =>
          have hx := hw x he
          have q := key _ (Tree.view_dia he) (Ctx.le_boxIn_diaIn Γ x)
          simp only [pack_dia he hx]
          exact or_cases (dia_or x hx (Δ₂ := []) (orl _ q))
            (lk List.mem_cons_self) (lk List.mem_cons_self)

/-- `pack` along a `◇_x`-edge with `□_x`-hypotheses of the parent moved into the child. -/
theorem pack_diaside {D : Tree} {Γ : Ctx} {c : Lab} {x : VarSymb}
    (he : D.edge c = some (.dia x)) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    {θs : List (WFF σ (Γ.diaIn x) 0)} {A B : WFF σ (D.view c Γ) 0}
    (p : Provable (A :: θs.map (WFF.mono (Ctx.le_of_eq (Tree.view_dia he).symm))) B) :
    Provable (pack D Γ c A :: θs.map (WFF.boxx x hx)) (pack D Γ c B) := by
  simp only [pack_dia he hx]
  have q := prov_cast (Tree.view_dia he) p
  rw [List.map_cons, List.map_map] at q
  have e : θs.map (WFF.mono (Ctx.le_of_eq (Tree.view_dia he)) ∘
      WFF.mono (Ctx.le_of_eq (Tree.view_dia he).symm)) = θs :=
    (List.map_congr_left fun ψ _ => by
      simp only [Function.comp, WFF.mono_mono]
      exact WFF.mono_refl _ ψ).trans (List.map_id' θs)
  rw [e] at q
  have r := dia_or x hx (Δ₁ := []) (orl (WFF.mono (Ctx.le_of_eq (Tree.view_dia he)) B)
    (by rw [List.map_nil, List.append_nil]; exact q))
  rw [List.map_nil, List.append_nil] at r
  exact or_cases r (lk List.mem_cons_self) (lk List.mem_cons_self)

/-- Adding a formula at a node: its reading, with the formula, from its reading. -/
theorem tr_add {D : Tree} {Δ Θ Δ' Θ' : Seq σ Γ₀ D} {c : Lab} {f : ℕ}
    {H : List (WFF σ (D.ctxAt Γ₀ c) 0)} {x : WFF σ (D.ctxAt Γ₀ c) 0}
    (hsub : ∀ σ', σ' ≠ c → Δ'.at σ' = Δ.at σ' ∧ Θ'.at σ' = Θ.at σ')
    (hC : ∀ φ ∈ Δ'.at c ++ (Θ'.at c).map WFF.neg, φ = x ∨ φ ∈ Δ.at c ++ (Θ.at c).map WFF.neg)
    (hx : Provable (tr D Δ Θ f c :: H) x) : Provable (tr D Δ Θ f c :: H) (tr D Δ' Θ' f c) := by
  have hc : ∀ φ ∈ Δ'.at c ++ (Θ'.at c).map WFF.neg, Provable (tr D Δ Θ f c :: H) φ :=
    fun φ hφ => (hC φ hφ).elim (fun e => e ▸ hx) fun h => sub (by lsub) (of_tr h)
  cases f with
  | zero =>
      rw [tr_zero D Δ' Θ' c]
      exact andI (conj_intro hc) ⟨.top_intro⟩
  | succ f =>
      rw [tr_succ D Δ' Θ' f c]
      have e : (D.children c).map (fun k => pack D (D.ctxAt Γ₀ c) (k :: c)
          (Pc D Δ' Θ' f (k :: c))) = (D.children c).map (fun k => pack D (D.ctxAt Γ₀ c) (k :: c)
          (Pc D Δ Θ f (k :: c))) := List.map_congr_left fun j _ => by
        rw [Pc_congr fun σ' hσ => hsub σ' (not_sub_child hσ)]
      rw [e]
      exact andI (conj_intro hc) ((lk List.mem_cons_self).map .and_elim_r)

/-! ## Rules that grow the tree -/

theorem ctxAt_eq_vw (D : Tree) (ρ : Lab) :
    D.ctxAt Γ₀ ρ = ((Vw D Γ₀ ρ).inserts (D.birthsAt ρ)).optInsK (D.opensAt ρ) := by
  cases ρ <;> rfl

/-- A formula of the node, weakened along any inclusion, from the node's reading. -/
theorem of_mono {D : Tree} {Δ Θ : Seq σ Γ₀ D} {τ : Lab} {f : ℕ} {Γ' : Ctx}
    (h : (D.ctxAt Γ₀ τ).Le Γ') {H : List (WFF σ Γ' 0)} (hH : WFF.mono h (tr D Δ Θ f τ) ∈ H)
    {c : WFF σ (D.ctxAt Γ₀ τ) 0} (hc : c ∈ Δ.at τ ++ (Θ.at τ).map WFF.neg) :
    Provable H (WFF.mono h c) := by
  have h₁ : Provable H (WFF.mono h (conj (Δ.at τ ++ (Θ.at τ).map WFF.neg))) := by
    cases f <;> exact (lk hH).map .and_elim_l
  rw [mono_conj] at h₁
  exact conj_elim h₁ _ (List.mem_map_of_mem hc)

section Grow

variable {D D' : Tree} {Δ Θ : Seq σ Γ₀ D} {Δ' Θ' : Seq σ Γ₀ D'}
  {hk : ∀ ρ, (D.ctxAt Γ₀ ρ).Le (D'.ctxAt Γ₀ ρ)} {hV : ∀ ρ, (Vw D Γ₀ ρ).Le (Vw D' Γ₀ ρ)}

/-- The premise's reading at a node whose children are unchanged. -/
theorem hole_grow (hW : D.WitOK Γ₀) {τ : Lab} {f : ℕ} {H : List (WFF σ (D'.ctxAt Γ₀ τ) 0)}
    (hH : WFF.mono (hk τ) (tr D Δ Θ f τ) ∈ H) (hch : D'.children τ = D.children τ)
    (he : ∀ j, D'.edge (j :: τ) = D.edge (j :: τ))
    (hcl : ∀ f' j, f = f' + 1 → j ∈ D.children τ → Claim Δ Θ Δ' Θ' hV f' (j :: τ))
    (hcont : ∀ φ ∈ Δ'.at τ ++ (Θ'.at τ).map WFF.neg, Provable H φ) :
    Provable H (tr D' Δ' Θ' f τ) := by
  cases f with
  | zero =>
      rw [tr_zero]
      exact andI (conj_intro hcont) ⟨.top_intro⟩
  | succ f' =>
      refine hole_tr hcont fun j hj => ?_
      rw [hch] at hj
      exact pack_of_claim hW hj (he j) (hcl f' j rfl hj) hH

/-- Closing a node whose births gain the eigenvariable at the head. -/
theorem claim_of_tr_cons (h0 : Γ₀.SlotsFrom 0) (hok : D.OK Γ₀) (hok' : D'.OK Γ₀) {ρ : Lab}
    {v : ℕ} {T : VarType} (hb : D'.birthsAt ρ = (.free v, T) :: D.birthsAt ρ)
    (ho : D'.opensAt ρ = D.opensAt ρ) {f : ℕ}
    (hbO : ((Vw D' Γ₀ ρ).inserts (D.birthsAt ρ)).OptsEff (D.opensAt ρ))
    (hfr : (((Vw D' Γ₀ ρ).inserts (D.birthsAt ρ)).optInsK (D.opensAt ρ)).RootFresh (.free v))
    (hs : ((Vw D' Γ₀ ρ).inserts (D.birthsAt ρ)).SlotsFrom 0)
    (hcast : (D'.ctxAt Γ₀ ρ).Le
      ((((Vw D' Γ₀ ρ).inserts (D.birthsAt ρ)).optInsK (D.opensAt ρ)).insert (.free v) T))
    (hA : (D.ctxAt Γ₀ ρ).Le (((Vw D' Γ₀ ρ).inserts (D.birthsAt ρ)).optInsK (D.opensAt ρ)))
    (p : Provable [WFF.mono hA (tr D Δ Θ f ρ)]
      (.ex T (WFF.bindFree v hfr (hs.optInsK _) T (WFF.mono hcast (tr D' Δ' Θ' f ρ))))) :
    Claim Δ Θ Δ' Θ' hV f ρ := by
  cases ρ with
  | nil =>
      exact closed_cons_of (hV []) hb ho (Tree.nok h0 hok []) (Tree.nok h0 hok' []) hbO hA hfr
        hs hcast p
  | cons k ρ =>
      exact closed_cons_of (hV (k :: ρ)) hb ho (Tree.nok h0 hok _) (Tree.nok h0 hok' _) hbO hA
        hfr hs hcast p

/-- Closing a node that gains an opening at the head. -/
theorem closed_open_of {V V' : Ctx} (hVV : V.Le V') {L L' : List (Root × VarType)}
    {O O' : List (WitKind × VarSymb)} {κ : WitKind} {y : VarSymb} (hL : L' = L)
    (hO : O' = (κ, y) :: O) (hb : NOK V L O) (hb' : NOK V' L' O')
    (hOn : ModalSys.Opt = true) (hy : ∃ X, ((V'.inserts L).optInsK O).witK κ y = some X)
    {A : WFF σ ((V.inserts L).optInsK O) 0} {B : WFF σ ((V'.inserts L').optInsK O') 0}
    (hA : ((V.inserts L).optInsK O).Le ((V'.inserts L).optInsK O))
    (hcast : ((V'.inserts L').optInsK O').Le (((V'.inserts L).optInsK O).optInK κ y))
    (p : Provable [WFF.mono hA A] (.optx hOn κ y hy (WFF.mono hcast B))) :
    Provable [WFF.mono hVV (closeN L O A)] (closeN L' O' B) := by
  subst L'
  subst O'
  have hbO : (V'.inserts L).OptsEff O := hb'.2.1
  rw [mono_closeN hVV hb ⟨hb'.1, hbO⟩ A]
  unfold closeN
  rw [closeO_cons hOn hy]
  refine or_cases (closeB_or hb'.1 (H := []) (orl _ ?_)) (lk List.mem_cons_self)
    (lk List.mem_cons_self)
  rw [WFF.mono_refl] at p
  exact or_cases (closeO_or hbO (H := []) (orl _ p)) (lk List.mem_cons_self)
    (lk List.mem_cons_self)

/-- A node that gains an opening at the head: its closed reading, from the opened reading. -/
theorem claim_of_tr_open (h0 : Γ₀.SlotsFrom 0) (hok : D.OK Γ₀) (hok' : D'.OK Γ₀) {ρ : Lab}
    {κ : WitKind} {y : VarSymb} (hb : D'.birthsAt ρ = D.birthsAt ρ)
    (ho : D'.opensAt ρ = (κ, y) :: D.opensAt ρ) {f : ℕ} (hOn : ModalSys.Opt = true)
    (hy : ∃ X, (((Vw D' Γ₀ ρ).inserts (D.birthsAt ρ)).optInsK (D.opensAt ρ)).witK κ y = some X)
    (hcast : (D'.ctxAt Γ₀ ρ).Le
      ((((Vw D' Γ₀ ρ).inserts (D.birthsAt ρ)).optInsK (D.opensAt ρ)).optInK κ y))
    (hA : (D.ctxAt Γ₀ ρ).Le (((Vw D' Γ₀ ρ).inserts (D.birthsAt ρ)).optInsK (D.opensAt ρ)))
    (p : Provable [WFF.mono hA (tr D Δ Θ f ρ)]
      (.optx hOn κ y hy (WFF.mono hcast (tr D' Δ' Θ' f ρ)))) :
    Claim Δ Θ Δ' Θ' hV f ρ := by
  cases ρ with
  | nil =>
      exact closed_open_of (hV []) hb ho (Tree.nok h0 hok []) (Tree.nok h0 hok' []) hOn hy hA
        hcast p
  | cons k ρ =>
      exact closed_open_of (hV (k :: ρ)) hb ho (Tree.nok h0 hok _) (Tree.nok h0 hok' _) hOn hy
        hA hcast p

end Grow

theorem vw_le_addEdge {D : Tree} {c : Lab} (hc : D.edge c = none) (e : EdgeKind) :
    ∀ ρ, (Vw D Γ₀ ρ).Le (Vw (D.addEdge c e) Γ₀ ρ)
  | [] => Ctx.Le.refl _
  | k :: ρ => Tree.view_le_view (Tree.ctxAt_addEdge hc e ρ) fun e₁ he₁ => ⟨e₁, by
      rw [Tree.edge_addEdge, if_neg fun h => by rw [h, hc] at he₁; cases he₁]
      exact he₁, EdgeKind.compat_refl e₁⟩

theorem vw_le_addBirth {D : Tree} {r : Root} (hf : D.Fresh Γ₀ r) (τ : Lab) (T : VarType) :
    ∀ ρ, (Vw D Γ₀ ρ).Le (Vw (D.addBirth τ r T) Γ₀ ρ)
  | [] => Ctx.Le.refl _
  | _ :: ρ => Tree.view_le_view (Tree.ctxAt_addBirth hf τ T ρ) fun e₁ he₁ =>
      ⟨e₁, he₁, EdgeKind.compat_refl e₁⟩

theorem vw_le_addOpen {D : Tree} (τ : Lab) (κ : WitKind) (y : VarSymb) :
    ∀ ρ, (Vw D Γ₀ ρ).Le (Vw (D.addOpen τ κ y) Γ₀ ρ)
  | [] => Ctx.Le.refl _
  | _ :: ρ => Tree.view_le_view (Tree.ctxAt_addOpen τ κ y ρ) fun e₁ he₁ =>
      ⟨e₁, he₁, EdgeKind.compat_refl e₁⟩

theorem vw_open_eq {D : Tree} (τ : Lab) (κ : WitKind) (y : VarSymb) :
    Vw (D.addOpen τ κ y) Γ₀ τ = Vw D Γ₀ τ := by
  cases τ with
  | nil => rfl
  | cons k ρ =>
      change (D.addOpen (k :: ρ) κ y).view (k :: ρ) ((D.addOpen (k :: ρ) κ y).ctxAt Γ₀ ρ) =
        D.view (k :: ρ) (D.ctxAt Γ₀ ρ)
      rw [Tree.ctxAt_addOpen_off (D := D) ρ fun h' => by have := h'.length_le; simp at this]
      rfl

theorem children_addEdge_ne {D : Tree} {k : ℕ} {τ ρ : Lab} (e : EdgeKind) (h : ρ ≠ τ) :
    (D.addEdge (k :: τ) e).children ρ = D.children ρ := by
  unfold Tree.children Tree.addEdge
  rw [List.filterMap_cons]
  dsimp only
  rw [if_neg (Ne.symm h)]

theorem mem_children_addEdge {D : Tree} {k j : ℕ} {τ : Lab} (e : EdgeKind) :
    j ∈ (D.addEdge (k :: τ) e).children τ ↔ j = k ∨ j ∈ D.children τ := by
  rw [Tree.mem_children, Tree.mem_children, Tree.edge_addEdge]
  by_cases hj : j = k
  · subst hj
    simp
  · rw [if_neg fun h => hj (List.cons.inj h).1]
    simp [hj]

/-! ## The invariants -/

/-- The formulas a rule can be principal on (every right formula, every left non-atom) are at
    reachable nodes, within the depth `d` with room for the height `n`.  Left atoms, which `ref`
    and `repl` may put anywhere, are free. -/
structure Inv {D : Tree} (n d : ℕ) (Δ Θ : Seq σ Γ₀ D) : Prop where
  right : ∀ p ∈ Θ, D.Reach p.1 ∧ p.1.length + n < d
  left : ∀ p ∈ Δ, ¬ p.2.IsAtom → D.Reach p.1 ∧ p.1.length + n < d

theorem inv_ext {D : Tree} {Δ Θ : Seq σ Γ₀ D} {n d : ℕ} (hi : Inv (n + 1) d Δ Θ) {τ : Lab}
    (hr : D.Reach τ) (hτ : τ.length + n < d) (L₁ R₁ : Seq σ Γ₀ D)
    (h₁ : ∀ q ∈ L₁ ++ R₁, q.1 = τ) : Inv n d (L₁ ++ Δ) (R₁ ++ Θ) := by
  refine ⟨fun p hp => ?_, fun p hp hna => ?_⟩
  · rcases List.mem_append.mp hp with hp | hp
    · rw [h₁ p (List.mem_append_right _ hp)]; exact ⟨hr, hτ⟩
    · have := hi.right p hp; exact ⟨this.1, by omega⟩
  · rcases List.mem_append.mp hp with hp | hp
    · rw [h₁ p (List.mem_append_left _ hp)]; exact ⟨hr, hτ⟩
    · have := hi.left p hp hna; exact ⟨this.1, by omega⟩

theorem inv_atom {D : Tree} {Δ Θ : Seq σ Γ₀ D} {n d : ℕ} (hi : Inv (n + 1) d Δ Θ)
    {x : LF σ Γ₀ D} (hx : x.2.IsAtom) : Inv n d (x :: Δ) Θ := by
  refine ⟨fun p hp => ?_, fun p hp hna => ?_⟩
  · have := hi.right p hp; exact ⟨this.1, by omega⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact absurd hx hna
    · have := hi.left p hp hna; exact ⟨this.1, by omega⟩

theorem Tree.reach_nil (D : Tree) : D.Reach [] := fun _ _ h => by
  have := h.length_le
  simp at this

theorem Tree.reach_cons {D : Tree} {ρ : Lab} {j : ℕ} (hr : D.Reach ρ)
    (he : D.edge (j :: ρ) ≠ none) : D.Reach (j :: ρ) := fun k ρ' h => by
  rcases List.suffix_cons_iff.mp h with e | h
  · rw [e]; exact he
  · exact hr k ρ' h

/-- The reading reads only the nodes it reaches. -/
theorem tr_vis {D : Tree} {Δ Θ Δ₁ Θ₁ : Seq σ Γ₀ D} :
    ∀ f ρ, D.Reach ρ → (∀ σ', ρ <:+ σ' → D.Reach σ' → σ'.length ≤ ρ.length + f →
      Δ₁.at σ' = Δ.at σ' ∧ Θ₁.at σ' = Θ.at σ') → tr D Δ₁ Θ₁ f ρ = tr D Δ Θ f ρ
  | 0, ρ, hr, h => by
      rw [tr_zero, tr_zero, (h ρ (List.suffix_refl _) hr (by omega)).1,
        (h ρ (List.suffix_refl _) hr (by omega)).2]
  | f + 1, ρ, hr, h => by
      rw [tr_succ, tr_succ, (h ρ (List.suffix_refl _) hr (by omega)).1,
        (h ρ (List.suffix_refl _) hr (by omega)).2]
      refine congrArg (WFF.and _) (congrArg conj (List.map_congr_left fun j hj => ?_))
      have e := tr_vis f (j :: ρ) (Tree.reach_cons hr (Tree.mem_children.mp hj))
        fun σ' hσ hr' hl => h σ' ((List.suffix_cons j ρ).trans hσ) hr' (by
          simp only [List.length_cons] at hl; omega)
      change pack _ _ _ (closeN _ _ (tr D Δ₁ Θ₁ f (j :: ρ))) =
        pack _ _ _ (closeN _ _ (tr D Δ Θ f (j :: ρ)))
      rw [e]

/-- A formula at a node the reading does not reach leaves it alone. -/
theorem Pc_vis {D : Tree} {Δ Θ Δ₁ Θ₁ : Seq σ Γ₀ D} {d : ℕ}
    (h : ∀ σ', D.Reach σ' → σ'.length ≤ d → Δ₁.at σ' = Δ.at σ' ∧ Θ₁.at σ' = Θ.at σ') :
    Pc D Δ₁ Θ₁ d [] = Pc D Δ Θ d [] := by
  change closeN _ _ (tr D Δ₁ Θ₁ d []) = closeN _ _ (tr D Δ Θ d [])
  rw [tr_vis d [] (Tree.reach_nil D) fun σ' _ hr hl => h σ' hr (by simpa using hl)]

theorem Seq.at_append_off {D : Tree} {L₁ L : Seq σ Γ₀ D} {ρ : Lab}
    (h : ∀ q ∈ L₁, q.1 ≠ ρ) : Seq.at (L₁ ++ L) ρ = L.at ρ := by
  induction L₁ with
  | nil => rfl
  | cons q L₁ ih =>
      rw [List.cons_append, Seq.at_cons_ne (h q List.mem_cons_self),
        ih fun q' hq' => h q' (List.mem_cons_of_mem _ hq')]

theorem ag_birth {D : Tree} {Δ Θ : Seq σ Γ₀ D} {v : ℕ} {T : VarType} {τ : Lab}
    (hv : D.Fresh Γ₀ (.free v)) (L₁ R₁ : Seq σ Γ₀ (D.addBirth τ (.free v) T))
    (h₁ : ∀ q ∈ L₁ ++ R₁, q.1 = τ) {σ' : Lab} (hσ : σ' ≠ τ) :
    Ag Δ Θ (L₁ ++ Seq.mono (Tree.ctxAt_addBirth hv τ T) Δ)
      (R₁ ++ Seq.mono (Tree.ctxAt_addBirth hv τ T) Θ) (Tree.ctxAt_addBirth hv τ T) σ' where
  left := by
    rw [Seq.at_append_off fun q hq h' => hσ (h'.symm.trans (h₁ q (List.mem_append_left _ hq))),
      Seq.at_mono]
  right := by
    rw [Seq.at_append_off fun q hq h' => hσ (h'.symm.trans (h₁ q (List.mem_append_right _ hq))),
      Seq.at_mono]
  children := rfl
  edge _ := rfl
  births := by rw [Tree.birthsAt_addBirth, if_neg hσ]
  opens := rfl

theorem ag_open {D : Tree} {Δ Θ : Seq σ Γ₀ D} {κ : WitKind} {y : VarSymb} {τ : Lab}
    (L₁ R₁ : Seq σ Γ₀ (D.addOpen τ κ y)) (h₁ : ∀ q ∈ L₁ ++ R₁, q.1 = τ) {σ' : Lab}
    (hσ : σ' ≠ τ) :
    Ag Δ Θ (L₁ ++ Seq.mono (Tree.ctxAt_addOpen τ κ y) Δ)
      (R₁ ++ Seq.mono (Tree.ctxAt_addOpen τ κ y) Θ) (Tree.ctxAt_addOpen τ κ y) σ' where
  left := by
    rw [Seq.at_append_off fun q hq h' => hσ (h'.symm.trans (h₁ q (List.mem_append_left _ hq))),
      Seq.at_mono]
  right := by
    rw [Seq.at_append_off fun q hq h' => hσ (h'.symm.trans (h₁ q (List.mem_append_right _ hq))),
      Seq.at_mono]
  children := rfl
  edge _ := rfl
  births := rfl
  opens := by rw [Tree.opensAt_addOpen, if_neg hσ]

theorem ag_edge {D : Tree} {Δ Θ : Seq σ Γ₀ D} {k : ℕ} {τ : Lab} {e : EdgeKind}
    (hc : D.edge (k :: τ) = none) (L₁ R₁ : Seq σ Γ₀ (D.addEdge (k :: τ) e))
    (h₁ : ∀ q ∈ L₁ ++ R₁, q.1 = k :: τ) {σ' : Lab} (hσ : σ' ≠ τ) (hσc : σ' ≠ k :: τ) :
    Ag Δ Θ (L₁ ++ Seq.mono (Tree.ctxAt_addEdge hc e) Δ)
      (R₁ ++ Seq.mono (Tree.ctxAt_addEdge hc e) Θ) (Tree.ctxAt_addEdge hc e) σ' where
  left := by
    rw [Seq.at_append_off fun q hq h' => hσc (h'.symm.trans (h₁ q (List.mem_append_left _ hq))),
      Seq.at_mono]
  right := by
    rw [Seq.at_append_off fun q hq h' => hσc (h'.symm.trans (h₁ q (List.mem_append_right _ hq))),
      Seq.at_mono]
  children := children_addEdge_ne e hσ
  edge j := by rw [Tree.edge_addEdge, if_neg fun h' => hσ (List.cons.inj h').2]
  births := rfl
  opens := rfl

theorem inv_grow {D D' : Tree} (hk : ∀ ρ, (D.ctxAt Γ₀ ρ).Le (D'.ctxAt Γ₀ ρ))
    {Δ Θ : Seq σ Γ₀ D} {n d : ℕ} (hi : Inv (n + 1) d Δ Θ) (hreach : ∀ ρ, D.Reach ρ → D'.Reach ρ)
    {τ : Lab} (hr : D'.Reach τ) (hτ : τ.length + n < d) (L₁ R₁ : Seq σ Γ₀ D')
    (h₁ : ∀ q ∈ L₁ ++ R₁, q.1 = τ) : Inv n d (L₁ ++ Seq.mono hk Δ) (R₁ ++ Seq.mono hk Θ) := by
  refine ⟨fun p hp => ?_, fun p hp hna => ?_⟩
  · rcases List.mem_append.mp hp with hp | hp
    · rw [h₁ p (List.mem_append_right _ hp)]; exact ⟨hr, hτ⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have := hi.right q hq
      exact ⟨hreach _ this.1, show q.1.length + n < d by omega⟩
  · rcases List.mem_append.mp hp with hp | hp
    · rw [h₁ p (List.mem_append_left _ hp)]; exact ⟨hr, hτ⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have := hi.left q hq fun ha => hna (isAtom_mono ha)
      exact ⟨hreach _ this.1, show q.1.length + n < d by omega⟩

theorem reach_addEdge {D : Tree} {c : Lab} (e : EdgeKind) {ρ : Lab} (hρ : D.Reach ρ) :
    (D.addEdge c e).Reach ρ := fun k ρ' hs => by
  rw [Tree.edge_addEdge]
  split
  · exact Option.some_ne_none _
  · exact hρ k ρ' hs

theorem vw_birth_eq {D : Tree} {v : ℕ} {T : VarType} (τ : Lab) :
    (Vw (D.addBirth τ (.free v) T) Γ₀ τ).inserts (D.birthsAt τ) = D.preAt Γ₀ τ := by
  cases τ with
  | nil => rfl
  | cons k ρ =>
      change ((D.addBirth (k :: ρ) (.free v) T).view (k :: ρ)
        ((D.addBirth (k :: ρ) (.free v) T).ctxAt Γ₀ ρ)).inserts (D.birthsAt (k :: ρ)) =
        (D.view (k :: ρ) (D.ctxAt Γ₀ ρ)).inserts (D.birthsAt (k :: ρ))
      rw [Tree.ctxAt_addBirth_off (D := D) ρ fun h' => by have := h'.length_le; simp at this]
      rfl

theorem closeN_nil {V : Ctx} {L : List (Root × VarType)} {O : List (WitKind × VarSymb)}
    (hL : L = []) (hO : O = []) {H : List (WFF σ V 0)} {φ : WFF σ ((V.inserts L).optInsK O) 0}
    (hcast : ((V.inserts L).optInsK O).Le V)
    (p : Provable H (WFF.mono hcast φ)) : Provable H (closeN L O φ) := by
  subst hL
  subst hO
  rw [WFF.mono_refl] at p
  exact p

/-- ⭐**A new child's closed reading**, from one hypothesis behind its edge: no births, no
    children, its formulas from the hypothesis. -/
theorem new_child {D' : Tree} {Δ' Θ' : Seq σ Γ₀ D'} {k : ℕ} {τ : Lab}
    {f : ℕ} (hL : D'.birthsAt (k :: τ) = []) (hO : D'.opensAt (k :: τ) = [])
    (hch : ∀ j, D'.edge (j :: k :: τ) = none)
    {y : WFF σ (Vw D' Γ₀ (k :: τ)) 0}
    (hcont : ∀ h : (Vw D' Γ₀ (k :: τ)).Le (D'.ctxAt Γ₀ (k :: τ)),
      ∀ φ ∈ Δ'.at (k :: τ) ++ (Θ'.at (k :: τ)).map WFF.neg, Provable [WFF.mono h y] φ) :
    Provable [y] (Pc D' Δ' Θ' f (k :: τ)) := by
  have e : D'.ctxAt Γ₀ (k :: τ) = Vw D' Γ₀ (k :: τ) :=
    (ctxAt_eq_vw D' (k :: τ)).trans (by rw [hL, hO]; rfl)
  have loc : Provable [WFF.mono (Ctx.le_of_eq e.symm) y] (tr D' Δ' Θ' f (k :: τ)) := by
    cases f with
    | zero =>
        rw [tr_zero]
        exact andI (conj_intro (hcont _)) ⟨.top_intro⟩
    | succ f =>
        refine hole_tr (hcont _) fun j hj => ?_
        exact absurd (hch j) (Tree.mem_children.mp hj)
  have q := prov_cast e loc
  rw [List.map_cons, List.map_nil, WFF.mono_mono, WFF.mono_refl] at q
  exact closeN_nil hL hO (Ctx.le_of_eq e) q

/-- `◇⁰` is monotone, with side hypotheses. -/
theorem opt_mono {Γ : Ctx} (hO : ModalSys.Opt = true) (κ : WitKind) (y : VarSymb)
    (hy : ∃ X, Γ.witK κ y = some X) {H : List (WFF σ Γ 0)} {A B : WFF σ (Γ.optInK κ y) 0}
    (p : Provable (A :: H.map (WFF.mono (Ctx.le_optInK Γ κ y))) B) :
    Provable (.optx hO κ y hy A :: H) (.optx hO κ y hy B) :=
  or_cases (opt_or hO κ y hy (orl B p)) (lk List.mem_cons_self) (lk List.mem_cons_self)

/-- The bridge, contraposed: `¬◇_x θ ⊢ □¬◇⁰_x θ`, the fold's negation boxed. -/
theorem box_fold_neg {Γ : Ctx} (hO : ModalSys.Opt = true) (x : VarSymb)
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {θ : WFF σ (Γ.diaIn x) 0} {H : List (WFF σ Γ 0)}
    (h : (WFF.dia x hx θ).neg ∈ H) : Provable H (WFF.box (Γ := Γ) (WFF.fold hO x hx θ).neg) :=
  dne (lam (contra (List.mem_cons_of_mem _ h)
    ⟨Proof.opt_dia hO x hx (Proof.lookup List.mem_cons_self)⟩))

theorem dpk_of_neg {Γ : Ctx} {A : WFF σ Γ.boxIn 0} {X : WFF σ Γ.boxIn 0}
    (hX : Provable [A.neg] X) : Provable [(WFF.box (Γ := Γ) A).neg] (dpk X) := by
  have k : Provable [X.neg] A :=
    byContra (mp (lk (List.mem_cons_of_mem _ List.mem_cons_self)) (sub (by lsub) hX))
  obtain ⟨k⟩ := k
  refine lam (contra (List.mem_cons_of_mem _ List.mem_cons_self) (dis ⟨Proof.K_box k⟩ ?_))
  intro ℓ hℓ
  rw [List.map_cons, List.map_nil, List.mem_singleton] at hℓ
  rw [hℓ]
  exact lk List.mem_cons_self

theorem dpk_D (hD : ModalSys.D = true) {Γ : Ctx} {H : List (WFF σ Γ 0)} {X : WFF σ Γ.boxIn 0}
    (hX : Provable [] X) : Provable H (dpk X) := by
  have k : Provable [X.neg] .bot := mp (lk List.mem_cons_self) (sub (by lsub) hX)
  obtain ⟨k⟩ := k
  exact lam ⟨.D_box hD (Proof.ofSubset (by lsub) (Proof.K_box k))⟩

theorem dia_mono_of {Γ : Ctx} (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    {A X : WFF σ (Γ.diaIn x) 0} (hX : Provable [A] X) :
    Provable [WFF.dia x hx A] (WFF.dia x hx X) :=
  or_cases (dia_or x hx (Δ₁ := []) (Δ₂ := []) (orl X hX)) (lk List.mem_cons_self)
    (lk List.mem_cons_self)

theorem vacant_at {D : Tree} {c : Lab} {Δ Θ : Seq σ Γ₀ D} (hv : Vacant D c Δ Θ) :
    Δ.at c = [] ∧ Θ.at c = [] := by
  constructor
  · refine List.eq_nil_iff_forall_not_mem.mpr fun φ hφ => ?_
    exact hv.left _ (Seq.mem_at.mp hφ) (List.suffix_refl _)
  · refine List.eq_nil_iff_forall_not_mem.mpr fun φ hφ => ?_
    exact hv.right _ (Seq.mem_at.mp hφ) (List.suffix_refl _)

theorem inv_grow0 {D D' : Tree} (hk : ∀ ρ, (D.ctxAt Γ₀ ρ).Le (D'.ctxAt Γ₀ ρ))
    {Δ Θ : Seq σ Γ₀ D} {n d : ℕ} (hi : Inv (n + 1) d Δ Θ)
    (hreach : ∀ ρ, D.Reach ρ → D'.Reach ρ) : Inv n d (Seq.mono hk Δ) (Seq.mono hk Θ) :=
  ⟨fun p hp => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have := hi.right q hq
    exact ⟨hreach _ this.1, show q.1.length + n < d by omega⟩,
  fun p hp hna => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have := hi.left q hq fun ha => hna (isAtom_mono ha)
    exact ⟨hreach _ this.1, show q.1.length + n < d by omega⟩⟩

theorem in_content_l {D : Tree} {Δ Θ : Seq σ Γ₀ D} {τ : Lab} {φ : WFF σ (D.ctxAt Γ₀ τ) 0}
    (h : (⟨τ, φ⟩ : LF σ Γ₀ D) ∈ Δ) : φ ∈ Δ.at τ ++ (Θ.at τ).map WFF.neg :=
  List.mem_append_left _ (Seq.mem_at.mpr h)

theorem in_content_r {D : Tree} {Δ Θ : Seq σ Γ₀ D} {τ : Lab} {φ : WFF σ (D.ctxAt Γ₀ τ) 0}
    (h : (⟨τ, φ⟩ : LF σ Γ₀ D) ∈ Θ) : φ.neg ∈ Δ.at τ ++ (Θ.at τ).map WFF.neg :=
  List.mem_append_right _ (List.mem_map_of_mem (Seq.mem_at.mpr h))

theorem conj_add {Γ : Ctx} {C C₁ E : List (WFF σ Γ 0)} (hC : ∀ c ∈ C₁, c ∈ E ∨ c ∈ C) :
    Provable (E ++ [conj C]) (conj C₁) :=
  conj_intro fun c hc => (hC c hc).elim (fun h => lk (List.mem_append_left _ h))
    fun h => conj_elim (lk (List.mem_append_right _ List.mem_cons_self)) c h

theorem not_and_or {Γ : Ctx} {H : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (h : (φ.and ψ).neg ∈ H) :
    Provable H (φ.neg.or ψ.neg) :=
  byContra (contra (List.mem_cons_of_mem _ h) (andI
    (byContra (contra (List.mem_cons_of_mem _ List.mem_cons_self) (orl _ (lk List.mem_cons_self))))
    (byContra (contra (List.mem_cons_of_mem _ List.mem_cons_self)
      (orr _ (lk List.mem_cons_self))))))

theorem imp_or {Γ : Ctx} {H : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (h : φ.imp ψ ∈ H) :
    Provable H (φ.neg.or ψ) :=
  or_cases ⟨.lem φ⟩ (orr _ (mp (lk (List.mem_cons_of_mem _ h)) (lk List.mem_cons_self)))
    (orl _ (lk List.mem_cons_self))

/-! ## ⭐GKN into natural deduction -/


set_option maxHeartbeats 4000000 in
-- One case per rule of `GKN`, each rearranging a node's formulas (`tauto`): long, not stuck.
/-- ⭐**GKN into natural deduction**: a derivation of a tree sequent refutes its reading at the
    root, at any depth with room for the derivation's height. -/
theorem toND [Γ₀.Presented] {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (p : GKN σ Γ₀ n D Δ Θ) :
    D.OK Γ₀ → D.WitOK Γ₀ → ∀ d, Inv n d Δ Θ → Provable [Pc D Δ Θ d []] .bot := by
  have h0 : Γ₀.SlotsFrom 0 := Ctx.NoSlots.slots
  induction p with
  | @ax n D Δ Θ τ P hP h₁ h₂ =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + n < d := hi.right _ h₂
      exact bot_hole (τ := τ) h0 hok hW (by omega) hr
        (mp (conj_elim (lk List.mem_cons_self) _ (in_content_r h₂))
          (conj_elim (lk List.mem_cons_self) _ (in_content_l h₁)))
  | @botL n D Δ Θ τ h =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + n < d := hi.left _ h id
      exact bot_hole (τ := τ) h0 hok hW (by omega) hr
        (conj_elim (lk List.mem_cons_self) _ (in_content_l h))
  | @topR n D Δ Θ τ h =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + n < d := hi.right _ h
      exact bot_hole (τ := τ) h0 hok hW (by omega) hr
        (mp (conj_elim (lk List.mem_cons_self) _ (in_content_r h)) ⟨.top_intro⟩)
  | @andL n D Δ Θ τ φ ψ h _ ih =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.left _ h id
      refine same_hole (τ := τ) h0 hok hW (by omega) (fun σ' hσ => ?_) (fun f χ hχ => ?_)
        (ih hok hW d (inv_ext (τ := τ) hi hr (by omega) [⟨τ, φ⟩, ⟨τ, ψ⟩] [] (by simp)))
      · exact ⟨by rw [Seq.at_cons_ne (Ne.symm hσ), Seq.at_cons_ne (Ne.symm hσ)], rfl⟩
      · rw [Seq.at_cons_self, Seq.at_cons_self] at hχ
        simp only [List.cons_append, List.mem_cons] at hχ
        rcases hχ with rfl | rfl | hχ
        · exact (of_tr (in_content_l h)).map .and_elim_l
        · exact (of_tr (in_content_l h)).map .and_elim_r
        · exact of_tr hχ
  | @TL n D Δ Θ hT τ hs φ h _ ih =>
      intro hok hW d hi
      haveI : (D.ctxAt Γ₀ τ).NoSlots := ⟨hs⟩
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.left _ h id
      refine same_hole (τ := τ) h0 hok hW (by omega) (fun σ' hσ => ?_) (fun f χ hχ => ?_)
        (ih hok hW d (inv_ext (τ := τ) hi hr (by omega)
          [⟨τ, WFF.collapse (Ctx.collapses_boxIn_self hT _) hs.boxIn φ⟩] [] (by simp)))
      · exact ⟨by rw [Seq.at_cons_ne (Ne.symm hσ)], rfl⟩
      · rw [Seq.at_cons_self] at hχ
        simp only [List.cons_append, List.mem_cons] at hχ
        rcases hχ with rfl | hχ
        · exact (of_tr (in_content_l h)).map (.T_box hT)
        · exact of_tr hχ
  | @diaT n D Δ Θ hT hO τ hs x hx φ h _ ih =>
      intro hok hW d hi
      haveI : (D.ctxAt Γ₀ τ).NoSlots := ⟨hs⟩
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.right _ h
      refine same_hole (τ := τ) (Θ' := ⟨τ, WFF.diaId hT hO x hx φ⟩ :: Θ) h0 hok hW (by omega)
        (fun σ' hσ => ⟨rfl, by rw [Seq.at_cons_ne (Ne.symm hσ)]⟩)
        (fun f χ hχ => ?_)
        (ih hok hW d (inv_ext (τ := τ) hi hr (by omega) [] [⟨τ, WFF.diaId hT hO x hx φ⟩]
          (by simp)))
      rw [Seq.at_cons_self] at hχ
      simp only [List.map_cons, List.mem_append, List.mem_cons] at hχ
      rcases hχ with hχ | rfl | hχ
      · exact of_tr (List.mem_append_left _ hχ)
      · have hb := dis (box_fold_neg hO x hx (H := [(WFF.dia x hx φ).neg]) List.mem_cons_self)
          fun ℓ hℓ => by
            rw [List.mem_singleton.mp hℓ]
            exact of_tr (Δ := Δ) (f := f) (in_content_r h)
        exact (congrArg (fun χ => Provable [tr D Δ Θ f τ] (WFF.neg χ))
          (WFF.collapse_fold hT hO x hx φ)).mp (hb.map (Proof.T_box hT))
      · exact of_tr (List.mem_append_right _ hχ)
  | @andR n D Δ Θ τ φ ψ h _ _ ih₁ ih₂ =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.right _ h
      refine same_hole2 (τ := τ) (Θ₁ := ⟨τ, φ⟩ :: Θ) (Θ₂ := ⟨τ, ψ⟩ :: Θ) h0 hok hW (by omega)
        (fun σ' hσ => ⟨⟨rfl, Seq.at_cons_ne (Ne.symm hσ)⟩, ⟨rfl, Seq.at_cons_ne (Ne.symm hσ)⟩⟩)
        ?_ (ih₁ hok hW d (inv_ext (τ := τ) hi hr (by omega) [] [⟨τ, φ⟩] (by simp)))
        (ih₂ hok hW d (inv_ext (τ := τ) hi hr (by omega) [] [⟨τ, ψ⟩] (by simp)))
      rw [Seq.at_cons_self, Seq.at_cons_self]
      refine or_cases (chain (conj_elim (lk List.mem_cons_self) _ (in_content_r h))
        (not_and_or List.mem_cons_self)) ?_ ?_
      · exact orl _ (conj_add (E := [φ.neg]) fun c hc => by
          simp only [List.map_cons, List.mem_append, List.mem_cons] at hc ⊢
          tauto)
      · exact orr _ (conj_add (E := [ψ.neg]) fun c hc => by
          simp only [List.map_cons, List.mem_append, List.mem_cons] at hc ⊢
          tauto)
  | @orL n D Δ Θ τ φ ψ h _ _ ih₁ ih₂ =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.left _ h id
      refine same_hole2 (τ := τ) (Δ₁ := ⟨τ, φ⟩ :: Δ) (Δ₂ := ⟨τ, ψ⟩ :: Δ) h0 hok hW (by omega)
        (fun σ' hσ => ⟨⟨Seq.at_cons_ne (Ne.symm hσ), rfl⟩, ⟨Seq.at_cons_ne (Ne.symm hσ), rfl⟩⟩)
        ?_ (ih₁ hok hW d (inv_ext (τ := τ) hi hr (by omega) [⟨τ, φ⟩] [] (by simp)))
        (ih₂ hok hW d (inv_ext (τ := τ) hi hr (by omega) [⟨τ, ψ⟩] [] (by simp)))
      rw [Seq.at_cons_self, Seq.at_cons_self]
      refine or_cases (conj_elim (lk List.mem_cons_self) _ (in_content_l h)) ?_ ?_
      · exact orl _ (conj_add (E := [φ]) fun c hc => by
          simp only [List.cons_append, List.mem_append, List.mem_cons] at hc ⊢
          tauto)
      · exact orr _ (conj_add (E := [ψ]) fun c hc => by
          simp only [List.cons_append, List.mem_append, List.mem_cons] at hc ⊢
          tauto)
  | @impL n D Δ Θ τ φ ψ h _ _ ih₁ ih₂ =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.left _ h id
      refine same_hole2 (τ := τ) (Θ₁ := ⟨τ, φ⟩ :: Θ) (Δ₂ := ⟨τ, ψ⟩ :: Δ) h0 hok hW (by omega)
        (fun σ' hσ => ⟨⟨rfl, Seq.at_cons_ne (Ne.symm hσ)⟩, ⟨Seq.at_cons_ne (Ne.symm hσ), rfl⟩⟩)
        ?_ (ih₁ hok hW d (inv_ext (τ := τ) hi hr (by omega) [] [⟨τ, φ⟩] (by simp)))
        (ih₂ hok hW d (inv_ext (τ := τ) hi hr (by omega) [⟨τ, ψ⟩] [] (by simp)))
      rw [Seq.at_cons_self, Seq.at_cons_self]
      refine or_cases (chain (conj_elim (lk List.mem_cons_self) _ (in_content_l h))
        (imp_or List.mem_cons_self)) ?_ ?_
      · exact orl _ (conj_add (E := [φ.neg]) fun c hc => by
          simp only [List.map_cons, List.mem_append, List.mem_cons] at hc ⊢
          tauto)
      · exact orr _ (conj_add (E := [ψ]) fun c hc => by
          simp only [List.cons_append, List.mem_append, List.mem_cons] at hc ⊢
          tauto)
  | @orR n D Δ Θ τ φ ψ h _ ih =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.right _ h
      refine same_hole (τ := τ) (Θ' := ⟨τ, φ⟩ :: ⟨τ, ψ⟩ :: Θ) h0 hok hW (by omega)
        (fun σ' hσ => ⟨rfl, by rw [Seq.at_cons_ne (Ne.symm hσ), Seq.at_cons_ne (Ne.symm hσ)]⟩)
        (fun f χ hχ => ?_)
        (ih hok hW d (inv_ext (τ := τ) hi hr (by omega) [] [⟨τ, φ⟩, ⟨τ, ψ⟩] (by simp)))
      rw [Seq.at_cons_self, Seq.at_cons_self] at hχ
      simp only [List.map_cons, List.mem_append, List.mem_cons] at hχ
      rcases hχ with hχ | rfl | rfl | hχ
      · exact of_tr (List.mem_append_left _ hχ)
      · exact chain (of_tr (in_content_r h))
          (lam (contra (List.mem_cons_of_mem _ List.mem_cons_self) (orl _ (lk List.mem_cons_self))))
      · exact chain (of_tr (in_content_r h))
          (lam (contra (List.mem_cons_of_mem _ List.mem_cons_self) (orr _ (lk List.mem_cons_self))))
      · exact of_tr (List.mem_append_right _ hχ)
  | @impR n D Δ Θ τ φ ψ h _ ih =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.right _ h
      refine same_hole (τ := τ) (Δ' := ⟨τ, φ⟩ :: Δ) (Θ' := ⟨τ, ψ⟩ :: Θ) h0 hok hW (by omega)
        (fun σ' hσ => ⟨Seq.at_cons_ne (Ne.symm hσ), Seq.at_cons_ne (Ne.symm hσ)⟩)
        (fun f χ hχ => ?_)
        (ih hok hW d (inv_ext (τ := τ) hi hr (by omega) [⟨τ, φ⟩] [⟨τ, ψ⟩] (by simp)))
      rw [Seq.at_cons_self, Seq.at_cons_self] at hχ
      simp only [List.map_cons, List.cons_append, List.mem_append, List.mem_cons] at hχ
      rcases hχ with rfl | hχ | rfl | hχ
      · exact chain (of_tr (in_content_r h)) (byContra (contra
          (List.mem_cons_of_mem _ List.mem_cons_self)
          (lam (botE _ (contra (List.mem_cons_of_mem _ List.mem_cons_self)
            (lk List.mem_cons_self))))))
      · exact of_tr (List.mem_append_left _ hχ)
      · exact chain (of_tr (in_content_r h))
          (lam (contra (List.mem_cons_of_mem _ List.mem_cons_self)
            (lam (lk (List.mem_cons_of_mem _ List.mem_cons_self)))))
      · exact of_tr (List.mem_append_right _ hχ)
  | @allL n D Δ Θ τ hs T φ a t h _ ih =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.left _ h id
      haveI : (D.ctxAt Γ₀ τ).NoSlots := ⟨hs⟩
      refine same_hole (τ := τ) h0 hok hW (by omega)
        (fun σ' hσ => ⟨Seq.at_cons_ne (Ne.symm hσ), rfl⟩) (fun f χ hχ => ?_)
        (ih hok hW d (inv_ext (τ := τ) hi hr (by omega) [⟨τ, _⟩] [] (by simp)))
      rw [Seq.at_cons_self] at hχ
      simp only [List.cons_append, List.mem_cons] at hχ
      rcases hχ with rfl | hχ
      · exact (of_tr (in_content_l h)).map (.all_elim T t)
      · exact of_tr hχ
  | @exR n D Δ Θ τ hs T φ a t h _ ih =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.right _ h
      haveI : (D.ctxAt Γ₀ τ).NoSlots := ⟨hs⟩
      refine same_hole (τ := τ) h0 hok hW (by omega)
        (fun σ' hσ => ⟨rfl, Seq.at_cons_ne (Ne.symm hσ)⟩) (fun f χ hχ => ?_)
        (ih hok hW d (inv_ext (τ := τ) hi hr (by omega) [] [⟨τ, _⟩] (by simp)))
      rw [Seq.at_cons_self] at hχ
      simp only [List.map_cons, List.mem_append, List.mem_cons] at hχ
      rcases hχ with hχ | rfl | hχ
      · exact of_tr (List.mem_append_left _ hχ)
      · exact chain (of_tr (in_content_r h))
          (lam (contra (List.mem_cons_of_mem _ List.mem_cons_self)
            ((lk List.mem_cons_self).map (.ex_intro T t))))
      · exact of_tr (List.mem_append_right _ hχ)
  | @ref n D Δ Θ τ t _ ih =>
      intro hok hW d hi
      have q := ih hok hW d (inv_atom (x := ⟨τ, .eq t t⟩) hi trivial)
      by_cases hv : D.Reach τ ∧ τ.length ≤ d
      · refine same_hole (τ := τ) h0 hok hW hv.2
          (fun σ' hσ => ⟨Seq.at_cons_ne (Ne.symm hσ), rfl⟩) (fun f χ hχ => ?_) q
        rw [Seq.at_cons_self] at hχ
        simp only [List.cons_append, List.mem_cons] at hχ
        rcases hχ with rfl | hχ
        · exact ⟨.eq_intro t⟩
        · exact of_tr hχ
      · rw [← Pc_vis (Δ₁ := ⟨τ, .eq t t⟩ :: Δ) (Θ₁ := Θ) fun σ' hr hl =>
          ⟨Seq.at_cons_ne fun e => by subst e; exact hv ⟨hr, hl⟩, rfl⟩]
        exact q
  | @repl n D Δ Θ τ hs P hP t₁ t₂ h₁ h₂ _ ih =>
      intro hok hW d hi
      haveI : (D.ctxAt Γ₀ τ).NoSlots := ⟨hs⟩
      have q := ih hok hW d (inv_atom (x := ⟨τ, WFF.instantiate hs t₂ P⟩) hi hP.instantiate)
      by_cases hv : D.Reach τ ∧ τ.length ≤ d
      · refine same_hole (τ := τ) h0 hok hW hv.2
          (fun σ' hσ => ⟨Seq.at_cons_ne (Ne.symm hσ), rfl⟩) (fun f χ hχ => ?_) q
        rw [Seq.at_cons_self] at hχ
        simp only [List.cons_append, List.mem_cons] at hχ
        rcases hχ with rfl | hχ
        · obtain ⟨p₁⟩ := of_tr (f := f) (in_content_l (Θ := Θ) h₁)
          obtain ⟨p₂⟩ := of_tr (f := f) (in_content_l (Θ := Θ) h₂)
          exact ⟨.eq_elim (φ := P) t₁ t₂ p₁ p₂⟩
        · exact of_tr hχ
      · rw [← Pc_vis (Δ₁ := ⟨τ, WFF.instantiate hs t₂ P⟩ :: Δ) (Θ₁ := Θ) fun σ' hr hl =>
          ⟨Seq.at_cons_ne fun e => by subst e; exact hv ⟨hr, hl⟩, rfl⟩]
        exact q
  | @boxL n D Δ Θ τ k e χ he hle h _ ih =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.left _ h id
      have hrc := Tree.reach_cons hr (by rw [he]; exact Option.some_ne_none _)
      have q := ih hok hW d (inv_ext (τ := k :: τ) hi hrc (by simp only [List.length_cons]; omega)
        [⟨k :: τ, WFF.mono hle χ⟩] [] (by simp))
      have hne : (k :: τ) ≠ τ := fun h' => by have := congrArg List.length h'; simp at this
      refine same_hole' (τ := τ) h0 hok hW (by omega)
        (fun σ' hσ => ⟨Seq.at_cons_ne fun e' => hσ (by subst e'; exact List.suffix_cons k τ), rfl⟩)
        (fun f => ?_) q
      cases f with
      | zero =>
          rw [tr_zero, tr_zero, Seq.at_cons_ne hne]
          exact lk List.mem_cons_self
      | succ f =>
          refine hole_tr (fun φ hφ => ?_) (fun j hj => ?_)
          · rw [Seq.at_cons_ne hne] at hφ
            exact of_tr hφ
          by_cases hjk : j = k
          · subst hjk
            have hp : Provable [tr D Δ Θ (f + 1) τ]
                (pack D (D.ctxAt Γ₀ τ) (j :: τ) (Pc D Δ Θ f (j :: τ))) :=
              conj_elim ((lk List.mem_cons_self).map .and_elim_r) _
                (List.mem_map_of_mem (f := fun k => pack D (D.ctxAt Γ₀ τ) (k :: τ)
                  (Pc D Δ Θ f (k :: τ))) hj)
            have hb : Provable [tr D Δ Θ (f + 1) τ] (WFF.box (Γ := D.ctxAt Γ₀ τ) χ) :=
              of_tr (in_content_l h)
            refine dis (pack_side (χs := [χ]) (A := Pc D Δ Θ f (j :: τ))
              (fun x he' => hW j τ x he') ?_) fun ℓ hℓ => ?_
            · change Provable (closeN _ _ (tr D Δ Θ f (j :: τ)) :: _)
                (closeN _ _ (tr D (⟨j :: τ, WFF.mono hle χ⟩ :: Δ) Θ f (j :: τ)))
              refine or_cases (closeN_or (Tree.nok h0 hok (j :: τ)) (orl _ ?_))
                (lk List.mem_cons_self) (lk List.mem_cons_self)
              refine tr_add (x := WFF.mono hle χ) (fun σ' hσ => ⟨Seq.at_cons_ne (Ne.symm hσ), rfl⟩)
                (fun φ hφ => ?_) ?_
              · rw [Seq.at_cons_self] at hφ
                simp only [List.cons_append, List.mem_cons] at hφ
                exact hφ
              · have e' : WFF.mono (Tree.nok h0 hok (j :: τ)).le
                    (WFF.mono (Tree.boxIn_le_view (j :: τ) (D.ctxAt Γ₀ τ)) χ) =
                    WFF.mono hle χ := by rw [WFF.mono_mono]
                refine (congrArg (fun y => Provable (tr D Δ Θ f (j :: τ) :: [y])
                  (WFF.mono hle χ)) e').mpr (lk (List.mem_cons_of_mem _ List.mem_cons_self))
            · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
                or_false] at hℓ
              rcases hℓ with rfl | rfl
              · exact hp
              · exact hb
          · rw [Pc_congr fun σ' hσ => ⟨Seq.at_cons_ne fun e' =>
              off_sub (List.suffix_refl _) hjk σ' hσ (by rw [← e']), rfl⟩]
            exact conj_elim ((lk List.mem_cons_self).map .and_elim_r) _
              (List.mem_map_of_mem (f := fun k => pack D (D.ctxAt Γ₀ τ) (k :: τ)
                (Pc D Δ Θ f (k :: τ))) hj)
  | @diaR n D Δ Θ τ k e x hx θ he hf hle h _ ih =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.right _ h
      have hrc := Tree.reach_cons hr (by rw [he]; exact Option.some_ne_none _)
      have q := ih hok hW d (inv_ext (τ := k :: τ) hi hrc (by simp only [List.length_cons]; omega)
        [] [⟨k :: τ, WFF.mono hle θ⟩] (by simp))
      have hne : (k :: τ) ≠ τ := fun h' => by have := congrArg List.length h'; simp at this
      refine same_hole' (τ := τ) h0 hok hW (by omega)
        (fun σ' hσ => ⟨rfl, Seq.at_cons_ne fun e' => hσ (by subst e'; exact List.suffix_cons k τ)⟩)
        (fun f => ?_) q
      cases f with
      | zero =>
          rw [tr_zero, tr_zero, Seq.at_cons_ne hne]
          exact lk List.mem_cons_self
      | succ f =>
          refine hole_tr (fun φ hφ => ?_) (fun j hj => ?_)
          · rw [Seq.at_cons_ne hne] at hφ
            exact of_tr hφ
          by_cases hjk : j = k
          · subst hjk
            by_cases hed : e = .dia x
            · subst hed
              have hp : Provable [tr D Δ Θ (f + 1) τ]
                  (pack D (D.ctxAt Γ₀ τ) (j :: τ) (Pc D Δ Θ f (j :: τ))) :=
                conj_elim ((lk List.mem_cons_self).map .and_elim_r) _
                  (List.mem_map_of_mem (f := fun k => pack D (D.ctxAt Γ₀ τ) (k :: τ)
                    (Pc D Δ Θ f (k :: τ))) hj)
              have hb : Provable [tr D Δ Θ (f + 1) τ] (WFF.boxx x hx θ.neg) :=
                dis (boxx_neg x hx (L := [(WFF.dia x hx θ).neg]) List.mem_cons_self)
                  fun ℓ hℓ => by
                    rw [List.mem_singleton.mp hℓ]
                    exact of_tr (in_content_r h)
              refine dis (pack_diaside he hx (θs := [θ.neg]) (A := Pc D Δ Θ f (j :: τ)) ?_)
                fun ℓ hℓ => ?_
              · change Provable (closeN _ _ (tr D Δ Θ f (j :: τ)) :: _)
                  (closeN _ _ (tr D Δ (⟨j :: τ, WFF.mono hle θ⟩ :: Θ) f (j :: τ)))
                refine or_cases (closeN_or (Tree.nok h0 hok (j :: τ)) (orl _ ?_))
                  (lk List.mem_cons_self) (lk List.mem_cons_self)
                refine tr_add (x := (WFF.mono hle θ).neg)
                  (fun σ' hσ => ⟨rfl, Seq.at_cons_ne (Ne.symm hσ)⟩) (fun φ hφ => ?_) ?_
                · rw [Seq.at_cons_self] at hφ
                  simp only [List.map_cons, List.mem_append, List.mem_cons] at hφ ⊢
                  tauto
                · have e' : WFF.mono (Tree.nok h0 hok (j :: τ)).le
                      (WFF.mono (Ctx.le_of_eq (Tree.view_dia he).symm) θ.neg) =
                      (WFF.mono hle θ).neg := by rw [WFF.mono_mono]; rfl
                  refine (congrArg (fun y => Provable (tr D Δ Θ f (j :: τ) :: [y])
                    (WFF.mono hle θ).neg) e').mpr (lk (List.mem_cons_of_mem _ List.mem_cons_self))
              · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
                  or_false] at hℓ
                rcases hℓ with rfl | rfl
                · exact hp
                · exact hb
            · have ho : (D.ctxAt Γ₀ (j :: τ)).Opened .arrow x := by
                rcases hf with hc | ⟨x', hx', ho⟩
                · cases e with
                  | box => exact hc.elim
                  | dia z =>
                      change x = z at hc
                      subst hc
                      exact absurd rfl hed
                · cases hx'
                  exact ho
              have hO := (Tree.wit_child_opt ho.choose_spec.1).1
              have hp : Provable [tr D Δ Θ (f + 1) τ]
                  (pack D (D.ctxAt Γ₀ τ) (j :: τ) (Pc D Δ Θ f (j :: τ))) :=
                conj_elim ((lk List.mem_cons_self).map .and_elim_r) _
                  (List.mem_map_of_mem (f := fun k => pack D (D.ctxAt Γ₀ τ) (k :: τ)
                    (Pc D Δ Θ f (k :: τ))) hj)
              have hb : Provable [tr D Δ Θ (f + 1) τ]
                  (WFF.box (Γ := D.ctxAt Γ₀ τ) (WFF.fold hO x hx θ).neg) :=
                dis (box_fold_neg hO x hx (H := [(WFF.dia x hx θ).neg]) List.mem_cons_self)
                  fun ℓ hℓ => by
                    rw [List.mem_singleton.mp hℓ]
                    exact of_tr (in_content_r h)
              refine dis (pack_side (χs := [(WFF.fold hO x hx θ).neg]) (A := Pc D Δ Θ f (j :: τ))
                (fun x' he' => hW j τ x' he') ?_) fun ℓ hℓ => ?_
              · change Provable (closeN _ _ (tr D Δ Θ f (j :: τ)) :: _)
                  (closeN _ _ (tr D Δ (⟨j :: τ, WFF.mono hle θ⟩ :: Θ) f (j :: τ)))
                refine or_cases (closeN_or (Tree.nok h0 hok (j :: τ)) (orl _ ?_))
                  (lk List.mem_cons_self) (lk List.mem_cons_self)
                refine tr_add (x := (WFF.mono hle θ).neg)
                  (fun σ' hσ => ⟨rfl, Seq.at_cons_ne (Ne.symm hσ)⟩) (fun φ hφ => ?_) ?_
                · rw [Seq.at_cons_self] at hφ
                  simp only [List.map_cons, List.mem_append, List.mem_cons] at hφ ⊢
                  tauto
                · have e' : WFF.mono (Tree.nok h0 hok (j :: τ)).le
                      (WFF.mono (Tree.boxIn_le_view (j :: τ) (D.ctxAt Γ₀ τ))
                        (WFF.fold hO x hx θ).neg) =
                      (WFF.mono (Tree.boxIn_le_child hok j τ) (WFF.fold hO x hx θ)).neg := by
                    rw [WFF.mono_mono]; rfl
                  refine (congrArg (fun y => Provable (tr D Δ Θ f (j :: τ) :: [y])
                    (WFF.mono hle θ).neg) e').mpr ?_
                  refine lam (contra (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    List.mem_cons_self)) ?_)
                  have r := Proof.opt_reopen hO .arrow x ho (Proof.lookup (Δ := WFF.mono hle θ ::
                    tr D Δ Θ f (j :: τ) ::
                      [(WFF.mono (Tree.boxIn_le_child hok j τ) (WFF.fold hO x hx θ)).neg])
                    List.mem_cons_self)
                  refine (congrArg (Provable _) ?_).mp ⟨r⟩
                  change WFF.optx hO .arrow x _ (WFF.mono (Ctx.le_optInK _ .arrow x)
                    (WFF.mono hle θ)) = WFF.optx hO .arrow x _
                      (WFF.mono ((Tree.boxIn_le_child hok j τ).optInK .arrow x) (WFF.mono _ θ))
                  rw [WFF.mono_mono, WFF.mono_mono]
              · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
                  or_false] at hℓ
                rcases hℓ with rfl | rfl
                · exact hp
                · exact hb
          · rw [Pc_congr fun σ' hσ => ⟨rfl, Seq.at_cons_ne fun e' =>
              off_sub (List.suffix_refl _) hjk σ' hσ (by rw [← e'])⟩]
            exact conj_elim ((lk List.mem_cons_self).map .and_elim_r) _
              (List.mem_map_of_mem (f := fun k => pack D (D.ctxAt Γ₀ τ) (k :: τ)
                (Pc D Δ Θ f (k :: τ))) hj)
  | @reopenR n D Δ Θ hO τ κ y hy χ h _ ih =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.right _ h
      refine same_hole (τ := τ) (Θ' := ⟨τ, χ⟩ :: Θ) h0 hok hW (by omega)
        (fun σ' hσ => ⟨rfl, by rw [Seq.at_cons_ne (Ne.symm hσ)]⟩)
        (fun f χ' hχ => ?_)
        (ih hok hW d (inv_ext (τ := τ) hi hr (by omega) [] [⟨τ, χ⟩] (by simp)))
      rw [Seq.at_cons_self] at hχ
      simp only [List.map_cons, List.mem_append, List.mem_cons] at hχ
      rcases hχ with hχ | rfl | hχ
      · exact of_tr (List.mem_append_left _ hχ)
      · exact chain (of_tr (in_content_r h))
          (lam (contra (List.mem_cons_of_mem _ List.mem_cons_self)
            ⟨Proof.opt_reopen hO κ y hy (Proof.lookup List.mem_cons_self)⟩))
      · exact of_tr (List.mem_append_right _ hχ)
  | @foldR n D Δ Θ hO τ k e x hx θ he hle h _ ih =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.right _ h
      have hrc := Tree.reach_cons hr (by rw [he]; exact Option.some_ne_none _)
      have q := ih hok hW d (inv_ext (τ := k :: τ) hi hrc (by simp only [List.length_cons]; omega)
        [] [⟨k :: τ, WFF.mono hle (WFF.fold hO x hx θ)⟩] (by simp))
      have hne : (k :: τ) ≠ τ := fun h' => by have := congrArg List.length h'; simp at this
      refine same_hole' (τ := τ) h0 hok hW (by omega)
        (fun σ' hσ => ⟨rfl, Seq.at_cons_ne fun e' => hσ (by subst e'; exact List.suffix_cons k τ)⟩)
        (fun f => ?_) q
      cases f with
      | zero =>
          rw [tr_zero, tr_zero, Seq.at_cons_ne hne]
          exact lk List.mem_cons_self
      | succ f =>
          refine hole_tr (fun φ hφ => ?_) (fun j hj => ?_)
          · rw [Seq.at_cons_ne hne] at hφ
            exact of_tr hφ
          by_cases hjk : j = k
          · subst hjk
            have hp : Provable [tr D Δ Θ (f + 1) τ]
                (pack D (D.ctxAt Γ₀ τ) (j :: τ) (Pc D Δ Θ f (j :: τ))) :=
              conj_elim ((lk List.mem_cons_self).map .and_elim_r) _
                (List.mem_map_of_mem (f := fun k => pack D (D.ctxAt Γ₀ τ) (k :: τ)
                  (Pc D Δ Θ f (k :: τ))) hj)
            have hb : Provable [tr D Δ Θ (f + 1) τ]
                (WFF.box (Γ := D.ctxAt Γ₀ τ) (WFF.fold hO x hx θ).neg) :=
              dis (box_fold_neg hO x hx (H := [(WFF.dia x hx θ).neg]) List.mem_cons_self)
                fun ℓ hℓ => by
                  rw [List.mem_singleton.mp hℓ]
                  exact of_tr (in_content_r h)
            refine dis (pack_side (χs := [(WFF.fold hO x hx θ).neg]) (A := Pc D Δ Θ f (j :: τ))
              (fun x' he' => hW j τ x' he') ?_) fun ℓ hℓ => ?_
            · change Provable (closeN _ _ (tr D Δ Θ f (j :: τ)) :: _)
                (closeN _ _ (tr D Δ (⟨j :: τ, WFF.mono hle (WFF.fold hO x hx θ)⟩ :: Θ) f (j :: τ)))
              refine or_cases (closeN_or (Tree.nok h0 hok (j :: τ)) (orl _ ?_))
                (lk List.mem_cons_self) (lk List.mem_cons_self)
              refine tr_add (x := (WFF.mono hle (WFF.fold hO x hx θ)).neg)
                (fun σ' hσ => ⟨rfl, Seq.at_cons_ne (Ne.symm hσ)⟩) (fun φ hφ => ?_) ?_
              · rw [Seq.at_cons_self] at hφ
                simp only [List.map_cons, List.mem_append, List.mem_cons] at hφ ⊢
                tauto
              · have e' : WFF.mono (Tree.nok h0 hok (j :: τ)).le
                    (WFF.mono (Tree.boxIn_le_view (j :: τ) (D.ctxAt Γ₀ τ))
                      (WFF.fold hO x hx θ).neg) =
                    (WFF.mono hle (WFF.fold hO x hx θ)).neg := by rw [WFF.mono_mono]; rfl
                refine (congrArg (fun y => Provable (tr D Δ Θ f (j :: τ) :: [y])
                  (WFF.mono hle (WFF.fold hO x hx θ)).neg) e').mpr
                  (lk (List.mem_cons_of_mem _ List.mem_cons_self))
            · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
                or_false] at hℓ
              rcases hℓ with rfl | rfl
              · exact hp
              · exact hb
          · rw [Pc_congr fun σ' hσ => ⟨rfl, Seq.at_cons_ne fun e' =>
              off_sub (List.suffix_refl _) hjk σ' hσ (by rw [← e'])⟩]
            exact conj_elim ((lk List.mem_cons_self).map .and_elim_r) _
              (List.mem_map_of_mem (f := fun k => pack D (D.ctxAt Γ₀ τ) (k :: τ)
                (Pc D Δ Θ f (k :: τ))) hj)
  | @optL n D Δ Θ hO τ κ y hy ψ hle h _ ih =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.left _ h id
      obtain ⟨X, hX⟩ := id hy
      have hk := Tree.ctxAt_addOpen (D := D) (Γ₀ := Γ₀) τ κ y
      have hok' := hok.addOpen hO hX
      have q := ih hok' (hW.addOpen τ κ y) d (inv_grow hk hi (fun _ h => h) (τ := τ) hr
        (by omega) [⟨τ, WFF.mono hle ψ⟩] [] (by simp))
      have ho : (D.addOpen τ κ y).opensAt τ = (κ, y) :: D.opensAt τ := by
        rw [Tree.opensAt_addOpen, if_pos rfl]
      have hWe : ((Vw (D.addOpen τ κ y) Γ₀ τ).inserts (D.birthsAt τ)).optInsK (D.opensAt τ) =
          D.ctxAt Γ₀ τ := by rw [vw_open_eq, ← ctxAt_eq_vw]
      have hA : (D.ctxAt Γ₀ τ).Le (((Vw (D.addOpen τ κ y) Γ₀ τ).inserts (D.birthsAt τ)).optInsK
          (D.opensAt τ)) := Ctx.le_of_eq hWe.symm
      have hy' : ∃ X, (((Vw (D.addOpen τ κ y) Γ₀ τ).inserts (D.birthsAt τ)).optInsK
          (D.opensAt τ)).witK κ y = some X := ⟨X, hA.witK hX⟩
      have e₀ : (D.addOpen τ κ y).ctxAt Γ₀ τ = (((Vw (D.addOpen τ κ y) Γ₀ τ).inserts
          (D.birthsAt τ)).optInsK (D.opensAt τ)).optInK κ y := by
        rw [Tree.ctxAt_addOpen_self, hWe]
      have hc := claim_path (Δ := Δ) (Θ := Θ) (d := d) (hk := hk) (hV := vw_le_addOpen τ κ y)
        h0 hok hok' hW τ (by omega)
        (fun σ' hσ => ag_open [⟨τ, WFF.mono hle ψ⟩] [] (by simp)
          fun e => hσ (e ▸ List.suffix_refl _))
        (claim_of_tr_open h0 hok hok' rfl ho hO hy' (Ctx.le_of_eq e₀) hA (by
          have hpos := of_mono hA (f := d - τ.length)
            (H := [WFF.mono hA (tr D Δ Θ (d - τ.length) τ)]) List.mem_cons_self
            (in_content_l (Θ := Θ) h)
          have loc : Provable [WFF.mono hle ψ, WFF.mono (hk τ) (tr D Δ Θ (d - τ.length) τ)]
              (tr (D.addOpen τ κ y) ([⟨τ, WFF.mono hle ψ⟩] ++ Seq.mono hk Δ)
                ([] ++ Seq.mono hk Θ) (d - τ.length) τ) := by
            refine hole_grow (hk := hk) (hV := vw_le_addOpen τ κ y) hW
              (List.mem_cons_of_mem _ List.mem_cons_self) rfl (fun _ => rfl)
              (fun f' j _ _ => claim_sub h0 hok hok' hW f' (j :: τ) fun σ' hσ =>
                ag_open [⟨τ, WFF.mono hle ψ⟩] [] (by simp) (not_sub_child hσ))
              (fun φ' hφ => ?_)
            rw [List.singleton_append, Seq.at_cons_self, Seq.at_mono, List.nil_append, Seq.at_mono,
              List.cons_append, List.mem_cons, List.mem_append] at hφ
            rcases hφ with rfl | hφ | hφ
            · exact lk List.mem_cons_self
            · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hφ
              exact of_content (hk := hk) (List.mem_cons_of_mem _ List.mem_cons_self)
                (List.mem_append_left _ hc)
            · obtain ⟨y', hy'', rfl⟩ := List.mem_map.mp hφ
              obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy''
              exact of_content (hk := hk) (List.mem_cons_of_mem _ List.mem_cons_self)
                (List.mem_append_right _ (List.mem_map_of_mem hc))
          have q₂ := prov_cast e₀ loc
          rw [List.map_cons, List.map_cons, List.map_nil, WFF.mono_mono, WFF.mono_mono] at q₂
          refine chain hpos (sub (by lsub) (opt_mono hO κ y hy'
            (H := [WFF.mono hA (tr D Δ Θ (d - τ.length) τ)]) ?_))
          rw [List.map_cons, List.map_nil, WFF.mono_mono]
          exact q₂))
      unfold Claim at hc
      rw [WFF.mono_refl] at hc
      exact chain hc (sub (by lsub) q)
  | @allR n D Δ Θ τ hs v T hv φ hle h _ ih =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.right _ h
      have hk := Tree.ctxAt_addBirth hv τ T
      have hok' := hok.addBirth hv τ T
      have q := ih hok' (hW.addBirth hv τ T) d (inv_grow hk hi (fun _ h => h) (τ := τ) hr
        (by omega) [] [⟨τ, WFF.mono hle φ⟩] (by simp))
      have hb : (D.addBirth τ (.free v) T).birthsAt τ = (.free v, T) :: D.birthsAt τ := by
        rw [Tree.birthsAt_addBirth, if_pos rfl]
      have hWe := vw_birth_eq (Γ₀ := Γ₀) (D := D) (v := v) (T := T) τ
      have hWe' : ((Vw (D.addBirth τ (.free v) T) Γ₀ τ).inserts (D.birthsAt τ)).optInsK
          (D.opensAt τ) = D.ctxAt Γ₀ τ := by rw [hWe, Tree.ctxAt_eq_pre]
      have hbO : ((Vw (D.addBirth τ (.free v) T) Γ₀ τ).inserts (D.birthsAt τ)).OptsEff
          (D.opensAt τ) := by rw [hWe]; exact hok.eff τ
      have hfr : (((Vw (D.addBirth τ (.free v) T) Γ₀ τ).inserts (D.birthsAt τ)).optInsK
          (D.opensAt τ)).RootFresh (.free v) := by rw [hWe']; exact hv.at τ
      have hfrP := Ctx.RootFresh.of_le (Ctx.le_optInsK _ _) hfr
      have hsW : (((Vw (D.addBirth τ (.free v) T) Γ₀ τ).inserts (D.birthsAt τ)).optInsK
          (D.opensAt τ)).SlotsFrom 0 := by rw [hWe']; exact hs
      have hsP : ((Vw (D.addBirth τ (.free v) T) Γ₀ τ).inserts (D.birthsAt τ)).SlotsFrom 0 :=
        hsW.of_le (Ctx.le_optInsK _ _)
      haveI : (((Vw (D.addBirth τ (.free v) T) Γ₀ τ).inserts (D.birthsAt τ)).optInsK
          (D.opensAt τ)).NoSlots := ⟨hsW⟩
      have e₀ : (D.addBirth τ (.free v) T).ctxAt Γ₀ τ =
          (((Vw (D.addBirth τ (.free v) T) Γ₀ τ).inserts (D.birthsAt τ)).optInsK
            (D.opensAt τ)).insert (.free v) T := by
        rw [ctxAt_eq_vw (D.addBirth τ (.free v) T) τ, hb]
        exact (Ctx.insert_optInsK_eq hfrP T hbO).symm
      have hA : (D.ctxAt Γ₀ τ).Le (((Vw (D.addBirth τ (.free v) T) Γ₀ τ).inserts
          (D.birthsAt τ)).optInsK (D.opensAt τ)) := Ctx.le_of_eq hWe'.symm
      have hc := claim_path (Δ := Δ) (Θ := Θ) (d := d) (hk := hk) (hV := vw_le_addBirth hv τ T)
        h0 hok hok' hW τ (by omega)
        (fun σ' hσ => ag_birth hv [] [⟨τ, WFF.mono hle φ⟩] (by simp)
          fun e => hσ (e ▸ List.suffix_refl _))
        (claim_of_tr_cons h0 hok hok' hb rfl hbO hfr hsP (Ctx.le_of_eq e₀) hA (by
          have hneg := of_mono hA (f := d - τ.length)
            (H := [WFF.mono hA (tr D Δ Θ (d - τ.length) τ)]) List.mem_cons_self
            (in_content_r (Δ := Δ) h)
          have e₁ : WFF.mono hA (WFF.all T (WFF.bindFree v (hv.at τ) hs T φ)).neg =
              (WFF.all T (WFF.bindFree v hfr hsW T (WFF.mono (hA.insert (.free v) T) φ))).neg := by
            change WFF.imp (WFF.all T (WFF.mono (hA.insert (.bnd 0) T) _)) .bot = _
            rw [WFF.mono_bindFree hA (hv.at τ) hfr hs hsW T φ]
          rw [e₁] at hneg
          have hex := chain hneg (not_all hfr T List.mem_cons_self)
          have loc : Provable [(WFF.mono hle φ).neg, WFF.mono (hk τ) (tr D Δ Θ (d - τ.length) τ)]
              (tr (D.addBirth τ (.free v) T) ([] ++ Seq.mono hk Δ)
                ([⟨τ, WFF.mono hle φ⟩] ++ Seq.mono hk Θ) (d - τ.length) τ) := by
            refine hole_grow (hk := hk) (hV := vw_le_addBirth hv τ T) hW
              (List.mem_cons_of_mem _ List.mem_cons_self) rfl (fun _ => rfl)
              (fun f' j _ _ => claim_sub h0 hok hok' hW f' (j :: τ) fun σ' hσ =>
                ag_birth hv [] [⟨τ, WFF.mono hle φ⟩] (by simp) (not_sub_child hσ))
              (fun φ' hφ => ?_)
            rw [List.nil_append, Seq.at_mono, List.singleton_append, Seq.at_cons_self, Seq.at_mono,
              List.map_cons, List.mem_append, List.mem_cons] at hφ
            rcases hφ with hφ | rfl | hφ
            · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hφ
              exact of_content (hk := hk) (List.mem_cons_of_mem _ List.mem_cons_self)
                (List.mem_append_left _ hc)
            · exact lk List.mem_cons_self
            · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hφ
              obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
              exact of_content (hk := hk) (List.mem_cons_of_mem _ List.mem_cons_self)
                (List.mem_append_right _ (List.mem_map_of_mem hc))
          have q₂ := prov_cast e₀ loc
          have e₂ : WFF.mono (Ctx.le_of_eq e₀) (WFF.mono hle φ).neg =
              (WFF.mono (hA.insert (.free v) T) φ).neg := by
            change (WFF.mono _ (WFF.mono hle φ)).neg = _
            rw [WFF.mono_mono]
          have e₃ : WFF.mono (Ctx.le_of_eq e₀) (WFF.mono (hk τ) (tr D Δ Θ (d - τ.length) τ)) =
              WFF.weaken hfr.root T (WFF.mono hA (tr D Δ Θ (d - τ.length) τ)) := by
            unfold WFF.weaken
            rw [WFF.mono_mono, WFF.mono_mono]
          rw [List.map_cons, List.map_cons, List.map_nil, e₂, e₃] at q₂
          exact or_cases (chain hex (ex_or hfr T
            (H := [WFF.mono hA (tr D Δ Θ (d - τ.length) τ)]) (orl _ q₂)))
            (lk List.mem_cons_self) (lk List.mem_cons_self)))
      unfold Claim at hc
      rw [WFF.mono_refl] at hc
      exact chain hc (sub (by lsub) q)
  | @exL n D Δ Θ τ hs v T hv φ hle h _ ih =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.left _ h id
      have hk := Tree.ctxAt_addBirth hv τ T
      have hok' := hok.addBirth hv τ T
      have q := ih hok' (hW.addBirth hv τ T) d (inv_grow hk hi (fun _ h => h) (τ := τ) hr
        (by omega) [⟨τ, WFF.mono hle φ⟩] [] (by simp))
      have hb : (D.addBirth τ (.free v) T).birthsAt τ = (.free v, T) :: D.birthsAt τ := by
        rw [Tree.birthsAt_addBirth, if_pos rfl]
      have hWe := vw_birth_eq (Γ₀ := Γ₀) (D := D) (v := v) (T := T) τ
      have hWe' : ((Vw (D.addBirth τ (.free v) T) Γ₀ τ).inserts (D.birthsAt τ)).optInsK
          (D.opensAt τ) = D.ctxAt Γ₀ τ := by rw [hWe, Tree.ctxAt_eq_pre]
      have hbO : ((Vw (D.addBirth τ (.free v) T) Γ₀ τ).inserts (D.birthsAt τ)).OptsEff
          (D.opensAt τ) := by rw [hWe]; exact hok.eff τ
      have hfr : (((Vw (D.addBirth τ (.free v) T) Γ₀ τ).inserts (D.birthsAt τ)).optInsK
          (D.opensAt τ)).RootFresh (.free v) := by rw [hWe']; exact hv.at τ
      have hfrP := Ctx.RootFresh.of_le (Ctx.le_optInsK _ _) hfr
      have hsW : (((Vw (D.addBirth τ (.free v) T) Γ₀ τ).inserts (D.birthsAt τ)).optInsK
          (D.opensAt τ)).SlotsFrom 0 := by rw [hWe']; exact hs
      have hsP : ((Vw (D.addBirth τ (.free v) T) Γ₀ τ).inserts (D.birthsAt τ)).SlotsFrom 0 :=
        hsW.of_le (Ctx.le_optInsK _ _)
      haveI : (((Vw (D.addBirth τ (.free v) T) Γ₀ τ).inserts (D.birthsAt τ)).optInsK
          (D.opensAt τ)).NoSlots := ⟨hsW⟩
      have e₀ : (D.addBirth τ (.free v) T).ctxAt Γ₀ τ =
          (((Vw (D.addBirth τ (.free v) T) Γ₀ τ).inserts (D.birthsAt τ)).optInsK
            (D.opensAt τ)).insert (.free v) T := by
        rw [ctxAt_eq_vw (D.addBirth τ (.free v) T) τ, hb]
        exact (Ctx.insert_optInsK_eq hfrP T hbO).symm
      have hA : (D.ctxAt Γ₀ τ).Le (((Vw (D.addBirth τ (.free v) T) Γ₀ τ).inserts
          (D.birthsAt τ)).optInsK (D.opensAt τ)) := Ctx.le_of_eq hWe'.symm
      have hc := claim_path (Δ := Δ) (Θ := Θ) (d := d) (hk := hk) (hV := vw_le_addBirth hv τ T)
        h0 hok hok' hW τ (by omega)
        (fun σ' hσ => ag_birth hv [⟨τ, WFF.mono hle φ⟩] [] (by simp)
          fun e => hσ (e ▸ List.suffix_refl _))
        (claim_of_tr_cons h0 hok hok' hb rfl hbO hfr hsP (Ctx.le_of_eq e₀) hA (by
          have hpos := of_mono hA (f := d - τ.length)
            (H := [WFF.mono hA (tr D Δ Θ (d - τ.length) τ)]) List.mem_cons_self
            (in_content_l (Θ := Θ) h)
          have e₁ : WFF.mono hA (WFF.ex T (WFF.bindFree v (hv.at τ) hs T φ)) =
              WFF.ex T (WFF.bindFree v hfr hsW T (WFF.mono (hA.insert (.free v) T) φ)) := by
            change WFF.ex T (WFF.mono (hA.insert (.bnd 0) T) _) = _
            rw [WFF.mono_bindFree hA (hv.at τ) hfr hs hsW T φ]
          rw [e₁] at hpos
          have loc : Provable [WFF.mono hle φ, WFF.mono (hk τ) (tr D Δ Θ (d - τ.length) τ)]
              (tr (D.addBirth τ (.free v) T) ([⟨τ, WFF.mono hle φ⟩] ++ Seq.mono hk Δ)
                ([] ++ Seq.mono hk Θ) (d - τ.length) τ) := by
            refine hole_grow (hk := hk) (hV := vw_le_addBirth hv τ T) hW
              (List.mem_cons_of_mem _ List.mem_cons_self) rfl (fun _ => rfl)
              (fun f' j _ _ => claim_sub h0 hok hok' hW f' (j :: τ) fun σ' hσ =>
                ag_birth hv [⟨τ, WFF.mono hle φ⟩] [] (by simp) (not_sub_child hσ))
              (fun φ' hφ => ?_)
            rw [List.singleton_append, Seq.at_cons_self, Seq.at_mono, List.nil_append, Seq.at_mono,
              List.cons_append, List.mem_cons, List.mem_append] at hφ
            rcases hφ with rfl | hφ | hφ
            · exact lk List.mem_cons_self
            · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hφ
              exact of_content (hk := hk) (List.mem_cons_of_mem _ List.mem_cons_self)
                (List.mem_append_left _ hc)
            · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hφ
              obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
              exact of_content (hk := hk) (List.mem_cons_of_mem _ List.mem_cons_self)
                (List.mem_append_right _ (List.mem_map_of_mem hc))
          have q₂ := prov_cast e₀ loc
          have e₂ : WFF.mono (Ctx.le_of_eq e₀) (WFF.mono hle φ) =
              WFF.mono (hA.insert (.free v) T) φ := by
            rw [WFF.mono_mono]
          have e₃ : WFF.mono (Ctx.le_of_eq e₀) (WFF.mono (hk τ) (tr D Δ Θ (d - τ.length) τ)) =
              WFF.weaken hfr.root T (WFF.mono hA (tr D Δ Θ (d - τ.length) τ)) := by
            unfold WFF.weaken
            rw [WFF.mono_mono, WFF.mono_mono]
          rw [List.map_cons, List.map_cons, List.map_nil, e₂, e₃] at q₂
          exact or_cases (chain hpos (ex_or hfr T
            (H := [WFF.mono hA (tr D Δ Θ (d - τ.length) τ)]) (orl _ q₂)))
            (lk List.mem_cons_self) (lk List.mem_cons_self)))
      unfold Claim at hc
      rw [WFF.mono_refl] at hc
      exact chain hc (sub (by lsub) q)
  | @boxR n D Δ Θ τ k φ hv hle h _ ih =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.right _ h
      have hc := hv.edge _ (List.suffix_refl _)
      have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hc EdgeKind.box
      have hok' := hok.addEdge hc EdgeKind.box
      have he₀ : (D.addEdge (k :: τ) .box).edge (k :: τ) = some .box := by
        rw [Tree.edge_addEdge, if_pos rfl]
      have hrc : (D.addEdge (k :: τ) .box).Reach (k :: τ) :=
        Tree.reach_cons (reach_addEdge _ hr) (by rw [he₀]; exact Option.some_ne_none _)
      have q := ih hok' (hW.addEdge hc .box fun _ _ _ _ he => by cases he) d
        (inv_grow hk hi (fun _ h => reach_addEdge _ h) (τ := k :: τ) hrc
          (by simp only [List.length_cons]; omega) [] [⟨k :: τ, WFF.mono hle φ⟩] (by simp))
      have hne : (k :: τ) ≠ τ := fun h' => by have := congrArg List.length h'; simp at this
      have hva := vacant_at hv
      have hc' := claim_path (Δ := Δ) (Θ := Θ) (d := d) (hk := hk) (hV := vw_le_addEdge hc .box)
        h0 hok hok' hW τ (by omega)
        (fun σ' hσ => ag_edge hc [] [⟨k :: τ, WFF.mono hle φ⟩] (by simp)
          (fun e => hσ (e ▸ List.suffix_refl _))
          fun e => hσ (by rw [e]; exact List.suffix_cons k τ))
        (claim_of_tr h0 hok hok' rfl rfl (by
          obtain ⟨f', hf⟩ : ∃ f', d - τ.length = f' + 1 := ⟨d - τ.length - 1, by omega⟩
          rw [hf]
          refine hole_tr (fun φ' hφ => ?_) (fun j hj => ?_)
          · rw [List.nil_append, Seq.at_mono, List.singleton_append, Seq.at_cons_ne hne,
              Seq.at_mono, List.mem_append] at hφ
            rcases hφ with hφ | hφ
            · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hφ
              exact of_content (hk := hk) List.mem_cons_self (List.mem_append_left _ hc)
            · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hφ
              obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
              exact of_content (hk := hk) List.mem_cons_self
                (List.mem_append_right _ (List.mem_map_of_mem hc))
          rcases (mem_children_addEdge .box).mp hj with rfl | hj
          · rw [pack_box (Or.inr he₀)]
            have hy := new_child (D' := D.addEdge (j :: τ) .box) (Δ' := [] ++ Seq.mono hk Δ)
              (Θ' := [⟨j :: τ, WFF.mono hle φ⟩] ++ Seq.mono hk Θ) (f := f') hv.birthsAt hv.opensAt
              (fun i => by
                rw [Tree.edge_addEdge, if_neg fun h' => by
                  have := congrArg List.length h'; simp at this]
                exact hv.edge _ (List.suffix_cons i _))
              (y := WFF.mono (Tree.boxIn_le_view (D := D.addEdge (j :: τ) .box) (j :: τ) _)
                (WFF.mono (hk τ).boxIn φ).neg)
              (fun h' φ'' hφ => by
                rw [List.nil_append, Seq.at_mono, hva.1, List.singleton_append, Seq.at_cons_self,
                  Seq.at_mono, hva.2] at hφ
                simp only [List.map_nil, List.nil_append, List.map_cons, List.mem_cons,
                  List.not_mem_nil, or_false] at hφ
                subst hφ
                refine (congrArg (fun z => Provable [z] (WFF.mono hle φ).neg) ?_).mpr
                  (lk List.mem_cons_self)
                change (WFF.mono _ (WFF.mono _ (WFF.mono _ φ))).neg = _
                rw [WFF.mono_mono, WFF.mono_mono])
            have hX := prov_cast (Tree.view_box (Or.inr he₀)) hy
            rw [List.map_cons, List.map_nil, WFF.mono_mono, WFF.mono_refl] at hX
            exact chain (of_content (hk := hk) List.mem_cons_self (in_content_r h))
              (sub (by lsub) (dpk_of_neg hX))
          · have hjk : j ≠ k := fun e => Tree.mem_children.mp hj (e ▸ hc)
            refine pack_of_claim (hV := vw_le_addEdge hc .box) hW hj (by
              rw [Tree.edge_addEdge, if_neg fun h' => hjk (List.cons.inj h').1])
              (claim_sub h0 hok hok' hW _ _ fun σ' hσ => ag_edge hc [] [⟨k :: τ, WFF.mono hle φ⟩]
                (by simp) (not_sub_child hσ)
                fun e => off_sub (List.suffix_refl _) hjk σ' hσ (by rw [e]))
              List.mem_cons_self))
      unfold Claim at hc'
      rw [WFF.mono_refl] at hc'
      exact chain hc' (sub (by lsub) q)
  | @diaL n D Δ Θ τ k x hx ψ hv hle h _ ih =>
      intro hok hW d hi
      obtain ⟨hr, hτ⟩ : D.Reach τ ∧ τ.length + (n + 1) < d := hi.left _ h id
      have hc := hv.edge _ (List.suffix_refl _)
      have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hc (EdgeKind.dia x)
      have hok' := hok.addEdge hc (EdgeKind.dia x)
      have he₀ : (D.addEdge (k :: τ) (.dia x)).edge (k :: τ) = some (.dia x) := by
        rw [Tree.edge_addEdge, if_pos rfl]
      have hrc : (D.addEdge (k :: τ) (.dia x)).Reach (k :: τ) :=
        Tree.reach_cons (reach_addEdge _ hr) (by rw [he₀]; exact Option.some_ne_none _)
      have q := ih hok' (hW.addEdge hc (.dia x) fun j ρ y hj he => by
          cases hj
          cases he
          exact hx) d
        (inv_grow hk hi (fun _ h => reach_addEdge _ h) (τ := k :: τ) hrc
          (by simp only [List.length_cons]; omega) [⟨k :: τ, WFF.mono hle ψ⟩] [] (by simp))
      have hne : (k :: τ) ≠ τ := fun h' => by have := congrArg List.length h'; simp at this
      have hva := vacant_at hv
      have hx' : ∃ X, ((D.addEdge (k :: τ) (.dia x)).ctxAt Γ₀ τ).ref x = some (.VTypeDia X) :=
        hx.imp fun _ hX => (hk τ).ref hX
      have hc' := claim_path (Δ := Δ) (Θ := Θ) (d := d) (hk := hk)
        (hV := vw_le_addEdge hc (.dia x)) h0 hok hok' hW τ (by omega)
        (fun σ' hσ => ag_edge hc [⟨k :: τ, WFF.mono hle ψ⟩] [] (by simp)
          (fun e => hσ (e ▸ List.suffix_refl _))
          fun e => hσ (by rw [e]; exact List.suffix_cons k τ))
        (claim_of_tr h0 hok hok' rfl rfl (by
          obtain ⟨f', hf⟩ : ∃ f', d - τ.length = f' + 1 := ⟨d - τ.length - 1, by omega⟩
          rw [hf]
          refine hole_tr (fun φ' hφ => ?_) (fun j hj => ?_)
          · rw [List.singleton_append, Seq.at_cons_ne hne, Seq.at_mono, List.nil_append,
              Seq.at_mono, List.mem_append] at hφ
            rcases hφ with hφ | hφ
            · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hφ
              exact of_content (hk := hk) List.mem_cons_self (List.mem_append_left _ hc)
            · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hφ
              obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
              exact of_content (hk := hk) List.mem_cons_self
                (List.mem_append_right _ (List.mem_map_of_mem hc))
          rcases (mem_children_addEdge (.dia x)).mp hj with rfl | hj
          · rw [pack_dia he₀ hx']
            have hy := new_child (D' := D.addEdge (j :: τ) (.dia x))
              (Δ' := [⟨j :: τ, WFF.mono hle ψ⟩] ++ Seq.mono hk Δ)
              (Θ' := [] ++ Seq.mono hk Θ) (f := f') hv.birthsAt hv.opensAt
              (fun i => by
                rw [Tree.edge_addEdge, if_neg fun h' => by
                  have := congrArg List.length h'; simp at this]
                exact hv.edge _ (List.suffix_cons i _))
              (y := WFF.mono (Ctx.le_of_eq (Tree.view_dia he₀).symm)
                (WFF.mono ((hk τ).diaIn x) ψ))
              (fun h' φ'' hφ => by
                rw [List.singleton_append, Seq.at_cons_self, Seq.at_mono, hva.1, List.nil_append,
                  Seq.at_mono, hva.2] at hφ
                simp only [List.map_nil, List.append_nil, List.mem_cons, List.not_mem_nil,
                  or_false] at hφ
                subst hφ
                refine (congrArg (fun z => Provable [z] (WFF.mono hle ψ)) ?_).mpr
                  (lk List.mem_cons_self)
                rw [WFF.mono_mono, WFF.mono_mono])
            have hX := prov_cast (Tree.view_dia he₀) hy
            rw [List.map_cons, List.map_nil, WFF.mono_mono, WFF.mono_refl] at hX
            exact chain (of_content (hk := hk) List.mem_cons_self (in_content_l (Θ := Θ) h))
              (sub (by lsub) (dia_mono_of x hx' hX))
          · have hjk : j ≠ k := fun e => Tree.mem_children.mp hj (e ▸ hc)
            refine pack_of_claim (hV := vw_le_addEdge hc (.dia x)) hW hj (by
              rw [Tree.edge_addEdge, if_neg fun h' => hjk (List.cons.inj h').1])
              (claim_sub h0 hok hok' hW _ _ fun σ' hσ => ag_edge hc [⟨k :: τ, WFF.mono hle ψ⟩] []
                (by simp) (not_sub_child hσ)
                fun e => off_sub (List.suffix_refl _) hjk σ' hσ (by rw [e]))
              List.mem_cons_self))
      unfold Claim at hc'
      rw [WFF.mono_refl] at hc'
      exact chain hc' (sub (by lsub) q)
  | @serial n D Δ Θ hD τ k hv _ ih =>
      intro hok hW d hi
      have hc := hv.edge _ (List.suffix_refl _)
      have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hc EdgeKind.box
      have hok' := hok.addEdge hc EdgeKind.box
      have he₀ : (D.addEdge (k :: τ) .box).edge (k :: τ) = some .box := by
        rw [Tree.edge_addEdge, if_pos rfl]
      have q := ih hok' (hW.addEdge hc .box fun _ _ _ _ he => by cases he) d
        (inv_grow0 hk hi fun _ h => reach_addEdge _ h)
      have hne : (k :: τ) ≠ τ := fun h' => by have := congrArg List.length h'; simp at this
      have hva := vacant_at hv
      have hcont : ∀ f, ∀ φ' ∈ Seq.at ([] ++ Seq.mono hk Δ) τ ++
          (Seq.at ([] ++ Seq.mono hk Θ) τ).map WFF.neg,
          Provable [WFF.mono (hk τ) (tr D Δ Θ f τ)] φ' := fun f φ' hφ => by
        rw [List.nil_append, List.nil_append, Seq.at_mono, Seq.at_mono, List.mem_append] at hφ
        rcases hφ with hφ | hφ
        · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hφ
          exact of_content (hk := hk) List.mem_cons_self (List.mem_append_left _ hc)
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hφ
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
          exact of_content (hk := hk) List.mem_cons_self
            (List.mem_append_right _ (List.mem_map_of_mem hc))
      by_cases hτd : τ.length ≤ d
      · have hc' := claim_path (Δ := Δ) (Θ := Θ) (Δ' := [] ++ Seq.mono hk Δ)
          (Θ' := [] ++ Seq.mono hk Θ) (d := d) (hk := hk) (hV := vw_le_addEdge hc .box)
          h0 hok hok' hW τ hτd
          (fun σ' hσ => ag_edge hc [] [] (by simp) (fun e => hσ (e ▸ List.suffix_refl _))
            fun e => hσ (by rw [e]; exact List.suffix_cons k τ))
          (claim_of_tr h0 hok hok' rfl rfl (by
            cases hf : d - τ.length with
            | zero =>
                rw [tr_zero (D.addEdge (k :: τ) .box)]
                exact andI (conj_intro (hcont 0)) ⟨.top_intro⟩
            | succ f' =>
                refine hole_tr (hcont (f' + 1)) fun j hj => ?_
                rcases (mem_children_addEdge .box).mp hj with rfl | hj
                · rw [pack_box (Or.inr he₀)]
                  have hy := new_child (D' := D.addEdge (j :: τ) .box)
                    (Δ' := [] ++ Seq.mono hk Δ) (Θ' := [] ++ Seq.mono hk Θ) (f := f')
                    hv.birthsAt hv.opensAt (fun i => by
                      rw [Tree.edge_addEdge, if_neg fun h' => by
                        have := congrArg List.length h'; simp at this]
                      exact hv.edge _ (List.suffix_cons i _)) (y := .top)
                    (fun h' φ'' hφ => by
                      rw [List.nil_append, List.nil_append, Seq.at_mono, hva.1, Seq.at_mono,
                        hva.2] at hφ
                      simp at hφ)
                  have hX := prov_cast (Tree.view_box (Or.inr he₀)) hy
                  exact dpk_D hD (chain ⟨.top_intro⟩ (sub (by lsub) hX))
                · have hjk : j ≠ k := fun e => Tree.mem_children.mp hj (e ▸ hc)
                  refine pack_of_claim (hV := vw_le_addEdge hc .box) hW hj (by
                    rw [Tree.edge_addEdge, if_neg fun h' => hjk (List.cons.inj h').1])
                    (claim_sub h0 hok hok' hW _ _ fun σ' hσ => ag_edge hc [] [] (by simp)
                      (not_sub_child hσ)
                      fun e => off_sub (List.suffix_refl _) hjk σ' hσ (by rw [e]))
                    List.mem_cons_self))
        unfold Claim at hc'
        rw [WFF.mono_refl] at hc'
        exact chain hc' (sub (by lsub) q)
      · have hs₀ : τ.drop (τ.length - d) <:+ τ := List.drop_suffix _ _
        have hl₀ : (τ.drop (τ.length - d)).length = d := by
          rw [List.length_drop]; omega
        have hne₀ : τ.drop (τ.length - d) ≠ τ := fun e => by
          rw [e] at hl₀; omega
        have hne₁ : τ.drop (τ.length - d) ≠ k :: τ := fun e => by
          have := congrArg List.length e
          simp only [List.length_cons] at this
          omega
        have hc' := claim_path (Δ := Δ) (Θ := Θ) (Δ' := [] ++ Seq.mono hk Δ)
          (Θ' := [] ++ Seq.mono hk Θ) (d := d) (hk := hk) (hV := vw_le_addEdge hc .box)
          h0 hok hok' hW (τ.drop (τ.length - d)) hl₀.le
          (fun σ' hσ => ag_edge hc [] [] (by simp) (fun e => hσ (by rw [e]; exact hs₀))
            fun e => hσ (by rw [e]; exact hs₀.trans (List.suffix_cons k τ)))
          (claim_of_tr h0 hok hok' rfl rfl (by
            rw [show d - (τ.drop (τ.length - d)).length = 0 by omega]
            exact step0 (ag_edge hc [] [] (by simp) hne₀ hne₁)))
        unfold Claim at hc'
        rw [WFF.mono_refl] at hc'
        exact chain hc' (sub (by lsub) q)


theorem mem_at_root {L : List (WFF σ Γ₀ 0)} {φ : WFF σ Γ₀ 0}
    (h : φ ∈ Seq.at (L.map fun ψ => (⟨[], ψ⟩ : LF σ Γ₀ {})) []) : φ ∈ L := by
  obtain ⟨ψ, hψ, he⟩ := List.mem_map.mp (Seq.mem_at.mp h)
  rw [← eq_of_heq (Sigma.mk.inj he).2]
  exact hψ

/-- ⭐**A one-node tree sequent into natural deduction**: `Δ ⇒ Θ` at the root of the empty tree
    gives `Δ, ¬Θ ⊢ ⊥`, as `GK.toND`. -/
theorem toND_root [Γ₀.Presented] {n : ℕ} {Δ Θ : List (WFF σ Γ₀ 0)}
    (p : GKN σ Γ₀ n {} (Δ.map fun φ => ⟨[], φ⟩) (Θ.map fun φ => ⟨[], φ⟩)) :
    Provable (Δ ++ Θ.map WFF.neg) .bot := by
  have hi : Inv n (n + 1) (Δ.map fun φ => (⟨[], φ⟩ : LF σ Γ₀ {}))
      (Θ.map fun φ => (⟨[], φ⟩ : LF σ Γ₀ {})) :=
    ⟨fun p hp => by
      obtain ⟨φ, _, rfl⟩ := List.mem_map.mp hp
      exact ⟨Tree.reach_nil _, by simp⟩,
    fun p hp _ => by
      obtain ⟨φ, _, rfl⟩ := List.mem_map.mp hp
      exact ⟨Tree.reach_nil _, by simp⟩⟩
  have q := toND p GKN.Tree.ok_empty Tree.witOK_empty (n + 1) hi
  refine dis q fun ℓ hℓ => ?_
  rw [List.mem_singleton.mp hℓ]
  change Provable _ (tr {} _ _ (n + 1) [])
  rw [tr_succ]
  refine andI (conj_intro fun φ hφ => ?_) (conj_intro fun z hz => ?_)
  · rcases List.mem_append.mp hφ with hφ | hφ
    · exact lk (List.mem_append_left _ (mem_at_root hφ))
    · obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hφ
      exact lk (List.mem_append_right _ (List.mem_map_of_mem (mem_at_root hψ)))
  · exact absurd hz (by simp [Tree.children])

end GKN

/-- ⭐**ND and cut-free `GKN` prove the same sequents** (K and KD, `Opt` on or off, and KT and
    KDT, over a presented context): `GKN.ofProof` one way, `GKN.toND_root` the other. -/
theorem GKN.provable_iff [ModalSys.GKBase] (hF : ModalSys.Four = false)
    {σ : Signature} {Γ₀ : Ctx}
    [Γ₀.Presented] {Δ : List (WFF σ Γ₀ 0)} {φ : WFF σ Γ₀ 0} :
    Provable Δ φ ↔ ∃ m, GKN σ Γ₀ m {} (Δ.map fun ψ => ⟨[], ψ⟩) [⟨[], φ⟩] := by
  refine ⟨fun ⟨p⟩ => GKN.ofProof hF p, fun ⟨m, d⟩ => ?_⟩
  exact NDP.byContra (NDP.sub (by lsub) (GKN.toND_root (Θ := [φ]) d))

end V12M
