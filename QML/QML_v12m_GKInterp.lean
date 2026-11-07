import QML.QML_v12m_GKToND

/-!
# QML v12m — Craig interpolation for K

⭐`GK.interp`: if a cut-free GK derivation proves `Δ ⇒ Θ` and the sequent is split into
`Δ₁ ; Θ₁ | Δ₂ ; Θ₂`, there is an **interpolant** `χ` with `Δ₁ ⇒ Θ₁, χ` and `χ, Δ₂ ⇒ Θ₂` derivable,
every relation symbol of `χ` occurring on both sides (`Itp`).  Maehara's method, by induction on
the derivation; equality is logical, and free variables and function symbols are not restricted
(both sides share the context).  ⭐`GK.craig`: for ND in K, from `φ ⊢ ψ`, an interpolant.

The cases, with the principal formula in the first part (the second by `Itp.swap`, which turns an
interpolant of the swapped split into its negation):
* axioms: `⊥`, or the atom itself when it crosses the split;
* one-premise rules keep the interpolant; two-premise rules take the disjunction;
* an eigenvariable rule binds the eigenvariable: `∃u χ'`;
* `□R`: the boxed hypotheses split by side; `◇χ'` (`¬□¬χ'`); `◇_xL`: `◇_x χ'`;
* `repl` with `t = s` on the other side: `t = s → χ'` (equality adds no relation symbol).
-/

namespace V12M

variable [ModalSys] {σ : Signature}

/-! ## Relation symbols -/

/-- The relation symbol of an atom. -/
def Rel.sym {Γ : Ctx} : {n : ℕ} → Rel σ Γ n → σ.RelSyms
  | _, .R r => r.1
  | _, .eval ρ _ => Rel.sym ρ

theorem Rel.sym_subst {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) : ∀ {n : ℕ} (ρ : Rel σ Γ n), (Rel.subst ι θ hθ hc ρ).sym = ρ.sym
  | _, .R _ => rfl
  | _, .eval ρ _ => Rel.sym_subst θ hθ hc ρ

theorem Rel.sym_mono {Γ Γ' : Ctx} (h : Γ.Le Γ') :
    ∀ {n : ℕ} (ρ : Rel σ Γ n), (Rel.mono h ρ).sym = ρ.sym
  | _, .R _ => rfl
  | _, .eval ρ _ => Rel.sym_mono h ρ

/-- The relation symbol `r` occurs in a formula (equality is logical). -/
def WFF.Occ (r : σ.RelSyms) : {Γ : Ctx} → {d : ℕ} → WFF σ Γ d → Prop
  | _, _, .atom ρ => ρ.sym = r
  | _, _, .eq _ _ => False
  | _, _, .top => False
  | _, _, .bot => False
  | _, _, .and φ ψ => φ.Occ r ∨ ψ.Occ r
  | _, _, .or φ ψ => φ.Occ r ∨ ψ.Occ r
  | _, _, .imp φ ψ => φ.Occ r ∨ ψ.Occ r
  | _, _, .all _ φ => φ.Occ r
  | _, _, .ex _ φ => φ.Occ r
  | _, _, .box φ => φ.Occ r
  | _, _, .dia _ _ φ => φ.Occ r
  | _, _, .here _ _ _ => False
  | _, _, .back _ _ _ _ => False
  | _, _, .retS _ _ _ Φ => Φ.Occ r
  | _, _, .retxS _ _ _ _ _ Φ => Φ.Occ r
  | _, _, .link _ _ _ Φ => Φ.Occ r
  | _, _, .linkx _ _ _ _ _ Φ => Φ.Occ r

/-- Substitution keeps the relation symbols. -/
theorem WFF.occ_subst (r : σ.RelSyms) : ∀ {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d d' : ℕ}
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom d)
    (hΔ : Δ.SlotsFrom d') (φ : WFF σ Γ d), (WFF.subst ι θ hθ hc hΓ hΔ φ).Occ r ↔ φ.Occ r
  | _, _, _, _, _, θ, hθ, hc, _, _, .atom ρ => by
      change (Rel.subst _ θ hθ hc ρ).sym = r ↔ ρ.sym = r
      rw [Rel.sym_subst]
  | _, _, _, _, _, _, _, _, _, _, .eq _ _ => Iff.rfl
  | _, _, _, _, _, _, _, _, _, _, .top => Iff.rfl
  | _, _, _, _, _, _, _, _, _, _, .bot => Iff.rfl
  | _, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .and φ ψ => by
      simp only [WFF.subst, WFF.Occ]
      rw [WFF.occ_subst r θ hθ hc hΓ hΔ φ, WFF.occ_subst r θ hθ hc hΓ hΔ ψ]
  | _, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .or φ ψ => by
      simp only [WFF.subst, WFF.Occ]
      rw [WFF.occ_subst r θ hθ hc hΓ hΔ φ, WFF.occ_subst r θ hθ hc hΓ hΔ ψ]
  | _, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .imp φ ψ => by
      simp only [WFF.subst, WFF.Occ]
      rw [WFF.occ_subst r θ hθ hc hΓ hΔ φ, WFF.occ_subst r θ hθ hc hΓ hΔ ψ]
  | _, _, _, _, _, _, _, _, _, _, .all _ φ => by
      simp only [WFF.subst, WFF.Occ]; rw [WFF.occ_subst r _ _ _ _ _ φ]
  | _, _, _, _, _, _, _, _, _, _, .ex _ φ => by
      simp only [WFF.subst, WFF.Occ]; rw [WFF.occ_subst r _ _ _ _ _ φ]
  | _, _, _, _, _, _, _, _, _, _, .box φ => by
      simp only [WFF.subst, WFF.Occ]; rw [WFF.occ_subst r _ _ _ _ _ φ]
  | _, _, _, _, _, _, _, _, _, _, .dia _ _ φ => by
      simp only [WFF.subst, WFF.Occ]; rw [WFF.occ_subst r _ _ _ _ _ φ]
  | _, _, _, _, _, _, _, _, _, _, .here _ _ _ => Iff.rfl
  | _, _, _, _, _, _, _, _, _, _, .back _ _ _ _ => Iff.rfl
  | _, _, _, _, _, _, _, _, _, _, .retS _ _ _ Φ => by
      simp only [WFF.subst, WFF.Occ]; rw [WFF.occ_subst r _ _ _ _ _ Φ]
  | _, _, _, _, _, _, _, _, _, _, .retxS _ _ _ _ _ Φ => by
      simp only [WFF.subst, WFF.Occ]; rw [WFF.occ_subst r _ _ _ _ _ Φ]
  | _, _, _, _, _, _, _, _, _, _, .link _ _ _ Φ => by
      simp only [WFF.subst, WFF.Occ]; rw [WFF.occ_subst r _ _ _ _ _ Φ]
  | _, _, _, _, _, _, _, _, _, _, .linkx _ _ _ _ _ Φ => by
      simp only [WFF.subst, WFF.Occ]; rw [WFF.occ_subst r _ _ _ _ _ Φ]

/-- Weakening keeps the relation symbols. -/
theorem WFF.occ_mono (r : σ.RelSyms) : ∀ {Γ Γ' : Ctx} {d : ℕ} (h : Γ.Le Γ') (φ : WFF σ Γ d),
    (WFF.mono h φ).Occ r ↔ φ.Occ r
  | _, _, _, h, .atom ρ => by
      change (Rel.mono h ρ).sym = r ↔ ρ.sym = r
      rw [Rel.sym_mono]
  | _, _, _, _, .eq _ _ => Iff.rfl
  | _, _, _, _, .top => Iff.rfl
  | _, _, _, _, .bot => Iff.rfl
  | _, _, _, h, .and φ ψ => by
      simp only [WFF.mono, WFF.Occ]; rw [WFF.occ_mono r h φ, WFF.occ_mono r h ψ]
  | _, _, _, h, .or φ ψ => by
      simp only [WFF.mono, WFF.Occ]; rw [WFF.occ_mono r h φ, WFF.occ_mono r h ψ]
  | _, _, _, h, .imp φ ψ => by
      simp only [WFF.mono, WFF.Occ]; rw [WFF.occ_mono r h φ, WFF.occ_mono r h ψ]
  | _, _, _, _, .all _ φ => by simp only [WFF.mono, WFF.Occ]; rw [WFF.occ_mono r _ φ]
  | _, _, _, _, .ex _ φ => by simp only [WFF.mono, WFF.Occ]; rw [WFF.occ_mono r _ φ]
  | _, _, _, _, .box φ => by simp only [WFF.mono, WFF.Occ]; rw [WFF.occ_mono r _ φ]
  | _, _, _, _, .dia _ _ φ => by simp only [WFF.mono, WFF.Occ]; rw [WFF.occ_mono r _ φ]
  | _, _, _, _, .here _ _ _ => Iff.rfl
  | _, _, _, _, .back _ _ _ _ => Iff.rfl
  | _, _, _, _, .retS _ _ _ Φ => by simp only [WFF.mono, WFF.Occ]; rw [WFF.occ_mono r _ Φ]
  | _, _, _, _, .retxS _ _ _ _ _ Φ => by simp only [WFF.mono, WFF.Occ]; rw [WFF.occ_mono r _ Φ]
  | _, _, _, _, .link _ _ _ Φ => by simp only [WFF.mono, WFF.Occ]; rw [WFF.occ_mono r _ Φ]
  | _, _, _, _, .linkx _ _ _ _ _ Φ => by simp only [WFF.mono, WFF.Occ]; rw [WFF.occ_mono r _ Φ]

theorem WFF.occ_instantiate (r : σ.RelSyms) {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {T : VarType}
    {a : Ann T} (t : Term σ Γ T a) (φ : WFF σ (Γ.insert (.bnd d) T) (d + 1)) :
    (WFF.instantiate hs t φ).Occ r ↔ φ.Occ r :=
  WFF.occ_subst r _ _ _ _ _ φ

theorem WFF.occ_bindFree (r : σ.RelSyms) {Γ : Ctx} {d : ℕ} (u : ℕ) (hu : Γ.RootFresh (.free u))
    (hs : Γ.SlotsFrom d) (T : VarType) (φ : WFF σ (Γ.insert (.free u) T) d) :
    (WFF.bindFree u hu hs T φ).Occ r ↔ φ.Occ r := by
  unfold WFF.bindFree WFF.renameRoot
  exact WFF.occ_subst r _ _ _ _ _ φ

theorem WFF.occ_box {r : σ.RelSyms} {Γ : Ctx} {d : ℕ} {φ : WFF σ Γ.boxIn d} :
    (WFF.box (Γ := Γ) φ).Occ r ↔ φ.Occ r := Iff.rfl

/-! ## Interpolants -/

/-- The relation symbol `r` occurs in a list. -/
def Lang {Γ : Ctx} (L : List (WFF σ Γ 0)) (r : σ.RelSyms) : Prop := ∃ φ ∈ L, φ.Occ r

/-- One list's symbols among another's. -/
def LangLe {Γ Γ' : Ctx} (L : List (WFF σ Γ 0)) (L' : List (WFF σ Γ' 0)) : Prop :=
  ∀ r, Lang L r → Lang L' r

namespace LangLe

variable {Γ Γ' : Ctx}

theorem sub {L L' : List (WFF σ Γ 0)} (h : L ⊆ L') : LangLe L L' :=
  fun _ ⟨φ, hφ, ho⟩ => ⟨φ, h hφ, ho⟩

theorem cons {a : WFF σ Γ 0} {L : List (WFF σ Γ 0)} {L' : List (WFF σ Γ' 0)}
    (ha : ∀ r, a.Occ r → Lang L' r) (h : LangLe L L') : LangLe (a :: L) L' :=
  fun r ⟨ψ, hψ, ho⟩ => (List.mem_cons.mp hψ).elim (fun e => ha r (e ▸ ho))
    (fun hψ => h r ⟨ψ, hψ, ho⟩)

theorem append {L₁ L₂ : List (WFF σ Γ 0)} {L' : List (WFF σ Γ' 0)} (h₁ : LangLe L₁ L')
    (h₂ : LangLe L₂ L') : LangLe (L₁ ++ L₂) L' :=
  fun r ⟨ψ, hψ, ho⟩ => (List.mem_append.mp hψ).elim (fun hψ => h₁ r ⟨ψ, hψ, ho⟩)
    (fun hψ => h₂ r ⟨ψ, hψ, ho⟩)

theorem map {f : WFF σ Γ' 0 → WFF σ Γ 0} (hf : ∀ φ r, (f φ).Occ r → φ.Occ r)
    {L : List (WFF σ Γ' 0)} {L' : List (WFF σ Γ' 0)} (h : L ⊆ L') : LangLe (L.map f) L' :=
  fun r ⟨ψ, hψ, ho⟩ => by
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hψ
    exact ⟨φ, h hφ, hf φ r ho⟩

end LangLe

theorem Lang.mem {Γ : Ctx} {L : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} {r : σ.RelSyms} (h : φ ∈ L)
    (ho : φ.Occ r) : Lang L r :=
  ⟨φ, h, ho⟩

/-- `χ` interpolates the split `Δ₁ ; Θ₁ | Δ₂ ; Θ₂`. -/
def Itp (Γ : Ctx) (Δ₁ Θ₁ Δ₂ Θ₂ : List (WFF σ Γ 0)) (χ : WFF σ Γ 0) : Prop :=
  (∃ k, GK σ k Γ Δ₁ (χ :: Θ₁)) ∧ (∃ k, GK σ k Γ (χ :: Δ₂) Θ₂) ∧
    ∀ r, χ.Occ r → Lang (Δ₁ ++ Θ₁) r ∧ Lang (Δ₂ ++ Θ₂) r

/-- Every split of the sequent has an interpolant. -/
def Interp (Γ : Ctx) (Δ Θ : List (WFF σ Γ 0)) : Prop :=
  ∀ Δ₁ Δ₂ Θ₁ Θ₂ : List (WFF σ Γ 0), Δ ⊆ Δ₁ ++ Δ₂ → Θ ⊆ Θ₁ ++ Θ₂ →
    ∃ χ, Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ

namespace Itp

variable {Γ : Ctx} {Δ₁ Θ₁ Δ₂ Θ₂ : List (WFF σ Γ 0)}

/-- ⭐Swapping the split negates the interpolant. -/
theorem swap {χ : WFF σ Γ 0} (h : Itp Γ Δ₂ Θ₂ Δ₁ Θ₁ χ) : Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ.neg := by
  obtain ⟨⟨k₁, e₁⟩, ⟨k₂, e₂⟩, hl⟩ := h
  refine ⟨⟨_, .impR List.mem_cons_self (e₂.weaken (fun _ h => h) (by lsub))⟩, ?_,
    fun r ho => ?_⟩
  · have e₁' := e₁.weaken (Δ' := χ.neg :: Δ₂) (Θ' := χ :: Θ₂) (by lsub) (by lsub)
    exact ⟨_, .impL List.mem_cons_self e₁' (.botL List.mem_cons_self)⟩
  · have ho' : χ.Occ r := by simpa [WFF.Occ] using ho
    exact ⟨(hl r ho').2, (hl r ho').1⟩

end Itp

theorem sub_swap {Γ : Ctx} {L L₁ L₂ : List (WFF σ Γ 0)} (h : L ⊆ L₁ ++ L₂) : L ⊆ L₂ ++ L₁ :=
  fun _ ha => (List.mem_append.mp (h ha)).elim (List.mem_append_right _) (List.mem_append_left _)

namespace GK

variable {Γ : Ctx} {Δ₁ Θ₁ Δ₂ Θ₂ : List (WFF σ Γ 0)}

/-! ## The cases, principal formula in the first part -/

theorem itp_ax (P : WFF σ Γ 0) (hP : P.IsAtom) (h₁ : P ∈ Δ₁) (h₂ : P ∈ Θ₁ ++ Θ₂) :
    ∃ χ, Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ := by
  rcases List.mem_append.mp h₂ with h₂ | h₂
  · exact ⟨.bot, ⟨0, .ax P hP h₁ (List.mem_cons_of_mem _ h₂)⟩, ⟨0, .botL List.mem_cons_self⟩,
      fun _ ho => ho.elim⟩
  · exact ⟨P, ⟨0, .ax P hP h₁ List.mem_cons_self⟩, ⟨0, .ax P hP List.mem_cons_self h₂⟩,
      fun _ ho => ⟨Lang.mem (List.mem_append_left _ h₁) ho,
        Lang.mem (List.mem_append_right _ h₂) ho⟩⟩

theorem itp_botL (h : .bot ∈ Δ₁) : ∃ χ, Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ :=
  ⟨.bot, ⟨0, .botL h⟩, ⟨0, .botL List.mem_cons_self⟩, fun _ ho => ho.elim⟩

theorem itp_topR (h : .top ∈ Θ₁) : ∃ χ, Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ :=
  ⟨.bot, ⟨0, .topR (List.mem_cons_of_mem _ h)⟩, ⟨0, .botL List.mem_cons_self⟩,
    fun _ ho => ho.elim⟩

theorem cover_cons {L L₁ L₂ : List (WFF σ Γ 0)} {a : WFF σ Γ 0} (h : L ⊆ L₁ ++ L₂) :
    a :: L ⊆ (a :: L₁) ++ L₂ := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact List.mem_cons_self
  · rcases List.mem_append.mp (h hb) with hb | hb
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ hb)
    · exact List.mem_append_right _ hb

theorem cover_map {Γ' : Ctx} {L L₁ L₂ : List (WFF σ Γ 0)} (f : WFF σ Γ 0 → WFF σ Γ' 0)
    (h : L ⊆ L₁ ++ L₂) : L.map f ⊆ L₁.map f ++ L₂.map f := by
  rw [← List.map_append]
  exact List.map_subset _ h

theorem langLe_cons_mem {a b : WFF σ Γ 0} {L L' : List (WFF σ Γ 0)} (hb : b ∈ L')
    (hab : ∀ r, a.Occ r → b.Occ r) (h : LangLe L L') : LangLe (a :: L) L' :=
  LangLe.cons (fun r ho => Lang.mem hb (hab r ho)) h

theorem itp_andL {Δ Θ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (h : φ.and ψ ∈ Δ₁)
    (ih : Interp Γ (φ :: ψ :: Δ) Θ) (hΔ : Δ ⊆ Δ₁ ++ Δ₂) (hΘ : Θ ⊆ Θ₁ ++ Θ₂) :
    ∃ χ, Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ := by
  obtain ⟨χ, ⟨k₁, e₁⟩, e₂, hl⟩ := ih (φ :: ψ :: Δ₁) Δ₂ Θ₁ Θ₂ (cover_cons (cover_cons hΔ)) hΘ
  refine ⟨χ, ⟨_, .andL h e₁⟩, e₂, fun r ho => ⟨?_, (hl r ho).2⟩⟩
  exact langLe_cons_mem (List.mem_append_left _ h) (fun _ => Or.inl)
    (langLe_cons_mem (List.mem_append_left _ h) (fun _ => Or.inr) (LangLe.sub fun _ h => h)) r
    (hl r ho).1

theorem itp_orR {Δ Θ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (h : φ.or ψ ∈ Θ₁)
    (ih : Interp Γ Δ (φ :: ψ :: Θ)) (hΔ : Δ ⊆ Δ₁ ++ Δ₂) (hΘ : Θ ⊆ Θ₁ ++ Θ₂) :
    ∃ χ, Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ := by
  obtain ⟨χ, ⟨k₁, e₁⟩, e₂, hl⟩ := ih Δ₁ Δ₂ (φ :: ψ :: Θ₁) Θ₂ hΔ (cover_cons (cover_cons hΘ))
  refine ⟨χ, ⟨_, .orR (List.mem_cons_of_mem _ h) (e₁.weaken (fun _ h => h) (by lsub))⟩, e₂,
    fun r ho => ⟨?_, (hl r ho).2⟩⟩
  refine LangLe.append (LangLe.sub (by lsub)) ?_ r (hl r ho).1
  exact langLe_cons_mem (List.mem_append_right _ h) (fun _ => Or.inl)
    (langLe_cons_mem (List.mem_append_right _ h) (fun _ => Or.inr) (LangLe.sub (by lsub)))

theorem itp_impR {Δ Θ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (h : φ.imp ψ ∈ Θ₁)
    (ih : Interp Γ (φ :: Δ) (ψ :: Θ)) (hΔ : Δ ⊆ Δ₁ ++ Δ₂) (hΘ : Θ ⊆ Θ₁ ++ Θ₂) :
    ∃ χ, Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ := by
  obtain ⟨χ, ⟨k₁, e₁⟩, e₂, hl⟩ := ih (φ :: Δ₁) Δ₂ (ψ :: Θ₁) Θ₂ (cover_cons hΔ) (cover_cons hΘ)
  refine ⟨χ, ⟨_, .impR (List.mem_cons_of_mem _ h) (e₁.weaken (fun _ h => h) (by lsub))⟩, e₂,
    fun r ho => ⟨?_, (hl r ho).2⟩⟩
  refine langLe_cons_mem (List.mem_append_right _ h) (fun _ => Or.inl) ?_ r (hl r ho).1
  exact LangLe.append (LangLe.sub (by lsub))
    (langLe_cons_mem (List.mem_append_right _ h) (fun _ => Or.inr) (LangLe.sub (by lsub)))

theorem itp_andR {Δ Θ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (h : φ.and ψ ∈ Θ₁)
    (ih₁ : Interp Γ Δ (φ :: Θ)) (ih₂ : Interp Γ Δ (ψ :: Θ)) (hΔ : Δ ⊆ Δ₁ ++ Δ₂)
    (hΘ : Θ ⊆ Θ₁ ++ Θ₂) : ∃ χ, Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ := by
  obtain ⟨χ₁, ⟨_, a₁⟩, ⟨_, b₁⟩, l₁⟩ := ih₁ Δ₁ Δ₂ (φ :: Θ₁) Θ₂ hΔ (cover_cons hΘ)
  obtain ⟨χ₂, ⟨_, a₂⟩, ⟨_, b₂⟩, l₂⟩ := ih₂ Δ₁ Δ₂ (ψ :: Θ₁) Θ₂ hΔ (cover_cons hΘ)
  have p₁ : GK σ _ Γ Δ₁ (φ :: χ₁.or χ₂ :: Θ₁) :=
    .orR (List.mem_cons_of_mem _ List.mem_cons_self) (a₁.weaken (fun _ h => h) (by lsub))
  have p₂ : GK σ _ Γ Δ₁ (ψ :: χ₁.or χ₂ :: Θ₁) :=
    .orR (List.mem_cons_of_mem _ List.mem_cons_self) (a₂.weaken (fun _ h => h) (by lsub))
  have q₁ := b₁.weaken (Δ' := χ₁ :: χ₁.or χ₂ :: Δ₂) (by lsub) (fun _ h => h)
  have q₂ := b₂.weaken (Δ' := χ₂ :: χ₁.or χ₂ :: Δ₂) (by lsub) (fun _ h => h)
  refine ⟨χ₁.or χ₂, ⟨_, .andR (List.mem_cons_of_mem _ h) (both p₁ p₂).1 (both p₁ p₂).2⟩,
    ⟨_, .orL List.mem_cons_self (both q₁ q₂).1 (both q₁ q₂).2⟩, fun r ho => ?_⟩
  have L₁ : LangLe (Δ₁ ++ φ :: Θ₁) (Δ₁ ++ Θ₁) := LangLe.append (LangLe.sub (by lsub))
    (langLe_cons_mem (List.mem_append_right _ h) (fun _ => Or.inl) (LangLe.sub (by lsub)))
  have L₂ : LangLe (Δ₁ ++ ψ :: Θ₁) (Δ₁ ++ Θ₁) := LangLe.append (LangLe.sub (by lsub))
    (langLe_cons_mem (List.mem_append_right _ h) (fun _ => Or.inr) (LangLe.sub (by lsub)))
  rcases ho with ho | ho
  · exact ⟨L₁ r (l₁ r ho).1, (l₁ r ho).2⟩
  · exact ⟨L₂ r (l₂ r ho).1, (l₂ r ho).2⟩

theorem itp_orL {Δ Θ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (h : φ.or ψ ∈ Δ₁)
    (ih₁ : Interp Γ (φ :: Δ) Θ) (ih₂ : Interp Γ (ψ :: Δ) Θ) (hΔ : Δ ⊆ Δ₁ ++ Δ₂)
    (hΘ : Θ ⊆ Θ₁ ++ Θ₂) : ∃ χ, Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ := by
  obtain ⟨χ₁, ⟨_, a₁⟩, ⟨_, b₁⟩, l₁⟩ := ih₁ (φ :: Δ₁) Δ₂ Θ₁ Θ₂ (cover_cons hΔ) hΘ
  obtain ⟨χ₂, ⟨_, a₂⟩, ⟨_, b₂⟩, l₂⟩ := ih₂ (ψ :: Δ₁) Δ₂ Θ₁ Θ₂ (cover_cons hΔ) hΘ
  have p₁ : GK σ _ Γ (φ :: Δ₁) (χ₁.or χ₂ :: Θ₁) :=
    .orR List.mem_cons_self (a₁.weaken (fun _ h => h) (by lsub))
  have p₂ : GK σ _ Γ (ψ :: Δ₁) (χ₁.or χ₂ :: Θ₁) :=
    .orR List.mem_cons_self (a₂.weaken (fun _ h => h) (by lsub))
  have q₁ := b₁.weaken (Δ' := χ₁ :: χ₁.or χ₂ :: Δ₂) (by lsub) (fun _ h => h)
  have q₂ := b₂.weaken (Δ' := χ₂ :: χ₁.or χ₂ :: Δ₂) (by lsub) (fun _ h => h)
  refine ⟨χ₁.or χ₂, ⟨_, .orL h (both p₁ p₂).1 (both p₁ p₂).2⟩,
    ⟨_, .orL List.mem_cons_self (both q₁ q₂).1 (both q₁ q₂).2⟩, fun r ho => ?_⟩
  have L₁ : LangLe ((φ :: Δ₁) ++ Θ₁) (Δ₁ ++ Θ₁) :=
    langLe_cons_mem (List.mem_append_left _ h) (fun _ => Or.inl) (LangLe.sub fun _ h => h)
  have L₂ : LangLe ((ψ :: Δ₁) ++ Θ₁) (Δ₁ ++ Θ₁) :=
    langLe_cons_mem (List.mem_append_left _ h) (fun _ => Or.inr) (LangLe.sub fun _ h => h)
  rcases ho with ho | ho
  · exact ⟨L₁ r (l₁ r ho).1, (l₁ r ho).2⟩
  · exact ⟨L₂ r (l₂ r ho).1, (l₂ r ho).2⟩

theorem itp_impL {Δ Θ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (h : φ.imp ψ ∈ Δ₁)
    (ih₁ : Interp Γ Δ (φ :: Θ)) (ih₂ : Interp Γ (ψ :: Δ) Θ) (hΔ : Δ ⊆ Δ₁ ++ Δ₂)
    (hΘ : Θ ⊆ Θ₁ ++ Θ₂) : ∃ χ, Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ := by
  obtain ⟨χ₁, ⟨_, a₁⟩, ⟨_, b₁⟩, l₁⟩ := ih₁ Δ₁ Δ₂ (φ :: Θ₁) Θ₂ hΔ (cover_cons hΘ)
  obtain ⟨χ₂, ⟨_, a₂⟩, ⟨_, b₂⟩, l₂⟩ := ih₂ (ψ :: Δ₁) Δ₂ Θ₁ Θ₂ (cover_cons hΔ) hΘ
  have p₁ : GK σ _ Γ Δ₁ (φ :: χ₁.or χ₂ :: Θ₁) :=
    .orR (List.mem_cons_of_mem _ List.mem_cons_self) (a₁.weaken (fun _ h => h) (by lsub))
  have p₂ : GK σ _ Γ (ψ :: Δ₁) (χ₁.or χ₂ :: Θ₁) :=
    .orR List.mem_cons_self (a₂.weaken (fun _ h => h) (by lsub))
  have q₁ := b₁.weaken (Δ' := χ₁ :: χ₁.or χ₂ :: Δ₂) (by lsub) (fun _ h => h)
  have q₂ := b₂.weaken (Δ' := χ₂ :: χ₁.or χ₂ :: Δ₂) (by lsub) (fun _ h => h)
  refine ⟨χ₁.or χ₂, ⟨_, .impL h (both p₁ p₂).1 (both p₁ p₂).2⟩,
    ⟨_, .orL List.mem_cons_self (both q₁ q₂).1 (both q₁ q₂).2⟩, fun r ho => ?_⟩
  have L₁ : LangLe (Δ₁ ++ φ :: Θ₁) (Δ₁ ++ Θ₁) := LangLe.append (LangLe.sub (by lsub))
    (langLe_cons_mem (List.mem_append_left _ h) (fun _ => Or.inl) (LangLe.sub (by lsub)))
  have L₂ : LangLe ((ψ :: Δ₁) ++ Θ₁) (Δ₁ ++ Θ₁) :=
    langLe_cons_mem (List.mem_append_left _ h) (fun _ => Or.inr) (LangLe.sub fun _ h => h)
  rcases ho with ho | ho
  · exact ⟨L₁ r (l₁ r ho).1, (l₁ r ho).2⟩
  · exact ⟨L₂ r (l₂ r ho).1, (l₂ r ho).2⟩

theorem itp_allL [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} (T : VarType)
    {φ : WFF σ (Γ.insert (.bnd 0) T) 1} {a : Ann T} (t : Term σ Γ T a) (h : .all T φ ∈ Δ₁)
    (ih : Interp Γ (WFF.instantiate Ctx.NoSlots.slots t φ :: Δ) Θ) (hΔ : Δ ⊆ Δ₁ ++ Δ₂)
    (hΘ : Θ ⊆ Θ₁ ++ Θ₂) : ∃ χ, Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ := by
  obtain ⟨χ, ⟨k₁, e₁⟩, e₂, hl⟩ := ih (_ :: Δ₁) Δ₂ Θ₁ Θ₂ (cover_cons hΔ) hΘ
  refine ⟨χ, ⟨_, .allL T t h e₁⟩, e₂, fun r ho => ⟨?_, (hl r ho).2⟩⟩
  exact langLe_cons_mem (List.mem_append_left _ h)
    (fun r ho => (WFF.occ_instantiate r _ t φ).mp ho) (LangLe.sub fun _ h => h) r (hl r ho).1

theorem itp_exR [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} (T : VarType)
    {φ : WFF σ (Γ.insert (.bnd 0) T) 1} {a : Ann T} (t : Term σ Γ T a) (h : .ex T φ ∈ Θ₁)
    (ih : Interp Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ :: Θ)) (hΔ : Δ ⊆ Δ₁ ++ Δ₂)
    (hΘ : Θ ⊆ Θ₁ ++ Θ₂) : ∃ χ, Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ := by
  obtain ⟨χ, ⟨k₁, e₁⟩, e₂, hl⟩ := ih Δ₁ Δ₂ (_ :: Θ₁) Θ₂ hΔ (cover_cons hΘ)
  refine ⟨χ, ⟨_, .exR T t (List.mem_cons_of_mem _ h) (e₁.weaken (fun _ h => h) (by lsub))⟩, e₂,
    fun r ho => ⟨?_, (hl r ho).2⟩⟩
  refine LangLe.append (LangLe.sub (by lsub)) ?_ r (hl r ho).1
  exact langLe_cons_mem (List.mem_append_right _ h)
    (fun r ho => (WFF.occ_instantiate r _ t φ).mp ho) (LangLe.sub (by lsub))

theorem itp_ref {Δ Θ : List (WFF σ Γ 0)} (t : Term σ Γ .Var .var) (ih : Interp Γ (.eq t t :: Δ) Θ)
    (hΔ : Δ ⊆ Δ₁ ++ Δ₂) (hΘ : Θ ⊆ Θ₁ ++ Θ₂) : ∃ χ, Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ := by
  obtain ⟨χ, ⟨k₁, e₁⟩, e₂, hl⟩ := ih (_ :: Δ₁) Δ₂ Θ₁ Θ₂ (cover_cons hΔ) hΘ
  exact ⟨χ, ⟨_, .ref t e₁⟩, e₂, fun r ho =>
    ⟨LangLe.cons (a := .eq t t) (fun _ ho => False.elim ho) (LangLe.sub fun _ h => h) r
      (hl r ho).1, (hl r ho).2⟩⟩

theorem itp_repl [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} {Q : WFF σ (Γ.insert (.bnd 0) .Var) 1}
    (hQ : Q.IsAtom) (t s : Term σ Γ .Var .var) (h₁ : .eq t s ∈ Δ)
    (h₂ : WFF.instantiate Ctx.NoSlots.slots t Q ∈ Δ₁)
    (ih : Interp Γ (WFF.instantiate Ctx.NoSlots.slots s Q :: Δ) Θ) (hΔ : Δ ⊆ Δ₁ ++ Δ₂)
    (hΘ : Θ ⊆ Θ₁ ++ Θ₂) : ∃ χ, Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ := by
  have hQs : ∀ r, (WFF.instantiate Ctx.NoSlots.slots s Q).Occ r →
      (WFF.instantiate Ctx.NoSlots.slots t Q).Occ r := fun r ho =>
    (WFF.occ_instantiate r _ t Q).mpr ((WFF.occ_instantiate r _ s Q).mp ho)
  rcases List.mem_append.mp (hΔ h₁) with e | e
  · obtain ⟨χ, ⟨k₁, e₁⟩, e₂, hl⟩ := ih (_ :: Δ₁) Δ₂ Θ₁ Θ₂ (cover_cons hΔ) hΘ
    exact ⟨χ, ⟨_, .repl hQ t s e h₂ e₁⟩, e₂, fun r ho =>
      ⟨langLe_cons_mem (List.mem_append_left _ h₂) hQs (LangLe.sub fun _ h => h) r (hl r ho).1,
        (hl r ho).2⟩⟩
  · obtain ⟨χ, ⟨k₁, e₁⟩, ⟨k₂, e₂⟩, hl⟩ := ih (_ :: .eq t s :: Δ₁) Δ₂ Θ₁ Θ₂
      (fun b hb => by
        rcases List.mem_cons.mp hb with rfl | hb
        · exact List.mem_cons_self
        · rcases List.mem_append.mp (hΔ hb) with hb | hb
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hb))
          · exact List.mem_append_right _ hb) hΘ
    refine ⟨(WFF.eq t s).imp χ, ⟨_, .impR List.mem_cons_self
      (.repl hQ t s List.mem_cons_self (List.mem_cons_of_mem _ h₂)
        (e₁.weaken (by lsub) (by lsub)))⟩, ?_, fun r ho => ?_⟩
    · have p : GK σ k₂ Γ ((WFF.eq t s).imp χ :: Δ₂) (.eq t s :: Θ₂) :=
        .ax (.eq t s) trivial (List.mem_cons_of_mem _ e) List.mem_cons_self
      have q := e₂.weaken (Δ' := χ :: (WFF.eq t s).imp χ :: Δ₂) (by lsub) (fun _ h => h)
      exact ⟨_, .impL List.mem_cons_self p q⟩
    · rcases ho with ho | ho
      · exact False.elim ho
      · exact ⟨langLe_cons_mem (List.mem_append_left _ h₂) hQs
          (LangLe.cons (a := .eq t s) (fun _ ho => False.elim ho) (LangLe.sub fun _ h => h)) r
          (hl r ho).1, (hl r ho).2⟩

/-- `◇χ'` as `¬□¬χ'`. -/
abbrev diaOf (χ : WFF σ Γ.boxIn 0) : WFF σ Γ 0 := (WFF.box (Γ := Γ) χ.neg).neg

theorem itp_boxR {Δ : List (WFF σ Γ 0)} {Δ' : List (WFF σ Γ.boxIn 0)} {φ : WFF σ Γ.boxIn 0}
    (h : WFF.box (Γ := Γ) φ ∈ Θ₁) (h₂ : ∀ χ ∈ Δ', WFF.box (Γ := Γ) χ ∈ Δ)
    (ih : Interp Γ.boxIn Δ' [φ]) (hΔ : Δ ⊆ Δ₁ ++ Δ₂) : ∃ χ, Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ := by
  let A := Δ'.filter fun χ => decide (WFF.box (Γ := Γ) χ ∈ Δ₁)
  let B := Δ'.filter fun χ => decide (WFF.box (Γ := Γ) χ ∈ Δ₂)
  have hA : ∀ χ ∈ A, WFF.box (Γ := Γ) χ ∈ Δ₁ := fun χ hχ =>
    of_decide_eq_true (List.mem_filter.mp hχ).2
  have hB : ∀ χ ∈ B, WFF.box (Γ := Γ) χ ∈ Δ₂ := fun χ hχ =>
    of_decide_eq_true (List.mem_filter.mp hχ).2
  have hcov : Δ' ⊆ A ++ B := fun χ hχ => by
    rcases List.mem_append.mp (hΔ (h₂ χ hχ)) with hb | hb
    · exact List.mem_append_left _ (List.mem_filter.mpr ⟨hχ, decide_eq_true hb⟩)
    · exact List.mem_append_right _ (List.mem_filter.mpr ⟨hχ, decide_eq_true hb⟩)
  obtain ⟨ka, a⟩ := (ih A B [φ] [] hcov (by simp)).choose_spec.1
  obtain ⟨kb, b⟩ := (ih A B [φ] [] hcov (by simp)).choose_spec.2.1
  have hl := (ih A B [φ] [] hcov (by simp)).choose_spec.2.2
  set χ' := (ih A B [φ] [] hcov (by simp)).choose
  have hbox : ∀ χ ∈ χ'.neg :: A, WFF.box (Γ := Γ) χ ∈ WFF.box (Γ := Γ) χ'.neg :: Δ₁ := by
    intro χ hχ
    rcases List.mem_cons.mp hχ with rfl | hχ
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hA χ hχ)
  have p₁ : GK σ (ka + 1 + 1 + 1) Γ Δ₁ (diaOf χ' :: Θ₁) :=
    .impR List.mem_cons_self (.boxR (Δ₁ := χ'.neg :: A)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)) hbox
      (.impL List.mem_cons_self (a.weaken (by lsub) (by lsub)) (.botL List.mem_cons_self)))
  have p₂ : GK σ (kb + 1 + 1 + 1) Γ (diaOf χ' :: Δ₂) Θ₂ :=
    .impL List.mem_cons_self (.boxR (Δ₁ := B) List.mem_cons_self
      (fun χ hχ => List.mem_cons_of_mem _ (hB χ hχ))
      (.impR List.mem_cons_self (b.weaken (fun _ h => h) (by lsub))))
      (.botL List.mem_cons_self)
  refine ⟨diaOf χ', ⟨_, p₁⟩, ⟨_, p₂⟩, fun r ho => ?_⟩
  · have ho' : χ'.Occ r := by simpa [WFF.Occ] using ho
    refine ⟨LangLe.append (fun r ⟨ψ, hψ, ho⟩ => Lang.mem (List.mem_append_left _ (hA ψ hψ)) ho)
      (fun r ⟨ψ, hψ, ho⟩ => ?_) r (hl r ho').1,
      LangLe.append (fun r ⟨ψ, hψ, ho⟩ => Lang.mem (List.mem_append_left _ (hB ψ hψ)) ho)
        (fun r ⟨ψ, hψ, ho⟩ => absurd hψ List.not_mem_nil) r (hl r ho').2⟩
    rw [List.mem_singleton.mp hψ] at ho
    exact Lang.mem (List.mem_append_right _ h) ho

theorem itp_diaL {Δ Θ : List (WFF σ Γ 0)} (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    {ψ : WFF σ (Γ.diaIn x) 0} {Δ' : List (WFF σ Γ.boxIn 0)} {Θ' : List (WFF σ (Γ.diaIn x) 0)}
    (h : .dia x hx ψ ∈ Δ₁) (h₂ : ∀ χ ∈ Δ', WFF.box (Γ := Γ) χ ∈ Δ)
    (h₃ : ∀ χ ∈ Θ', .dia x hx χ ∈ Θ)
    (ih : Interp (Γ.diaIn x) (ψ :: Δ'.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x))) Θ')
    (hΔ : Δ ⊆ Δ₁ ++ Δ₂) (hΘ : Θ ⊆ Θ₁ ++ Θ₂) : ∃ χ, Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ := by
  let A := Δ'.filter fun χ => decide (WFF.box (Γ := Γ) χ ∈ Δ₁)
  let B := Δ'.filter fun χ => decide (WFF.box (Γ := Γ) χ ∈ Δ₂)
  let C := Θ'.filter fun χ => decide (WFF.dia x hx χ ∈ Θ₁)
  let D := Θ'.filter fun χ => decide (WFF.dia x hx χ ∈ Θ₂)
  have hA : ∀ χ ∈ A, WFF.box (Γ := Γ) χ ∈ Δ₁ := fun χ hχ =>
    of_decide_eq_true (List.mem_filter.mp hχ).2
  have hB : ∀ χ ∈ B, WFF.box (Γ := Γ) χ ∈ Δ₂ := fun χ hχ =>
    of_decide_eq_true (List.mem_filter.mp hχ).2
  have hC : ∀ χ ∈ C, WFF.dia x hx χ ∈ Θ₁ := fun χ hχ =>
    of_decide_eq_true (List.mem_filter.mp hχ).2
  have hD : ∀ χ ∈ D, WFF.dia x hx χ ∈ Θ₂ := fun χ hχ =>
    of_decide_eq_true (List.mem_filter.mp hχ).2
  have hcov₁ : ψ :: Δ'.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)) ⊆
      (ψ :: A.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x))) ++
        B.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)) := by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact List.mem_cons_self
    obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hc
    rcases List.mem_append.mp (hΔ (h₂ χ hχ)) with hb | hb
    · exact List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_map_of_mem (List.mem_filter.mpr ⟨hχ, decide_eq_true hb⟩)))
    · exact List.mem_append_right _
        (List.mem_map_of_mem (List.mem_filter.mpr ⟨hχ, decide_eq_true hb⟩))
  have hcov₂ : Θ' ⊆ C ++ D := fun χ hχ => by
    rcases List.mem_append.mp (hΘ (h₃ χ hχ)) with hb | hb
    · exact List.mem_append_left _ (List.mem_filter.mpr ⟨hχ, decide_eq_true hb⟩)
    · exact List.mem_append_right _ (List.mem_filter.mpr ⟨hχ, decide_eq_true hb⟩)
  obtain ⟨χ', ⟨_, a⟩, ⟨_, b⟩, hl⟩ := ih _ _ C D hcov₁ hcov₂
  refine ⟨.dia x hx χ', ⟨_, .diaL x hx (Δ₁ := A) (Θ₁ := χ' :: C) h (fun χ hχ => hA χ hχ)
      (fun χ hχ => ?_) a⟩,
    ⟨_, .diaL x hx (Δ₁ := B) (Θ₁ := D) List.mem_cons_self
      (fun χ hχ => List.mem_cons_of_mem _ (hB χ hχ)) (fun χ hχ => hD χ hχ) b⟩, fun r ho => ?_⟩
  · rcases List.mem_cons.mp hχ with rfl | hχ
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hC χ hχ)
  · have hm : ∀ (χ : WFF σ Γ.boxIn 0) r, (WFF.mono (Ctx.le_boxIn_diaIn Γ x) χ).Occ r →
        (WFF.box (Γ := Γ) χ).Occ r :=
      fun χ r ho => WFF.occ_box.mpr ((WFF.occ_mono r _ χ).mp ho)
    have L₁ : LangLe ((ψ :: A.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x))) ++ C) (Δ₁ ++ Θ₁) := by
      rintro r ⟨c, hc, ho⟩
      rcases List.mem_append.mp hc with hc | hc
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact Lang.mem (List.mem_append_left _ h) ho
        · obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hc
          exact Lang.mem (List.mem_append_left _ (hA χ hχ)) (hm χ r ho)
      · exact Lang.mem (List.mem_append_right _ (hC c hc)) ho
    have L₂ : LangLe (B.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)) ++ D) (Δ₂ ++ Θ₂) := by
      rintro r ⟨c, hc, ho⟩
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hc
        exact Lang.mem (List.mem_append_left _ (hB χ hχ)) (hm χ r ho)
      · exact Lang.mem (List.mem_append_right _ (hD c hc)) ho
    exact ⟨L₁ r (hl r ho).1, L₂ r (hl r ho).2⟩

theorem itp_allR [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} (u : ℕ) (T : VarType)
    (hu : Γ.RootFresh (.free u)) {φ : WFF σ (Γ.insert (.free u) T) 0}
    (h : .all T (WFF.bindFree u hu Ctx.NoSlots.slots T φ) ∈ Θ₁)
    (ih : Interp (Γ.insert (.free u) T) (Δ.map (WFF.weaken hu.root T))
      (φ :: Θ.map (WFF.weaken hu.root T)))
    (hΔ : Δ ⊆ Δ₁ ++ Δ₂) (hΘ : Θ ⊆ Θ₁ ++ Θ₂) : ∃ χ, Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ := by
  obtain ⟨χ', ⟨ka, a⟩, ⟨_, b⟩, hl⟩ := ih _ _ (φ :: Θ₁.map (WFF.weaken hu.root T)) _
    (cover_map _ hΔ) (cover_cons (cover_map _ hΘ))
  have e : WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free u)) T
      (Ctx.ref_insert_root Γ _ T)) (WFF.mono ((Ctx.le_insert hu.root T).insert (.bnd 0) T)
        (WFF.bindFree u hu Ctx.NoSlots.slots T χ')) = χ' := by
    rw [WFF.instantiate_eta_openFree _ hu Ctx.NoSlots.slots Ctx.NoSlots.slots,
      WFF.openFree_bindFree]
  have p : GK σ ka (Γ.insert (.free u) T) (Δ₁.map (WFF.weaken hu.root T))
      (WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free u)) T
        (Ctx.ref_insert_root Γ _ T)) (WFF.mono ((Ctx.le_insert hu.root T).insert (.bnd 0) T)
          (WFF.bindFree u hu Ctx.NoSlots.slots T χ')) ::
        φ :: (WFF.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T χ') :: Θ₁).map
          (WFF.weaken hu.root T)) := by
    rw [e]
    exact a.weaken (fun _ h => h) (by lsub)
  refine ⟨.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T χ'), ⟨_, .allR u T hu
      (List.mem_cons_of_mem _ h) (.exR T _ (List.mem_cons_of_mem _ List.mem_cons_self) p)⟩,
    ⟨_, .exL u T hu List.mem_cons_self (b.weaken (by lsub) (fun _ h => h))⟩, fun r ho => ?_⟩
  · have ho' : χ'.Occ r := (WFF.occ_bindFree r u hu _ T χ').mp ho
    have hw : ∀ (δ : WFF σ Γ 0) r, (WFF.weaken hu.root T δ).Occ r → δ.Occ r :=
      fun δ r ho => (WFF.occ_mono r _ δ).mp ho
    refine ⟨LangLe.append (LangLe.map hw (L' := Δ₁ ++ Θ₁) (by lsub))
        (LangLe.cons (fun r ho => Lang.mem (List.mem_append_right _ h)
          ((WFF.occ_bindFree r u hu _ T φ).mpr ho)) (LangLe.map hw (by lsub))) r (hl r ho').1,
      LangLe.append (LangLe.map hw (L' := Δ₂ ++ Θ₂) (by lsub)) (LangLe.map hw (by lsub)) r
        (hl r ho').2⟩

theorem itp_exL [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} (u : ℕ) (T : VarType)
    (hu : Γ.RootFresh (.free u)) {φ : WFF σ (Γ.insert (.free u) T) 0}
    (h : .ex T (WFF.bindFree u hu Ctx.NoSlots.slots T φ) ∈ Δ₁)
    (ih : Interp (Γ.insert (.free u) T) (φ :: Δ.map (WFF.weaken hu.root T))
      (Θ.map (WFF.weaken hu.root T)))
    (hΔ : Δ ⊆ Δ₁ ++ Δ₂) (hΘ : Θ ⊆ Θ₁ ++ Θ₂) : ∃ χ, Itp Γ Δ₁ Θ₁ Δ₂ Θ₂ χ := by
  obtain ⟨χ', ⟨ka, a⟩, ⟨_, b⟩, hl⟩ := ih (φ :: Δ₁.map (WFF.weaken hu.root T)) _ _ _
    (cover_cons (cover_map _ hΔ)) (cover_map _ hΘ)
  have e : WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free u)) T
      (Ctx.ref_insert_root Γ _ T)) (WFF.mono ((Ctx.le_insert hu.root T).insert (.bnd 0) T)
        (WFF.bindFree u hu Ctx.NoSlots.slots T χ')) = χ' := by
    rw [WFF.instantiate_eta_openFree _ hu Ctx.NoSlots.slots Ctx.NoSlots.slots,
      WFF.openFree_bindFree]
  have p : GK σ ka (Γ.insert (.free u) T) (φ :: Δ₁.map (WFF.weaken hu.root T))
      (WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free u)) T
        (Ctx.ref_insert_root Γ _ T)) (WFF.mono ((Ctx.le_insert hu.root T).insert (.bnd 0) T)
          (WFF.bindFree u hu Ctx.NoSlots.slots T χ')) ::
        (WFF.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T χ') :: Θ₁).map
          (WFF.weaken hu.root T)) := by
    rw [e]
    exact a.weaken (fun _ h => h) (by lsub)
  refine ⟨.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T χ'), ⟨_, .exL u T hu h
      (.exR T _ List.mem_cons_self p)⟩,
    ⟨_, .exL u T hu List.mem_cons_self (b.weaken (by lsub) (fun _ h => h))⟩, fun r ho => ?_⟩
  · have ho' : χ'.Occ r := (WFF.occ_bindFree r u hu _ T χ').mp ho
    have hw : ∀ (δ : WFF σ Γ 0) r, (WFF.weaken hu.root T δ).Occ r → δ.Occ r :=
      fun δ r ho => (WFF.occ_mono r _ δ).mp ho
    refine ⟨LangLe.append (LangLe.cons (fun r ho => Lang.mem (List.mem_append_left _ h)
          ((WFF.occ_bindFree r u hu _ T φ).mpr ho)) (LangLe.map hw (L' := Δ₁ ++ Θ₁) (by lsub)))
        (LangLe.map hw (by lsub)) r (hl r ho').1,
      LangLe.append (LangLe.map hw (L' := Δ₂ ++ Θ₂) (by lsub)) (LangLe.map hw (by lsub)) r
        (hl r ho').2⟩

/-! ## The induction -/

/-- ⭐**Interpolation for GK**: every split of a derivable sequent has an interpolant. -/
theorem interp {n : ℕ} {Δ Θ : List (WFF σ Γ 0)} (d : GK σ n Γ Δ Θ) : Interp Γ Δ Θ := by
  induction d with
  | ax P hP h₁ h₂ =>
      intro Δ₁ Δ₂ Θ₁ Θ₂ hΔ hΘ
      rcases List.mem_append.mp (hΔ h₁) with h | h
      · exact itp_ax P hP h (hΘ h₂)
      · obtain ⟨χ, hχ⟩ := itp_ax (Δ₂ := Δ₁) (Θ₂ := Θ₁) P hP h (sub_swap hΘ h₂)
        exact ⟨_, hχ.swap⟩
  | botL h =>
      intro Δ₁ Δ₂ Θ₁ Θ₂ hΔ hΘ
      rcases List.mem_append.mp (hΔ h) with h | h
      · exact itp_botL h
      · obtain ⟨χ, hχ⟩ := itp_botL (Θ₁ := Θ₂) (Δ₂ := Δ₁) (Θ₂ := Θ₁) h
        exact ⟨_, hχ.swap⟩
  | topR h =>
      intro Δ₁ Δ₂ Θ₁ Θ₂ hΔ hΘ
      rcases List.mem_append.mp (hΘ h) with h | h
      · exact itp_topR h
      · obtain ⟨χ, hχ⟩ := itp_topR (Δ₁ := Δ₂) (Δ₂ := Δ₁) (Θ₂ := Θ₁) h
        exact ⟨_, hχ.swap⟩
  | andL h _ ih =>
      intro Δ₁ Δ₂ Θ₁ Θ₂ hΔ hΘ
      rcases List.mem_append.mp (hΔ h) with h | h
      · exact itp_andL h ih hΔ hΘ
      · obtain ⟨χ, hχ⟩ := itp_andL h ih (sub_swap hΔ) (sub_swap hΘ)
        exact ⟨_, hχ.swap⟩
  | andR h _ _ ih₁ ih₂ =>
      intro Δ₁ Δ₂ Θ₁ Θ₂ hΔ hΘ
      rcases List.mem_append.mp (hΘ h) with h | h
      · exact itp_andR h ih₁ ih₂ hΔ hΘ
      · obtain ⟨χ, hχ⟩ := itp_andR h ih₁ ih₂ (sub_swap hΔ) (sub_swap hΘ)
        exact ⟨_, hχ.swap⟩
  | orL h _ _ ih₁ ih₂ =>
      intro Δ₁ Δ₂ Θ₁ Θ₂ hΔ hΘ
      rcases List.mem_append.mp (hΔ h) with h | h
      · exact itp_orL h ih₁ ih₂ hΔ hΘ
      · obtain ⟨χ, hχ⟩ := itp_orL h ih₁ ih₂ (sub_swap hΔ) (sub_swap hΘ)
        exact ⟨_, hχ.swap⟩
  | orR h _ ih =>
      intro Δ₁ Δ₂ Θ₁ Θ₂ hΔ hΘ
      rcases List.mem_append.mp (hΘ h) with h | h
      · exact itp_orR h ih hΔ hΘ
      · obtain ⟨χ, hχ⟩ := itp_orR h ih (sub_swap hΔ) (sub_swap hΘ)
        exact ⟨_, hχ.swap⟩
  | impL h _ _ ih₁ ih₂ =>
      intro Δ₁ Δ₂ Θ₁ Θ₂ hΔ hΘ
      rcases List.mem_append.mp (hΔ h) with h | h
      · exact itp_impL h ih₁ ih₂ hΔ hΘ
      · obtain ⟨χ, hχ⟩ := itp_impL h ih₁ ih₂ (sub_swap hΔ) (sub_swap hΘ)
        exact ⟨_, hχ.swap⟩
  | impR h _ ih =>
      intro Δ₁ Δ₂ Θ₁ Θ₂ hΔ hΘ
      rcases List.mem_append.mp (hΘ h) with h | h
      · exact itp_impR h ih hΔ hΘ
      · obtain ⟨χ, hχ⟩ := itp_impR h ih (sub_swap hΔ) (sub_swap hΘ)
        exact ⟨_, hχ.swap⟩
  | allL T t h _ ih =>
      intro Δ₁ Δ₂ Θ₁ Θ₂ hΔ hΘ
      rcases List.mem_append.mp (hΔ h) with h | h
      · exact itp_allL T t h ih hΔ hΘ
      · obtain ⟨χ, hχ⟩ := itp_allL T t h ih (sub_swap hΔ) (sub_swap hΘ)
        exact ⟨_, hχ.swap⟩
  | allR u T hu h _ ih =>
      intro Δ₁ Δ₂ Θ₁ Θ₂ hΔ hΘ
      rcases List.mem_append.mp (hΘ h) with h | h
      · exact itp_allR u T hu h ih hΔ hΘ
      · obtain ⟨χ, hχ⟩ := itp_allR u T hu h ih (sub_swap hΔ) (sub_swap hΘ)
        exact ⟨_, hχ.swap⟩
  | exL u T hu h _ ih =>
      intro Δ₁ Δ₂ Θ₁ Θ₂ hΔ hΘ
      rcases List.mem_append.mp (hΔ h) with h | h
      · exact itp_exL u T hu h ih hΔ hΘ
      · obtain ⟨χ, hχ⟩ := itp_exL u T hu h ih (sub_swap hΔ) (sub_swap hΘ)
        exact ⟨_, hχ.swap⟩
  | exR T t h _ ih =>
      intro Δ₁ Δ₂ Θ₁ Θ₂ hΔ hΘ
      rcases List.mem_append.mp (hΘ h) with h | h
      · exact itp_exR T t h ih hΔ hΘ
      · obtain ⟨χ, hχ⟩ := itp_exR T t h ih (sub_swap hΔ) (sub_swap hΘ)
        exact ⟨_, hχ.swap⟩
  | ref t _ ih =>
      intro Δ₁ Δ₂ Θ₁ Θ₂ hΔ hΘ
      exact itp_ref t ih hΔ hΘ
  | repl hQ t s h₁ h₂ _ ih =>
      intro Δ₁ Δ₂ Θ₁ Θ₂ hΔ hΘ
      rcases List.mem_append.mp (hΔ h₂) with h | h
      · exact itp_repl hQ t s h₁ h ih hΔ hΘ
      · obtain ⟨χ, hχ⟩ := itp_repl hQ t s h₁ h ih (sub_swap hΔ) (sub_swap hΘ)
        exact ⟨_, hχ.swap⟩
  | boxR h₁ h₂ _ ih =>
      intro Δ₁ Δ₂ Θ₁ Θ₂ hΔ hΘ
      rcases List.mem_append.mp (hΘ h₁) with h | h
      · exact itp_boxR h h₂ ih hΔ
      · obtain ⟨χ, hχ⟩ := itp_boxR (Θ₂ := Θ₁) h h₂ ih (sub_swap hΔ)
        exact ⟨_, hχ.swap⟩
  | diaL x hx h₁ h₂ h₃ _ ih =>
      intro Δ₁ Δ₂ Θ₁ Θ₂ hΔ hΘ
      rcases List.mem_append.mp (hΔ h₁) with h | h
      · exact itp_diaL x hx h h₂ h₃ ih hΔ hΘ
      · obtain ⟨χ, hχ⟩ := itp_diaL x hx h h₂ h₃ ih (sub_swap hΔ) (sub_swap hΘ)
        exact ⟨_, hχ.swap⟩

/-- ⭐**Craig interpolation for K**: if `φ ⊢ ψ` in natural deduction over a presented context,
    there is `χ` with `φ ⊢ χ` and `χ ⊢ ψ`, every relation symbol of `χ` occurring in both `φ` and
    `ψ`. -/
theorem craig [ModalSys.IsK] [Γ.Presented] {φ ψ : WFF σ Γ 0} (p : Provable [φ] ψ) :
    ∃ χ : WFF σ Γ 0, Provable [φ] χ ∧ Provable [χ] ψ ∧ ∀ r, χ.Occ r → φ.Occ r ∧ ψ.Occ r := by
  obtain ⟨n, d⟩ := provable_iff_der.mp p
  obtain ⟨χ, ⟨_, a⟩, ⟨_, b⟩, hl⟩ := interp d [φ] [] [] [ψ] (by simp) (by simp)
  refine ⟨χ, provable_iff_der.mpr ⟨_, a⟩, provable_iff_der.mpr ⟨_, b⟩, fun r ho => ?_⟩
  obtain ⟨⟨a', ha', oa⟩, ⟨b', hb', ob⟩⟩ := hl r ho
  simp only [List.append_nil, List.mem_singleton, List.nil_append] at ha' hb'
  subst ha' hb'
  exact ⟨oa, ob⟩

end GK

end V12M
