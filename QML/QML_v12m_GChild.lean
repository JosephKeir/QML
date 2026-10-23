import QML.QML_v12m_GLift

/-!
# QML v12m — the growing tree: creating a child

A child of a world `l` is made for a true `◇_k φ` (for a failing `□φ`, `◇¬φ`), with all of `l`'s
variables committed at once: the child's variables are `l`'s at their `gc` types, and for a child
made for `◇_x` also `x`'s content `X` (`childL`).  Its item map is the fresh realisation of every
variable (`gchildMap`: `gImg`, or `gImgX` with `x.dia` to the content).

* ⭐`subst_gpull_child`: pulling back — each child variable to the tuple of the corresponding
  variable's items (`gtup`), the content to `x.dia` (`gpullS`) — undoes the child's map.
* ⭐`gchild_consistent`: the existence lemma.  The child's seed `{φ'} ∪ {ψ' : □_k ψ}` is
  consistent: a refutation pulls back into the view, and `□_k ψ, ◇_k φ` refute each other
  (`kBox_kDia_bot`).  B's `child_consistent` and `childX_consistent` together.
-/

namespace V12M

variable [ModalSys]

namespace Ctx

instance {Γ : Ctx} [Γ.Presented] {k : Option VarSymb} : (Γ.kView k).Presented := by
  cases k <;> (unfold kView; infer_instance)

end Ctx

namespace GArrow

open BArrow

variable {σ : Signature}

/-! ## The child's variables -/

/-- The child's variables: the world's at the `gc` types, and for a child made for `◇_x` the
    content's type `X` last. -/
def childL (l : List VarType) : Option VarSymb → VarType → List VarType
  | none, _ => l.map VarType.gc
  | some _, X => X :: l.map VarType.gc

omit [ModalSys] in
theorem rootTy_map {f : VarType → VarType} (l : List VarType) {r : ℕ} (h : r < l.length) :
    rootTy (l.map f) r = f (rootTy l r) := by
  unfold rootTy
  rw [← List.map_reverse, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_eq_getElem (by simpa using h)]
  rfl

theorem childL_lt (l : List VarType) (k : Option VarSymb) (X : VarType) {r : ℕ}
    (h : r < l.length) : ctxOf (childL l k X) (.root (.free r)) = some (rootTy l r).gc := by
  cases k with
  | none =>
      rw [ctxOf_root_lt (by simpa [childL] using h)]
      exact congrArg some (rootTy_map l h)
  | some x =>
      change ctxOf (X :: l.map VarType.gc) (.root (.free r)) = _
      rw [ctxOf_root_lt (by simp; omega), rootTy_old (by simpa using h)]
      exact congrArg some (rootTy_map l h)

theorem childL_cx (l : List VarType) (x : VarSymb) (X : VarType) :
    ctxOf (childL l (some x) X) (.root (.free l.length)) = some X := by
  have h := ctxOf_ref_new X (l.map VarType.gc)
  rw [List.length_map] at h
  exact h

theorem childL_ge {l : List VarType} {k : Option VarSymb} {X : VarType} {r : ℕ}
    (h : l.length ≤ r) (hk : k = none ∨ l.length < r) :
    ctxOf (childL l k X) (.root (.free r)) = none := by
  cases k with
  | none => exact (ctxOf_fresh (l := l.map VarType.gc) (by simpa using h)) _ rfl
  | some x =>
      rcases hk with hk | hk
      · cases hk
      · exact (ctxOf_fresh (l := X :: l.map VarType.gc) (by simp; omega)) _ rfl

/-- The witness's content type, for a child of kind `k`. -/
def KContent (Γ : Ctx) (k : Option VarSymb) (X : VarType) : Prop :=
  ∀ x, k = some x → Γ.ref x = some (.VTypeDia X)

theorem kContent_none (Γ : Ctx) (X : VarType) : KContent Γ none X := fun _ h => by cases h

theorem kDecl_of_kContent {Γ : Ctx} {k : Option VarSymb} {X : VarType}
    (hk : KContent Γ k X) : KDecl Γ k := fun x e => ⟨X, hk x e⟩

/-- The child's map: every variable freshly realised, `x.dia` to the content. -/
def gchildMap (l : List VarType) : Option VarSymb → VarSymb → VarSymb
  | none => gImg l id
  | some x => gImgX l id x l.length

theorem gImgOk_child (l : List VarType) (k : Option VarSymb) (X : VarType) :
    GImgOk l (ctxOf (childL l k X)) id := fun r hr => by
  change (ctxOf (childL l k X)).ref (.root (.free r)) = _
  rw [Ctx.ref_nonproj _ rfl]
  exact childL_lt l k X hr

theorem itemOk_gchild (hF : ModalSys.Four = true) (l : List VarType) {k : Option VarSymb}
    {X : VarType} (hk : KContent (ctxOf l) k X) :
    ItemOk ((ctxOf l).kView k) (ctxOf (childL l k X)) (gchildMap l k) := by
  cases k with
  | none => exact itemOk_gImg hF (gImgOk_child l none X)
  | some x =>
      exact itemOk_gImgX hF (gImgOk_child l (some x) X) (hk x rfl)
        (by rw [Ctx.ref_nonproj _ rfl]; exact childL_cx l x X)

/-- ⭐The child's map, applied to a formula of the view. -/
noncomputable abbrev gchildArrow (hF : ModalSys.Four = true) (l : List VarType)
    {k : Option VarSymb} {X : VarType} (hk : KContent (ctxOf l) k X)
    (χ : WFF σ ((ctxOf l).kView k) 0) : WFF σ (ctxOf (childL l k X)) 0 :=
  WFF.subst (eIdx (ofRen (gchildMap l k))) (eS σ (ctxOf (childL l k X)) (ofRen (gchildMap l k)))
    (ok_eS_kView (entOk_ofRen (itemOk_gchild hF l hk)))
    (coh_eS_kView (entOk_ofRen (itemOk_gchild hF l hk))) Ctx.NoSlots.slots Ctx.NoSlots.slots χ

/-! ## Pulling back -/

theorem ref_root_lt {l : List VarType} {r : ℕ} (h : r < l.length) :
    (ctxOf l).ref (.root (.free r)) = some (rootTy l r) := by
  rw [Ctx.ref_nonproj _ rfl]
  exact ctxOf_root_lt h

/-- The pull-back's entry beyond the world's variables: the content, to `x.dia`. -/
def gpullCx (σ : Signature) (l : List VarType) : (k : Option VarSymb) → (X : VarType) →
    KContent (ctxOf l) k X → ℕ → SubE σ ((ctxOf l).kView k)
  | some x, X, hk, r =>
      if r = l.length then .tm (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of (hk x rfl))) else .hide
  | none, _, _, _ => .hide

/-- Each child variable back to the tuple of the corresponding variable's items, the content
    to `x.dia`. -/
def gpullS (hF : ModalSys.Four = true) (σ : Signature) (l : List VarType) (k : Option VarSymb)
    (X : VarType) (hk : KContent (ctxOf l) k X) : Subst σ ((ctxOf l).kView k) := fun v =>
  match v with
  | .root (.free r) =>
      if h : r < l.length then
        .tm (Term.mono (Ctx.le_boxIn_kView _ k)
          (gtup hF (.root (.free r)) (rootTy l r) (ref_root_lt h)))
      else gpullCx σ l k X hk r
  | _ => .hide

/-- Where pulling back sends annotation indices: along the entries' annotations. -/
def gpullIdx (l : List VarType) (k : Option VarSymb) (X : VarType) (a : VarSymb) : VarSymb :=
  match a.rt with
  | .free r =>
      if r < l.length then
        (gtupAnnB (.root (.free r)) (rootTy l r) ModalSys.keepOnly).idxAt a.path
      else
        match k with
        | some x => if r = l.length then (Ann.eta (.step x .dia) X).idxAt a.path else a
        | none => a
  | .bnd _ => a

theorem gpull_lt (hF : ModalSys.Four = true) (l : List VarType) (k : Option VarSymb)
    (X : VarType) (hk : KContent (ctxOf l) k X) {r : ℕ} (h : r < l.length) :
    gpullS hF σ l k X hk (.root (.free r)) = .tm (Term.mono (Ctx.le_boxIn_kView _ k)
      (gtup hF (.root (.free r)) (rootTy l r) (ref_root_lt h))) :=
  dif_pos h

theorem gpull_cx (hF : ModalSys.Four = true) (l : List VarType) (x : VarSymb) (X : VarType)
    (hk : KContent (ctxOf l) (some x) X) :
    gpullS hF σ l (some x) X hk (.root (.free l.length)) =
      .tm (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of (hk x rfl))) := by
  change (if h : l.length < l.length then _ else gpullCx σ l (some x) X hk l.length) = _
  rw [dif_neg (lt_irrefl _)]
  exact if_pos rfl

theorem ok_gpullS (hF : ModalSys.Four = true) (l : List VarType) (k : Option VarSymb)
    (X : VarType) (hk : KContent (ctxOf l) k X) :
    Subst.Ok (ctxOf (childL l k X)) (gpullS hF σ l k X hk) := by
  intro v T _ hv
  obtain ⟨r, rfl⟩ := ctxOf_decl hv
  by_cases hr : r < l.length
  · rw [childL_lt l k X hr] at hv
    cases hv
    rw [gpull_lt hF l k X hk hr]
    rfl
  · cases k with
    | none =>
        rw [childL_ge (Nat.le_of_not_lt hr) (Or.inl rfl)] at hv
        cases hv
    | some x =>
        by_cases he : r = l.length
        · subst he
          rw [childL_cx] at hv
          cases hv
          rw [gpull_cx hF l x X hk]
          rfl
        · rw [childL_ge (Nat.le_of_not_lt hr) (Or.inr (by omega))] at hv
          cases hv

theorem coh_gpullS (hF : ModalSys.Four = true) (l : List VarType) (k : Option VarSymb)
    (X : VarType) (hk : KContent (ctxOf l) k X) :
    Subst.Coh (gpullIdx l k X) (ctxOf (childL l k X)) (gpullS hF σ l k X hk) := by
  refine Subst.coh_of (ok_gpullS hF l k X hk) ?_
  intro v T _ hv p
  obtain ⟨r, rfl⟩ := ctxOf_decl hv
  have e : ((VarSymb.root (.free r)).ext p).rt = .free r := VarSymb.ext_rt _ _
  by_cases hr : r < l.length
  · rw [gpull_lt hF l k X hk hr]
    change (gtupAnnB (.root (.free r)) (rootTy l r) ModalSys.keepOnly).idxAt p = gpullIdx l k X _
    rw [gpullIdx, e]
    simp only [if_pos hr]
    rw [VarSymb.ext_path]
    rfl
  · cases k with
    | none =>
        rw [childL_ge (Nat.le_of_not_lt hr) (Or.inl rfl)] at hv
        cases hv
    | some x =>
        by_cases he : r = l.length
        · subst he
          rw [gpull_cx hF l x X hk]
          change (Ann.eta (.step x .dia) X).idxAt p = gpullIdx l (some x) X _
          rw [gpullIdx, e]
          simp only [if_neg hr]
          rw [VarSymb.ext_path]
          rfl
        · rw [childL_ge (Nat.le_of_not_lt hr) (Or.inr (by omega))] at hv
          cases hv

/-- An item of an edge's view other than the witness's content is an item of the `□` view. -/
theorem kView_boxIn' {l : List VarType} {k : Option VarSymb} {u : VarSymb} {s : Step}
    {T : VarType} (h : (ctxOf l).kView k (.step u s) = some T)
    (hne : ¬ ∃ x, k = some x ∧ u = x ∧ s = .dia) : (ctxOf l).boxIn (.step u s) = some T := by
  cases k with
  | none => exact h
  | some x =>
      cases s with
      | dia =>
          change (if u = x then _ else none) = some T at h
          split_ifs at h with hux
          · exact absurd ⟨x, rfl, hux, rfl⟩ hne
      | box => exact h
      | keep => exact h
      | fst => exact h
      | snd => exact h
      | here => exact h

/-- ⭐Pulling back undoes the child's map. -/
theorem subst_gpull_child (hF : ModalSys.Four = true) (l : List VarType) {k : Option VarSymb}
    {X : VarType} (hk : KContent (ctxOf l) k X) (χ : WFF σ ((ctxOf l).kView k) 0) :
    WFF.subst (gpullIdx l k X) (gpullS hF σ l k X hk) (ok_gpullS hF l k X hk)
      (coh_gpullS hF l k X hk) Ctx.NoSlots.slots Ctx.NoSlots.slots (gchildArrow hF l hk χ) = χ := by
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ Subst.ok_idS Subst.coh_idS _ _ _ ?_ χ).trans
    (WFF.subst_id _ _ _ χ)
  refine Subst.sim_of ?_
  intro v T hl hv
  obtain ⟨u, s, rfl, hup, U, hU⟩ := kView_item hv
  have hs' : s.isProj = false := hl
  change SubE.Sim T (.ren (.step u s))
    ((if s.isProj then SubE.hide else .ren (gchildMap l k (.step u s))).comp _ _ _)
  rw [if_neg (by simp [hs'])]
  by_cases hx : ∃ x, k = some x ∧ u = x ∧ s = .dia
  · obtain ⟨x, rfl, rfl, rfl⟩ := hx
    change SubE.Sim T _ ((gpullS hF σ l (some u) X hk).at (gImgX l id u l.length (.step u .dia)))
    rw [show gImgX l id u l.length (.step u .dia) = .root (.free l.length) from if_pos rfl]
    change SubE.Sim T _ (gpullS hF σ l (some u) X hk (.root (.free l.length)))
    rw [gpull_cx hF l u X hk]
    have hT : T = X := by
      change (if u = u then (match (ctxOf l).ref u with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      rw [if_pos rfl, hk u rfl] at hv
      exact (Option.some.inj hv).symm
    subst hT
    exact .ren_eta _ _
  · have hb := kView_boxIn' hv hx
    obtain ⟨r, hr, hlt, hR⟩ := ref_rt hU
    have hmap : gchildMap l k (.step u s) =
        (VarSymb.root (.free r)).ext (gPath (rootTy l r) u.path s) := by
      cases k with
      | none => exact gImg_item l id hr s
      | some x =>
          change (if VarSymb.step u s = .step x .dia then VarSymb.root (.free l.length)
            else gImg l id (.step u s)) = _
          rw [if_neg (fun e => hx ⟨x, rfl, (VarSymb.step.inj e).1, (VarSymb.step.inj e).2⟩)]
          exact gImg_item l id hr s
    rw [hmap]
    change SubE.Sim T _ ((gpullS hF σ l k X hk).at
      ((VarSymb.root (.free r)).ext (gPath (rootTy l r) u.path s)))
    have hwalk : (rootTy l r).walk u.path = some U := by
      have e := Ctx.ref_ext_ppath (ctxOf l) u.path (.root u.rt) hup
      rw [← VarSymb.eq_root_ext u, hU, hR] at e
      exact e.symm
    have hit : (ctxOf l).boxIn.ref (.step u s) = some T := by
      rw [Ctx.ref_nonproj _ hl]
      exact hb
    rw [at_gPath_gtupB hF (Ctx.le_boxIn_kView _ k) (gpullS hF σ l k X hk) ModalSys.keepOnly rfl
      hs' (rootTy l r) u.path (.root (.free r)) (.root (.free r)) (ref_root_lt hlt) hup hwalk
      (gpull_lt hF l k X hk hlt) u (by rw [← hr]; exact VarSymb.eq_root_ext u) hit,
      Term.mono_eta]
    exact .ren_eta _ _

/-! ## Creating a child -/

/-- ⭐**The existence lemma for a child.**  If `◇_k φ` holds, the `□_k`-necessities sent along
    the child's map are consistent with the image of `φ`. -/
theorem gchild_consistent (hF : ModalSys.Four = true) {l : List VarType}
    {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.IsMCS M) {k : Option VarSymb} {X : VarType}
    (hk : KContent (ctxOf l) k X) {φ : WFF σ ((ctxOf l).kView k) 0}
    (hφ : kDia k (kDecl_of_kContent hk) φ ∈ M) :
    Theory.Consistent ({gchildArrow hF l hk φ} ∪
      {χ | ∃ ψ, kBox k (kDecl_of_kContent hk) ψ ∈ M ∧ χ = gchildArrow hF l hk ψ}) := by
  have kd := kDecl_of_kContent hk
  rintro ⟨L, hL, p⟩
  obtain ⟨ψ, hψ, hder⟩ := list_reduce (fun ψ => kBox k kd ψ ∈ M)
    (by simpa only [WFF.mono_refl] using kBox_top_mem hM (Ctx.Le.refl _) kd)
    (fun h₁ h₂ => by
      simpa only [WFF.mono_refl] using kBox_and_mem hM (Ctx.Le.refl _) kd
        (by rw [WFF.mono_refl]; exact h₁) (by rw [WFF.mono_refl]; exact h₂))
    (gchildArrow hF l hk) (fun _ _ => rfl) {gchildArrow hF l hk φ} L (fun δ hδ => hL δ hδ)
  obtain ⟨Δ, hΔ, ⟨q⟩⟩ := derives_of_derives hder p
  have q' : Proof σ (ctxOf (childL l k X)) [gchildArrow hF l hk ψ, gchildArrow hF l hk φ] .bot :=
    Proof.ofSubset (fun x hx => by
      rcases hΔ x hx with hx | hx
      · rw [Set.mem_singleton_iff.mp hx]; exact List.mem_cons_of_mem _ List.mem_cons_self
      · rw [Set.mem_singleton_iff.mp hx]; exact List.mem_cons_self) q
  have q'' := Proof.subst q' (gpullS hF σ l k X hk) (ok_gpullS hF l k X hk)
    (coh_gpullS hF l k X hk) Ctx.NoSlots.slots
  simp only [List.map_cons, List.map_nil, subst_gpull_child] at q''
  exact hM.1 ⟨[kBox k kd ψ, kDia k kd φ], fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hψ
    · rw [List.mem_singleton.mp hx]; exact hφ, kBox_kDia_bot k kd ⟨q''⟩⟩

end GArrow

end V12M
