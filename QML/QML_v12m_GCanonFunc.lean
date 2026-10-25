import QML.QML_v12m_GCanonDom

/-!
# QML v12m — the growing tree's canonical model: the function algebra

As B's `BCanonFunc`, with paths for arrows.

* The frame is transitive (`gtrans`): paths compose.
* A necessary term along a path of two or more edges is its first edge's kept translation along
  the rest (`grden_boxtm_cons`), and a possible term likewise with the kept witness
  (`grden_diatm_cons`).
* ⭐`grden_dup`: `□□` of the shifted body reads, two arrows on, what `□` of the body reads along
  the composite — by induction on the first arrow, with the kept translation commuting with the
  shift (`eTrK_dup`, from `applyG_subst`).
-/

namespace V12M

variable [ModalSys]

/-- T is off: the growing tree's first canonical model has no identity arrows (T + 4 is to
    follow, as for B). -/
class ModalSys.NoT [ModalSys] : Prop where
  noT : ModalSys.T = false

omit [ModalSys] in
theorem absT [ModalSys] [ModalSys.NoT] (hT : ModalSys.T = true) : False := by
  rw [ModalSys.NoT.noT] at hT
  cases hT

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-! ## The frame -/

variable {hM₀ : Theory.IsMCS M₀}

/-! ## Denotations along a given path -/

theorem grden_boxtm_path {A : VarType} {a : Ann A} {Γ : Ctx} {s : GW hF M₀} {i : ℕ}
    (e : Γ.Le (ctxOf (glat s i))) (b : Term σ Γ.boxIn A a) (t : GW hF M₀) (hR : GR s t)
    (P : List ℕ) (h : t.1 = nodeOf s.1 P) (hP : PathOk P) :
    grden hM₀ s i e (.boxtm b) ⟨t, ⟨hR⟩⟩ =
      grden hM₀ t (pstg s t P h i) (Ctx.Le.refl _)
        (pTr hM₀ s t P h hP i (Term.mono e.boxIn b)).2 := by
  obtain rfl := pathOf_of hR h
  rfl

theorem grden_diatm_mem {A : VarType} {a : Ann A} {Γ : Ctx} {s : GW hF M₀} {i : ℕ}
    (e : Γ.Le (ctxOf (glat s i))) (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (b : Term σ (Γ.diaIn x) A a) (t : GW hF M₀) (hR : GR s t) (P : List ℕ)
    (h : t.1 = nodeOf s.1 P) :
    (⟨t, ⟨hR⟩⟩ : GAcc hF M₀ s) ∈ (grden hM₀ s i e (.diatm x hx b)).E ↔ GMem hM₀ s t P h x := by
  obtain rfl := pathOf_of hR h
  exact Iff.rfl

/-- Without T a path is in a witness's canonical extent when it is in its extent. -/
theorem gmem_noT [ModalSys.NoT] {s t : GW hF M₀} {P : List ℕ} {h : t.1 = nodeOf s.1 P}
    {x : VarSymb} : GMem hM₀ s t P h x ↔ InExt s t P h x :=
  ⟨fun hm => (hm.resolve_left (BWorld.not_realised ModalSys.NoT.noT)).2,
    fun hm => .inr ⟨ModalSys.NoT.noT, hm⟩⟩

open Classical in
omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- Without T no witness is realised, so a possible term's content is read by `pTrX`. -/
theorem dite_noReal [ModalSys.NoT] {α : Sort*} {w : BWorld σ} {x : VarSymb}
    (t : w.Realised x → α)
    (f : ¬ w.Realised x → α) :
    dite (w.Realised x) t f = f (BWorld.not_realised ModalSys.NoT.noT) :=
  dif_neg _

theorem grden_diatm_cont {A : VarType} {a : Ann A} {Γ : Ctx} {s : GW hF M₀} {i : ℕ}
    (e : Γ.Le (ctxOf (glat s i))) (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (b : Term σ (Γ.diaIn x) A a) (t : GW hF M₀) (hR : GR s t) (P : List ℕ)
    (h : t.1 = nodeOf s.1 P)
    (hm : (⟨t, ⟨hR⟩⟩ : GAcc hF M₀ s) ∈ (grden hM₀ s i e (.diatm x hx b)).E)
    (hr : ¬ (gw hM₀ t).Realised (kw s t P h x)) (hm' : InExt s t P h x) :
    (grden hM₀ s i e (.diatm x hx b)).c ⟨_, hm⟩ =
      grden hM₀ t (pstg s t P h i) (Ctx.Le.refl _)
        (pTrX hM₀ s t P h i x (hx.imp fun _ h => e.ref h) hm' (Term.mono (e.diaIn x) b)).2 := by
  obtain rfl := pathOf_of hR h
  exact dif_neg hr

/-- Along a path whose end realises the kept witness, a possible term's content is its body
    translated with the witness kept, realised there. -/
theorem grden_diatm_real {A : VarType} {a : Ann A} {Γ : Ctx} {s : GW hF M₀} {i : ℕ}
    (e : Γ.Le (ctxOf (glat s i))) (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (b : Term σ (Γ.diaIn x) A a) (t : GW hF M₀) (hR : GR s t) (P : List ℕ)
    (h : t.1 = nodeOf s.1 P)
    (hm : (⟨t, ⟨hR⟩⟩ : GAcc hF M₀ s) ∈ (grden hM₀ s i e (.diatm x hx b)).E)
    (hr : (gw hM₀ t).Realised (kw s t P h x)) :
    (grden hM₀ s i e (.diatm x hx b)).c ⟨_, hm⟩ =
      grden hM₀ t (max (pstg s t P h i) hr.data.i₀) (Ctx.Le.refl _)
        (grealT hr (Ctx.Le.refl _) (kw_decl hM₀ s t P h i (hx.imp fun _ h => e.ref h))
          (pTrXK hM₀ s t P h i x (hx.imp fun _ h => e.ref h) (Term.mono (e.diaIn x) b)).2).2 := by
  obtain rfl := pathOf_of hR h
  exact dif_pos hr

/-! ## The first edge, kept -/

variable (hM₀) in
/-- ⭐The first edge's translation of a `□` view's term, kept (`pTr`'s step). -/
noncomputable def eTrK (s : GW hF M₀) (c : ℕ) (hb : GBorn hF M₀ (c :: s.1)) (i : ℕ)
    {A : VarType} {a : Ann A} (b : Term σ ((ctxOf (glat s i)).kView none) A a) :
    Σ b' : Ann A,
      Term σ ((ctxOf (glat (stepW s c hb) (glstg s (stepW s c hb) i))).kView none) A b' :=
  ⟨_, Term.subst (eIdx (fmapL hF M₀ (c :: s.1)))
    (eS σ (ctxOf (glat (stepW s c hb) (glstg s (stepW s c hb) i))) (fmapL hF M₀ (c :: s.1))).box
    (Subst.ok_box (ok_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)))
    (Subst.coh_box (ok_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i))
      (coh_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)))
    (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b)⟩

/-- Along two or more edges, a necessary term is its first edge's kept translation along the
    rest. -/
theorem grden_boxtm_cons {A : VarType} {a : Ann A} {s : GW hF M₀} {i : ℕ}
    (b : Term σ ((ctxOf (glat s i)).kView none) A a) (t : GW hF M₀) (hR : GR s t) (c c' : ℕ)
    (P : List ℕ) (h : t.1 = nodeOf s.1 (c :: c' :: P)) :
    grden hM₀ s i (Ctx.Le.refl _) (.boxtm b) ⟨t, ⟨hR⟩⟩ =
      grden hM₀ (stepW s c (born_step h)) (glstg s (stepW s c (born_step h)) i) (Ctx.Le.refl _)
        (.boxtm (eTrK hM₀ s c (born_step h) i b).2)
        ⟨t, ⟨(⟨c' :: P, pathOk_cons, h⟩ : GR (stepW s c (born_step h)) t)⟩⟩ := by
  rw [grden_boxtm_path (Ctx.Le.refl _) b t hR (c :: c' :: P) h (pathOk_cons),
    grden_boxtm_path (Ctx.Le.refl _) _ t _ (c' :: P) h (pathOk_cons),
    Term.mono_refl, Term.mono_refl]
  rfl

/-- ⭐The kept translation commutes with `dup`'s shift. -/
theorem eTrK_dup (s : GW hF M₀) (c : ℕ) (hb : GBorn hF M₀ (c :: s.1)) (i : ℕ) {A : VarType}
    {a : Ann A} (b : Term σ ((ctxOf (glat s i)).kView none) A a) :
    (⟨_, .boxtm (eTrK hM₀ s c hb i
        (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat s i))) b))).2⟩ :
        Σ b', Term σ (ctxOf (glat (stepW s c hb) (glstg s (stepW s c hb) i)))
          (.VTypeBox (.VTypeBox A)) b') =
      ⟨_, .boxtm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (eTrK hM₀ s c hb i b).2))⟩ := by
  have hθ := ok_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
  have hc := coh_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
  have H1 := Term.shift_shift_same (m := 0) (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat s i)))
    (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat s i)).boxIn)
    (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat s i))).boxIn b
  have H2 := Canon.applyG_subst (.dup hF) _ hθ hc
    (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat s i))) b))
  exact (sig_subst _ hθ hc (sig_boxtm (sig_boxtm H1.symm))).trans H2.symm

/-! ## Kept translations under T -/

variable (hM₀) in
/-- ⭐A `□` view's term translated along a path into the end's `□` view: every edge kept, as
    `pTr` keeps all but the last.  Under T collapsing it is `pTr` (`collapse_pTrK`). -/
noncomputable def pTrK : (s t : GW hF M₀) → (P : List ℕ) → (h : t.1 = nodeOf s.1 P) → (i : ℕ) →
    {A : VarType} → {a : Ann A} → Term σ ((ctxOf (glat s i)).kView none) A a →
      Σ b : Ann A, Term σ ((ctxOf (glat t (pstg s t P h i))).kView none) A b
  | _, _, [], h, i, _, _, b => ⟨_, Term.mono ((glat_le_of_eq h i).kView none) b⟩
  | _, t, [c], h, i, _, _, b =>
      ⟨_, Term.subst (eIdx (fmapL hF M₀ t.1))
        (eS σ (ctxOf (glat t (glstg _ t i))) (fmapL hF M₀ t.1)).box
        (Subst.ok_box (ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)))
        (Subst.coh_box (ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i))
          (coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)))
        (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b)⟩
  | s, t, c :: c' :: P, h, i, _, _, b =>
      pTrK (stepW s c (born_step h)) t (c' :: P) h (glstg s (stepW s c (born_step h)) i)
        (eTrK hM₀ s c (born_step h) i b).2

/-- ⭐**Under T a path's translation is its kept translation collapsed**: along an edge, collapsing
    the kept substitution is substituting into the collapsed term (`Term.collapse_subst`,
    `Subst.corr_box_self`), and collapsing the shift undoes it. -/
theorem collapse_pTrK (hT : ModalSys.T = true) : ∀ (s t : GW hF M₀) (P : List ℕ)
    (h : t.1 = nodeOf s.1 P) (hP : PathOk P) (i : ℕ) {A : VarType} {a : Ann A}
    (b : Term σ ((ctxOf (glat s i)).kView none) A a),
    (⟨_, Term.collapse (Ctx.collapses_boxIn_self hT _) (pTrK hM₀ s t P h i b).2⟩ :
        Σ c, Term σ (ctxOf (glat t (pstg s t P h i))) A c) = pTr hM₀ s t P h hP i b
  | s, _, [], h, _, i, _, _, b => by
      change (⟨_, Term.collapse _ (Term.mono _ b)⟩ : Σ c, Term σ _ _ c) =
        ⟨_, Term.mono _ (Term.collapse _ b)⟩
      rw [Term.collapse_mono (Ctx.collapses_boxIn_self hT (ctxOf (glat s i)))
        (Ctx.collapses_boxIn_self hT _) _ (glat_le_of_eq h i)]
  | s, t, [c], h, _, i, _, _, b => by
      have hθ := ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)
      have hk : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
      have hcs := Term.collapse_shift_same (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat s i)))
        (Ctx.collapses_boxIn_self hT (ctxOf (glat s i)).boxIn) (Ctx.Le.refl _)
        (Ctx.shiftCollapseId_keepOnly hk (ctxOf (glat s i))) b
      rw [Term.mono_refl] at hcs
      exact (Term.collapse_subst (Ctx.collapses_boxIn_self hT _)
        (Ctx.collapses_boxIn_self hT _) _ (Subst.ok_box hθ) (Subst.coh_box hθ hc) _ hθ hc
        (Subst.corr_box_self hT hθ) _).trans (sig_subst _ hθ hc hcs)
  | s, t, c :: c' :: P, h, _, _, _, _, _ =>
      collapse_pTrK hT (stepW s c (born_step h)) t (c' :: P) h pathOk_cons _ _

/-- ⭐**`dup` along paths**: `□□` of the shifted body reads, two arrows on, what `□` of the body
    reads along the composite. -/
theorem grden_dup : ∀ (P : List ℕ) (s v : GW hF M₀) (_ : v.1 = nodeOf s.1 P)
    (_ : PathOk P)
    (i : ℕ) {A : VarType} {a : Ann A} (b : Term σ ((ctxOf (glat s i)).kView none) A a)
    (hR : GR s v) (u : GAcc hF M₀ v),
    grden hM₀ s i (Ctx.Le.refl _)
        (.boxtm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat s i))) b)))
        ⟨v, ⟨hR⟩⟩ u =
      grden hM₀ s i (Ctx.Le.refl _) (.boxtm b) ⟨u.1, ⟨gtrans hR u.2.down⟩⟩
  | [], s, v, h, hP, i, _, _, b, hR, ⟨u, ⟨hu⟩⟩ => by
      have hT := hP.T_of_nil
      obtain rfl : v = s := gw_eq h
      rw [grden_boxtm_path (Ctx.Le.refl _) _ v hR [] h hP, Term.mono_refl]
      have hsh := sig_boxtm (Term.collapse_shift_self (m := 0)
        (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat v i)))
        (Ctx.collapses_boxIn_self hT (ctxOf (glat v i))).boxIn (Ctx.Le.refl _) b)
      rw [Term.mono_refl] at hsh
      change grden hM₀ v i (Ctx.Le.refl _) (Term.mono (glat_le_of_eq h i)
        (Term.collapse (Ctx.collapses_boxIn_self hT _) (Term.boxtm _))) ⟨u, ⟨hu⟩⟩ = _
      rw [grden_mono]
      exact (congrFun (grden_sigma _ hsh) _).trans (congrFun (grden_congr _ _ _ _ _ _) _)
  | [c], s, ⟨v, hv⟩, h, _, i, _, _, b, hR, ⟨u, ⟨hu⟩⟩ => by
      change v = c :: s.1 at h
      subst h
      obtain ⟨Q, hQ, hq⟩ := hu
      rcases Q with _ | ⟨c', Q'⟩
      · have hT := hQ.T_of_nil
        obtain rfl : u = ⟨c :: s.1, hv⟩ := gw_eq hq
        rw [grden_boxtm_path (Ctx.Le.refl _) _ ⟨c :: s.1, hv⟩ hR [c] rfl (pathOk_cons),
          Term.mono_refl]
        change grden hM₀ ⟨c :: s.1, hv⟩ (glstg s ⟨c :: s.1, hv⟩ i) (Ctx.Le.refl _)
          (.boxtm (pTrK hM₀ s ⟨c :: s.1, hv⟩ [c] rfl i b).2) ⟨⟨c :: s.1, hv⟩, ⟨⟨[], hQ, hq⟩⟩⟩ = _
        rw [grden_boxtm_path (Ctx.Le.refl _) _ ⟨c :: s.1, hv⟩ _ [] hq hQ, Term.mono_refl,
          grden_boxtm_path (Ctx.Le.refl _) b ⟨c :: s.1, hv⟩ _ [c] rfl pathOk_cons, Term.mono_refl]
        change grden hM₀ _ _ (Ctx.Le.refl _) (Term.mono (glat_le_of_eq hq _)
          (Term.collapse _ (pTrK hM₀ s ⟨c :: s.1, hv⟩ [c] rfl i b).2)) = _
        rw [grden_mono]
        exact (grden_sigma _ (collapse_pTrK hT s _ [c] rfl pathOk_cons i b)).trans
          (grden_congr _ _ _ _ _ _)
      rw [grden_boxtm_path (Ctx.Le.refl _) _ ⟨c :: s.1, hv⟩ hR [c] rfl (pathOk_cons),
        grden_boxtm_cons b u _ c c' Q' hq, Term.mono_refl]
      rfl
  | c :: c₂ :: P, s, v, h, _, i, _, _, b, hR, ⟨u, ⟨hu⟩⟩ => by
      have hR' : GR (stepW s c (born_step h)) v := ⟨c₂ :: P, pathOk_cons, h⟩
      rw [grden_boxtm_cons _ v hR c c₂ P h]
      refine (congrFun (congrFun (grden_sigma (Ctx.Le.refl _)
        (eTrK_dup s c (born_step h) i b)) ⟨v, ⟨hR'⟩⟩) ⟨u, ⟨hu⟩⟩).trans ?_
      refine (grden_dup (c₂ :: P) (stepW s c (born_step h)) v h (pathOk_cons) _
        (eTrK hM₀ s c (born_step h) i b).2 hR' ⟨u, ⟨hu⟩⟩).trans ?_
      obtain ⟨Q, -, hq⟩ := hu
      have hu' : u.1 = nodeOf s.1 (c :: c₂ :: (P ++ Q)) := by
        rw [hq, h, ← nodeOf_append]
        rfl
      exact (grden_boxtm_cons b u _ c c₂ (P ++ Q) hu').symm

/-! ## Keeping possible objects -/

theorem GRPos.ext_E {s : GW hF M₀} {A : VarType} {C : GAcc hF M₀ s → Type} {p q : GRPos s A C}
    (hE : p.E = q.E) (hc : ∀ b (hp : b ∈ p.E) (hq : b ∈ q.E), p.c ⟨b, hp⟩ = q.c ⟨b, hq⟩)
    (hτ : ∀ hT, p.tag hT = q.tag hT) : p = q := by
  obtain ⟨E, c, τ⟩ := p
  obtain ⟨E', c', τ'⟩ := q
  change E = E' at hE
  subst hE
  exact GRPos.congr_cont (funext fun b => hc b.1 b.2 b.2) hτ

variable (hM₀) in
/-- ⭐A possible object kept along an arrow: the arrows on from there whose composite is in its
    extent, with the same contents, and its shape kept along the arrow. -/
noncomputable def gkeep {A : VarType} {s : GW hF M₀} (o : GRDom hM₀ (.VTypeDia A) s)
    (v : GAcc hF M₀ s) :
    GRDom hM₀ (.VTypeDia A) v.1 :=
  ⟨{b | (⟨b.1, ⟨gtrans v.2.down b.2.down⟩⟩ : GAcc hF M₀ s) ∈ o.E},
    fun b => o.c ⟨⟨b.1.1, ⟨gtrans v.2.down b.1.2.down⟩⟩, b.2⟩,
    fun hT => (o.3 hT).map (Arrows.Leaf.keepAlong hF v)⟩

/-- Under T keeping along the world's own arrow is the object itself. -/
theorem gkeep_refl (hT : ModalSys.T = true) {A : VarType} {s : GW hF M₀}
    (o : GRDom hM₀ (.VTypeDia A) s) (hR : GR s s) : gkeep hM₀ o ⟨s, ⟨hR⟩⟩ = o := by
  refine GRPos.ext_E (Set.ext fun ⟨_, ⟨_⟩⟩ => Iff.rfl) (fun ⟨_, ⟨_⟩⟩ _ _ => rfl) fun hT' => ?_
  change (o.3 hT').map _ = _
  refine Eq.trans ?_ (Shp.map_id _)
  exact congrArg (fun g => Shp.map g _) (funext fun ℓ =>
    Arrows.Leaf.keepAlong_refl (F := garrows hF M₀) hT hF ℓ)

/-- Under T a path is in a witness's canonical extent exactly when its end realises the witness
    kept along it. -/
theorem gmem_T (hT : ModalSys.T = true) {s t : GW hF M₀} {P : List ℕ}
    {h : t.1 = nodeOf s.1 P} {x : VarSymb} :
    GMem hM₀ s t P h x ↔ (gw hM₀ t).Realised (kw s t P h x) :=
  ⟨fun hm => hm.resolve_right fun h' => absurd (hT.symm.trans h'.1) (by decide), Or.inl⟩

/-- Keeping a witness's view along the empty path changes nothing. -/
theorem pTrXK_nil (s : GW hF M₀) (h : s.1 = nodeOf s.1 []) (i : ℕ) (x : VarSymb)
    (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (u : Term σ ((ctxOf (glat s i)).kView (some x)) A a) :
    pTrXK hM₀ s s [] h i x hx u = ⟨_, u⟩ := by
  change (⟨_, Term.mono (Ctx.Le.refl _) u⟩ :
    Σ b, Term σ ((ctxOf (glat s i)).kView (some x)) A b) = _
  rw [Term.mono_refl]

variable (hM₀) in
/-- ⭐The first edge's translation of a witness's view, kept (`pTrX`'s step). -/
noncomputable def eTrKX (s : GW hF M₀) (c : ℕ) (hb : GBorn hF M₀ (c :: s.1)) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    {A : VarType} {a : Ann A} (u : Term σ ((ctxOf (glat s i)).kView (some x)) A a) :
    Σ b' : Ann A, Term σ ((ctxOf (glat (stepW s c hb) (glstg s (stepW s c hb) i))).kView
      (some (wit (stepW s c hb) x))) A b' :=
  ⟨_, Term.subst (eIdx (fmapL hF M₀ (c :: s.1)))
    ((eS σ (ctxOf (glat (stepW s c hb) (glstg s (stepW s c hb) i)))
      (fmapL hF M₀ (c :: s.1))).dia (.step x .keep) (wit (stepW s c hb) x))
    (Subst.ok_dia (ok_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i))
      (Ctx.exists_keep_dia hF hx)
      ((coh_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i))
        (.step x .keep) _ (Ctx.exists_keep_dia hF hx).choose_spec []))
    (Subst.coh_dia (ok_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i))
      (coh_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i))
      (Ctx.exists_keep_dia hF hx))
    (Term.shift (Ctx.shifts_diaIn_keep hF _ x) u)⟩

/-- Keeping along an arrow of two or more edges is keeping the first edge's kept translation
    along the rest. -/
theorem gkeep_cons {A : VarType} {a : Ann A} {s : GW hF M₀} {i : ℕ} (x : VarSymb)
    (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (b : Term σ ((ctxOf (glat s i)).diaIn x) A a) (v : GW hF M₀) (hR : GR s v) (c c₂ : ℕ)
    (P : List ℕ) (h : v.1 = nodeOf s.1 (c :: c₂ :: P)) :
    gkeep hM₀ (grden hM₀ s i (Ctx.Le.refl _) (.diatm x hx b)) ⟨v, ⟨hR⟩⟩ =
      gkeep hM₀ (grden hM₀ (stepW s c (born_step h)) (glstg s (stepW s c (born_step h)) i)
          (Ctx.Le.refl _) (.diatm (wit (stepW s c (born_step h)) x)
            (wit_ref hM₀ (born_step h) i hx) (eTrKX hM₀ s c (born_step h) i x hx b).2))
        ⟨v, ⟨(⟨c₂ :: P, pathOk_cons, h⟩ : GR (stepW s c (born_step h)) v)⟩⟩ := by
  refine GRPos.ext_E (Set.ext fun ⟨t, ⟨ht⟩⟩ => ?_) (fun ⟨t, ⟨ht⟩⟩ hp hq => ?_) fun hT => ?_
  · obtain ⟨Q, -, hq⟩ := ht
    have ht' : t.1 = nodeOf s.1 (c :: c₂ :: (P ++ Q)) := by
      rw [hq, h, ← nodeOf_append]
      rfl
    dsimp only [gkeep, Set.mem_setOf_eq]
    exact (grden_diatm_mem _ _ _ _ t _ _ ht').trans
      (grden_diatm_mem _ _ _ _ t _ (c₂ :: (P ++ Q)) ht').symm
  · obtain ⟨Q, -, hq'⟩ := ht
    have ht' : t.1 = nodeOf s.1 (c :: c₂ :: (P ++ Q)) := by
      rw [hq', h, ← nodeOf_append]
      rfl
    dsimp only [gkeep, Set.mem_setOf_eq] at hp hq ⊢
    by_cases hr : (gw hM₀ t).Realised (kw s t (c :: c₂ :: (P ++ Q)) ht' x)
    · rw [grden_diatm_real _ _ _ _ t _ _ ht' hp hr,
        grden_diatm_real _ _ _ _ t _ (c₂ :: (P ++ Q)) ht' hq hr, Term.mono_refl, Term.mono_refl]
      rfl
    have hi := (Or.resolve_left ((grden_diatm_mem _ _ _ _ t _ _ ht').mp hp) hr).2
    rw [grden_diatm_cont _ _ _ _ t _ _ ht' hp hr hi,
      grden_diatm_cont _ _ _ _ t _ (c₂ :: (P ++ Q)) ht' hq hr hi, Term.mono_refl, Term.mono_refl]
    rfl
  · have key := termShp_pTr_keepDia hT hM₀ [c] s (stepW s c (born_step h)) rfl pathOk_cons i hx b
    change _ = Shp.map _ (Model.termShp _ 0 (pTr hM₀ s (stepW s c (born_step h)) [c] rfl
      pathOk_cons i (Term.diatm (.step x .keep) (Ctx.exists_keep_dia hF hx)
        (Term.shift (Ctx.shifts_diaIn_keep hF _ x) b))).2)
    refine Eq.trans ?_ (congrArg (Shp.map _) key).symm
    rw [Shp.map_map]
    exact congrArg (fun g => Shp.map g _)
      (funext fun ℓ => (Arrows.Leaf.keepAlong_comp hF (F := garrows hF M₀)
        (⟨stepW s c (born_step h), ⟨⟨[c], pathOk_cons, rfl⟩⟩⟩ : GAcc hF M₀ s)
        (⟨v, ⟨⟨c₂ :: P, pathOk_cons, h⟩⟩⟩ : GAcc hF M₀ (stepW s c (born_step h))) ℓ).symm)

/-- ⭐The kept translation commutes with `dkeep`'s shift. -/
theorem eTrK_dkeep (s : GW hF M₀) (c : ℕ) (hb : GBorn hF M₀ (c :: s.1)) (i : ℕ) (x : VarSymb)
    (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (u : Term σ ((ctxOf (glat s i)).diaIn x) A a) :
    (⟨_, .boxtm (eTrK hM₀ s c hb i (.diatm (.step x .keep) (Ctx.exists_keep_dia hF hx)
        (Term.shift (Ctx.shifts_diaIn_keep hF (ctxOf (glat s i)) x) u))).2⟩ :
        Σ b', Term σ (ctxOf (glat (stepW s c hb) (glstg s (stepW s c hb) i)))
          (.VTypeBox (.VTypeDia A)) b') =
      ⟨_, .boxtm (.diatm (.step (wit (stepW s c hb) x) .keep)
        (Ctx.exists_keep_dia hF (wit_ref hM₀ hb i hx))
        (Term.shift (Ctx.shifts_diaIn_keep hF _ (wit (stepW s c hb) x))
          (eTrKX hM₀ s c hb i x hx u).2))⟩ := by
  have hθ := ok_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
  have hc := coh_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
  have H1 : (⟨_, Term.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat s i)))
        (Term.diatm (.step x .keep) (Ctx.exists_keep_dia hF hx)
          (Term.shift (Ctx.shifts_diaIn_keep hF (ctxOf (glat s i)) x) u))⟩ :
        Σ b, Term σ (ctxOf (glat s i)).boxIn.boxIn (.VTypeDia A) b) =
      ⟨_, Term.diatm (.step (.step x .keep) .keep)
        (Ctx.exists_keep_dia hF (Ctx.exists_keep_dia hF hx))
        (Term.shift (Ctx.shifts_diaIn_keep hF (ctxOf (glat s i)).boxIn (.step x .keep))
          (Term.shift (Ctx.shifts_diaIn_keep hF (ctxOf (glat s i)) x) u))⟩ := by
    simp only [Term.shift]
    have H := Term.shift_shift_same (m := 0) (Ctx.shifts_diaIn_keep hF (ctxOf (glat s i)) x)
      (Ctx.shifts_diaIn_keep hF (ctxOf (glat s i)).boxIn (.step x .keep))
      ((Ctx.shifts_boxIn_boxIn hF (ctxOf (glat s i))).diaIn (.step x .keep)) u
    first
      | exact sig_diatm H
      | exact sig_diatm H.symm
  have H2 := Canon.applyG_subst (.dkeep hF) _ hθ hc
    (Term.diatm (.step x .keep) (Ctx.exists_keep_dia hF hx)
      (Term.shift (Ctx.shifts_diaIn_keep hF (ctxOf (glat s i)) x) u))
  exact (sig_subst _ hθ hc (sig_boxtm H1)).trans H2.symm

/-- ⭐**`dkeep` along paths**: `□◇_{x.keep}` of the shifted body is, along each arrow, the possible
    object kept along it.  Its shape is the keep law (`termShp_pTr_keepDia`). -/
theorem grden_dkeep : ∀ (P : List ℕ) (s v : GW hF M₀) (_ : v.1 = nodeOf s.1 P)
    (_ : PathOk P)
    (i : ℕ) {A : VarType} {a : Ann A} (x : VarSymb)
    (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (u : Term σ ((ctxOf (glat s i)).diaIn x) A a) (hR : GR s v),
    grden hM₀ s i (Ctx.Le.refl _)
        (.boxtm (.diatm (.step x .keep) (Ctx.exists_keep_dia hF hx)
          (Term.shift (Ctx.shifts_diaIn_keep hF (ctxOf (glat s i)) x) u))) ⟨v, ⟨hR⟩⟩ =
      gkeep hM₀ (grden hM₀ s i (Ctx.Le.refl _) (.diatm x hx u)) ⟨v, ⟨hR⟩⟩
  | [], s, v, h, hP, i, _, _, x, hx, u, hR => by
      have hT := hP.T_of_nil
      obtain rfl : v = s := gw_eq h
      rw [gkeep_refl hT, grden_boxtm_path (Ctx.Le.refl _) _ v hR [] h hP, Term.mono_refl]
      have hsh := sig_diatm (hx := hx) (hx' := hx)
        ((Term.collapse_shift_self (m := 0) (Ctx.shifts_diaIn_keep hF (ctxOf (glat v i)) x)
          ((Ctx.collapses_boxIn_self hT (ctxOf (glat v i))).diaIn (.step x .keep))
          (Ctx.Le.refl _) u).trans (congrArg (Sigma.mk _) (Term.mono_refl _ u)))
      change grden hM₀ v i (Ctx.Le.refl _) (Term.mono (glat_le_of_eq h i)
        (Term.collapse (Ctx.collapses_boxIn_self hT _) (Term.diatm _ _ _))) = _
      rw [grden_mono]
      exact (grden_sigma _ hsh).trans (grden_congr _ _ _ _ _ _)
  | [c], s, ⟨v, hv⟩, h, _, i, _, _, x, hx, u, hR => by
      change v = c :: s.1 at h
      subst h
      rw [grden_boxtm_path (Ctx.Le.refl _) _ ⟨c :: s.1, hv⟩ hR [c] rfl (pathOk_cons),
        Term.mono_refl]
      change grden hM₀ (stepW s c hv) _ (Ctx.Le.refl _) (.diatm (wit (stepW s c hv) x)
        (wit_ref hM₀ hv i hx) (eTrKX hM₀ s c hv i x hx u).2) = _
      refine GRPos.ext_E (Set.ext fun ⟨t, ⟨ht⟩⟩ => ?_) (fun ⟨t, ⟨ht⟩⟩ hp hq => ?_)
        fun hT => termShp_pTr_keepDia hT hM₀ [c] s _ rfl pathOk_cons i hx u
      · obtain ⟨Q, hQ, hq⟩ := ht
        rcases Q with _ | ⟨c', Q'⟩
        · have hT := hQ.T_of_nil
          obtain rfl : t = stepW s c hv := gw_eq hq
          exact (grden_diatm_mem _ _ _ _ _ _ [] hq).trans (gmem_T hT) |>.trans
            ((grden_diatm_mem (hM₀ := hM₀) (Ctx.Le.refl _) x hx u _ (gtrans hR ⟨_, hQ, hq⟩)
              [c] rfl).trans (gmem_T hT)).symm
        exact (grden_diatm_mem _ _ _ _ t _ (c' :: Q') hq).trans
          (grden_diatm_mem (hM₀ := hM₀) (Ctx.Le.refl _) x hx u t (gtrans hR ⟨_, hQ, hq⟩)
            (c :: c' :: Q') hq).symm
      · obtain ⟨Q, hQ, hq'⟩ := ht
        dsimp only [gkeep]
        rcases Q with _ | ⟨c', Q'⟩
        · have hT := hQ.T_of_nil
          obtain rfl : t = stepW s c hv := gw_eq hq'
          have hr := (gmem_T hT).mp ((grden_diatm_mem _ _ _ _ _ _ [] hq').mp hp)
          have hq₂ : (⟨stepW s c hv, ⟨gtrans hR ⟨_, hQ, hq'⟩⟩⟩ : GAcc hF M₀ s) ∈
              (grden hM₀ s i (Ctx.Le.refl _) (.diatm x hx u)).E := hq
          rw [grden_diatm_real _ _ _ _ _ _ [] hq' hp hr,
            grden_diatm_real _ _ _ _ _ _ [c] rfl hq₂ hr]
          refine grden_sigma _ (grealT_sigma hr _ _ ((pTrXK_nil _ hq' _ _ _ _).trans ?_))
          rw [Term.mono_refl, Term.mono_refl]
          rfl
        have hq₂ : (⟨t, ⟨gtrans hR ⟨_, hQ, hq'⟩⟩⟩ : GAcc hF M₀ s) ∈
            (grden hM₀ s i (Ctx.Le.refl _) (.diatm x hx u)).E := hq
        by_cases hr : (gw hM₀ t).Realised (kw s t (c :: c' :: Q') hq' x)
        · rw [grden_diatm_real _ _ _ _ t _ (c' :: Q') hq' hp hr,
            grden_diatm_real _ _ _ _ t _ (c :: c' :: Q') hq' hq₂ hr, Term.mono_refl,
            Term.mono_refl]
          rfl
        have hi := (Or.resolve_left ((grden_diatm_mem _ _ _ _ t _ (c' :: Q') hq').mp hp) hr).2
        rw [grden_diatm_cont _ _ _ _ t _ (c' :: Q') hq' hp hr hi,
          grden_diatm_cont _ _ _ _ t _ (c :: c' :: Q') hq' hq₂ hr hi, Term.mono_refl,
          Term.mono_refl]
        rfl
  | c :: c₂ :: P, s, v, h, _, i, _, _, x, hx, u, hR => by
      have hR' : GR (stepW s c (born_step h)) v := ⟨c₂ :: P, pathOk_cons, h⟩
      rw [grden_boxtm_cons _ v hR c c₂ P h]
      refine (congrFun (grden_sigma (Ctx.Le.refl _)
        (eTrK_dkeep s c (born_step h) i x hx u)) ⟨v, ⟨hR'⟩⟩).trans ?_
      refine (grden_dkeep (c₂ :: P) (stepW s c (born_step h)) v h (pathOk_cons) _ _
        (wit_ref hM₀ (born_step h) i hx) (eTrKX hM₀ s c (born_step h) i x hx u).2 hR').trans ?_
      exact (gkeep_cons x hx u v hR c c₂ P h).symm

/-! ## Translation and the function algebra -/

/-- ⭐Translating along a path commutes with applying a definable map. -/
theorem pTr_applyG {A C : VarType} (g : GFunc σ A C) : ∀ (s t : GW hF M₀) (P : List ℕ)
    (h : t.1 = nodeOf s.1 P) (hP : PathOk P) (i : ℕ) {a : Ann A}
    (b : Term σ ((ctxOf (glat s i)).kView none) A a),
    pTr hM₀ s t P h hP i (Canon.applyG g b).2 = Canon.applyG g (pTr hM₀ s t P h hP i b).2
  | _, _, [], _, hP, i, _, b => by
      simp only [pTr]
      rw [Canon.applyG_mono, Canon.applyG_collapse]
  | _, _, [_], _, _, _, _, b => (Canon.applyG_subst g _ _ _ b).symm
  | s, t, c :: c' :: P, h, _, i, _, b => by
      have hθ := ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)
      refine (pTr_sigma hM₀ _ t (c' :: P) h (pathOk_cons) _
        ((sig_subst _ (Subst.ok_box hθ) (Subst.coh_box hθ hc)
          (Canon.applyG_shift g (Ctx.shifts_boxIn_boxIn hF _) b).symm).trans
          (Canon.applyG_subst g _ (Subst.ok_box hθ) (Subst.coh_box hθ hc) _).symm)).trans ?_
      exact pTr_applyG g (stepW s c (born_step h)) t (c' :: P) h (pathOk_cons) _ _

/-- ⭐Translating a witness's view along a path commutes with applying a definable map. -/
theorem pTrX_applyG {A C : VarType} (g : GFunc σ A C) : ∀ (s t : GW hF M₀) (P : List ℕ)
    (h : t.1 = nodeOf s.1 P) (i : ℕ) (x : VarSymb)
    (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) (hm : InExt s t P h x)
    {a : Ann A} (u : Term σ ((ctxOf (glat s i)).kView (some x)) A a),
    pTrX hM₀ s t P h i x hx hm (Canon.applyG g u).2 =
      Canon.applyG g (pTrX hM₀ s t P h i x hx hm u).2
  | _, _, [], _, _, _, _, hm, _, _ => hm.elim
  | _, _, [_], _, _, _, _, _, _, u => (Canon.applyG_subst g _ _ _ u).symm
  | s, t, c :: c' :: P, h, i, x, hx, hm, _, u => by
      have hθ := ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)
      have hw := hc (.step x .keep) _ (Ctx.exists_keep_dia hF hx).choose_spec []
      have hok := Subst.ok_dia hθ (Ctx.exists_keep_dia hF hx) hw
      have hcoh := Subst.coh_dia hθ hc (Ctx.exists_keep_dia hF hx)
      refine (pTrX_sigma hM₀ _ t (c' :: P) h _ _ (wit_ref hM₀ (born_step h) i hx) hm
        ((sig_subst _ hok hcoh
          (Canon.applyG_shift g (Ctx.shifts_diaIn_keep hF _ x) u).symm).trans
          (Canon.applyG_subst g _ hok hcoh _).symm)).trans ?_
      exact pTrX_applyG g _ t (c' :: P) h _ _ _ hm _

theorem pTr_pair : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (hP : PathOk P)
    (i : ℕ) {A C : VarType} {a₁ : Ann A} {a₂ : Ann C}
    (b : Term σ ((ctxOf (glat s i)).kView none) A a₁)
    (d : Term σ ((ctxOf (glat s i)).kView none) C a₂),
    pTr hM₀ s t P h hP i (.pair b d) =
      ⟨_, .pair (pTr hM₀ s t P h hP i b).2 (pTr hM₀ s t P h hP i d).2⟩
  | _, _, [], _, _, _, _, _, _, _, _, _ => rfl
  | _, _, [_], _, _, _, _, _, _, _, _, _ => rfl
  | s, t, c :: c' :: P, h, _, _, _, _, _, _, _, _ =>
      pTr_pair (stepW s c (born_step h)) t (c' :: P) h (pathOk_cons) _ _ _

theorem pTrX_pair : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hm : InExt s t P h x) {A C : VarType} {a₁ : Ann A} {a₂ : Ann C}
    (b : Term σ ((ctxOf (glat s i)).kView (some x)) A a₁)
    (d : Term σ ((ctxOf (glat s i)).kView (some x)) C a₂),
    pTrX hM₀ s t P h i x hx hm (.pair b d) =
      ⟨_, .pair (pTrX hM₀ s t P h i x hx hm b).2 (pTrX hM₀ s t P h i x hx hm d).2⟩
  | _, _, [], _, _, _, _, hm, _, _, _, _, _, _ => hm.elim
  | _, _, [_], _, _, _, _, _, _, _, _, _, _, _ => rfl
  | s, t, c :: c' :: P, h, _, _, _, hm, _, _, _, _, _, _ =>
      pTrX_pair (stepW s c (born_step h)) t (c' :: P) h _ _ _ hm _ _

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- Keeping a `□` view's term into the kept witness's view is weakening its kept translation. -/
theorem subst_dia_shift_mono {Γ Δ : Ctx} {ι : VarSymb → VarSymb} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ.boxIn θ) (hc : Subst.Coh ι Γ.boxIn θ) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (hw : (θ.at (.step x .keep)).idxAlong [] = ι (.step x .keep)) {A : VarType} {a : Ann A}
    (b : Term σ Γ.boxIn A a) :
    Term.subst ι (θ.dia (.step x .keep) (ι (.step x .keep)))
        (Subst.ok_dia hθ (Ctx.exists_keep_dia hF hx) hw)
        (Subst.coh_dia hθ hc (Ctx.exists_keep_dia hF hx))
        (Term.shift (Ctx.shifts_diaIn_keep hF Γ x) (Term.mono (Ctx.le_boxIn_diaIn Γ x) b)) =
      Term.mono (Ctx.le_boxIn_diaIn Δ (ι (.step x .keep)))
        (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc)
          (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b)) := by
  rw [Term.shift_mono (Ctx.shifts_boxIn_boxIn hF Γ) (Ctx.shifts_diaIn_keep hF Γ x)
    (Ctx.le_boxIn_diaIn Γ x) (Ctx.le_boxIn_diaIn Γ.boxIn (.step x .keep)) b]
  exact Canon.Term.subst_dia_mono θ hθ hc (Ctx.exists_keep_dia hF hx) hw _

/-- ⭐A witness's translation agrees with the plain one on the `□` view. -/
theorem pTrX_box : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (hP : PathOk P)
    (i : ℕ) (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hm : InExt s t P h x) {A : VarType} {a : Ann A}
    (b : Term σ ((ctxOf (glat s i)).kView none) A a),
    pTrX hM₀ s t P h i x hx hm (Term.mono (Ctx.le_boxIn_diaIn _ x) b) = pTr hM₀ s t P h hP i b
  | _, _, [], _, _, _, _, _, hm, _, _, _ => hm.elim
  | _, _, [_], _, _, _, _, _, _, _, _, b => congrArg (Sigma.mk _) (Term.subst_mono _ _ _ _ b)
  | s, t, c :: c' :: P, h, _, i, x, hx, hm, _, _, b => by
      have hθ := ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)
      have hw := hc (.step x .keep) _ (Ctx.exists_keep_dia hF hx).choose_spec []
      simp only [pTr, pTrX]
      exact (pTrX_sigma hM₀ _ t (c' :: P) h _ _ (wit_ref hM₀ (born_step h) i hx) hm
        (congrArg (Sigma.mk _) (subst_dia_shift_mono (hF := hF) _ hθ hc hx hw b))).trans
        (pTrX_box _ t (c' :: P) h (pathOk_cons) _ _ _ hm _)

/-- ⭐A witness's kept translation of a `□` view's term is its kept translation, weakened into the
    kept witness's view. -/
theorem pTrXK_box : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {A : VarType}
    {a : Ann A} (b : Term σ ((ctxOf (glat s i)).kView none) A a),
    pTrXK hM₀ s t P h i x hx (Term.mono (Ctx.le_boxIn_diaIn _ x) b) =
      ⟨_, Term.mono (Ctx.le_boxIn_diaIn _ (kw s t P h x)) (pTrK hM₀ s t P h i b).2⟩
  | _, _, [], _, _, _, _, _, _, b => by
      change (⟨_, Term.mono _ (Term.mono _ b)⟩ : Σ c, Term σ _ _ c) =
        ⟨_, Term.mono _ (Term.mono _ b)⟩
      rw [Term.mono_mono, Term.mono_mono]
  | _, t, [c], h, i, x, hx, _, _, b => by
      have hθ := ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)
      have hw := hc (.step x .keep) _ (Ctx.exists_keep_dia hF hx).choose_spec []
      exact congrArg (Sigma.mk _) (subst_dia_shift_mono (hF := hF) _ hθ hc hx hw b)
  | s, t, c :: c' :: P, h, i, x, hx, _, _, b => by
      have hθ := ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)
      have hw := hc (.step x .keep) _ (Ctx.exists_keep_dia hF hx).choose_spec []
      simp only [pTrXK, pTrK]
      exact (pTrXK_sigma hM₀ _ t (c' :: P) h _ _ (wit_ref hM₀ (born_step h) i hx)
        (congrArg (Sigma.mk _) (subst_dia_shift_mono (hF := hF) _ hθ hc hx hw b))).trans
        (pTrXK_box _ t (c' :: P) h _ _ _ _)

/-- Keeping a witness's view along a path commutes with applying a definable map. -/
theorem pTrXK_applyG {A C : VarType} (g : GFunc σ A C) : ∀ (s t : GW hF M₀) (P : List ℕ)
    (h : t.1 = nodeOf s.1 P) (i : ℕ) (x : VarSymb)
    (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    {a : Ann A} (u : Term σ ((ctxOf (glat s i)).kView (some x)) A a),
    pTrXK hM₀ s t P h i x hx (Canon.applyG g u).2 =
      Canon.applyG g (pTrXK hM₀ s t P h i x hx u).2
  | _, _, [], _, _, _, _, _, u => (Canon.applyG_mono g _ u).symm
  | _, t, [c], h, i, x, hx, _, u => by
      have hθ := ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)
      have hw := hc (.step x .keep) _ (Ctx.exists_keep_dia hF hx).choose_spec []
      have hok := Subst.ok_dia hθ (Ctx.exists_keep_dia hF hx) hw
      have hcoh := Subst.coh_dia hθ hc (Ctx.exists_keep_dia hF hx)
      exact (sig_subst _ hok hcoh
        (Canon.applyG_shift g (Ctx.shifts_diaIn_keep hF _ x) u).symm).trans
        (Canon.applyG_subst g _ hok hcoh _).symm
  | s, t, c :: c' :: P, h, i, x, hx, _, u => by
      have hθ := ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)
      have hw := hc (.step x .keep) _ (Ctx.exists_keep_dia hF hx).choose_spec []
      have hok := Subst.ok_dia hθ (Ctx.exists_keep_dia hF hx) hw
      have hcoh := Subst.coh_dia hθ hc (Ctx.exists_keep_dia hF hx)
      refine (pTrXK_sigma hM₀ _ t (c' :: P) h _ _ (wit_ref hM₀ (born_step h) i hx)
        ((sig_subst _ hok hcoh
          (Canon.applyG_shift g (Ctx.shifts_diaIn_keep hF _ x) u).symm).trans
          (Canon.applyG_subst g _ hok hcoh _).symm)).trans ?_
      exact pTrXK_applyG g _ t (c' :: P) h _ _ _ _

theorem pTrXK_pair : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    {A C : VarType} {a₁ : Ann A} {a₂ : Ann C}
    (b : Term σ ((ctxOf (glat s i)).kView (some x)) A a₁)
    (d : Term σ ((ctxOf (glat s i)).kView (some x)) C a₂),
    pTrXK hM₀ s t P h i x hx (.pair b d) =
      ⟨_, .pair (pTrXK hM₀ s t P h i x hx b).2 (pTrXK hM₀ s t P h i x hx d).2⟩
  | _, _, [], _, _, _, _, _, _, _, _, _, _ => rfl
  | _, _, [_], _, _, _, _, _, _, _, _, _, _ => rfl
  | s, t, c :: c' :: P, h, _, _, _, _, _, _, _, _, _ =>
      pTrXK_pair (stepW s c (born_step h)) t (c' :: P) h _ _ _ _ _

/-- Applying a definable map commutes with realising (B's `applyG_realTerm`). -/
theorem grealT_applyG {A C : VarType} (g : GFunc σ A C) {t : GW hF M₀} {y : VarSymb}
    (hr : (gw hM₀ t).Realised y) {Γ : Ctx} {i : ℕ} (e : Γ.Le (ctxOf (glat t i)))
    (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)) {a : Ann A} (b : Term σ (Γ.diaIn y) A a) :
    grealT hr e hy (Canon.applyG g b).2 = Canon.applyG g (grealT hr e hy b).2 := by
  simp only [grealT]
  rw [Canon.applyG_realiseAtA, Canon.applyG_mono]

/-- ⭐The realised content of a term of the `□` view is what the term denotes here: realisation
    collapses it (B's `rden_realTerm_mono_boxIn`). -/
theorem grden_grealT_mono_boxIn {t : GW hF M₀} {y : VarSymb} (hr : (gw hM₀ t).Realised y)
    {j : ℕ} (hy : ∃ Y, (ctxOf (glat t j)).ref y = some (.VTypeDia Y)) {A : VarType}
    {a : Ann A} (b : Term σ (ctxOf (glat t j)).boxIn A a) :
    grden hM₀ t _ (Ctx.Le.refl _)
        (grealT hr (Ctx.Le.refl _) hy (Term.mono (Ctx.le_boxIn_diaIn _ y) b)).2 =
      grden hM₀ t j (Ctx.Le.refl _) (Term.collapse (Ctx.collapses_boxIn_self hr.T _) b) := by
  have hle : (ctxOf (glat t j)).boxIn.Le (ctxOf (glat t (max j hr.data.i₀))).boxIn :=
    (gle hM₀ t (le_max_left _ _)).boxIn
  have hcomb : Term.mono (((Ctx.Le.refl _).trans (gle hM₀ t (le_max_left _ _))).diaIn y)
      (Term.mono (Ctx.le_boxIn_diaIn _ y) b) =
      Term.mono (Ctx.le_boxIn_diaIn (ctxOf (glat t (max j hr.data.i₀))) y) (Term.mono hle b) := by
    rw [Term.mono_mono, Term.mono_mono]
  simp only [grealT]
  rw [hcomb, grden_sigma _ (Term.realiseAtA_mono_boxIn hr.data.hT y _ _ (Term.mono hle b)),
    Term.collapse_mono (Ctx.collapses_boxIn_self hr.T _)
      (Ctx.collapses_boxIn_self hr.data.hT _) hle (gle hM₀ t (le_max_left _ _)) b,
    grden_mono]
  exact grden_congr _ _ _ _ _ _

/-! ## The function algebra on raw objects -/


variable (hM₀) in
/-- ⭐The function algebra on raw objects.  `extract` reads a necessary object along the world's
    own arrow, `dup` along the composite arrow; `dkeep` keeps a possible object (`gkeep`). -/
noncomputable def grawEval :
    {A C : VarType} → GFunc σ A C → (s : GW hF M₀) → GRDom hM₀ A s → GRDom hM₀ C s
  | _, _, .id _, _, o => o
  | _, _, .comp g f, s, o => grawEval g s (grawEval f s o)
  | _, _, .fst, _, o => o.1
  | _, _, .snd, _, o => o.2
  | _, _, .pair f g, s, o => (grawEval f s o, grawEval g s o)
  | _, _, .unit _, _, _ => PUnit.unit
  | _, _, .func f args, s, o => (gw hM₀ s).canonFunc f (fun k => grawEval (args k) s o)
  | _, _, .boxMap f, _, o => fun a => grawEval f a.1 (o a)
  | _, _, .boxPair _ _, _, o => fun a => (o.1 a, o.2 a)
  | _, _, .boxUnit, _, _ => fun _ => PUnit.unit
  | _, _, .diaMap f, _, o =>
      ⟨o.E, fun a => grawEval f a.1.1 (o.c a),
        fun hT => .dia (o.3 hT).label (GFunc.shp f 1 (o.3 hT).body)⟩
  | _, _, .strength _ _, _, o =>
      ⟨o.2.E, fun a => (o.1 a.1, o.2.c a),
        fun hT => .dia (o.2.3 hT).label
          (.prod (Arrows.transposeShp (F := garrows hF M₀) (Root := fun _ => VarSymb)
            fun a => grawShape hT (o.1 a)) (o.2.3 hT).body)⟩
  | _, _, .extract hT, s, o => o ⟨s, ⟨grefl hT s⟩⟩
  | _, _, .dup _, _, o => fun v u => o ⟨u.1, ⟨gtrans v.2.down u.2.down⟩⟩
  | _, _, .dkeep _, _, o => fun v => gkeep hM₀ o v

theorem grden_varTerm {Γ : Ctx} (s : GW hF M₀) (i : ℕ) (e : Γ.Le (ctxOf (glat s i))) :
    ∀ p : (Σ b : Ann .Var, Term σ Γ .Var b),
      grden hM₀ s i e (Canon.varTerm p) = grden hM₀ s i e p.2
  | ⟨.var, _⟩ => rfl

theorem grden_var_mono {Γ : Ctx} {s : GW hF M₀} {i : ℕ} (e : Γ.Le (ctxOf (glat s i))) :
    ∀ u : Term σ Γ .Var .var, grden hM₀ s i e u = (gw hM₀ s).cls i (Term.mono e u)
  | .var _ _ => rfl
  | .func _ => rfl

/-- ⭐**Denoting a map applied to a term is applying the map to the denotation.**  Along a path,
    applying commutes with translating (`pTr_applyG`, `pTrX_applyG`); `strength`'s necessary part
    is read by the witness's translation as by the plain one (`pTrX_box`); `dup` and `dkeep` are
    `grden_dup` and `grden_dkeep`. -/
theorem grden_applyG :
    ∀ {A C : VarType} (g : GFunc σ A C) {Γ : Ctx} {a : Ann A} (t : Term σ Γ A a)
      (s : GW hF M₀) (i : ℕ) (e : Γ.Le (ctxOf (glat s i))),
    grden hM₀ s i e (Canon.applyG g t).2 = grawEval hM₀ g s (grden hM₀ s i e t)
  | _, _, .id _, _, _, _, _, _, _ => rfl
  | _, _, .comp g f, _, _, t, s, i, e =>
      (grden_applyG g _ s i e).trans (congrArg (grawEval hM₀ g s) (grden_applyG f t s i e))
  | _, _, .fst, _, _, .pair _ _, _, _, _ => rfl
  | _, _, .snd, _, _, .pair _ _, _, _, _ => rfl
  | _, _, .pair f g, _, _, t, s, i, e =>
      Prod.ext (grden_applyG f t s i e) (grden_applyG g t s i e)
  | _, _, .unit _, _, _, _, _, _, _ => rfl
  | _, _, .func f args, _, _, t, s, i, e => by
      change grden hM₀ s i e (.func _) =
        (gw hM₀ s).canonFunc f (fun k => grawEval hM₀ (args k) s (grden hM₀ s i e t))
      have hk : (fun k => grawEval hM₀ (args k) s (grden hM₀ s i e t)) =
          fun k => (gw hM₀ s).cls i (Term.mono e (Canon.varTerm (Canon.applyG (args k) t))) := by
        funext k
        rw [← grden_applyG (args k) t s i e, ← grden_varTerm, grden_var_mono]
      rw [hk, BWorld.canonFunc_cls, grden_var_mono, Term.mono_fill, Spine.mono_ofFn]
      rfl
  | _, _, .boxMap f, _, _, .boxtm b, s, i, e => funext fun a => by
      obtain ⟨t, ⟨hR⟩⟩ := a
      change grden hM₀ s i e (.boxtm (Canon.applyG f b).2) ⟨t, ⟨hR⟩⟩ =
        grawEval hM₀ f t (grden hM₀ s i e (.boxtm b) ⟨t, ⟨hR⟩⟩)
      rw [grden_boxtm_path e _ t hR _ (pathOf_eq hR) (pathOf_ok hR),
        grden_boxtm_path e b t hR _ (pathOf_eq hR) (pathOf_ok hR)]
      refine (grden_sigma (Ctx.Le.refl _)
        ((pTr_sigma hM₀ _ _ _ _ _ _ (Canon.applyG_mono f e.boxIn b).symm).trans
          (pTr_applyG f _ _ _ _ _ _ _))).trans ?_
      exact grden_applyG f _ t _ (Ctx.Le.refl _)
  | _, _, .boxPair _ _, _, _, .pair (.boxtm b) (.boxtm c), s, i, e => funext fun a => by
      obtain ⟨t, ⟨hR⟩⟩ := a
      change grden hM₀ s i e (.boxtm (.pair b c)) ⟨t, ⟨hR⟩⟩ =
        (grden hM₀ s i e (.boxtm b) ⟨t, ⟨hR⟩⟩, grden hM₀ s i e (.boxtm c) ⟨t, ⟨hR⟩⟩)
      rw [grden_boxtm_path e _ t hR _ (pathOf_eq hR) (pathOf_ok hR),
        grden_boxtm_path e b t hR _ (pathOf_eq hR) (pathOf_ok hR),
        grden_boxtm_path e c t hR _ (pathOf_eq hR) (pathOf_ok hR)]
      exact grden_sigma (Ctx.Le.refl _) (pTr_pair _ _ _ _ _ _ _ _)
  | _, _, .boxUnit, _, _, .unit, _, _, _ => funext fun _ => rfl
  | _, _, .diaMap f, Γ, _, .diatm x hx c, s, i, e =>
      GRPos.congr_cont (funext fun a => by
        obtain ⟨⟨t, ⟨hR⟩⟩, hm⟩ := a
        by_cases hr : (gw hM₀ t).Realised (kw s t (pathOf hR) (pathOf_eq hR) x)
        · simp only [grden, dif_pos hr]
          refine (grden_sigma _ ((grealT_sigma hr _ _ ((pTrXK_sigma hM₀ _ _ _ _ _ _ _
            (Canon.applyG_mono f (e.diaIn x) c).symm).trans
              (pTrXK_applyG f _ _ _ _ _ _ _ _))).trans (grealT_applyG f hr _ _ _))).trans ?_
          exact grden_applyG f _ t _ (Ctx.Le.refl _)
        simp only [grden, dif_neg hr]
        refine (grden_sigma (Ctx.Le.refl _)
          ((pTrX_sigma hM₀ _ _ _ _ _ _ _ _ (Canon.applyG_mono f (e.diaIn x) c).symm).trans
            (pTrX_applyG f _ _ _ _ _ _ _ _ _))).trans ?_
        exact grden_applyG f _ t _ (Ctx.Le.refl _))
        fun _ => Canon.termShp_applyG (.diaMap f) (.diatm x hx c) (famEnv cEnv Γ s) 0 (lw := [])
          rfl (fun _ => famEnv_wf (fun t v T => cEnv_wf t v T) Γ s)
  | _, _, .strength _ _, Γ, _, .pair (.boxtm b) (.diatm x hx c), s, i, e =>
      GRPos.congr_cont (funext fun a => by
        obtain ⟨⟨t, ⟨hR⟩⟩, hm⟩ := a
        have hb : Term.mono (e.diaIn x) (Term.mono (Ctx.le_boxIn_diaIn Γ x) b) =
            Term.mono (Ctx.le_boxIn_diaIn _ x) (Term.mono e.boxIn b) := by
          rw [Term.mono_mono, Term.mono_mono]
        by_cases hr : (gw hM₀ t).Realised (kw s t (pathOf hR) (pathOf_eq hR) x)
        · simp only [grden, dif_pos hr]
          refine (grden_sigma _ (grealT_sigma hr _ _ (pTrXK_pair _ _ _ _ _ _ _ _ _))).trans
            (Prod.ext ?_ rfl)
          change grden hM₀ t _ (Ctx.Le.refl _) (grealT hr (Ctx.Le.refl _)
              (kw_decl hM₀ s t _ (pathOf_eq hR) i (hx.imp fun _ h => e.ref h))
              (pTrXK hM₀ s t (pathOf hR) (pathOf_eq hR) i x (hx.imp fun _ h => e.ref h)
                (Term.mono (e.diaIn x) (Term.mono (Ctx.le_boxIn_diaIn Γ x) b))).2).2 =
            grden hM₀ s i e (.boxtm b) ⟨t, ⟨hR⟩⟩
          rw [grden_boxtm_path e b t hR _ (pathOf_eq hR) (pathOf_ok hR)]
          refine (grden_sigma _ (grealT_sigma hr _ _ ((pTrXK_sigma hM₀ _ _ _ _ _ _ _
            (congrArg (Sigma.mk _) hb)).trans (pTrXK_box _ _ _ _ _ _ _ _)))).trans ?_
          rw [grden_grealT_mono_boxIn]
          exact grden_sigma _ (collapse_pTrK hr.T _ _ _ _ (pathOf_ok hR) _ _)
        simp only [grden, dif_neg hr]
        refine (grden_sigma (Ctx.Le.refl _) (pTrX_pair _ _ _ _ _ _ _ _ _ _)).trans
          (Prod.ext ?_ rfl)
        change _ = grden hM₀ s i e (.boxtm b) ⟨t, ⟨hR⟩⟩
        rw [grden_boxtm_path e b t hR _ (pathOf_eq hR) (pathOf_ok hR)]
        exact grden_sigma (Ctx.Le.refl _)
          ((pTrX_sigma hM₀ _ _ _ _ _ _ _ _ (congrArg (Sigma.mk _) hb)).trans
            (pTrX_box _ _ _ _ (pathOf_ok hR) _ _ _ _ _)))
        fun hT =>
          (Canon.termShp_applyG (.strength _ _) (.pair (.boxtm b) (.diatm x hx c))
            (famEnv cEnv Γ s) 0 (lw := []) rfl
            (fun _ => famEnv_wf (fun t v T => cEnv_wf t v T) Γ s)).trans (by
            change _ = Shp.dia _ (Shp.prod (grawShape hT (grden hM₀ s i e (.boxtm b))).inner _)
            rw [grawShape_grden hT s i e (.boxtm b)]
            rfl)
  | _, _, .extract hT, _, _, .boxtm b, s, i, e => by
      change grden hM₀ s i e (Term.collapse _ b) = grden hM₀ s i e (.boxtm b) ⟨s, ⟨grefl hT s⟩⟩
      rw [grden_boxtm_path e b s (grefl hT s) [] rfl (Or.inr hT)]
      change _ = grden hM₀ s i (Ctx.Le.refl _)
        (Term.mono _ (Term.collapse _ (Term.mono e.boxIn b)))
      rw [Term.collapse_mono (Ctx.collapses_boxIn_self hT _) (Ctx.collapses_boxIn_self hT _)
        e.boxIn e, Term.mono_mono, grden_mono]
  | _, _, .dup _, Γ, _, .boxtm b, s, i, e => funext fun v => funext fun u => by
      obtain ⟨v, ⟨hR⟩⟩ := v
      refine (congrFun (congrFun (grden_mono e
        (.boxtm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b))) s i (Ctx.Le.refl _))
          ⟨v, ⟨hR⟩⟩) u).symm.trans ?_
      refine Eq.trans ?_ (congrFun (grden_mono e (.boxtm b) s i (Ctx.Le.refl _))
        ⟨u.1, ⟨gtrans hR u.2.down⟩⟩)
      change grden hM₀ s i (Ctx.Le.refl _) (.boxtm (.boxtm (Term.mono e.boxIn.boxIn
          (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b)))) ⟨v, ⟨hR⟩⟩ u =
        grden hM₀ s i (Ctx.Le.refl _) (.boxtm (Term.mono e.boxIn b)) ⟨u.1, ⟨gtrans hR u.2.down⟩⟩
      rw [← Term.shift_mono (Ctx.shifts_boxIn_boxIn hF Γ) (Ctx.shifts_boxIn_boxIn hF _) e.boxIn
        e.boxIn.boxIn b]
      exact grden_dup (pathOf hR) s v (pathOf_eq hR) (pathOf_ok hR) i _ hR u
  | _, _, .dkeep _, Γ, _, .diatm x hx c, s, i, e => funext fun v => by
      obtain ⟨v, ⟨hR⟩⟩ := v
      refine (congrFun (grden_mono e
        (.boxtm (.diatm (.step x .keep) (Ctx.exists_keep_dia hF hx)
          (Term.shift (Ctx.shifts_diaIn_keep hF Γ x) c))) s i (Ctx.Le.refl _))
          ⟨v, ⟨hR⟩⟩).symm.trans ?_
      refine Eq.trans ?_ (congrArg (fun o => gkeep hM₀ o ⟨v, ⟨hR⟩⟩)
        (grden_mono e (.diatm x hx c) s i (Ctx.Le.refl _)))
      change grden hM₀ s i (Ctx.Le.refl _) (.boxtm (.diatm (.step x .keep) _
          (Term.mono (e.boxIn.diaIn (.step x .keep))
            (Term.shift (Ctx.shifts_diaIn_keep hF Γ x) c)))) ⟨v, ⟨hR⟩⟩ =
        gkeep hM₀ (grden hM₀ s i (Ctx.Le.refl _) (.diatm x _ (Term.mono (e.diaIn x) c)))
          ⟨v, ⟨hR⟩⟩
      rw [← Term.shift_mono (Ctx.shifts_diaIn_keep hF Γ x) (Ctx.shifts_diaIn_keep hF _ x)
        (e.diaIn x) (e.boxIn.diaIn (.step x .keep)) c]
      exact grden_dkeep (pathOf hR) s v (pathOf_eq hR) (pathOf_ok hR) i x _ _ hR

/-- ⭐Definable objects are closed under the function algebra. -/
theorem gdefinable_rawEval {A C : VarType} (g : GFunc σ A C) {s : GW hF M₀}
    {o : GRDom hM₀ A s} (h : GDefinable hM₀ A s o) :
    GDefinable hM₀ C s (grawEval hM₀ g s o) := by
  obtain ⟨i, a, t, rfl⟩ := h
  exact ⟨i, _, (Canon.applyG g t).2, grden_applyG g t s i _⟩

end GArrow

end V12M
