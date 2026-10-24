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
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} [ModalSys.NoT]

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
    (⟨t, ⟨hR⟩⟩ : GAcc hF M₀ s) ∈ (grden hM₀ s i e (.diatm x hx b)).E ↔ InExt s t P h x := by
  obtain rfl := pathOf_of hR h
  exact Iff.rfl

theorem grden_diatm_cont {A : VarType} {a : Ann A} {Γ : Ctx} {s : GW hF M₀} {i : ℕ}
    (e : Γ.Le (ctxOf (glat s i))) (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (b : Term σ (Γ.diaIn x) A a) (t : GW hF M₀) (hR : GR s t) (P : List ℕ)
    (h : t.1 = nodeOf s.1 P)
    (hm : (⟨t, ⟨hR⟩⟩ : GAcc hF M₀ s) ∈ (grden hM₀ s i e (.diatm x hx b)).E)
    (hm' : InExt s t P h x) :
    (grden hM₀ s i e (.diatm x hx b)).c ⟨_, hm⟩ =
      grden hM₀ t (pstg s t P h i) (Ctx.Le.refl _)
        (pTrX hM₀ s t P h i x (hx.imp fun _ h => e.ref h) hm' (Term.mono (e.diaIn x) b)).2 := by
  obtain rfl := pathOf_of hR h
  rfl

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

/-- ⭐**`dup` along paths**: `□□` of the shifted body reads, two arrows on, what `□` of the body
    reads along the composite. -/
theorem grden_dup : ∀ (P : List ℕ) (s v : GW hF M₀) (_ : v.1 = nodeOf s.1 P) (_ : PathOk P)
    (i : ℕ) {A : VarType} {a : Ann A} (b : Term σ ((ctxOf (glat s i)).kView none) A a)
    (hR : GR s v) (u : GAcc hF M₀ v),
    grden hM₀ s i (Ctx.Le.refl _)
        (.boxtm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat s i))) b)))
        ⟨v, ⟨hR⟩⟩ u =
      grden hM₀ s i (Ctx.Le.refl _) (.boxtm b) ⟨u.1, ⟨gtrans hR u.2.down⟩⟩
  | [], _, _, _, hP, _, _, _, _, _, _ => (absT hP.T_of_nil).elim
  | [c], s, ⟨v, hv⟩, h, _, i, _, _, b, hR, ⟨u, ⟨hu⟩⟩ => by
      change v = c :: s.1 at h
      subst h
      obtain ⟨Q, hQ, hq⟩ := hu
      obtain ⟨c', Q', rfl⟩ := List.exists_cons_of_ne_nil (hQ.resolve_right absT)
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

theorem GRPos.ext_E {s : GW hF M₀} {C : GAcc hF M₀ s → Type} {p q : GRPos s C}
    (hE : p.E = q.E) (hc : ∀ b (hp : b ∈ p.E) (hq : b ∈ q.E), p.c ⟨b, hp⟩ = q.c ⟨b, hq⟩) :
    p = q := by
  obtain ⟨E, c⟩ := p
  obtain ⟨E', c'⟩ := q
  change E = E' at hE
  subst hE
  exact GRPos.congr_cont (funext fun b => hc b.1 b.2 b.2)

variable (hM₀) in
/-- ⭐A possible object kept along an arrow: the arrows on from there whose composite is in its
    extent, with the same contents. -/
def gkeep {A : VarType} {s : GW hF M₀} (o : GRDom hM₀ (.VTypeDia A) s) (v : GAcc hF M₀ s) :
    GRDom hM₀ (.VTypeDia A) v.1 :=
  ⟨{b | (⟨b.1, ⟨gtrans v.2.down b.2.down⟩⟩ : GAcc hF M₀ s) ∈ o.E},
    fun b => o.c ⟨⟨b.1.1, ⟨gtrans v.2.down b.1.2.down⟩⟩, b.2⟩⟩

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
  refine GRPos.ext_E (Set.ext fun ⟨t, ⟨ht⟩⟩ => ?_) fun ⟨t, ⟨ht⟩⟩ hp hq => ?_
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
    have hi := (grden_diatm_mem _ _ _ _ t _ _ ht').mp hp
    rw [grden_diatm_cont _ _ _ _ t _ _ ht' hp hi,
      grden_diatm_cont _ _ _ _ t _ (c₂ :: (P ++ Q)) ht' hq hi, Term.mono_refl, Term.mono_refl]
    rfl

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
    object kept along it. -/
theorem grden_dkeep : ∀ (P : List ℕ) (s v : GW hF M₀) (_ : v.1 = nodeOf s.1 P) (_ : PathOk P)
    (i : ℕ) {A : VarType} {a : Ann A} (x : VarSymb)
    (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (u : Term σ ((ctxOf (glat s i)).diaIn x) A a) (hR : GR s v),
    grden hM₀ s i (Ctx.Le.refl _)
        (.boxtm (.diatm (.step x .keep) (Ctx.exists_keep_dia hF hx)
          (Term.shift (Ctx.shifts_diaIn_keep hF (ctxOf (glat s i)) x) u))) ⟨v, ⟨hR⟩⟩ =
      gkeep hM₀ (grden hM₀ s i (Ctx.Le.refl _) (.diatm x hx u)) ⟨v, ⟨hR⟩⟩
  | [], _, _, _, hP, _, _, _, _, _, _, _ => (absT hP.T_of_nil).elim
  | [c], s, ⟨v, hv⟩, h, _, i, _, _, x, hx, u, hR => by
      change v = c :: s.1 at h
      subst h
      rw [grden_boxtm_path (Ctx.Le.refl _) _ ⟨c :: s.1, hv⟩ hR [c] rfl (pathOk_cons),
        Term.mono_refl]
      change grden hM₀ (stepW s c hv) _ (Ctx.Le.refl _) (.diatm (wit (stepW s c hv) x)
        (wit_ref hM₀ hv i hx) (eTrKX hM₀ s c hv i x hx u).2) = _
      refine GRPos.ext_E (Set.ext fun ⟨t, ⟨ht⟩⟩ => ?_) fun ⟨t, ⟨ht⟩⟩ hp hq => ?_
      · obtain ⟨Q, hQ, hq⟩ := ht
        obtain ⟨c', Q', rfl⟩ := List.exists_cons_of_ne_nil (hQ.resolve_right absT)
        exact (grden_diatm_mem _ _ _ _ t _ (c' :: Q') hq).trans
          (grden_diatm_mem (hM₀ := hM₀) (Ctx.Le.refl _) x hx u t (gtrans hR ⟨_, hQ, hq⟩)
            (c :: c' :: Q') hq).symm
      · obtain ⟨Q, hQ, hq'⟩ := ht
        obtain ⟨c', Q', rfl⟩ := List.exists_cons_of_ne_nil (hQ.resolve_right absT)
        have hq₂ : (⟨t, ⟨gtrans hR ⟨_, hQ, hq'⟩⟩⟩ : GAcc hF M₀ s) ∈
            (grden hM₀ s i (Ctx.Le.refl _) (.diatm x hx u)).E := hq
        have hi := (grden_diatm_mem _ _ _ _ t _ (c' :: Q') hq').mp hp
        dsimp only [gkeep]
        rw [grden_diatm_cont _ _ _ _ t _ (c' :: Q') hq' hp hi,
          grden_diatm_cont _ _ _ _ t _ (c :: c' :: Q') hq' hq₂ hi, Term.mono_refl,
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
  | _, _, [], _, hP, _, _, _ => (absT hP.T_of_nil).elim
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
  | _, _, [], _, hP, _, _, _, _, _, _, _ => (absT hP.T_of_nil).elim
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
  | _, _, [], _, hP, _, _, _, _, _, _, _ => (absT hP.T_of_nil).elim
  | _, _, [_], _, _, _, _, _, _, _, _, b => congrArg (Sigma.mk _) (Term.subst_mono _ _ _ _ b)
  | s, t, c :: c' :: P, h, _, i, x, hx, hm, _, _, b => by
      have hθ := ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)
      have hw := hc (.step x .keep) _ (Ctx.exists_keep_dia hF hx).choose_spec []
      simp only [pTr, pTrX]
      exact (pTrX_sigma hM₀ _ t (c' :: P) h _ _ (wit_ref hM₀ (born_step h) i hx) hm
        (congrArg (Sigma.mk _) (subst_dia_shift_mono (hF := hF) _ hθ hc hx hw b))).trans
        (pTrX_box _ t (c' :: P) h (pathOk_cons) _ _ _ hm _)

/-! ## The function algebra on raw objects -/


variable (hM₀) in
/-- ⭐The function algebra on raw objects.  `extract` does not arise (T is off); `dup` reads a
    necessary object along the composite arrow, `dkeep` keeps a possible object (`gkeep`). -/
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
  | _, _, .diaMap f, _, o => ⟨o.E, fun a => grawEval f a.1.1 (o.c a)⟩
  | _, _, .strength _ _, _, o => ⟨o.2.E, fun a => (o.1 a.1, o.2.c a)⟩
  | _, _, .extract hT, _, _ => absurd hT (by rw [ModalSys.NoT.noT]; decide)
  | _, _, .dup _, _, o => fun v u => o ⟨u.1, ⟨gtrans v.2.down u.2.down⟩⟩
  | _, _, .dkeep _, _, o => fun v => gkeep hM₀ o v

omit [ModalSys.NoT] in
theorem grden_varTerm {Γ : Ctx} (s : GW hF M₀) (i : ℕ) (e : Γ.Le (ctxOf (glat s i))) :
    ∀ p : (Σ b : Ann .Var, Term σ Γ .Var b),
      grden hM₀ s i e (Canon.varTerm p) = grden hM₀ s i e p.2
  | ⟨.var, _⟩ => rfl

omit [ModalSys.NoT] in
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
  | _, _, .diaMap f, _, _, .diatm x hx c, s, i, e =>
      GRPos.congr_cont (funext fun a => by
        refine (grden_sigma (Ctx.Le.refl _)
          ((pTrX_sigma hM₀ _ _ _ _ _ _ _ _ (Canon.applyG_mono f (e.diaIn x) c).symm).trans
            (pTrX_applyG f _ _ _ _ _ _ _ _ _))).trans ?_
        exact grden_applyG f _ a.1.1 _ (Ctx.Le.refl _))
  | _, _, .strength _ _, Γ, _, .pair (.boxtm b) (.diatm x hx c), s, i, e =>
      GRPos.congr_cont (funext fun a => by
        obtain ⟨⟨t, ⟨hR⟩⟩, hm⟩ := a
        have hb : Term.mono (e.diaIn x) (Term.mono (Ctx.le_boxIn_diaIn Γ x) b) =
            Term.mono (Ctx.le_boxIn_diaIn _ x) (Term.mono e.boxIn b) := by
          rw [Term.mono_mono, Term.mono_mono]
        refine (grden_sigma (Ctx.Le.refl _) (pTrX_pair _ _ _ _ _ _ _ _ _ _)).trans
          (Prod.ext ?_ rfl)
        change _ = grden hM₀ s i e (.boxtm b) ⟨t, ⟨hR⟩⟩
        rw [grden_boxtm_path e b t hR _ (pathOf_eq hR) (pathOf_ok hR)]
        exact grden_sigma (Ctx.Le.refl _)
          ((pTrX_sigma hM₀ _ _ _ _ _ _ _ _ (congrArg (Sigma.mk _) hb)).trans
            (pTrX_box _ _ _ _ (pathOf_ok hR) _ _ _ _ _)))
  | _, _, .extract hT, _, _, _, _, _, _ => absurd hT (by rw [ModalSys.NoT.noT]; decide)
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
