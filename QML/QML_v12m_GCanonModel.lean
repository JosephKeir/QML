import QML.QML_v12m_GCanonFunc

/-!
# QML v12m — the growing tree's canonical model: frame, carriers and operations

As B's `BCanonModel`, for 4 without T or B.

* The frame: the worlds ever born, strict descendants as arrows (`GR`, transitive by `gtrans`),
  the root as the actual world, serial under D (`glex` at `□⊥`).
* The carriers are the definable raw objects; the function algebra acts by `grawEval`
  (`gops`, `geval_toDom`).  `necDup_eval` will hold by definition: `dup` reads along the
  composite arrow.
* Strong D (`gposSerial_canon`) as B's.

The model itself (`GCanonLift`) needs strong 4's lift as well.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

section Flags

variable [ModalSys.NoT] [ModalSys.NoB]

omit [ModalSys.NoT] in
theorem absB (hB : ModalSys.B = true) : False := by
  rw [ModalSys.NoB.noB] at hB
  cases hB

theorem absShaped (h : ModalSys.shaped = true) : False := by
  simp [ModalSys.shaped, ModalSys.NoT.noT, ModalSys.NoB.noBStrong] at h

omit [ModalSys.NoT] in
/-- Without B the only shaped flag is T. -/
theorem gT_of_shaped (h : ModalSys.shaped = true) : ModalSys.T = true := by
  simpa [ModalSys.shaped, ModalSys.NoB.noBStrong] using h

end Flags

variable (hF M₀) in
/-- The root of the tree. -/
def groot : GW hF M₀ := ⟨[], 0, trivial⟩

variable [ModalSys.NoB] (hM₀ : Theory.IsMCS M₀)

omit [ModalSys.NoB] in
/-- Under D every world has an arrow out: `□⊥` fails, since `D_box` refutes it. -/
theorem gserial (hM₀ : Theory.IsMCS M₀) (hD : ModalSys.D = true) (s : GW hF M₀) :
    ∃ t, Nonempty (GR s t) := by
  have hnot : WFF.box (.bot : WFF σ (ctxOf (glat s 0)).boxIn 0) ∉ (gw hM₀ s).M 0 := fun h =>
    ((gw hM₀ s).mcs 0).bot_not_mem (BWorld.mem_of_provable (Δ := [.box .bot])
      (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact h)
      ⟨Proof.D_box hD (Proof.lookup List.mem_cons_self)⟩)
  obtain ⟨t, ⟨c, hc⟩, -, -⟩ := glex hM₀ s 0 .bot hnot
  exact ⟨t, ⟨⟨[c], pathOk_cons, hc⟩⟩⟩

variable (hF) in
/-- ⭐The canonical frame. -/
noncomputable def gframe : Frame.{0, 0} σ where
  toArrows := garrows hF M₀
  actual := groot hF M₀
  serial := fun hD s => gserial hM₀ hD s
  symm := fun hB => (absB hB).elim
  homeUnique := fun _ => ⟨fun _ _ => rfl⟩
  D s := (gw hM₀ s).D
  Nec A s := {o : GRDom hM₀ (.VTypeBox A) s // GDefinable hM₀ (.VTypeBox A) s o}
  Pos A s := {o : GRDom hM₀ (.VTypeDia A) s // GDefinable hM₀ (.VTypeDia A) s o}
  funcInterp f s args := (gw hM₀ s).canonFunc f args
  relInterp r s args := (gw hM₀ s).canonRel r args

/-- A definable raw object as a frame object. -/
def gtoDom : (A : VarType) → (s : GW hF M₀) → (o : GRDom hM₀ A s) → GDefinable hM₀ A s o →
    (gframe hF hM₀).Dom A s
  | .Var, _, o, _ => o
  | .VTypeOne, _, _, _ => PUnit.unit
  | .VTypeProd A C, s, o, h =>
      (gtoDom A s o.1 (gdefinable_fst h), gtoDom C s o.2 (gdefinable_snd h))
  | .VTypeBox A, s, o, h =>
      (Subtype.mk o h : {o : GRDom hM₀ (.VTypeBox A) s // GDefinable hM₀ (.VTypeBox A) s o})
  | .VTypeDia A, s, o, h =>
      (Subtype.mk o h : {o : GRDom hM₀ (.VTypeDia A) s // GDefinable hM₀ (.VTypeDia A) s o})

/-- A frame object as a raw object. -/
def gfromDom : (A : VarType) → (s : GW hF M₀) → (gframe hF hM₀).Dom A s → GRDom hM₀ A s
  | .Var, _, d => d
  | .VTypeOne, _, _ => PUnit.unit
  | .VTypeProd A C, s, d =>
      (gfromDom A s (d : (gframe hF hM₀).Dom A s × (gframe hF hM₀).Dom C s).1,
        gfromDom C s (d : (gframe hF hM₀).Dom A s × (gframe hF hM₀).Dom C s).2)
  | .VTypeBox A, s, d =>
      (d : {o : GRDom hM₀ (.VTypeBox A) s // GDefinable hM₀ (.VTypeBox A) s o}).1
  | .VTypeDia A, s, d =>
      (d : {o : GRDom hM₀ (.VTypeDia A) s // GDefinable hM₀ (.VTypeDia A) s o}).1

theorem gdefinable_fromDom : ∀ (A : VarType) (s : GW hF M₀) (d : (gframe hF hM₀).Dom A s),
    GDefinable hM₀ A s (gfromDom hM₀ A s d)
  | .Var, _, d => gdefinable_var d
  | .VTypeOne, _, _ => gdefinable_unit _
  | .VTypeProd A C, s, d =>
      gdefinable_pair
        (gdefinable_fromDom A s (d : (gframe hF hM₀).Dom A s × (gframe hF hM₀).Dom C s).1)
        (gdefinable_fromDom C s (d : (gframe hF hM₀).Dom A s × (gframe hF hM₀).Dom C s).2)
  | .VTypeBox A, s, d =>
      (d : {o : GRDom hM₀ (.VTypeBox A) s // GDefinable hM₀ (.VTypeBox A) s o}).2
  | .VTypeDia A, s, d =>
      (d : {o : GRDom hM₀ (.VTypeDia A) s // GDefinable hM₀ (.VTypeDia A) s o}).2

theorem gfromDom_toDom : ∀ (A : VarType) (s : GW hF M₀) (o : GRDom hM₀ A s)
    (h : GDefinable hM₀ A s o), gfromDom hM₀ A s (gtoDom hM₀ A s o h) = o
  | .Var, _, _, _ => rfl
  | .VTypeOne, _, _, _ => rfl
  | .VTypeProd A C, s, o, h =>
      Prod.ext (gfromDom_toDom A s o.1 (gdefinable_fst h))
        (gfromDom_toDom C s o.2 (gdefinable_snd h))
  | .VTypeBox _, _, _, _ => rfl
  | .VTypeDia _, _, _, _ => rfl

theorem gtoDom_fromDom : ∀ (A : VarType) (s : GW hF M₀) (d : (gframe hF hM₀).Dom A s),
    gtoDom hM₀ A s (gfromDom hM₀ A s d) (gdefinable_fromDom hM₀ A s d) = d
  | .Var, _, _ => rfl
  | .VTypeOne, _, _ => rfl
  | .VTypeProd A C, s, d =>
      Prod.ext (gtoDom_fromDom A s (d : (gframe hF hM₀).Dom A s × (gframe hF hM₀).Dom C s).1)
        (gtoDom_fromDom C s (d : (gframe hF hM₀).Dom A s × (gframe hF hM₀).Dom C s).2)
  | .VTypeBox _, _, _ => rfl
  | .VTypeDia _, _, _ => rfl

variable {hM₀}

theorem gtoDom_inj {A : VarType} {s : GW hF M₀} {o o' : GRDom hM₀ A s}
    {h : GDefinable hM₀ A s o} {h' : GDefinable hM₀ A s o'}
    (e : gtoDom hM₀ A s o h = gtoDom hM₀ A s o' h') : o = o' := by
  rw [← gfromDom_toDom hM₀ A s o h, ← gfromDom_toDom hM₀ A s o' h', e]

theorem gtoDom_congr {A : VarType} {s : GW hF M₀} {o o' : GRDom hM₀ A s} (e : o = o')
    (h : GDefinable hM₀ A s o) (h' : GDefinable hM₀ A s o') :
    gtoDom hM₀ A s o h = gtoDom hM₀ A s o' h' := by
  subst e
  rfl

variable (hM₀)

/-- Evaluation of necessary objects. -/
def gnecEval {A : VarType} {s : GW hF M₀} (n : (gframe hF hM₀).Nec A s) :
    (gframe hF hM₀).NecSec A s :=
  fun a => gtoDom hM₀ A a.1 (n.1 a) (gdefinable_box_apply n.2 a)

/-- Evaluation of possible objects. -/
def gposEval {A : VarType} {s : GW hF M₀} (p : (gframe hF hM₀).Pos A s) :
    (gframe hF hM₀).PosSec A s :=
  ⟨p.1.E, fun a => gtoDom hM₀ A a.1.1 (p.1.c a) (gdefinable_dia_apply p.2 a)⟩

theorem gnecEval_injective {A : VarType} {s : GW hF M₀} :
    Function.Injective (gnecEval hM₀ (A := A) (s := s)) := by
  intro n n' h
  apply Subtype.ext
  funext a
  exact gtoDom_inj (congrFun h a)

/-- ⭐Evaluation of possible objects, in full: the section and, when shaped (under T, B being
    off), the stored shape. -/
def gposFull {A : VarType} {s : GW hF M₀} (p : (gframe hF hM₀).Pos A s) :
    (gframe hF hM₀).PosSec A s × (ModalSys.shaped = true → GShape hF M₀ s (.VTypeDia A)) :=
  (gposEval hM₀ p, fun hSh => p.1.3 (gT_of_shaped hSh))

/-- A possible object is its section and, when shaped, its shape. -/
theorem gposFull_injective {A : VarType} {s : GW hF M₀} :
    Function.Injective (gposFull hM₀ (A := A) (s := s)) := by
  rintro ⟨⟨E, c, τ⟩, hp⟩ ⟨⟨E', c', τ'⟩, hp'⟩ h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [gposFull, gposEval] at h₁ h₂
  obtain ⟨rfl, hc⟩ := Sigma.mk.inj_iff.mp h₁
  have hc' := eq_of_heq hc
  apply Subtype.ext
  exact GRPos.congr_cont (funext fun a => gtoDom_inj (congrFun hc' a))
    fun hT => congrFun h₂ (ModalSys.shaped_of_T hT)

/-- ⭐**The canonical shapes are well-formed**: a possible object is a term's denotation, whose
    stored shape is the term's canonical shape (`grawShape_grden`), well-formed as the canonical
    environment is. -/
theorem gposShape_wf_canon (hT : ModalSys.T = true) {A : VarType} {s : GW hF M₀}
    (p : (gframe hF hM₀).Pos A s) :
    Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (p.1.3 hT) := by
  obtain ⟨i, a, t, ht⟩ := p.2
  change Model.ShWF [] (grawShape hT p.1)
  rw [← ht, grawShape_grden hT]
  exact Model.shWF_termShp (lw := []) (famEnv_wf (fun t v T => cEnv_wf t v T) _ s) t

/-- When shaped, a frame object's shape is its raw object's. -/
theorem gdomShape_toDom (hSh : ModalSys.shaped = true) : ∀ (A : VarType) (s : GW hF M₀)
    (o : GRDom hM₀ A s) (h : GDefinable hM₀ A s o),
    Frame.domShape (gnecEval hM₀) (fun q => (gposFull hM₀ q).2 hSh) (gtoDom hM₀ A s o h) =
      grawShape (gT_of_shaped hSh) o
  | .Var, _, _, _ => rfl
  | .VTypeOne, _, _, _ => rfl
  | .VTypeProd A C, s, o, h =>
      congrArg₂ Shp.prod (gdomShape_toDom hSh A s o.1 (gdefinable_fst h))
        (gdomShape_toDom hSh C s o.2 (gdefinable_snd h))
  | .VTypeBox A, _, o, h =>
      congrArg Shp.box (congrArg Arrows.transposeShp (funext fun a =>
        gdomShape_toDom hSh A a.1 (o a) (gdefinable_box_apply h a)))
  | .VTypeDia _, _, _, _ => rfl

variable (hF) in
/-- The function algebra on the carriers. -/
noncomputable def gops : (gframe hF hM₀).Ops where
  necMap g n := ⟨grawEval hM₀ (.boxMap g) _ n.1, gdefinable_rawEval (.boxMap g) n.2⟩
  necPair a b := ⟨grawEval hM₀ (.boxPair _ _) _
      ((a.1, b.1) : GRDom hM₀ (.VTypeProd (.VTypeBox _) (.VTypeBox _)) _),
    gdefinable_rawEval (.boxPair _ _) (gdefinable_pair a.2 b.2)⟩
  necUnit := ⟨grawEval hM₀ .boxUnit _ (PUnit.unit : GRDom hM₀ .VTypeOne _),
    gdefinable_rawEval .boxUnit (gdefinable_unit _)⟩
  posMap g p := ⟨grawEval hM₀ (.diaMap g) _ p.1, gdefinable_rawEval (.diaMap g) p.2⟩
  posStrength n p := ⟨grawEval hM₀ (.strength _ _) _
      ((n.1, p.1) : GRDom hM₀ (.VTypeProd (.VTypeBox _) (.VTypeDia _)) _),
    gdefinable_rawEval (.strength _ _) (gdefinable_pair n.2 p.2)⟩
  necExtract hT n :=
    gtoDom hM₀ _ _ (grawEval hM₀ (.extract hT) _ n.1) (gdefinable_rawEval (.extract hT) n.2)
  necDup hF' n := ⟨grawEval hM₀ (.dup hF') _ n.1, gdefinable_rawEval (.dup hF') n.2⟩
  posKeep hF' p := ⟨grawEval hM₀ (.dkeep hF') _ p.1, gdefinable_rawEval (.dkeep hF') p.2⟩

/-- ⭐Evaluating a map on a frame object is evaluating it on the raw object. -/
theorem geval_toDom : ∀ {A C : VarType} (g : GFunc σ A C) (s : GW hF M₀) (o : GRDom hM₀ A s)
    (h : GDefinable hM₀ A s o),
    GFunc.eval (gops hF hM₀) g s (gtoDom hM₀ A s o h) =
      gtoDom hM₀ C s (grawEval hM₀ g s o) (gdefinable_rawEval g h)
  | _, _, .id _, _, _, _ => rfl
  | _, _, .comp g f, s, o, h =>
      (congrArg (GFunc.eval (gops hF hM₀) g s) (geval_toDom f s o h)).trans (geval_toDom g s _ _)
  | _, _, .fst, _, _, _ => rfl
  | _, _, .snd, _, _, _ => rfl
  | _, _, .pair f g, s, o, h => Prod.ext (geval_toDom f s o h) (geval_toDom g s o h)
  | _, _, .unit _, _, _, _ => rfl
  | _, _, .func f args, s, o, h =>
      congrArg ((gw hM₀ s).canonFunc f) (funext fun k => geval_toDom (args k) s o h)
  | _, _, .boxMap _, _, _, _ => rfl
  | _, _, .boxPair _ _, _, _, _ => rfl
  | _, _, .boxUnit, _, _, _ => rfl
  | _, _, .diaMap _, _, _, _ => rfl
  | _, _, .strength _ _, _, _, _ => rfl
  | _, _, .extract _, _, _, _ => rfl
  | _, _, .dup _, _, _, _ => rfl
  | _, _, .dkeep _, _, _, _ => rfl

/-! ## Strong D -/

omit [ModalSys.NoB] in
/-- ⭐**Under T a `◇_x`-child realises the witness's image** (the tree's
    `realised_keep_of_boxx`): `here_keep` at the η-expansion of `x`'s content is a `□_x`-formula of
    the parent, and its translation into the child (`gltrX`) is a `Here` atom about `wit t x`. -/
theorem grealised_wit (hT : ModalSys.T = true) {s t : GW hF M₀} (h : GCh hF M₀ s t)
    {x : VarSymb} (hkd : lkd t = some x) (i : ℕ) {X : VarType}
    (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X)) :
    (gw hM₀ t).Realised (wit t x) := by
  have hmem : WFF.hereKeep hT hF x ⟨X, hx⟩ (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx)) ∈
      (gw hM₀ s).M i :=
    BWorld.mem_of_provable (Δ := []) (fun _ h => by simp at h)
      ⟨Proof.here_keep hT hF x ⟨X, hx⟩ _⟩
  have h₁ := gltrX hM₀ h hkd i hx _ hmem
  obtain ⟨Z, hk⟩ := wit_ref_ch hM₀ h i ⟨X, hx⟩
  exact (gw hM₀ t).datum_of_here hT hk _ _ h₁

/-- ⭐Under strong D every world has a possible object of type `𝟙` with a nonempty extent: the
    axiom's Henkin witness is a possible term `◇_x u`, whose extent has the child made for `x`
    (`glexX`). -/
theorem gposSerial_canon (hDS : ModalSys.DStrong = true) (s : GW hF M₀) :
    ∃ p : (gframe hF hM₀).Pos .VTypeOne s, Nonempty (gposEval hM₀ p).1 := by
  have hax : (WFF.somePoss : WFF σ ((gw hM₀ s).ctx 0) 0) ∈ (gw hM₀ s).M 0 :=
    BWorld.mem_of_provable (Δ := []) (fun _ h => by simp at h) ⟨Proof.D_ex hDS⟩
  obtain ⟨j, _, _, t, hmem⟩ := (gw hM₀ s).exW_term hax
  match t with
  | .diatm x hx u =>
      obtain ⟨X, hX⟩ := id hx
      obtain ⟨t', ⟨c, hc⟩, hk, -, -, -⟩ := glexX hM₀ s j x X hX .top (by
        have e : (WFF.instantiate Ctx.NoSlots.slots (Term.diatm x hx u)
            (WFF.mono ((ctxOf_le_of_suffix ((gw hM₀ s).suf (Nat.zero_le j))).insert (.bnd 0)
              (.VTypeDia .VTypeOne))
              (.dia (.root (.bnd 0)) ⟨.VTypeOne, Ctx.ref_insert_root _ (.bnd 0) _⟩ .top))) =
            WFF.dia x ⟨X, hX⟩ .top := rfl
        rw [← e]
        exact hmem)
      have hR : GR s t' := ⟨[c], pathOk_cons, hc⟩
      refine ⟨⟨grden hM₀ s j (Ctx.Le.refl _) (.diatm x hx u), gdefinable_rden _ _⟩,
        ⟨⟨⟨t', ⟨hR⟩⟩, ?_⟩⟩⟩
      refine (grden_diatm_mem (hM₀ := hM₀) (Ctx.Le.refl _) x hx u t' hR [c] hc).mpr ?_
      by_cases hT : ModalSys.T = true
      · exact .inl (grealised_wit hM₀ hT ⟨c, hc⟩ hk j hX)
      · exact .inr ⟨Bool.eq_false_iff.mpr hT, hk⟩

/-! ## Indistinguishability -/

/-- ⭐**Canonical indistinguishability**: objects with representatives the world's theory cannot
    tell apart (`DTerm.Rel`) — B's `Ind`, the tree's `Canon.Ind`. -/
def gInd {A : VarType} {s : GW hF M₀} (o o' : (gframe hF hM₀).Dom A s) : Prop :=
  ∃ u u' : Canon.DTerm (gw hM₀ s).sys (gw hM₀ s).T A,
    grden hM₀ s u.i (Ctx.Le.refl _) u.t = gfromDom hM₀ A s o ∧
      grden hM₀ s u'.i (Ctx.Le.refl _) u'.t = gfromDom hM₀ A s o' ∧ u.Rel u'

/-- Every object is definable, so it is related to itself. -/
theorem gInd_refl {A : VarType} {s : GW hF M₀} (o : (gframe hF hM₀).Dom A s) : gInd hM₀ o o := by
  obtain ⟨i, a, t, ht⟩ := gdefinable_fromDom hM₀ A s o
  exact ⟨⟨i, a, t⟩, ⟨i, a, t⟩, ht, ht, Canon.DTerm.Rel.refl _⟩

variable {hM₀}

omit [ModalSys.NoB] in
/-- ⭐A realised witness's possible object has its realisation as content here (B's
    `mem_here_real`). -/
theorem gmem_here_real {s : GW hF M₀} {x : VarSymb} (hr : (gw hM₀ s).Realised x) {i : ℕ}
    {X : VarType} (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {A : VarType} {β : Ann A}
    (bd : Term σ ((ctxOf (glat s i)).diaIn x) A β) :
    WFF.here hr.T (Term.mono (gle hM₀ s (le_max_left i hr.data.i₀)) (Term.diatm x ⟨X, hx⟩ bd))
        (grealT hr (Ctx.Le.refl _) ⟨X, hx⟩ bd).2 ∈ (gw hM₀ s).M (max i hr.data.i₀) :=
  Canon.mem_here_datum hr.data (le_max_left _ _) (le_max_right _ _) hx bd

omit [ModalSys.NoB] in
/-- ⭐**A `Here` atom relates the witness's realisation to its term** (B's `rel_here`). -/
theorem grel_here {s : GW hF M₀} {A : VarType} (hT : ModalSys.T = true) {i : ℕ} {x : VarSymb}
    (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {β : Ann A}
    (bd : Term σ ((ctxOf (glat s i)).diaIn x) A β) {a : Ann A}
    (t : Term σ (ctxOf (glat s i)) A a) (hr : (gw hM₀ s).Realised x)
    (hmem : WFF.here hT (Term.diatm x hx bd) t ∈ (gw hM₀ s).M i) :
    (⟨max i hr.data.i₀, _, (grealT hr (Ctx.Le.refl _) hx bd).2⟩ :
      Canon.DTerm (gw hM₀ s).sys (gw hM₀ s).T A).Rel ⟨i, a, t⟩ := by
  obtain ⟨X, hx'⟩ := id hx
  have hk : i ≤ max i hr.data.i₀ := le_max_left _ _
  have ht : WFF.here hT (Term.mono (gle hM₀ s hk) (Term.diatm x hx bd))
      (Term.mono (gle hM₀ s hk) t) ∈ (gw hM₀ s).M (max i hr.data.i₀) :=
    (BWorld.mem_lift hk).mp hmem
  exact (Canon.DTerm.rel_of_coname hT _ (BWorld.mem_T.mpr (gmem_here_real hr hx' bd))
    (BWorld.mem_T.mpr ht)).trans
    (Canon.DTerm.rel_lift (⟨i, a, t⟩ : Canon.DTerm (gw hM₀ s).sys (gw hM₀ s).T _) hk).symm

omit [ModalSys.NoB] in
/-- A term and its lift to a later stage denote alike. -/
theorem grden_lift {s : GW hF M₀} {i K : ℕ} (h : i ≤ K) {A : VarType} {a : Ann A}
    (t : Term σ (ctxOf (glat s i)) A a) :
    grden hM₀ s K (Ctx.Le.refl _) (Term.mono (gle hM₀ s h) t) =
      grden hM₀ s i (Ctx.Le.refl _) t := by
  rw [grden_mono]
  exact grden_congr _ _ _ _ _ _

omit [ModalSys.NoB] in
/-- ⭐The realised content of the witness's own content address is the datum's content (B's
    `rden_realTerm_eta`). -/
theorem grden_grealT_eta {s : GW hF M₀} {x : VarSymb} (hr : (gw hM₀ s).Realised x) {k : ℕ}
    (hx : ∃ X, (ctxOf (glat s k)).ref x = some (.VTypeDia X))
    (hdia : ((ctxOf (glat s k)).diaIn x).ref (.step x .dia) = some hr.data.A) :
    grden hM₀ s _ (Ctx.Le.refl _)
        (grealT hr (Ctx.Le.refl _) hx (Term.eta (.step x .dia) hr.data.A hdia)).2 =
      grden hM₀ s hr.data.i₀ (Ctx.Le.refl _) hr.data.t₀ := by
  have hdecl : (ctxOf (glat s (max k hr.data.i₀))).ref x = some (.VTypeDia hr.data.A) :=
    hr.data.hdeclOf _ (hx.imp fun _ h => (gle hM₀ s (le_max_left _ _)).ref h)
  have hmono : (⟨_, Term.mono (((Ctx.Le.refl _).trans (gle hM₀ s (le_max_left _ _))).diaIn x)
      (Term.eta (.step x .dia) hr.data.A hdia)⟩ : Σ z : Ann hr.data.A,
        Term σ ((ctxOf (glat s (max k hr.data.i₀))).diaIn x) hr.data.A z) =
      ⟨_, Term.eta (.step x .dia) hr.data.A (Ctx.ref_diaIn_of hdecl)⟩ := by
    rw [Term.mono_eta]
  simp only [grealT]
  rw [grden_sigma _ (Canon.Term.realiseAtA_sigma hr.data.hT x hdecl _ hmono),
    grden_sigma _ (Term.realiseAtA_eta hr.data.hT x hdecl
      (Term.mono (gle hM₀ s (le_max_right _ _)) hr.data.t₀)),
    grden_mono]
  exact grden_congr _ _ _ _ _ _

omit [ModalSys.NoB] in
/-- ⭐The content, along the world's own arrow, of the possible object a realised witness names:
    what its datum's content denotes (B's `rden_eta_real`). -/
theorem grden_eta_real {s : GW hF M₀} {x : VarSymb} (hr : (gw hM₀ s).Realised x) {k : ℕ}
    (hdecl : (ctxOf (glat s k)).ref x = some (.VTypeDia hr.data.A)) (hm) :
    (grden hM₀ s k (Ctx.Le.refl _) (Term.eta x (.VTypeDia hr.data.A) hdecl)).c
        ⟨⟨s, ⟨grefl hr.T s⟩⟩, hm⟩ = grden hM₀ s hr.data.i₀ (Ctx.Le.refl _) hr.data.t₀ := by
  refine (grden_diatm_real (Ctx.Le.refl _) x ⟨hr.data.A, hdecl⟩
    (Term.eta (.step x .dia) hr.data.A (Ctx.ref_diaIn_of hdecl)) s (grefl hr.T s) [] rfl hm
    hr).trans ?_
  have h₁ : pTrXK hM₀ s s [] rfl k x ⟨hr.data.A, hdecl⟩
      (Term.mono ((Ctx.Le.refl _).diaIn x)
        (Term.eta (.step x .dia) hr.data.A (Ctx.ref_diaIn_of hdecl))) =
      ⟨_, Term.eta (.step x .dia) hr.data.A (Ctx.ref_diaIn_of hdecl)⟩ := by
    rw [pTrXK_nil, Term.mono_refl]
  exact (grden_sigma _ (grealT_sigma hr _ _ h₁)).trans
    (grden_grealT_eta hr ⟨hr.data.A, hdecl⟩ (Ctx.ref_diaIn_of hdecl))

variable (hM₀)

/-- ⭐**Strong T: every object of a domain is, up to `Ind`, the content along the world's own
    arrow of a possible object** (B's `posRet_exists_canon`): the object is a term's denotation;
    the theory has a `Here` atom for that term about some witness (`BWorld.retW`), which is then
    realised (`datum_of_here`); the witness's η-expansion has the own arrow in its extent, with
    the datum's content there (`grden_eta_real`), and the atom relates that content and the term
    (`grel_here`). -/
theorem gposRet_exists_canon {A : VarType} {s : GW hF M₀} (hT : ModalSys.T = true)
    (hS : ModalSys.TStrong = true) (o : (gframe hF hM₀).Dom A s) :
    ∃ (p : (gframe hF hM₀).Pos A s) (hm : (gframe hF hM₀).reflAcc hT s ∈ (gposEval hM₀ p).1),
      gInd hM₀ ((gposEval hM₀ p).2 ⟨(gframe hF hM₀).reflAcc hT s, hm⟩) o := by
  obtain ⟨i, a', t, ht⟩ := gdefinable_fromDom hM₀ A s o
  obtain ⟨i', hi, y, hy, hmem⟩ := (gw hM₀ s).retW hT hS i t
  have hr : (gw hM₀ s).Realised y :=
    (gw hM₀ s).datum_of_here hT hy (Term.eta (.step y .dia) A (Ctx.ref_diaIn_of hy)) _ hmem
  obtain rfl : hr.data.A = A := by
    have := (hr.data.hdeclOf i' ⟨A, hy⟩).symm.trans hy
    simpa using this
  have hm : (gframe hF hM₀).reflAcc hT s ∈ (grden hM₀ s hr.data.i₀ (Ctx.Le.refl _)
      (Term.eta y (.VTypeDia hr.data.A) hr.data.hd₀)).E :=
    (grden_diatm_mem (Ctx.Le.refl _) y _ _ s (grefl hT s) [] rfl).mpr (Or.inl hr)
  refine ⟨⟨grden hM₀ s hr.data.i₀ (Ctx.Le.refl _) (Term.eta y (.VTypeDia hr.data.A) hr.data.hd₀),
      gdefinable_rden _ _⟩, hm, _, ⟨i', _, Term.mono (gle hM₀ s hi) t⟩, ?_, ?_,
      grel_here hT ⟨_, hy⟩ (Term.eta (.step y .dia) hr.data.A (Ctx.ref_diaIn_of hy)) _ hr hmem⟩
  · have hc : gtoDom hM₀ _ s (grden hM₀ s hr.data.i₀ (Ctx.Le.refl _) hr.data.t₀)
        (gdefinable_rden _ _) =
        (gposEval hM₀ ⟨grden hM₀ s hr.data.i₀ (Ctx.Le.refl _)
          (Term.eta y (.VTypeDia hr.data.A) hr.data.hd₀), gdefinable_rden _ _⟩).2
          ⟨(gframe hF hM₀).reflAcc hT s, hm⟩ :=
      gtoDom_congr (grden_eta_real hr hr.data.hd₀ _).symm _ _
    rw [grden_grealT_eta hr ⟨_, hy⟩ (Ctx.ref_diaIn_of hy), ← hc, gfromDom_toDom]
  · exact (grden_lift hi t).trans ht

end GArrow

end V12M
