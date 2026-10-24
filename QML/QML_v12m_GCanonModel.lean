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

/-- B is off, in both strengths: the growing tree has no arrows back. -/
class ModalSys.NoSym [ModalSys] : Prop where
  noB : ModalSys.B = false
  noBStrong : ModalSys.BStrong = false

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

section Flags

variable [ModalSys.NoT] [ModalSys.NoSym]

omit [ModalSys.NoSym] in
theorem absT (hT : ModalSys.T = true) : False := by
  rw [ModalSys.NoT.noT] at hT
  cases hT

omit [ModalSys.NoT] in
theorem absB (hB : ModalSys.B = true) : False := by
  rw [ModalSys.NoSym.noB] at hB
  cases hB

theorem absShaped (h : ModalSys.shaped = true) : False := by
  simp [ModalSys.shaped, ModalSys.NoT.noT, ModalSys.NoSym.noBStrong] at h

end Flags

variable (hF M₀) in
/-- The root of the tree. -/
def groot : GW hF M₀ := ⟨[], 0, trivial⟩

variable [ModalSys.NoT] [ModalSys.NoSym] (hM₀ : Theory.IsMCS M₀)

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoSym] in
/-- ⭐The growing tree's arrows: strict descendants, composed by appending paths. -/
abbrev garrows : Arrows.{0, 0} σ where
  W := GW hF M₀
  R := GR
  refl := fun hT _ => (absT hT).elim
  trans := fun _ {_ _ _} h₁ h₂ => gtrans h₁ h₂
  refl_trans := fun hT _ _ _ _ => (absT hT).elim
  trans_refl := fun hT _ _ _ _ => (absT hT).elim
  trans_assoc := fun _ _ _ _ _ _ _ _ => rfl

omit [ModalSys.NoT] [ModalSys.NoSym] in
/-- Under D every world has an arrow out: `□⊥` fails, since `D_box` refutes it. -/
theorem gserial (hM₀ : Theory.IsMCS M₀) (hD : ModalSys.D = true) (s : GW hF M₀) :
    ∃ t, Nonempty (GR s t) := by
  have hnot : WFF.box (.bot : WFF σ (ctxOf (glat s 0)).boxIn 0) ∉ (gw hM₀ s).M 0 := fun h =>
    ((gw hM₀ s).mcs 0).bot_not_mem (BWorld.mem_of_provable (Δ := [.box .bot])
      (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact h)
      ⟨Proof.D_box hD (Proof.lookup List.mem_cons_self)⟩)
  obtain ⟨t, ⟨c, hc⟩, -, -⟩ := glex hM₀ s 0 .bot hnot
  exact ⟨t, ⟨⟨[c], List.cons_ne_nil _ _, hc⟩⟩⟩

variable (hF) in
/-- ⭐The canonical frame. -/
noncomputable def gframe : Frame.{0, 0} σ where
  toArrows := garrows (hF := hF) (M₀ := M₀)
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

theorem gposEval_injective {A : VarType} {s : GW hF M₀} :
    Function.Injective (gposEval hM₀ (A := A) (s := s)) := by
  rintro ⟨⟨E, c⟩, hp⟩ ⟨⟨E', c'⟩, hp'⟩ h
  simp only [gposEval] at h
  obtain ⟨rfl, hc⟩ := Sigma.mk.inj_iff.mp h
  have hc' := eq_of_heq hc
  apply Subtype.ext
  exact GRPos.congr_cont (funext fun a => gtoDom_inj (congrFun hc' a))

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
  necExtract hT _ := (absT hT).elim
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
  | _, _, .extract hT, _, _, _ => (absT hT).elim
  | _, _, .dup _, _, _, _ => rfl
  | _, _, .dkeep _, _, _, _ => rfl

/-! ## Strong D -/

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
      obtain ⟨t', ⟨c, hc⟩, hk, -⟩ := glexX hM₀ s j x X hX .top (by
        have e : (WFF.instantiate Ctx.NoSlots.slots (Term.diatm x hx u)
            (WFF.mono ((ctxOf_le_of_suffix ((gw hM₀ s).suf (Nat.zero_le j))).insert (.bnd 0)
              (.VTypeDia .VTypeOne))
              (.dia (.root (.bnd 0)) ⟨.VTypeOne, Ctx.ref_insert_root _ (.bnd 0) _⟩ .top))) =
            WFF.dia x ⟨X, hX⟩ .top := rfl
        rw [← e]
        exact hmem)
      have hR : GR s t' := ⟨[c], List.cons_ne_nil _ _, hc⟩
      refine ⟨⟨grden hM₀ s j (Ctx.Le.refl _) (.diatm x hx u), gdefinable_rden _ _⟩,
        ⟨⟨⟨t', ⟨hR⟩⟩, ?_⟩⟩⟩
      exact (grden_diatm_mem (hM₀ := hM₀) (Ctx.Le.refl _) x hx u t' hR [c] hc).mpr hk

end GArrow

end V12M
