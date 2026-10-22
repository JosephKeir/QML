import QML.QML_v12m_BCanonFunc

/-!
# QML v12m — B's canonical model: the model

The frame of `BData`: its worlds, its symmetric accessibility (so the frame condition for B holds
by construction), serial under D (from `ex` at `□⊥`), the base domains, and as carriers the
definable raw objects.  The model evaluates them as raw objects; the function algebra acts by
`rawEval`.  Strong D's condition comes from its axiom, a Henkin witness and `exX`
(`posSerial_canon`).

⭐`BData.model`: the canonical model.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## Realising a necessary term -/

/-- ⭐**Realising a necessary term, read at the world itself**: the realisation of `□s` is a
    necessary term `□W`, and `W` collapsed is the realisation of `s` collapsed — collapsing
    commutes with the realisation's two substitutions (`Subst.corr_box_self`), and the two
    collapses of `s`'s levels commute (`Term.collapse_collapse`). -/
theorem _root_.V12M.Term.realiseAtA_boxtm {Γ : Ctx} [hp : Γ.Presented] (hT : ModalSys.T = true)
    (x : VarSymb) {A : VarType} (hcA : Γ.ref x = some (.VTypeDia A)) {a₀ : Ann A}
    (t₀ : Term σ Γ A a₀) {T : VarType} {b : Ann T} (s : Term σ (Γ.diaIn x).boxIn T b) :
    ∃ (c : Ann T) (W : Term σ Γ.boxIn T c),
      (⟨_, Term.realiseAtA hT x hcA t₀ (Term.boxtm s)⟩ : Σ d, Term σ Γ (.VTypeBox T) d) =
        ⟨_, Term.boxtm W⟩ ∧
      (⟨_, Term.collapse (Ctx.collapses_boxIn_self hT Γ) W⟩ : Σ d, Term σ Γ T d) =
        ⟨_, Term.realiseAtA hT x hcA t₀
          (Term.collapse (Ctx.collapses_boxIn_self hT (Γ.diaIn x)) s)⟩ := by
  have h₀ : Γ.boxIn (.root (.bnd 0)) = none := (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root
  have hrf : Γ.boxIn.RootFresh (.bnd 0) := (Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)
  refine ⟨_, _, rfl, ?_⟩
  have hok := Subst.ok_single (σ := σ) (r := .bnd 0) (Ctx.Le.refl Γ) (e := .tm t₀) (T := A) rfl
  have hcoh := Subst.coh_single (σ := σ) ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0))
    (Ctx.Le.refl Γ) (e := .tm t₀) (T := A) rfl
  have hokA := Subst.ok_diaAbsA (σ := σ) hcA (hp.not_below hcA rfl)
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).root)
  have hcohA := Subst.coh_diaAbsA (σ := σ) hcA (hp.not_below hcA rfl)
    hp.viewFresh ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).root)
  have hcol : ∀ {a a' : Ann T} {u : Term σ (Γ.boxIn.insert (.bnd 0) A) T a}
      {u' : Term σ (Γ.boxIn.insert (.bnd 0) A) T a'},
      (⟨a, u⟩ : Σ d, Term σ _ T d) = ⟨a', u'⟩ →
      (⟨_, Term.collapse ((Ctx.collapses_boxIn_self hT Γ).insert hrf A) u⟩ :
        Σ d, Term σ (Γ.insert (.bnd 0) A) T d) =
        ⟨_, Term.collapse ((Ctx.collapses_boxIn_self hT Γ).insert hrf A) u'⟩ := by
    intro _ _ _ _ h
    cases h
    rfl
  refine (Term.collapse_subst (Ctx.collapses_boxIn_self hT (Γ.insert (.bnd 0) A))
    (Ctx.collapses_boxIn_self hT Γ) _ _ _ _ hok hcoh (Subst.corr_box_self hT hok) _).trans ?_
  refine sig_subst _ hok hcoh ((Term.collapse_collapse (k := 0) (m := 0) _ _
    (Ctx.collapses_boxIn_self hT (Γ.boxIn.insert (.bnd 0) A))
    ((Ctx.collapses_boxIn_self hT Γ).insert hrf A) _).trans (hcol ?_))
  exact Term.collapse_subst (Ctx.collapses_boxIn_self hT (Γ.diaIn x))
    (Ctx.collapses_boxIn_self hT (Γ.boxIn.insert (.bnd 0) A)) _ _ _ _ hokA hcohA
    (Subst.corr_box_self hT hokA) s

namespace BData

variable [ModalSys.NoFour] (B : BData σ)

/-- Under D every world has an arrow out: `□⊥` fails, since `D_box` refutes it. -/
theorem serial_canon (hD : ModalSys.D = true) (s : B.W) : ∃ t, Nonempty (B.RT s t) := by
  have hnot : WFF.box (.bot : WFF σ ((B.w s).ctx 0).boxIn 0) ∉ (B.w s).M 0 := fun h =>
    ((B.w s).mcs 0).bot_not_mem (BWorld.mem_of_provable (Δ := [.box .bot])
      (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact h)
      ⟨Proof.D_box hD (Proof.lookup List.mem_cons_self)⟩)
  obtain ⟨t, h, _⟩ := B.ex s 0 .bot hnot
  exact ⟨t, ⟨Or.inl h⟩⟩

/-- ⭐The canonical frame. -/
noncomputable def frame : Frame.{0, 0} σ where
  toArrows := B.arrows
  actual := B.actual
  serial := fun hD s => B.serial_canon hD s
  symm := fun _ {_ _} h => ⟨h.elim (fun h => Or.inl (B.symm h)) fun h => Or.inr ⟨h.1, h.2.symm⟩⟩
  homeUnique := fun _ => ⟨fun _ _ => rfl⟩
  D s := (B.w s).D
  Nec A s := {o : B.RDom (.VTypeBox A) s // B.Definable (.VTypeBox A) s o}
  Pos A s := {o : B.RDom (.VTypeDia A) s // B.Definable (.VTypeDia A) s o}
  funcInterp f s args := (B.w s).canonFunc f args
  relInterp r s args := (B.w s).canonRel r args

/-- A definable raw object as a frame object. -/
def toDom : (A : VarType) → (s : B.W) → (o : B.RDom A s) → B.Definable A s o →
    B.frame.Dom A s
  | .Var, _, o, _ => o
  | .VTypeOne, _, _, _ => PUnit.unit
  | .VTypeProd A C, s, o, h =>
      (toDom A s o.1 (definable_fst h), toDom C s o.2 (definable_snd h))
  | .VTypeBox A, s, o, h =>
      (Subtype.mk o h : {o : B.RDom (.VTypeBox A) s // B.Definable (.VTypeBox A) s o})
  | .VTypeDia A, s, o, h =>
      (Subtype.mk o h : {o : B.RDom (.VTypeDia A) s // B.Definable (.VTypeDia A) s o})

/-- A frame object as a raw object. -/
def fromDom : (A : VarType) → (s : B.W) → B.frame.Dom A s → B.RDom A s
  | .Var, _, d => d
  | .VTypeOne, _, _ => PUnit.unit
  | .VTypeProd A C, s, d =>
      (fromDom A s (d : B.frame.Dom A s × B.frame.Dom C s).1,
        fromDom C s (d : B.frame.Dom A s × B.frame.Dom C s).2)
  | .VTypeBox A, s, d =>
      (d : {o : B.RDom (.VTypeBox A) s // B.Definable (.VTypeBox A) s o}).1
  | .VTypeDia A, s, d =>
      (d : {o : B.RDom (.VTypeDia A) s // B.Definable (.VTypeDia A) s o}).1

theorem definable_fromDom : ∀ (A : VarType) (s : B.W) (d : B.frame.Dom A s),
    B.Definable A s (B.fromDom A s d)
  | .Var, _, d => definable_var d
  | .VTypeOne, _, _ => definable_unit _
  | .VTypeProd A C, s, d =>
      definable_pair (definable_fromDom A s (d : B.frame.Dom A s × B.frame.Dom C s).1)
        (definable_fromDom C s (d : B.frame.Dom A s × B.frame.Dom C s).2)
  | .VTypeBox A, s, d => (d : {o : B.RDom (.VTypeBox A) s // B.Definable (.VTypeBox A) s o}).2
  | .VTypeDia A, s, d => (d : {o : B.RDom (.VTypeDia A) s // B.Definable (.VTypeDia A) s o}).2

theorem fromDom_toDom : ∀ (A : VarType) (s : B.W) (o : B.RDom A s) (h : B.Definable A s o),
    B.fromDom A s (B.toDom A s o h) = o
  | .Var, _, _, _ => rfl
  | .VTypeOne, _, _, _ => rfl
  | .VTypeProd A C, s, o, h =>
      Prod.ext (fromDom_toDom A s o.1 (definable_fst h)) (fromDom_toDom C s o.2 (definable_snd h))
  | .VTypeBox _, _, _, _ => rfl
  | .VTypeDia _, _, _, _ => rfl

theorem toDom_fromDom : ∀ (A : VarType) (s : B.W) (d : B.frame.Dom A s),
    B.toDom A s (B.fromDom A s d) (B.definable_fromDom A s d) = d
  | .Var, _, _ => rfl
  | .VTypeOne, _, _ => rfl
  | .VTypeProd A C, s, d =>
      Prod.ext (toDom_fromDom A s (d : B.frame.Dom A s × B.frame.Dom C s).1)
        (toDom_fromDom C s (d : B.frame.Dom A s × B.frame.Dom C s).2)
  | .VTypeBox _, _, _ => rfl
  | .VTypeDia _, _, _ => rfl

variable {B}

theorem toDom_inj {A : VarType} {s : B.W} {o o' : B.RDom A s} {h : B.Definable A s o}
    {h' : B.Definable A s o'} (e : B.toDom A s o h = B.toDom A s o' h') : o = o' := by
  rw [← B.fromDom_toDom A s o h, ← B.fromDom_toDom A s o' h', e]

theorem toDom_congr {A : VarType} {s : B.W} {o o' : B.RDom A s} (e : o = o')
    (h : B.Definable A s o) (h' : B.Definable A s o') : B.toDom A s o h = B.toDom A s o' h' := by
  subst e
  rfl

variable (B)

/-- Evaluation of necessary objects. -/
def necEval {A : VarType} {s : B.W} (n : B.frame.Nec A s) : B.frame.NecSec A s :=
  fun a => B.toDom A a.1 (n.1 a) (definable_box_apply n.2 a)

/-- Evaluation of possible objects. -/
def posEval {A : VarType} {s : B.W} (p : B.frame.Pos A s) : B.frame.PosSec A s :=
  ⟨p.1.1, fun a => B.toDom A a.1.1 (p.1.2 a) (definable_dia_apply p.2 a)⟩

theorem necEval_injective {A : VarType} {s : B.W} :
    Function.Injective (B.necEval (A := A) (s := s)) := by
  intro n n' h
  apply Subtype.ext
  funext a
  exact toDom_inj (congrFun h a)

/-- The function algebra on the carriers. -/
noncomputable def ops : B.frame.Ops where
  necMap g n := ⟨B.rawEval (.boxMap g) _ n.1, definable_rawEval (.boxMap g) n.2⟩
  necPair a b := ⟨B.rawEval (.boxPair _ _) _
      ((a.1, b.1) : B.RDom (.VTypeProd (.VTypeBox _) (.VTypeBox _)) _),
    definable_rawEval (.boxPair _ _) (definable_pair a.2 b.2)⟩
  necUnit := ⟨B.rawEval .boxUnit _ (PUnit.unit : B.RDom .VTypeOne _),
    definable_rawEval .boxUnit (definable_unit _)⟩
  posMap g p := ⟨B.rawEval (.diaMap g) _ p.1, definable_rawEval (.diaMap g) p.2⟩
  posStrength n p := ⟨B.rawEval (.strength _ _) _
      ((n.1, p.1) : B.RDom (.VTypeProd (.VTypeBox _) (.VTypeDia _)) _),
    definable_rawEval (.strength _ _) (definable_pair n.2 p.2)⟩
  necExtract hT n :=
    B.toDom _ _ (B.rawEval (.extract hT) _ n.1) (definable_rawEval (.extract hT) n.2)
  necDup hF _ := (noFour hF).elim

/-- ⭐Evaluating a map on a frame object is evaluating it on the raw object. -/
theorem eval_toDom : ∀ {A C : VarType} (g : GFunc σ A C) (s : B.W) (o : B.RDom A s)
    (h : B.Definable A s o),
    GFunc.eval B.ops g s (B.toDom A s o h) = B.toDom C s (B.rawEval g s o) (definable_rawEval g h)
  | _, _, .id _, _, _, _ => rfl
  | _, _, .comp g f, s, o, h =>
      (congrArg (GFunc.eval B.ops g s) (eval_toDom f s o h)).trans (eval_toDom g s _ _)
  | _, _, .fst, _, _, _ => rfl
  | _, _, .snd, _, _, _ => rfl
  | _, _, .pair f g, s, o, h => Prod.ext (eval_toDom f s o h) (eval_toDom g s o h)
  | _, _, .unit _, _, _, _ => rfl
  | _, _, .func f args, s, o, h =>
      congrArg ((B.w s).canonFunc f) (funext fun k => eval_toDom (args k) s o h)
  | _, _, .boxMap _, _, _, _ => rfl
  | _, _, .boxPair _ _, _, _, _ => rfl
  | _, _, .boxUnit, _, _, _ => rfl
  | _, _, .diaMap _, _, _, _ => rfl
  | _, _, .strength _ _, _, _, _ => rfl
  | _, _, .extract _, _, _, _ => rfl
  | _, _, .dup hF, _, _, _ => (noFour hF).elim

/-- ⭐Evaluation of possible objects, in full: the section and, when shaped, the stored shape. -/
def posFull {A : VarType} {s : B.W} (p : B.frame.Pos A s) :
    B.frame.PosSec A s × (ModalSys.shaped = true → B.CShape s (.VTypeDia A)) :=
  (B.posEval p, p.1.3)

/-- A possible object is its section and, when shaped, its shape. -/
theorem posFull_injective {A : VarType} {s : B.W} :
    Function.Injective (B.posFull (A := A) (s := s)) := by
  rintro ⟨⟨E, c, τ⟩, hp⟩ ⟨⟨E', c', τ'⟩, hp'⟩ h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [posFull] at h₁ h₂
  simp only [posEval] at h₁
  obtain ⟨rfl, hc⟩ := Sigma.mk.inj_iff.mp h₁
  have hc' := eq_of_heq hc
  apply Subtype.ext
  exact RPos.congr_cont (funext fun a => toDom_inj (congrFun hc' a)) (congrFun h₂)

/-- When shaped, a frame object's shape is its raw object's. -/
theorem domShape_toDom (hSh : ModalSys.shaped = true) : ∀ (A : VarType) (s : B.W) (o : B.RDom A s)
    (h : B.Definable A s o),
    Frame.domShape B.necEval (fun q => (B.posFull q).2 hSh) (B.toDom A s o h) = B.rawShape hSh o
  | .Var, _, _, _ => rfl
  | .VTypeOne, _, _, _ => rfl
  | .VTypeProd A C, s, o, h =>
      congrArg₂ Shp.prod (domShape_toDom hSh A s o.1 (definable_fst h))
        (domShape_toDom hSh C s o.2 (definable_snd h))
  | .VTypeBox A, _, o, h =>
      congrArg Shp.box (congrArg Arrows.transposeShp (funext fun a =>
        domShape_toDom hSh A a.1 (o a) (definable_box_apply h a)))
  | .VTypeDia _, _, _, _ => rfl

/-! ## Strong D -/

/-- ⭐Under strong D every world has a possible object of type `𝟙` with a nonempty extent: the
    axiom's Henkin witness is a possible term `◇_x u`, whose extent is `x`'s, which `exX` makes
    nonempty. -/
theorem posSerial_canon (hDS : ModalSys.DStrong = true) (s : B.W) :
    ∃ p : B.frame.Pos .VTypeOne s, Nonempty (B.posEval p).1 := by
  have hax : (WFF.somePoss : WFF σ ((B.w s).ctx 0) 0) ∈ (B.w s).M 0 :=
    BWorld.mem_of_provable (Δ := []) (fun _ h => by simp at h) ⟨Proof.D_ex hDS⟩
  obtain ⟨j, _, _, t, hmem⟩ := (B.w s).exW_term hax
  match t with
  | .diatm x hx u =>
      obtain ⟨X, hX⟩ := hx
      obtain ⟨t', hk, _⟩ := B.exX s j x X hX .top (by
        have e : (WFF.instantiate Ctx.NoSlots.slots (Term.diatm x ⟨X, hX⟩ u)
            (WFF.mono ((ctxOf_le_of_suffix ((B.w s).suf (Nat.zero_le j))).insert (.bnd 0)
              (.VTypeDia .VTypeOne))
              (.dia (.root (.bnd 0)) ⟨.VTypeOne, Ctx.ref_insert_root _ (.bnd 0) _⟩ .top))) =
            WFF.dia x ⟨X, hX⟩ .top := rfl
        rw [← e]
        exact hmem)
      refine ⟨⟨B.rden s j (Ctx.Le.refl _) (.diatm x ⟨X, hX⟩ u), definable_rden _ _⟩,
        ⟨⟨⟨t', ⟨Or.inl (B.kdR hk)⟩⟩, Or.inl ⟨X, B.kd_lb hk⟩⟩⟩⟩

/-! ## Indistinguishability -/

/-- ⭐**Canonical indistinguishability**: objects with representatives the world's theory cannot
    tell apart (`DTerm.Rel`: interchangeable in every slot formula, at every later stage) — the
    tree's `Canon.Ind`.  Strong B once needed a smaller relation (§11.16: a negative `Back` atom at
    a `◇`-typed content had to find a return related to nothing); with "comes back as" a model
    primitive (`Model.Ret`, §11.20) every use of `Ind` asks only that related objects be
    interchangeable, so the equivalence serves. -/
def Ind {A : VarType} {s : B.W} (o o' : B.frame.Dom A s) : Prop :=
  ∃ u u' : Canon.DTerm (B.w s).sys (B.w s).T A,
    B.rden s u.i (Ctx.Le.refl _) u.t = B.fromDom A s o ∧
      B.rden s u'.i (Ctx.Le.refl _) u'.t = B.fromDom A s o' ∧ u.Rel u'

/-- Every object is definable, so it is related to itself. -/
theorem Ind_refl {A : VarType} {s : B.W} (o : B.frame.Dom A s) : B.Ind o o := by
  obtain ⟨i, a, t, ht⟩ := B.definable_fromDom A s o
  exact ⟨⟨i, a, t⟩, ⟨i, a, t⟩, ht, ht, Canon.DTerm.Rel.refl _⟩

variable {B} in
/-- ⭐A realised witness's possible object has its realisation as content here: from the datum's
    atom, `here_beta` with the body abstracted, and the round trip (`Canon.mem_here_datum`). -/
theorem mem_here_real {s : B.W} {x : VarSymb} (hr : (B.w s).Realised x) {i : ℕ}
    {X : VarType} (hx : ((B.w s).ctx i).ref x = some (.VTypeDia X)) {A : VarType} {β : Ann A}
    (bd : Term σ (((B.w s).ctx i).diaIn x) A β) :
    WFF.here hr.T (Term.mono ((B.w s).le (le_max_left i hr.data.i₀)) (Term.diatm x ⟨X, hx⟩ bd))
        (B.realTerm hr (Ctx.Le.refl _) ⟨X, hx⟩ bd).2 ∈ (B.w s).M (max i hr.data.i₀) :=
  Canon.mem_here_datum hr.data (le_max_left _ _) (le_max_right _ _) hx bd

variable {B} in
/-- ⭐**A `Here` atom relates the witness's realisation to its term**: both co-name the witness's
    content (`mem_here_real`, `DTerm.rel_of_coname`). -/
theorem rel_here {s : B.W} {A : VarType} (hT : ModalSys.T = true) {i : ℕ} {x : VarSymb}
    (hx : ∃ X, ((B.w s).ctx i).ref x = some (.VTypeDia X)) {β : Ann A}
    (bd : Term σ (((B.w s).ctx i).diaIn x) A β) {a : Ann A} (t : Term σ ((B.w s).ctx i) A a)
    (hr : (B.w s).Realised x) (hmem : WFF.here hT (Term.diatm x hx bd) t ∈ (B.w s).M i) :
    (⟨max i hr.data.i₀, _, (B.realTerm hr (Ctx.Le.refl _) hx bd).2⟩ :
      Canon.DTerm (B.w s).sys (B.w s).T A).Rel ⟨i, a, t⟩ := by
  obtain ⟨X, hx'⟩ := id hx
  have hk : i ≤ max i hr.data.i₀ := le_max_left _ _
  have ht : WFF.here hT (Term.mono ((B.w s).le hk) (Term.diatm x hx bd))
      (Term.mono ((B.w s).le hk) t) ∈ (B.w s).M (max i hr.data.i₀) :=
    (BWorld.mem_lift hk).mp hmem
  exact (Canon.DTerm.rel_of_coname hT _ (BWorld.mem_T.mpr (mem_here_real hr hx' bd))
    (BWorld.mem_T.mpr ht)).trans
    (Canon.DTerm.rel_lift (⟨i, a, t⟩ : Canon.DTerm (B.w s).sys (B.w s).T _) hk).symm

variable {B} in
/-- A term and its lift to a later stage denote alike. -/
theorem rden_lift {s : B.W} {i K : ℕ} (h : i ≤ K) {A : VarType} {a : Ann A}
    (t : Term σ ((B.w s).ctx i) A a) :
    B.rden s K (Ctx.Le.refl _) (Term.mono ((B.w s).le h) t) = B.rden s i (Ctx.Le.refl _) t := by
  rw [rden_mono]
  exact rden_congr _ _ _ _ _ _

/-! ## Strong B: "comes back as" -/

/-- A carrier's round-trip data on the canonical frame (`Model.carrierData`). -/
def cData : (L : BLeg) → {A : VarType} → {s : B.W} → B.frame.Dom (L.carrier A) s →
    Σ S : Set (B.frame.Acc s), (a : S) → (b : B.frame.Acc a.1.1) → B.frame.Dom A b.1
  | .nec, A, s, c =>
      ⟨Set.univ, fun a b => B.necEval (B.necEval (c : B.frame.Nec (.VTypeBox A) s) a.1) b⟩
  | .pos, A, _, c =>
      ⟨(B.posEval (c : B.frame.Pos (.VTypeBox A) _)).1,
        fun a b => B.necEval ((B.posEval (c : B.frame.Pos (.VTypeBox A) _)).2 a) b⟩

/-- ⭐**Canonical "comes back as"** (docs §11.20): at a `◇`-free content, the round trip; and
    what a `Back` atom of the theory says — round-trip data that are a carrier term's, and the
    value term's denotation. -/
def Ret {A : VarType} {s : B.W} (S : Set (B.frame.Acc s))
    (val : (a : S) → (b : B.frame.Acc a.1.1) → B.frame.Dom A b.1) (o : B.frame.Dom A s) :
    Prop :=
  (A.diaFree = true ∧ Nonempty S ∧ ∀ a : S, ∃ r : B.RT a.1.1 s, B.Ind (val a ⟨s, ⟨r⟩⟩) o) ∨
  ∃ (hS : ModalSys.BStrong = true) (i : ℕ) (L : BLeg) (c : Ann (L.carrier A))
    (ct : Term σ ((B.w s).ctx i) (L.carrier A) c) (a : Ann A) (t : Term σ ((B.w s).ctx i) A a),
    WFF.back hS L ct t ∈ (B.w s).M i ∧
    B.cData L (B.toDom _ s (B.rden s i (Ctx.Le.refl _) ct) (definable_rden _ _)) = ⟨S, val⟩ ∧
    B.toDom A s (B.rden s i (Ctx.Le.refl _) t) (definable_rden _ _) = o

variable {B} in
/-- A `Back` atom's leg is nonempty along the plain leg: `back_ne` gives `◇⊤`, and `ex` an arrow. -/
theorem exists_R_of_dia_top {s : B.W} {i : ℕ}
    (h : (OutLeg.nec : OutLeg ((B.w s).ctx i)).dia (.top : WFF σ _ 0) ∈ (B.w s).M i) :
    ∃ k, B.R s k := by
  obtain ⟨k, hk, _⟩ := B.ex s i (WFF.neg .top) (((B.w s).mcs i).neg_mem_iff.mp h)
  exact ⟨k, hk⟩

variable {B} in
/-- Under T a world has a network arrow: `◇⊤` holds by `T`, and `ex` gives an arrow. -/
theorem exists_R_of_T (hT : ModalSys.T = true) (s : B.W) : ∃ k, B.R s k := by
  have hdia : (OutLeg.nec : OutLeg ((B.w s).ctx 0)).dia (.top : WFF σ _ 0) ∈ (B.w s).M 0 :=
    BWorld.mem_of_provable (Δ := []) (fun _ h => absurd h List.not_mem_nil)
      ⟨Proof.imp_intro (Proof.imp_elim (Proof.T_box hT (Proof.lookup List.mem_cons_self))
        Proof.top_intro)⟩
  exact exists_R_of_dia_top hdia

variable {B} in
/-- Under T a realised witness labels a network arrow: its `Here` atom (`mem_here_real`) gives
    `◇_y ⊤` (`here_intro`), and `exX` an arrow labelled `y` (§11.21, risk 3). -/
theorem exists_kd_of_realised {s : B.W} {y : VarSymb} (hr : (B.w s).Realised y) {i : ℕ}
    {Y : VarType} (hy : ((B.w s).ctx i).ref y = some (.VTypeDia Y)) :
    ∃ k, B.kd s k = some (y, Y) := by
  have hyK : ((B.w s).ctx (max i hr.data.i₀)).ref y = some (.VTypeDia Y) :=
    ((B.w s).le (le_max_left _ _)).ref hy
  have hh := mem_here_real hr hy (Term.unit : Term σ (((B.w s).ctx i).diaIn y) .VTypeOne _)
  have hdia : WFF.dia y ⟨Y, hyK⟩ (.top : WFF σ _ 0) ∈ (B.w s).M (max i hr.data.i₀) :=
    BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hh)
      ⟨Proof.here_intro hr.T y ⟨Y, hyK⟩ _ Term.unit .top (Proof.lookup List.mem_cons_self)
        Proof.top_intro⟩
  obtain ⟨k, hk, _⟩ := B.exX s _ y Y hyK .top hdia
  exact ⟨k, hk⟩

variable {B} in
/-- ⭐**`Back` at the own arrow** (`back_here`): under T a row-1 carrier read here twice is
    interchangeable with its value, at every later stage (`¬φ` gives the converse). -/
theorem back_here_rel (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true) {s : B.W}
    {i : ℕ} {A : VarType} {a₀ : Ann A} (bd : Term σ ((B.w s).ctx i).boxIn.boxIn A a₀)
    {a : Ann A} (t : Term σ ((B.w s).ctx i) A a)
    (hmem : WFF.back hS .nec (Term.boxtm (Term.boxtm bd)) t ∈ (B.w s).M i) :
    Canon.DTerm.Rel (S := (B.w s).sys) (T := (B.w s).T)
      ⟨i, _, Term.collapse (Ctx.collapses_boxIn_self hT _)
        (Term.collapse (Ctx.collapses_boxIn_self hT _) bd)⟩ ⟨i, a, t⟩ := by
  intro j hj hj' χ
  have hm := (B.w s).sub hj _ hmem
  have key : ∀ φ : WFF σ (((B.w s).ctx j).insert (.bnd 0) A) 1,
      WFF.instantiate Ctx.NoSlots.slots (Term.mono ((B.w s).le hj) t) φ ∈ (B.w s).M j →
      WFF.instantiate Ctx.NoSlots.slots (Term.mono ((B.w s).le hj)
        (Term.collapse (Ctx.collapses_boxIn_self hT _)
          (Term.collapse (Ctx.collapses_boxIn_self hT _) bd))) φ ∈ (B.w s).M j := by
    intro φ hφ
    have h := BWorld.mem_of_provable (Δ := [_, _]) (fun ψ hψ => by
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact hm
        · rw [List.mem_singleton.mp hψ]; exact hφ)
      ⟨Proof.back_here hS hT (Term.mono ((B.w s).le hj).boxIn.boxIn bd)
        (Term.mono ((B.w s).le hj) t) φ (Proof.lookup List.mem_cons_self)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩
    rwa [Term.collapse_mono (Ctx.collapses_boxIn_self hT ((B.w s).ctx i).boxIn)
        (Ctx.collapses_boxIn_self hT ((B.w s).ctx j).boxIn) ((B.w s).le hj).boxIn.boxIn
        ((B.w s).le hj).boxIn,
      Term.collapse_mono (Ctx.collapses_boxIn_self hT ((B.w s).ctx i))
        (Ctx.collapses_boxIn_self hT ((B.w s).ctx j)) ((B.w s).le hj).boxIn
        ((B.w s).le hj)] at h
  change WFF.instantiate _ (Term.mono ((B.w s).le hj) _) χ ∈ (B.w s).M j ↔
    WFF.instantiate _ (Term.mono ((B.w s).le hj') t) χ ∈ (B.w s).M j
  refine ⟨fun h => ?_, key χ⟩
  by_contra hn
  exact ((B.w s).mcs j).neg_mem_iff.mp (key χ.neg (((B.w s).mcs j).neg_mem_iff.mpr hn)) h

variable {B} in
/-- ⭐**`Back` at the own arrow, along `◇_y`** (`back_hereX`): under T, with `y` realised, the
    realisation of a row-2 carrier's body collapsed (its `Here` atom, `mem_here_real`) is
    interchangeable with the value, at every later stage. -/
theorem back_hereX_rel (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true) {s : B.W}
    {i : ℕ} {y : VarSymb} {Y : VarType} (hY : ((B.w s).ctx i).ref y = some (.VTypeDia Y))
    {A : VarType} {a₀ : Ann A} (bd : Term σ (((B.w s).ctx i).diaIn y).boxIn A a₀) {a : Ann A}
    (t : Term σ ((B.w s).ctx i) A a)
    (hmem : WFF.back hS .pos (Term.diatm y ⟨Y, hY⟩ (Term.boxtm bd)) t ∈ (B.w s).M i)
    (hr : (B.w s).Realised y) :
    Canon.DTerm.Rel (S := (B.w s).sys) (T := (B.w s).T)
      ⟨max i hr.data.i₀, _, (B.realTerm hr (Ctx.Le.refl _) ⟨Y, hY⟩
        (Term.collapse (Ctx.collapses_boxIn_self hT _) bd)).2⟩ ⟨i, a, t⟩ := by
  set K := max i hr.data.i₀
  have hh := mem_here_real hr hY (Term.collapse (Ctx.collapses_boxIn_self hT _) bd)
  intro j hj hj' χ
  have hm := (B.w s).sub hj' _ hmem
  have hhj := (B.w s).sub hj _ hh
  have hyj : ((B.w s).ctx j).ref y = some (.VTypeDia Y) := ((B.w s).le hj').ref hY
  have key : ∀ φ : WFF σ (((B.w s).ctx j).insert (.bnd 0) A) 1,
      WFF.instantiate Ctx.NoSlots.slots (Term.mono ((B.w s).le hj') t) φ ∈ (B.w s).M j →
      WFF.instantiate Ctx.NoSlots.slots (Term.mono ((B.w s).le hj)
        (B.realTerm hr (Ctx.Le.refl _) ⟨Y, hY⟩
          (Term.collapse (Ctx.collapses_boxIn_self hT _) bd)).2) φ ∈ (B.w s).M j := by
    intro φ hφ
    have hhere : WFF.here hT (Term.diatm y ⟨Y, hyj⟩
        (Term.collapse (Ctx.collapses_boxIn_self hT (((B.w s).ctx j).diaIn y))
          (Term.mono (((B.w s).le hj').diaIn y).boxIn bd)))
        (Term.mono ((B.w s).le hj) (B.realTerm hr (Ctx.Le.refl _) ⟨Y, hY⟩
          (Term.collapse (Ctx.collapses_boxIn_self hT _) bd)).2) ∈ (B.w s).M j := by
      rw [Term.collapse_mono (Ctx.collapses_boxIn_self hT (((B.w s).ctx i).diaIn y))
        (Ctx.collapses_boxIn_self hT (((B.w s).ctx j).diaIn y)) (((B.w s).le hj').diaIn y).boxIn
        (((B.w s).le hj').diaIn y)]
      have hhj' : WFF.here hT (Term.mono ((B.w s).le hj) (Term.mono ((B.w s).le
          (le_max_left i hr.data.i₀)) (Term.diatm y ⟨Y, hY⟩
            (Term.collapse (Ctx.collapses_boxIn_self hT _) bd))))
          (Term.mono ((B.w s).le hj) (B.realTerm hr (Ctx.Le.refl _) ⟨Y, hY⟩
            (Term.collapse (Ctx.collapses_boxIn_self hT _) bd)).2) ∈ (B.w s).M j := hhj
      rw [Term.mono_mono] at hhj'
      exact hhj'
    exact BWorld.mem_of_provable (Δ := [_, _, _]) (fun ψ hψ => by
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact hm
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact hhere
        · rw [List.mem_singleton.mp hψ]; exact hφ)
      ⟨Proof.back_hereX hS hT y ⟨Y, hyj⟩ (Term.mono (((B.w s).le hj').diaIn y).boxIn bd)
        (Term.mono ((B.w s).le hj') t) _ φ (Proof.lookup List.mem_cons_self)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
        (Proof.lookup (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
  change WFF.instantiate _ (Term.mono ((B.w s).le hj) _) χ ∈ (B.w s).M j ↔
    WFF.instantiate _ (Term.mono ((B.w s).le hj') t) χ ∈ (B.w s).M j
  refine ⟨fun h => ?_, key χ⟩
  by_contra hn
  exact ((B.w s).mcs j).neg_mem_iff.mp (key χ.neg (((B.w s).mcs j).neg_mem_iff.mpr hn)) h

variable {B} in
/-- ⭐**The realised content of a necessary term, read along the world's own arrow**: the
    realisation of its body collapsed (`Term.realiseAtA_boxtm`, `rden_boxtm_self`). -/
theorem rden_realTerm_boxtm_self {s : B.W} {x : VarSymb} (hr : (B.w s).Realised x) {Γ : Ctx}
    {i : ℕ} (e : Γ.Le ((B.w s).ctx i)) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType}
    {a : Ann A} (bd : Term σ (Γ.diaIn x).boxIn A a) (rk : B.RT s s) (hb : ¬ B.R s s) :
    B.rden s _ (Ctx.Le.refl _) (B.realTerm hr e hx (Term.boxtm bd)).2 ⟨s, ⟨rk⟩⟩ =
      B.rden s _ (Ctx.Le.refl _) (B.realTerm hr e hx
        (Term.collapse (Ctx.collapses_boxIn_self hr.T _) bd)).2 := by
  have hle := (e.trans ((B.w s).le (le_max_left i hr.data.i₀))).diaIn x
  have hdecl : ((B.w s).ctx (max i hr.data.i₀)).ref x = some (.VTypeDia hr.data.A) :=
    hr.data.hdeclOf _ (hx.imp fun _ h => ((B.w s).le (le_max_left _ _)).ref (e.ref h))
  obtain ⟨c, W, h1, h2⟩ := Term.realiseAtA_boxtm hr.data.hT x hdecl
    (Term.mono ((B.w s).le (le_max_right _ _)) hr.data.t₀) (Term.mono hle.boxIn bd)
  change B.rden s _ (Ctx.Le.refl _) (⟨_, Term.realiseAtA hr.data.hT x hdecl _
    (Term.boxtm (Term.mono hle.boxIn bd))⟩ : Σ d, Term σ _ (.VTypeBox A) d).2 ⟨s, ⟨rk⟩⟩ =
    B.rden s _ (Ctx.Le.refl _) (⟨_, Term.realiseAtA hr.data.hT x hdecl _
      (Term.mono hle (Term.collapse (Ctx.collapses_boxIn_self hr.T _) bd))⟩ :
        Σ d, Term σ _ A d).2
  rw [rden_sigma _ h1, rden_boxtm_self _ _ ⟨s, ⟨rk⟩⟩ hb]
  refine (rden_congr _ _ _ _ _ (Ctx.Le.refl _)).trans ((rden_sigma _ h2).trans ?_)
  refine rden_sigma _ (Canon.Term.realiseAtA_sigma hr.data.hT x hdecl _ ?_)
  exact congrArg (Sigma.mk _) (Term.collapse_mono (Ctx.collapses_boxIn_self hr.T (Γ.diaIn x))
    (Ctx.collapses_boxIn_self hr.data.hT _) hle.boxIn hle bd)

/-- ⭐**What comes back makes the round trip** (`Model.Ret_fwd`): an atom's leg is nonempty
    (`back_ne`), and along each of its arrows the carrier read out and home again is related to the
    value (`backRel`, `backRelX`). -/
theorem ret_fwd (_hS : ModalSys.BStrong = true) {A : VarType} {s : B.W} {S : Set (B.frame.Acc s)}
    {val : (a : S) → (b : B.frame.Acc a.1.1) → B.frame.Dom A b.1} {o : B.frame.Dom A s}
    (h : B.Ret S val o) :
    Nonempty S ∧ ∀ a : S, ∃ r : B.RT a.1.1 s, B.Ind (val a ⟨s, ⟨r⟩⟩) o := by
  rcases h with ⟨-, h⟩ | ⟨hS', i, L, c, ct, a, t, hmem, hdata, rfl⟩
  · exact h
  revert c ct hmem hdata
  cases L with
  | nec =>
      intro c ct
      cases ct with
      | boxtm u =>
          cases u with
          | boxtm bd =>
              intro hmem hdata
              cases hdata
              have hdia : (OutLeg.nec : OutLeg ((B.w s).ctx i)).dia (.top : WFF σ _ 0) ∈
                  (B.w s).M i :=
                BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by
                  rw [List.mem_singleton.mp hψ]; exact hmem)
                  ⟨Proof.back_ne hS' .nec bd t (Proof.lookup List.mem_cons_self)⟩
              obtain ⟨k, hk⟩ := exists_R_of_dia_top hdia
              refine ⟨⟨⟨⟨k, ⟨Or.inl hk⟩⟩, Set.mem_univ _⟩⟩, fun ⟨⟨k, ⟨rk⟩⟩, _⟩ => ?_⟩
              by_cases hk : B.R s k
              swap
              · -- the own arrow (`back_here`)
                obtain ⟨hT, rfl⟩ := self_of_not_R (a := ⟨k, ⟨rk⟩⟩) hk
                refine ⟨rk, _, ⟨i, a, t⟩, ?_, (fromDom_toDom _ _ _ _ _).symm,
                  back_here_rel hS' hT bd t hmem⟩
                change _ = B.fromDom A s (B.toDom A s ((B.rden s i (Ctx.Le.refl _)
                  (Term.boxtm (Term.boxtm bd))) ⟨s, ⟨rk⟩⟩ ⟨s, ⟨rk⟩⟩) _)
                rw [fromDom_toDom, rden_boxtm_self _ _ ⟨s, ⟨rk⟩⟩ hk]
                erw [rden_boxtm_self _ _ ⟨s, ⟨rk⟩⟩ hk]
                exact (rden_congr _ _ _ _ _ _).trans
                  (rden_sigma _ (Term.collapse_collapse (k := 0) (m := 0) _ _ _ _ bd)).symm
              refine ⟨Or.inl (B.symm hk), _, ⟨i, a, t⟩, ?_, (fromDom_toDom _ _ _ _ _).symm,
                B.backRel hS' bd t hmem hk⟩
              change _ = B.fromDom A s (B.toDom A s ((B.rden s i (Ctx.Le.refl _)
                (Term.boxtm (Term.boxtm bd))) ⟨k, ⟨rk⟩⟩ ⟨s, ⟨Or.inl (B.symm hk)⟩⟩) _)
              rw [fromDom_toDom, rden_boxtm_net _ _ _ hk]
              exact (rden_boxtm_net _ _ _ (B.symm hk)).symm
  | pos =>
      intro c ct
      cases ct with
      | diatm y hy u =>
          cases u with
          | boxtm bd =>
              intro hmem hdata
              cases hdata
              obtain ⟨Y, hY⟩ := hy
              have hdia : WFF.dia y ⟨Y, hY⟩ (.top : WFF σ _ 0) ∈ (B.w s).M i :=
                BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by
                  rw [List.mem_singleton.mp hψ]; exact hmem)
                  ⟨Proof.back_ne hS' (.pos y ⟨Y, hY⟩) bd t (Proof.lookup List.mem_cons_self)⟩
              obtain ⟨k, hk, _⟩ := B.exX s i y Y hY .top hdia
              refine ⟨⟨⟨⟨k, ⟨Or.inl (B.kdR hk)⟩⟩, Or.inl ⟨Y, B.kd_lb hk⟩⟩⟩,
                fun ⟨⟨k, ⟨rk⟩⟩, hm⟩ => ?_⟩
              by_cases hR : B.R s k
              swap
              · -- the own arrow, `y` realised (`back_hereX`)
                obtain ⟨hT, rfl⟩ := self_of_not_R (a := ⟨k, ⟨rk⟩⟩) hR
                have hr : (B.w s).Realised y :=
                  (mem_extent_self (x := y) (a := ⟨s, ⟨rk⟩⟩) hm
                    (fun ⟨_, hX⟩ => hR (B.lbR hX))).2
                refine ⟨rk, ⟨max i hr.data.i₀, _, (B.realTerm hr (Ctx.Le.refl _) ⟨Y, hY⟩
                  (Term.collapse (Ctx.collapses_boxIn_self hT _) bd)).2⟩, ⟨i, a, t⟩, ?_,
                  (fromDom_toDom _ _ _ _ _).symm, back_hereX_rel hS' hT hY bd t hmem hr⟩
                change _ = B.fromDom A s (B.toDom A s (((B.rden s i (Ctx.Le.refl _)
                  (Term.diatm y ⟨_, hY⟩ (Term.boxtm bd))).2 ⟨⟨s, ⟨rk⟩⟩, hm⟩) ⟨s, ⟨rk⟩⟩) _)
                rw [fromDom_toDom, rden_diatm_self _ _ _ ⟨⟨s, ⟨rk⟩⟩, hm⟩
                  (fun ⟨_, hX⟩ => hR (B.lbR hX))]
                exact (rden_realTerm_boxtm_self hr _ _ bd rk hR).symm
              have hk : ∃ X, B.lb s k y = some X := by
                rcases hm with hm | hm
                · exact hm
                · exact absurd hR hm.1
              obtain ⟨X, hkX⟩ := hk
              obtain rfl := B.lb_hxX hkX i Y hY
              refine ⟨Or.inl (B.symm hR), _, ⟨i, a, t⟩, ?_, (fromDom_toDom _ _ _ _ _).symm,
                B.backRelX hS' hY bd t hmem hkX⟩
              change _ = B.fromDom A s (B.toDom A s (((B.rden s i (Ctx.Le.refl _)
                (Term.diatm y ⟨_, hY⟩ (Term.boxtm bd))).2 ⟨⟨k, ⟨rk⟩⟩, hm⟩)
                ⟨s, ⟨Or.inl (B.symm hR)⟩⟩) _)
              rw [fromDom_toDom, rden_diatm_net _ _ _ ⟨⟨k, ⟨rk⟩⟩, hm⟩ ⟨_, hkX⟩]
              exact (rden_boxtm_net _ _ _ (B.symm hR)).symm

omit [ModalSys.NoFour] in
/-- Filling the carrier slot of a row-1 `Back` atom. -/
theorem WFF.instantiate_backAt_slot {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    {A : VarType} {a : Ann A} (t : Term σ Γ A a) {b : Ann (.VTypeBox (.VTypeBox A))}
    (u : Term σ Γ (.VTypeBox (.VTypeBox A)) b) :
    WFF.instantiate (d := 0) Ctx.NoSlots.slots u
        (WFF.back hS .nec (Term.eta (.root (.bnd 0)) (.VTypeBox (.VTypeBox A))
            (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeBox (.VTypeBox A))))
          (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root _) t)) =
      WFF.back hS .nec u t := by
  rw [WFF.instantiate, WFF.substRoot]
  refine WFF.back_congr hS .nec ?_ ?_
  · exact Term.subst_eta_tm _ _ _ (.VTypeBox (.VTypeBox A)) (.root (.bnd 0)) _ u
      (Subst.at_single_root _ _)
  · refine (congrArg (Sigma.mk _) (Term.subst_mono _ _ _ _ t)).trans ?_
    refine ((Term.subst_ren (Ctx.Le.refl Γ) _ _ _ ?_ t).trans
      (congrArg (Sigma.mk _) (Term.mono_refl _ t)))
    intro v T hv
    exact Subst.single_at_ne
      (Ctx.ref_rt_ne ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) hv)

/-- `∃c:□□A. Back c t`: some carrier comes back as `t` (`B_strong`'s formula). -/
abbrev WFF.backEx {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) {A : VarType}
    {a : Ann A} (t : Term σ Γ A a) : WFF σ Γ 0 :=
  .ex (.VTypeBox (.VTypeBox A)) (WFF.back hS .nec
    (Term.eta (.root (.bnd 0)) (.VTypeBox (.VTypeBox A))
      (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeBox (.VTypeBox A))))
    (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root _) t))

omit [ModalSys.NoFour] in
/-- ⭐`◇⊤ ⊢ ∃c:□□A. Back c t`, from `B_strong` by `∃`-introduction at its fresh carrier. -/
def Proof.backEx {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
    {A : VarType} {a : Ann A} (t : Term σ Γ A a) (c : ℕ) (hc : Γ.RootFresh (.free c))
    (h : Proof σ Γ Δ ((OutLeg.nec : OutLeg Γ).dia .top)) : Proof σ Γ Δ (WFF.backEx hS t) := by
  refine Proof.B_strong hS t c hc h ?_
  refine Proof.ex_intro (.VTypeBox (.VTypeBox A))
    (Term.eta (.root (.free c)) _ (Ctx.ref_insert_root Γ (.free c) _)) ?_
  refine Proof.conv ?_ (Proof.lookup List.mem_cons_self)
  refine Eq.symm ((congrArg (WFF.instantiate _ _) ?_).trans
    (WFF.instantiate_backAt_slot hS (Term.weaken hc.root _ t) _))
  refine WFF.back_congr' hS .nec (Term.mono_eta _ _ _ _) ?_
  simp only [Term.weaken, Term.mono_mono]

/-- ⭐**Every object comes back** (`Model.backRet_exists`): on a way out the theory has `◇⊤`, so
    `∃c. Back c t` (`Proof.backEx`); Henkin witnessing names the carrier. -/
theorem backRet_exists_canon (hS : ModalSys.BStrong = true) {A : VarType} {s : B.W}
    (hne : Nonempty (B.frame.Acc s)) (o : B.frame.Dom A s) :
    ∃ c : B.frame.Nec (.VTypeBox A) s,
      B.Ret (Set.univ : Set (B.frame.Acc s)) (fun a b => B.necEval (B.necEval c a.1) b) o := by
  obtain ⟨i, a, t, ht⟩ := B.definable_fromDom A s o
  obtain ⟨k, hk⟩ : ∃ k, B.R s k := by
    obtain ⟨⟨k, ⟨rk⟩⟩⟩ := hne
    rcases rk with hk | ⟨hT, -⟩
    · exact ⟨k, hk⟩
    · exact exists_R_of_T hT s
  have hdia : (OutLeg.nec : OutLeg ((B.w s).ctx i)).dia (.top : WFF σ _ 0) ∈ (B.w s).M i := by
    refine ((B.w s).mcs i).neg_mem_iff.mpr fun hbox => ?_
    exact ((B.w k).mcs _).neg_mem_iff.mp (B.tr hk i _ hbox) ((B.w k).mcs _).top_mem
  have hex : WFF.backEx hS t ∈ (B.w s).M i :=
    BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hdia)
      ⟨Proof.backEx hS t _ (ctxOf_fresh le_rfl) (Proof.lookup List.mem_cons_self)⟩
  obtain ⟨j, hij, cb, c, hm⟩ := (B.w s).exW_term hex
  have hm' : WFF.back hS .nec c (Term.mono ((B.w s).le hij) t) ∈ (B.w s).M j := by
    convert hm using 1
    refine Eq.symm ((congrArg (WFF.instantiate _ _) ?_).trans
      (WFF.instantiate_backAt_slot hS (Term.mono ((B.w s).le hij) t) _))
    refine WFF.back_congr' hS .nec (Term.mono_eta _ _ _ _) ?_
    simp only [Term.mono_mono]
  refine ⟨⟨B.rden s j (Ctx.Le.refl _) c, definable_rden _ _⟩,
    Or.inr ⟨hS, j, .nec, cb, c, a, Term.mono ((B.w s).le hij) t, hm', rfl, ?_⟩⟩
  exact (toDom_congr ((rden_lift hij t).trans ht) _ _).trans (B.toDom_fromDom A s o)

/-! ## Strong T: every object is the content of a possible object here -/

variable {B} in
/-- ⭐The content, along a world's own arrow, of the possible object a realised witness names:
    what its datum's content denotes. -/
theorem rden_eta_real {s : B.W} {x : VarSymb} (hr : (B.w s).Realised x) {k : ℕ}
    (hdecl : ((B.w s).ctx k).ref x = some (.VTypeDia hr.data.A)) (hm) :
    (B.rden s k (Ctx.Le.refl _) (Term.eta x (.VTypeDia hr.data.A) hdecl)).2
        ⟨⟨s, ⟨Or.inr ⟨hr.T, rfl⟩⟩⟩, hm⟩ = B.rden s hr.data.i₀ (Ctx.Le.refl _) hr.data.t₀ :=
  (rden_diatm_self (Ctx.Le.refl _) ⟨hr.data.A, hdecl⟩
    (Term.eta (.step x .dia) hr.data.A (Ctx.ref_diaIn_of hdecl)) ⟨_, hm⟩
    (fun ⟨_, hk⟩ => B.irrefl s (B.lbR hk))).trans
    (rden_realTerm_eta hr (Ctx.Le.refl _) ⟨hr.data.A, hdecl⟩ (Ctx.ref_diaIn_of hdecl) _ _)

/-- ⭐**Every object of a domain is, up to `Ind`, the content along the world's own arrow of a
    possible object** — the tree's `Canon.posRet_exists_canon`, at every type.  The object is some
    term's denotation; the theory has a `Here` atom for that term about some witness
    (`BWorld.retW`), which makes the witness realised (`BWorld.datum_of_here`); the witness's
    η-expansion has the own arrow in its extent, with the datum's content there (`rden_eta_real`);
    and the atom relates that content and the term (`rel_here`), which is what `Ind` asks. -/
theorem posRet_exists_canon {A : VarType} {s : B.W} (hT : ModalSys.T = true)
    (hS : ModalSys.TStrong = true) (o : B.frame.Dom A s) :
    ∃ (p : B.frame.Pos A s) (hm : B.frame.reflAcc hT s ∈ (B.posEval p).1),
      B.Ind ((B.posEval p).2 ⟨B.frame.reflAcc hT s, hm⟩) o := by
  obtain ⟨i, a', t, ht⟩ := B.definable_fromDom A s o
  obtain ⟨i', hi, y, hy, hmem⟩ := (B.w s).retW hT hS i t
  have hr : (B.w s).Realised y :=
    (B.w s).datum_of_here hT hy (Term.eta (.step y .dia) A (Ctx.ref_diaIn_of hy)) _ hmem
  obtain rfl : hr.data.A = A := by
    have := (hr.data.hdeclOf i' ⟨A, hy⟩).symm.trans hy
    simpa using this
  have hm : B.frame.reflAcc hT s ∈ B.extent s y := Or.inr ⟨B.irrefl s, hr⟩
  refine ⟨⟨B.rden s hr.data.i₀ (Ctx.Le.refl _) (Term.eta y (.VTypeDia hr.data.A) hr.data.hd₀),
      definable_rden _ _⟩, hm, _, ⟨i', _, Term.mono ((B.w s).le hi) t⟩, ?_, ?_,
      rel_here hT ⟨_, hy⟩ (Term.eta (.step y .dia) hr.data.A (Ctx.ref_diaIn_of hy)) _ hr hmem⟩
  · have hc : B.toDom _ s (B.rden s hr.data.i₀ (Ctx.Le.refl _) hr.data.t₀) (definable_rden _ _) =
        (B.posEval ⟨B.rden s hr.data.i₀ (Ctx.Le.refl _)
          (Term.eta y (.VTypeDia hr.data.A) hr.data.hd₀), definable_rden _ _⟩).2
          ⟨B.frame.reflAcc hT s, hm⟩ :=
      toDom_congr (rden_eta_real hr hr.data.hd₀ _).symm _ _
    rw [rden_realTerm_eta hr (Ctx.Le.refl _) ⟨_, hy⟩ (Ctx.ref_diaIn_of hy) _ _, ← hc,
      fromDom_toDom]
  · exact (rden_lift hi t).trans ht

/-! ## Rows 3–4: every object is the content of a possible object along the way back -/

/-- A denoting term depends on its term only as a dependent pair. -/
theorem dterm_congr {s : B.W} {i : ℕ} {A : VarType} {a a' : Ann A}
    {t : Term σ ((B.w s).ctx i) A a} {t' : Term σ ((B.w s).ctx i) A a'}
    (h : (⟨a, t⟩ : Σ b, Term σ ((B.w s).ctx i) A b) = ⟨a', t'⟩) :
    (⟨i, a, t⟩ : Canon.DTerm (B.w s).sys (B.w s).T A) = ⟨i, a', t'⟩ := by
  cases h
  rfl

/-- ⭐⭐**Rows 3–4: along any arrow, every object at its target is, up to `Ind`, the content of a
    possible object at its source** (`Model.posBack_exists`; docs §11.23, paper check 2).  Along
    the world's own arrow it is strong T's `posRet_exists` (`ModalSys.WCoh`).  Along a network
    arrow `v → w`: the object is a term `t` at `w`; `w` has a carrier `c` with `Back(c, t)`
    (`Proof.backEx`, Henkin witnessing); the arrow is labelled by a witness `ω` (`BData.lab`); the
    possible object `◇_ω (c's image).box` has the arrow in its extent, and its content there is
    `c`'s round trip, which is `t`'s class (`BData.backRel`). -/
theorem posBack_exists_canon [ModalSys.WCoh] (hS : ModalSys.BStrong = true)
    (hW : ModalSys.BStrongW = true) {A : VarType} {w v : B.W} (b : B.frame.R v w)
    (o : B.frame.Dom A w) :
    ∃ (p : B.frame.Pos A v) (hm : (⟨w, ⟨b⟩⟩ : B.frame.Acc v) ∈ (B.posEval p).1),
      B.Ind ((B.posEval p).2 ⟨⟨w, ⟨b⟩⟩, hm⟩) o := by
  rcases b with hR | ⟨hT, rfl⟩
  swap
  · exact B.posRet_exists_canon hT (ModalSys.WCoh.strongT hW hT) o
  -- the object, and its carrier at `w`
  obtain ⟨i, a, t, ht⟩ := B.definable_fromDom A w o
  have hdia : (OutLeg.nec : OutLeg ((B.w w).ctx i)).dia (.top : WFF σ _ 0) ∈ (B.w w).M i := by
    refine ((B.w w).mcs i).neg_mem_iff.mpr fun hbox => ?_
    exact ((B.w v).mcs _).neg_mem_iff.mp (B.tr (B.symm hR) i _ hbox) ((B.w v).mcs _).top_mem
  have hex : WFF.backEx hS t ∈ (B.w w).M i :=
    BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hdia)
      ⟨Proof.backEx hS t _ (ctxOf_fresh le_rfl) (Proof.lookup List.mem_cons_self)⟩
  obtain ⟨j, hij, c, hc, hm⟩ := (B.w w).exW hex
  have hm' : WFF.back hS .nec (Term.eta (.root (.free c)) (.VTypeBox (.VTypeBox A)) hc)
      (Term.mono ((B.w w).le hij) t) ∈ (B.w w).M j := by
    convert hm using 1
    refine Eq.symm ((congrArg (WFF.instantiate _ _) ?_).trans
      (WFF.instantiate_backAt_slot hS (Term.mono ((B.w w).le hij) t) _))
    refine WFF.back_congr' hS .nec (Term.mono_eta _ _ _ _) ?_
    simp only [Term.mono_mono]
  have hrel := B.backRel hS
    (Term.eta ((VarSymb.root (.free c)).inner).inner A (Ctx.ref_inner (Ctx.ref_inner hc)))
    (Term.mono ((B.w w).le hij) t) hm' (B.symm hR)
  -- the label of the arrow, and the possible object
  obtain ⟨ω, Ω, hlb, i₀, hω⟩ := B.lab hS hW hR
  set K := max i₀ (B.stg w v j) with hK
  have hK₀ : B.stg w v j ≤ K := le_max_right _ _
  have hωK : ((B.w v).ctx K).ref ω = some (.VTypeDia Ω) := ((B.w v).le (le_max_left _ _)).ref hω
  have hstg := B.stg_mono hR hK₀
  have hmem : (⟨w, ⟨Or.inl hR⟩⟩ : B.frame.Acc v) ∈ B.extent v ω := Or.inl ⟨Ω, hlb⟩
  -- the carrier's image at `v`, and the possible object's body
  set u₀ : Term σ ((B.w v).ctx (B.stg w v j)).boxIn A _ :=
    Term.subst (arrowIdx (B.img w v)) (arrowS σ _ (B.img w v)).box
      (Subst.ok_box (ok_arrowS (B.imgOk (B.symm hR) j)))
      (Subst.coh_box (ok_arrowS (B.imgOk (B.symm hR) j)) (coh_arrowS (B.imgOk (B.symm hR) j)))
      (Term.eta ((VarSymb.root (.free c)).inner).inner A (Ctx.ref_inner (Ctx.ref_inner hc)))
    with hu₀
  have hL : ((B.w v).ctx (B.stg w v j)).boxIn.Le (((B.w v).ctx K).diaIn ω) :=
    ((B.w v).le hK₀).boxIn.trans (Ctx.le_boxIn_diaIn _ ω)
  -- its content along the arrow is the carrier's round trip, lifted
  have e : (⟨_, Term.subst (arrowXIdx (B.img v w) ω (B.cx v w ω))
        (arrowXS σ ((B.w w).ctx (B.stg v w K)) (B.img v w) ω (B.cx v w ω))
        (B.arXOk ⟨Ω, hlb⟩ K ⟨Ω, hωK⟩) (B.arXCoh ⟨Ω, hlb⟩ K ⟨Ω, hωK⟩) (Term.mono hL u₀)⟩ :
        Σ b, Term σ ((B.w w).ctx (B.stg v w K)) A b) =
      ⟨_, Term.mono ((B.w w).le hstg) (Term.subst (arrowIdx (B.img v w))
        (arrowS σ ((B.w w).ctx (B.stg v w (B.stg w v j))) (B.img v w))
        (ok_arrowS (B.imgOk hR (B.stg w v j))) (coh_arrowS (B.imgOk hR (B.stg w v j))) u₀)⟩ := by
    rw [Term.subst_mono, Term.mono_subst]
    refine Term.subst_congr _ _ _ _ _ _ ?_ u₀
    rw [arrowS_mono]
    exact sim_arrowXS_arrowS (fun _ _ => rfl)
  refine ⟨⟨B.rden v K (Ctx.Le.refl _) (Term.diatm ω ⟨Ω, hωK⟩ (Term.mono hL u₀)),
      definable_rden _ _⟩, hmem,
    ⟨B.stg v w K, _, Term.subst (arrowXIdx (B.img v w) ω (B.cx v w ω))
      (arrowXS σ _ (B.img v w) ω (B.cx v w ω)) (B.arXOk ⟨Ω, hlb⟩ K ⟨Ω, hωK⟩)
      (B.arXCoh ⟨Ω, hlb⟩ K ⟨Ω, hωK⟩) (Term.mono hL u₀)⟩, ⟨i, a, t⟩, ?_, ht, ?_⟩
  · change _ = B.fromDom A w (B.toDom A w _ _)
    rw [fromDom_toDom]
    exact (rden_diatm_net _ _ _ ⟨⟨w, ⟨Or.inl hR⟩⟩, hmem⟩ ⟨Ω, hlb⟩).symm
  · rw [B.dterm_congr e]
    exact ((Canon.DTerm.rel_lift _ hstg).symm.trans hrel).trans
      (Canon.DTerm.rel_lift (⟨i, a, t⟩ : Canon.DTerm (B.w w).sys (B.w w).T A) hij).symm

/-- ⭐The canonical model. -/
noncomputable def model : Model.{0, 0} σ where
  frame := B.frame
  necEval := B.necEval
  nec_inj := fun h => B.necEval_injective h
  RootPoss _ := VarSymb
  posFull p := B.posFull p
  posFull_inj := fun h => B.posFull_injective (Prod.ext (congrArg Prod.fst h :)
    (funext fun hSh => congrFun (congrArg Prod.snd h) hSh))
  ops := B.ops
  necMap_eval g _ a := (B.eval_toDom g a.1 _ _).symm
  necPair_eval _ _ _ := rfl
  posMap_full g _ := Prod.ext
    (congrArg (Sigma.mk _) (funext fun a => (B.eval_toDom g a.1.1 _ _).symm)) rfl
  posStrength_full n _ := Prod.ext rfl (funext fun hSh =>
    congrArg (fun z => Shp.dia _ (Shp.prod z _)) (congrArg Arrows.transposeShp (funext fun s =>
      (B.domShape_toDom hSh _ s.1 (n.1 s)
        (definable_box_apply n.2 s)).symm)))
  necExtract_eval _ _ := rfl
  necDup_eval hF _ _ _ := (noFour hF).elim
  posRet_exists hT hS a := B.posRet_exists_canon hT hS a
  posSerial hDS s := B.posSerial_canon hDS s
  Ret S val o := B.Ret S val o
  Ret_fwd := by intro _ _ hS _ _ _ h; exact B.ret_fwd hS h
  Ret_conv := by intro _ _ _ hA _ _ _ h; exact Or.inl ⟨hA, h⟩
  backRet_exists hS hne o := B.backRet_exists_canon hS hne o
  posBack_exists hS hW b o := B.posBack_exists_canon hS hW b o
  Ind o o' := B.Ind o o'
  Ind_refl o := B.Ind_refl o

end BData

end BArrow

end V12M
